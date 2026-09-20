/- ========================================================================= -/
/-                     Schedule/Writeback.lean                               -/
/-  写回仲裁（writeback.scala）的 Lean 4 模型、测试与证明                       -/
/-                                                                           -/
/-  核心交付：I-9（FloatRegFileBank 旁路不看写掩码，RegFile.lean Q1）的可达性    -/
/-  核销——"记分板 busy 清除拍 vs 寄存器堆写拍"时序链的形式化证明：              -/
/-  写回 fire 拍 = bank 写拍 = busy 清除拍（同拍），清除下拍可见，               -/
/-  依赖指令的读地址最早在写拍 +1 呈现，永远错过旁路窗口 ⇒ I-9 不可达。         -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    pipeline/writeback.scala（Writeback :44-107；Branch_back :18-36）        -/
/-    chisel v6.4.0 util/Arbiter.scala：class Arbiter（固定优先级，纯组合，      -/
/-      无状态；chosen 默认 n-1、valid 从低到高 last-connect-wins；             -/
/-      grant = ArbiterCtrl(valid)；in.ready(i) = grant(i) && out.ready；      -/
/-      out.valid = !grant.last || in.last.valid）                             -/
/-    chisel v6.4.0 util/Decoupled.scala：Queue.apply 的 entries==0 分支       -/
/-      （deq.valid := enq.valid; deq.bits := enq.bits; enq.ready := deq.ready -/
/-      ——零深度队列 = 纯组合直连）                                            -/
/-  例化点（活代码判定，全仓 grep 核实）：                                      -/
/-    Writeback(6,6) ← pipe.scala:84；in_x(0..5) ← alu/fpu/lsu2wb/csr/sfu/mul -/
/-      （pipe.scala:416-421）；in_v(0..5) ← valu/fpu/lsu2wb/sfu/mul/tc        -/
/-      （pipe.scala:422-427）；out_x/out_v → operandCollector                 -/
/-      （pipe.scala:288-289）。Branch_back ← pipe.scala:130（in0=alu.out2br   -/
/-      :392，in1=simt_stack.fetch_ctl :388，out=warp_sche.branch :148）。     -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. writeback.scala:52-59 的 Queue.apply(io.in_*(i), 0) 是零深度队列，     -/
/-      chisel v6.4.0 Decoupled.scala 的 Queue.apply 对 entries==0 生成为      -/
/-      纯组合直连（valid/bits/ready 三根线对穿）。模型中不建模任何队列状态。  -/
/-      后果：Writeback 全模块无寄存器，执行单元 out fire 拍 = wb out fire 拍。-/
/-  D2. chisel `Arbiter`（writeback.scala:60-61）是固定优先级组合仲裁器        -/
/-      （不是 RRArbiter，无 lastGrant 寄存器）：chosen = 最低 valid 下标，     -/
/-      无 valid 时默认 n-1。复用 RRArbiter.lean 的 rraCtrl/rraFindNat/        -/
/-      rraLoopNat 机制（rra 前缀），wbArb 前缀为本文件的固定优先级版本。      -/
/-  D3. payload 建模为抽象类型 α：仲裁逻辑只依赖 valid 向量（BitVec n）。      -/
/-      WriteScalarCtrl/WriteVecCtrl 的具体字段只在 I-9 链接线语义中出现      -/
/-      （wvd/wxd/reg_idxw/wvd_mask/wb_wvd_rd，见第 4 节）。                   -/
/-  D4. SPIKE_OUTPUT 的 printf（writeback.scala:30-35,67-81）与 GVM_ENABLED    -/
/-      观测逻辑（:82-107，默认关闭）只读不写数据通路，不建模。                -/
/-  D5. I-9 链的连线事实（均已逐行核实）：                                     -/
/-        out.ready 恒 true（operandCollector.scala:623-624）⇒ fire = valid； -/
/-        bank 写使能 rdwen = wvd && valid（向量 :621）/                        -/
/-        wxd && valid && reg_idxw.orR（标量 :620）——同拍写；                  -/
/-        busy 清除 = wb out fire（pipe.scala:271-272 → scoreboard.scala:110,  -/
/-        112）——同拍注册、下拍可见；                                          -/
/-        发射门控 warp_ready = !(scoreboard_busy | ...)（warp_schedule.scala:  -/
/-        181，scoreboard_busy = scoreb.delay，pipe.scala:161,222-224）。      -/
/-  D6. I-9 链的形式化前提（A1-A4，超出本文件范围的系统级事实，作为假设记录）：-/
/-        A1 同物理 bank 地址 ⇒ 同 warp（vgpr/sgpr 按 warp 分配不相交区间）；  -/
/-        A2 warp 内发射顺序 = 程序序，记分板 delay 读 _r 非旁路视图            -/
/-          （Scoreboard.lean D3，sbRead 读当前 _r）；                         -/
/-        A3 OpCol 串行化（scoreboard.scala:115-118 + pipe.scala:262-268）：   -/
/-          同 warp 前序指令离开 collector（out fire，读全部完成）之前，        -/
/-          后续指令被 read_op_colV/X 阻塞 ⇒ 写拍 W 不会有同 warp 前序指令的   -/
/-          迟到读撞上同地址（WAR/乱序读排除）；                               -/
/-        A4 写回通路全组合（D1 + Arbiter 无状态 + out.ready≡true）⇒ 执行单元  -/
/-          fire 拍 = bank 写拍 = busy 清除拍，无中间寄存器使 bank 写晚于清除。 -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1. Writeback 用固定优先级 Arbiter（非 RR）：in_x(5)=mul、in_v(5)=tc 等    -/
/-      低优先级源在高优先级源持续 valid 时会被饿死。各执行单元通常在 out     -/
/-      fire 前保持 valid（否则数据丢失——那是更严重的违约），在实际机器中     -/
/-      高优先级源不会无限连续产出，故属性能隐患而非功能 bug。记录。           -/
/-  Q2. 向量 bank 旁路（regfile.scala:57-58）在本文件所证协议下恒不触发       -/
/-      （没有任何读与写同拍同址，见第 4 节）——旁路是死硬件；I-9（RegFile.    -/
/-      lean Q1 的旁路/mem 发散）随之不可达。若未来改动破坏 A1-A4（如          -/
/-      collector 流水化使读提前到写拍），需重审。                            -/
/-  Q3. Branch_back 的固定优先级使 in0（alu.out2br）恒优先于 in1（simt_       -/
/-      stack.fetch_ctl）：alu 分支持续产生时 SIMT 汇合点回传会饿死。同 Q1，  -/
/-      记录。                                                               -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.Handshake
import Ventus.Schedule.Scoreboard
import Ventus.Schedule.RRArbiter
import Ventus.Arith.RegFile
import Std.Tactic.BVDecide

namespace Ventus.Schedule

open Ventus.Arith
open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 固定优先级仲裁器 wbArb（chisel Arbiter，writeback.scala:60-61）          -/
/- ========================================================================= -/

/-- grant（Arbiter.scala 的 ArbiterCtrl(io.in.map(_.valid))）：
    grant(i) = 前 i 项 valid 全 false。复用 rraCtrl（语义由 rraCtrl_eq_true_iff 钉死）。 -/
def wbArbGrant {n : Nat} (v : BitVec n) (i : Fin n) : Bool :=
  rraCtrl (fun j => v.getLsbD j) i.val

/-- grant 语义：grant(i) ⟺ i 之前无 valid -/
theorem wbArbGrant_eq_true_iff {n : Nat} (v : BitVec n) (i : Fin n) :
    wbArbGrant v i = true ↔ ∀ j, j < i.val → v.getLsbD j = false :=
  rraCtrl_eq_true_iff

/-- 硬件形式 chosen（Arbiter.scala：`io.chosen := (n-1).asUInt` 默认，
    `for (i <- n-2 to 0 by -1) when(in(i).valid) chosen := i`——last-connect-wins
    ⇒ 最低 valid 下标）。复用 rraLoopNat。 -/
def wbArbChoiceHw {n : Nat} (v : BitVec n) : Nat :=
  rraLoopNat (fun j => v.getLsbD j) (n - 1) (n - 2)

/-- 语义形式 chosen：最低 valid 下标（无 valid 时默认 n-1） -/
def wbArbChoiceNat {n : Nat} (v : BitVec n) : Nat :=
  (rraFindNat (fun j => v.getLsbD j) 0 n).getD (n - 1)

/-- 桥接定理：硬件循环形式 = 语义形式。
    注意硬件循环只覆盖 [0, n-1)，下标 n-1 由默认值覆盖——两种形式结果一致
    （只有 n-1 有效时两边都给 n-1）。 -/
theorem wbArbChoiceHw_eq {n : Nat} (v : BitVec n) :
    wbArbChoiceHw v = wbArbChoiceNat v := by
  unfold wbArbChoiceHw wbArbChoiceNat
  rw [rraLoopNat_spec]
  by_cases hn : n ≤ 1
  · cases n with
    | zero => cases h : v.getLsbD 0 <;> simp [rraFindNat, h]
    | succ n' =>
      cases n' with
      | zero => rfl
      | succ n'' => exact absurd hn (by omega)
  · have h1 : n - 2 + 1 = n - 1 := by omega
    rw [h1]
    generalize hp : (fun j => v.getLsbD j) = pv
    generalize hm : n - 1 = m
    have hnm : n = m + 1 := by omega
    rw [hnm, rraFindNat_succ]
    cases h : rraFindNat pv 0 m with
    | some j => rfl
    | none =>
      simp only [Nat.zero_add]
      cases hv : pv m <;> simp [hv]

/-- chosen 值恒 < n -/
theorem wbArbChoiceNat_lt {n : Nat} (v : BitVec n) (hn : 0 < n) :
    wbArbChoiceNat v < n := by
  unfold wbArbChoiceNat
  cases h : rraFindNat (fun j => v.getLsbD j) 0 n with
  | some j =>
    obtain ⟨hlo, hhi, -, -⟩ := rraFindNat_some_spec h
    simp [h]
    omega
  | none =>
    simp [h]
    omega

/-- io.chosen 的 Fin 形式 -/
def wbArbChoice {n : Nat} (hn : 0 < n) (v : BitVec n) : Fin n :=
  ⟨wbArbChoiceNat v, wbArbChoiceNat_lt v hn⟩

/-- io.out.valid（Arbiter.scala：`!grant.last || in.last.valid`）。
    grant.last = 前 n-1 项 valid 全 false。 -/
def wbArbOutValid {n : Nat} (v : BitVec n) : Bool :=
  !rraCtrl (fun j => v.getLsbD j) (n - 1) || v.getLsbD (n - 1)

/-- io.out.bits（`io.out.bits := in(chosen).bits`，组合直通） -/
def wbArbOutBits {n : Nat} {α : Type} (hn : 0 < n) (bits : Fin n → α) (v : BitVec n) : α :=
  bits (wbArbChoice hn v)

/-- io.in(i).ready（`in.ready := g && io.out.ready`） -/
def wbArbInReady {n : Nat} (v : BitVec n) (outReady : Bool) (i : Fin n) : Bool :=
  wbArbGrant v i && outReady

/-- io.in(i).fire = in(i).valid && in(i).ready -/
def wbArbInFire {n : Nat} (v : BitVec n) (outReady : Bool) (i : Fin n) : Bool :=
  v.getLsbD i.val && wbArbInReady v outReady i

/-- rraCtrl = false 的刻画：区间内存在请求 -/
theorem wbCtrl_false_iff {req : Nat → Bool} {k : Nat} :
    rraCtrl req k = false ↔ ∃ j, j < k ∧ req j = true := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    have ht : rraCtrl req k = true := by
      rw [rraCtrl_eq_true_iff]
      intro j hj
      cases hr : req j with
      | false => rfl
      | true => exact absurd ⟨j, hj, hr⟩ hne
    rw [ht] at h
    contradiction
  · intro ⟨j, hj, hrj⟩
    cases hc : rraCtrl req k with
    | false => rfl
    | true =>
      rw [rraCtrl_eq_true_iff] at hc
      rw [hc j hj] at hrj
      contradiction

/-- WB0：out.valid ⟺ 存在 valid 输入 -/
theorem wb_arb_out_valid {n : Nat} (hn : 0 < n) (v : BitVec n) :
    wbArbOutValid v = true ↔ ∃ i : Fin n, v.getLsbD i.val = true := by
  unfold wbArbOutValid
  constructor
  · intro h
    by_cases hc : rraCtrl (fun j => v.getLsbD j) (n - 1) = false
    · rw [wbCtrl_false_iff] at hc
      obtain ⟨j, hj, hvj⟩ := hc
      exact ⟨⟨j, by omega⟩, hvj⟩
    · have hct : rraCtrl (fun j => v.getLsbD j) (n - 1) = true := by
        generalize hb : rraCtrl (fun j => v.getLsbD j) (n - 1) = b
        cases b with
        | false => rw [hb] at hc; exact absurd rfl hc
        | true => rfl
      rw [hct] at h
      simp at h
      exact ⟨⟨n - 1, by omega⟩, h⟩
  · intro ⟨i, hvi⟩
    by_cases hi : i.val < n - 1
    · have hf : rraCtrl (fun j => v.getLsbD j) (n - 1) = false :=
        wbCtrl_false_iff.mpr ⟨i.val, hi, hvi⟩
      simp [hf]
    · have he : i.val = n - 1 := by omega
      have ht : v.getLsbD (n - 1) = true := he ▸ hvi
      simp [ht]

/-- WB1 互斥：单拍至多一个输入 fire -/
theorem wb_arb_mutex {n : Nat} (v : BitVec n) (r : Bool) (i j : Fin n)
    (hfi : wbArbInFire v r i = true) (hfj : wbArbInFire v r j = true) :
    i = j := by
  unfold wbArbInFire wbArbInReady at hfi hfj
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfi hfj
  obtain ⟨hvi, hgi, -⟩ := hfi
  obtain ⟨hvj, hgj, -⟩ := hfj
  rw [wbArbGrant_eq_true_iff] at hgi hgj
  by_cases h : i.val = j.val
  · exact Fin.ext h
  · rcases Nat.lt_or_gt_of_ne h with hij | hji
    · exfalso
      rw [hgj i.val hij] at hvi
      contradiction
    · exfalso
      rw [hgi j.val hji] at hvj
      contradiction

/-- WB2 选择正确性：有 valid 时 chosen 为最低 valid 下标（valid 且 ≤ 任何 valid 输入） -/
theorem wb_arb_choice_valid {n : Nat} (hn : 0 < n) (v : BitVec n) {i : Fin n}
    (hvi : v.getLsbD i.val = true) :
    v.getLsbD (wbArbChoice hn v).val = true ∧ (wbArbChoice hn v).val ≤ i.val := by
  have hfind : rraFindNat (fun j => v.getLsbD j) 0 n ≠ none := by
    intro hf
    have hf' := rraFindNat_none_spec hf i.val (Nat.zero_le _) (by simpa using i.isLt)
    rw [hf'] at hvi
    contradiction
  cases h : rraFindNat (fun j => v.getLsbD j) 0 n with
  | none => exact absurd h hfind
  | some j =>
    obtain ⟨hlo, hhi, hvj, hmin⟩ := rraFindNat_some_spec h
    have hcv : (wbArbChoice hn v).val = j := by simp [wbArbChoice, wbArbChoiceNat, h]
    refine ⟨by rw [hcv]; exact hvj, ?_⟩
    rw [hcv]
    by_cases hij : j ≤ i.val
    · exact hij
    · exfalso
      have hf := hmin i.val (Nat.zero_le _) (by omega)
      rw [hf] at hvi
      contradiction

/-- WB3 fire 完整性：out.fire（= chosen valid && out.ready）时，
    被消费的恰是 chosen 输入——chosen 同拍 fire（grant 与 chosen 对齐） -/
theorem wb_arb_fire_integrity {n : Nat} (hn : 0 < n) (v : BitVec n) (r : Bool)
    (hv : v.getLsbD (wbArbChoice hn v).val = true) :
    wbArbInFire v r (wbArbChoice hn v) = r := by
  have hg : wbArbGrant v (wbArbChoice hn v) = true := by
    rw [wbArbGrant_eq_true_iff]
    intro j hj
    cases h : rraFindNat (fun j => v.getLsbD j) 0 n with
    | some c =>
      obtain ⟨hlo, hhi, hvc, hmin⟩ := rraFindNat_some_spec h
      have hcv : (wbArbChoice hn v).val = c := by simp [wbArbChoice, wbArbChoiceNat, h]
      rw [hcv] at hj
      exact hmin j (Nat.zero_le _) hj
    | none =>
      have hcv : (wbArbChoice hn v).val = n - 1 := by simp [wbArbChoice, wbArbChoiceNat, h]
      rw [hcv] at hj
      exact rraFindNat_none_spec h j (Nat.zero_le _) (by omega)
  simp [wbArbInFire, wbArbInReady, hv, hg]

/-- WB4 进度：out.ready = true（实际连线，operandCollector.scala:623-624）时，
    任一 valid 输入存在的当拍，chosen 输入必 fire——写回不排队、不丢于本模块 -/
theorem wb_arb_progress {n : Nat} (hn : 0 < n) (v : BitVec n) {i : Fin n}
    (hvi : v.getLsbD i.val = true) :
    wbArbInFire v true (wbArbChoice hn v) = true := by
  rw [wb_arb_fire_integrity hn v true (wb_arb_choice_valid hn v hvi).1]

/- ========================================================================= -/
/- 2. 数值回归测试（先测试；全部 `by decide`；Writeback(6,6)，Branch_back n=2） -/
/- ========================================================================= -/

section WbRegressionTests

-- T1 无 valid：out.valid = false；chosen 默认 5（= n-1）
example : wbArbOutValid 0b000000#6 = false := by decide
example : wbArbChoiceNat 0b000000#6 = 5 := by decide

-- T2 单一 valid：chosen = 该下标；ready 时恰好它 fire
example : wbArbChoiceNat 0b000100#6 = 2 := by decide
example : wbArbOutValid 0b000100#6 = true := by decide
example : wbArbInFire 0b000100#6 true ⟨2, by decide⟩ = true := by decide
example : wbArbInFire 0b000100#6 true ⟨0, by decide⟩ = false := by decide

-- T3 多 valid：最低下标胜（固定优先级，非轮转）
example : wbArbChoiceNat 0b010100#6 = 2 := by decide
example : wbArbInFire 0b010100#6 true ⟨4, by decide⟩ = false := by decide
example : wbArbInFire 0b010100#6 true ⟨2, by decide⟩ = true := by decide
example : wbArbChoiceNat 0b111111#6 = 0 := by decide

-- T4 反压：out.ready = false 时无输入 fire，但 out.valid/choice 不变（纯组合）
example : wbArbInFire 0b000100#6 false ⟨2, by decide⟩ = false := by decide
example : wbArbOutValid 0b000100#6 = true := by decide

-- T5 Branch_back（writeback.scala:18-36）：n=2，in0（alu.out2br）优先
example : wbArbChoiceNat 0b11#2 = 0 := by decide
example : wbArbChoiceNat 0b10#2 = 1 := by decide
example : wbArbInFire 0b11#2 true ⟨0, by decide⟩ = true := by decide
example : wbArbInFire 0b11#2 true ⟨1, by decide⟩ = false := by decide

-- T6 硬件形式与语义形式在具体向量上一致（桥接定理的数值佐证）
example : wbArbChoiceHw 0b010100#6 = wbArbChoiceNat 0b010100#6 := by decide
example : wbArbChoiceHw 0b100000#6 = 5 := by decide
example : wbArbChoiceHw 0b000000#6 = 5 := by decide

end WbRegressionTests

/- ========================================================================= -/
/- 3. I-9 核销链：连线语义（D5）                                              -/
/- ========================================================================= -/

/-- wb out 的 ready 恒 true（operandCollector.scala:623-624 `io.writeVecCtrl.ready
    := true.B` / `io.writeScalarCtrl.ready := true.B`）⇒ out.fire = out.valid -/
def wbOutReady : Bool := true

/-- 向量 bank 写使能（operandCollector.scala:621：`rdwen := wvd & writeVecCtrl.valid`，
    ready≡true ⇒ valid = fire）：wb fire 拍即 bank 写拍 -/
def wbBankWenV (fire wvd : Bool) : Bool := wvd && fire

/-- 标量 bank 写使能（:620：多一个 `reg_idxw.orR`——x0 不写） -/
def wbBankWenX (fire wxd : Bool) (idxw : BitVec 8) : Bool :=
  wxd && fire && (idxw != 0#8)

/-- 发射门控（pipe.scala:222-224 + warp_schedule.scala:181）：
    warp 可发射 ⇒ scoreboard delay = 0。wbGateOpen = !delay -/
def wbGateOpen (delay : Bool) : Bool := !delay

/-- 连线语义：bank 写使能 = wvd && out.fire（ready≡true 的改写） -/
theorem wb_bank_wen_eq (valid wvd : Bool) :
    wbBankWenV (valid && wbOutReady) wvd = (wvd && valid) := by
  simp [wbBankWenV, wbOutReady]

/-- 连线语义（标量）：写 x0 被 orR 抑制 -/
theorem wb_bank_wen_x_x0 (fire wxd : Bool) :
    wbBankWenX fire wxd 0#8 = false := by
  simp [wbBankWenX]

/-- 发射门控语义：delay=1 ⇒ 不发射 -/
theorem wb_gate_closed_of_delay : wbGateOpen true = false := rfl

/-- I9-1 写拍门闭：wb fire 拍 W，busy(a) 在当前 _r 视图中仍为 1（清除是寄存器，
    W+1 才可见，scoreboard.scala:88-97），故读 a 的依赖指令（sel_alu1=A1_VRS1，
    reg_idx1=a）当拍 delay=1、不能发射。 -/
theorem wb_i9_gate_closed (s : SbState) (c : SbCtrl) (a : BitVec 8)
    (hbusy : sbRead false s.vectorReg a = true)
    (hsel : c.sel_alu1 = sbA1_VRS1) (hr1 : c.reg_idx1 = a) :
    wbGateOpen (sbDelay s c) = false := by
  have h1 : sbRead1 s c = true := by
    simp [sbRead1, hsel, hr1, sbA1_VRS1, sbA1_RS1, hbusy]
  simp [wbGateOpen, sbDelay, h1]

/-- I9-2 清除次拍可见：wb_v fire 清 a 后，下拍 vectorReg 在 a 处读为 0
    （Scoreboard.lean sb3_wb_clear 的重述；set 先于 clear，同拍同址 clear 胜） -/
theorem wb_i9_clear_visible (s : SbState) (i : SbInputs) (a : BitVec 8)
    (hbf : i.wb_v_fire = true) (hbw : i.wb_v_wvd = true) (hba : i.wb_v_idxw = a)
    (hns : (i.if_fire && i.if_ctrl.wvd && (i.if_ctrl.reg_idxw == a)) = false) :
    sbRead false (sbStep s i).vectorReg a = false :=
  sb3_wb_clear s i a hbf hbw hba hns

/-- I9-3 时序不等式：清除下拍可见（I9-1/I9-2）⇒ 依赖发射拍 tFire ≥ W+1；
    collector 在 control.fire 当拍即可组合呈现读地址（operandCollector.scala:
    103-118），即最早 tRead = tFire。故 tRead ≥ W+1——永远错过旁路窗口
    （旁路寄存器 RegNext(rd) 只在 W+1 有效，且需要 W 当拍呈现读地址）。 -/
theorem wb_i9_timing {tW tFire tRead : Nat} (hFire : tW + 1 ≤ tFire)
    (hRead : tFire ≤ tRead) :
    tW + 1 ≤ tRead :=
  Nat.le_trans hFire hRead

/-- I9-4 旁路触发的必要条件：bank 在拍 R+1 前递写数据，仅当拍 R 同拍出现
    同地址读写（rsidx = rdidx 且 rdwen）。即：依赖读要撞上旁路，必须在
    写拍 W 当拍呈现读地址。 -/
theorem wb_i9_bypass_same_cycle (s : RfVState) (i : RfVInputs)
    (h : (rfVStep s i).bypass = true) :
    i.rsidx = i.rdidx ∧ i.rdwen = true := by
  have hb : ((i.rsidx == i.rdidx) && i.rdwen) = true := h
  rw [Bool.and_eq_true, beq_iff_eq] at hb
  exact hb

/-- I9-5 主定理（I-9 不可达，向量 bank）：拍 W 写 a（掩码 m、数据 v），
    依赖读在拍 R ≥ W+1 呈现（rsidx = a）且该拍无写（rdwen = false）。
    则：(1) 旁路不触发（bypass = false）；(2) 读到的是 mem 中的掩码合并值
    （掩码 lane 取新值、被掩 lane 保留旧值）——而非旁路前递的完整新行。
    RegFile.lean Q1 的发散机制（rfV_bypass_mem_diverge）要求读在拍 W 呈现，
    被 I9-1/I9-2/I9-3 排除。 -/
theorem wb_i9_unreachable (rf : RfVState) (a c : BitVec 8) (v x : RfVRow)
    (m m' : RfVMask) (rsx : BitVec 8) (t : Fin 32) :
    (rfVStep (rfVStep rf ⟨rsx, a, v, true, m⟩) ⟨a, c, x, false, m'⟩).bypass = false ∧
    rfVOut (rfVStep (rfVStep rf ⟨rsx, a, v, true, m⟩) ⟨a, c, x, false, m'⟩) t =
      (if m t then v t else rf.mem a.toFin t) := by
  refine ⟨?_, ?_⟩
  · simp [rfVStep]
  · simp [rfVOut, rfVStep, rfVUpd, rfVRowUpd]

/-- I9-5 标量版：标量 bank 无写掩码（无发散机制），写后 ≥1 拍的读读到写入值 -/
theorem wb_i9_scalar (s : RfSState) (a c rsx : BitVec 8) (v x : BitVec 32) :
    rfSOut (rfSStep (rfSStep s ⟨rsx, a, v, true⟩) ⟨a, c, x, false⟩) = v := by
  simp [rfSOut, rfSStep, rf_read_write_same]

/-- I9 capstone：写回拍 W 的同时性——同拍 bank 写使能（D5）与 busy 清除注册
    （scoreboard.scala:110,112），且当拍依赖指令门闭（I9-1）、下拍清除可见
    （I9-2）。配合 I9-3/I9-4/I9-5，I-9 的旁路污染对记分板保护的依赖读不可达。 -/
theorem wb_i9_chain (s : SbState) (i : SbInputs) (c : SbCtrl) (a : BitVec 8)
    (hbusy : sbRead false s.vectorReg a = true)
    (hsel : c.sel_alu1 = sbA1_VRS1) (hr1 : c.reg_idx1 = a)
    (hbf : i.wb_v_fire = true) (hbw : i.wb_v_wvd = true) (hba : i.wb_v_idxw = a)
    (hns : (i.if_fire && i.if_ctrl.wvd && (i.if_ctrl.reg_idxw == a)) = false) :
    wbGateOpen (sbDelay s c) = false ∧
    sbRead false (sbStep s i).vectorReg a = false :=
  ⟨wb_i9_gate_closed s c a hbusy hsel hr1,
   wb_i9_clear_visible s i a hbf hbw hba hns⟩

/- ========================================================================= -/
/- 4. I-9 链数值回归测试（先测试后证明的测试侧；全部 `by decide`）             -/
/- ========================================================================= -/

section WbI9Tests

/-- 依赖指令 B 的控制字：读 v5（sel_alu1 = A1_VRS1, reg_idx1 = 5） -/
def wbI9CtrlB : SbCtrl := { sbCtrl0 with sel_alu1 := sbA1_VRS1, reg_idx1 := 5#8 }

/-- 拍 W-? ：生产者发射，置位 busy(v5) -/
def wbI9InIssueV5 : SbInputs :=
  { sbInNop with if_fire := true, if_ctrl := { sbCtrl0 with wvd := true, reg_idxw := 5#8 } }

/-- 拍 W：v5 写回 fire -/
def wbI9InWbV5 : SbInputs :=
  { sbInNop with wb_v_fire := true, wb_v_wvd := true, wb_v_idxw := 5#8 }

/-- busy(v5) 已置位的状态 -/
def wbI9S1 : SbState := sbStep sbInit wbI9InIssueV5

-- S1 写拍 W：busy(v5)=1，B 门闭（不能发射，读地址不可能在 W 呈现）
example : sbRead false wbI9S1.vectorReg 5#8 = true := by decide
example : wbGateOpen (sbDelay wbI9S1 wbI9CtrlB) = false := by decide

-- S2 拍 W+1：busy 清除可见，B 门开（最早发射拍）
example : wbGateOpen (sbDelay (sbStep wbI9S1 wbI9InWbV5) wbI9CtrlB) = true := by decide

-- S3 旁路机制的数值佐证：若读地址在写拍 W 同拍呈现（被 I9-1 排除的情形），
--    旁路确实触发且前递被掩 lane 的新值——机制存在但不可达
def wbI9RowNew : RfVRow := fun t => 0xAA00#32 + BitVec.ofNat 32 t.val
def wbI9Mask0 : RfVMask := fun t => decide (t.val = 0)   -- 只开 lane 0

example : (rfVStep rfVInit ⟨5#8, 5#8, wbI9RowNew, true, wbI9Mask0⟩).bypass = true := by decide
example : rfVOut (rfVStep rfVInit ⟨5#8, 5#8, wbI9RowNew, true, wbI9Mask0⟩) ⟨5, by decide⟩
    = 0xAA05#32 := by decide  -- 旁路前递被掩 lane 的新值（污染形态）

-- S4 实际链：拍 W 写 v5（只开 lane 0），拍 W+1 B 读 v5
def wbI9RfW : RfVState := rfVStep rfVInit ⟨0#8, 5#8, wbI9RowNew, true, wbI9Mask0⟩
def wbI9RfR : RfVState := rfVStep wbI9RfW ⟨5#8, 0#8, wbI9RowNew, false, wbI9Mask0⟩

-- 旁路不触发
example : wbI9RfR.bypass = false := by decide
-- 掩码 lane 0 读到新值
example : rfVOut wbI9RfR ⟨0, by decide⟩ = 0xAA00#32 := by decide
-- 被掩 lane 5 读到旧值（0）——未被旁路污染，与 S3 的 0xAA05 形成对照
example : rfVOut wbI9RfR ⟨5, by decide⟩ = 0#32 := by decide

-- S5 标量版数值佐证
example : rfSOut (rfSStep (rfSStep rfSInit ⟨0#8, 5#8, 0xDEADBEEF#32, true⟩)
    ⟨5#8, 0#8, 0#32, false⟩) = 0xDEADBEEF#32 := by decide

-- S6 连线：x0 不写标量 bank；向量写使能 = wvd && fire
example : wbBankWenX true true 0#8 = false := by decide
example : wbBankWenX true true 4#8 = true := by decide
example : wbBankWenV true true = true := by decide
example : wbBankWenV true false = false := by decide

end WbI9Tests

/- ========================================================================= -/
/- 5. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms wb_arb_mutex
#print axioms wb_arb_choice_valid
#print axioms wb_arb_fire_integrity
#print axioms wb_arb_progress
#print axioms wb_i9_gate_closed
#print axioms wb_i9_clear_visible
#print axioms wb_i9_unreachable
#print axioms wb_i9_scalar
#print axioms wb_i9_chain

end Ventus.Schedule
