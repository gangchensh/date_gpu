/- ========================================================================= -/
/-                 Schedule/OperandCollector.lean                            -/
/-  操作数收集器顶层（operandArbiter / crossBar / instDemux / 写回 /          -/
/-  DualIssueIO，WP2 收官下半）的 Lean 4 模型、测试与证明                       -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/                    -/
/-      operandCollector.scala                                                -/
/-    operandArbiter   :329-378（2×num_bank 个 RRArbiter(n=32) + valid 过滤） -/
/-    crossBar         :380-435（纯组合路由；chosen/valid 经 RegNext 与         -/
/-                      SyncReadMem 1 拍延迟对齐，:549-552）                   -/
/-    instDemux        :440-517（num_warp=8>1 ⇒ :495-512 分支）               -/
/-    operandCollector :518-672（顶层连线 + 写回 :593-624 + DualIssueIO        -/
/-                              :627-664）                                    -/
/-  collectorUnit 本体见 Schedule/CollectorUnit.lean（本文件复用其            -/
/-  CuCtrl/CuState/cuStep/cuRun/cuInit/cuWmask_deadlock 等，模型前缀 cu）。   -/
/-  参数（top/parameters.scala，同 CollectorUnit.lean 头部，已核实）：         -/
/-    num_bank=4 num_collectorUnit=num_warp=8 depth_regBank=8 xLen=32         -/
/-    sgpr_base 12 位 vgpr_base 11 位 widSliceHigh=1 num_thread=32            -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 规模：仲裁/crossbar/写回/DualIssue 按真实配置（8 CU、4 bank、32 路     -/
/-      仲裁）建模；I-4 witness（第 8 节）用 2 CU 缩放配置——机制（demux 只    -/
/-      按 CU ready 分配 + CU 三态机）与规模无关，偏离在此注明。              -/
/-  D2. 仲裁器复用 Schedule/RRArbiter.lean 的 rra 模型（n=4*8=32，:340/:344）；-/
/-      每 bank 一对标量/向量仲裁器，各自独立 lastGrant（Fin 32）。            -/
/-  D3. 32 路过滤后 valid 打包为 BitVec 32（ocPack）：Chisel 侧是 32 根独立    -/
/-      线分别接 io.in(p).valid（:362-365），与"bit p = 过滤函数 f p"等价，    -/
/-      由桥接引理 ocPack_getLsbD 钉死。                                       -/
/-  D4. RegNext（:549-552）与 SyncReadMem 1 拍读延迟不显式建模：crossbar 定    -/
/-      理对"任意一拍的 chosen/valid/data 输入"全称量化，组合正确性对寄存后    -/
/-      的值逐拍成立；chosen/valid 与读数据同拍对齐由 :549-552 的同 RegNext    -/
/-      结构保证（属集成事实，不在本文件证明范围内）。                          -/
/-  D5. instDemux 只建 :495-512（num_warp>1）分支；:456-457 priorityXorV 与    -/
/-      :465/:475/:484 的 outX_sel_oh 在该分支无消费者（:500 outX_sel 由       -/
/-      PriorityEncoder 直算），不建模。:497-499 语义：outV_sel=最低 ready     -/
/-      CU；outReady2 = outReady1 去掉 outV_sel 位（outV_sel_oh 全 0 时 ~后    -/
/-      全 1，行为一致，Q7）；outX_sel = outReady2 的最低置位位。              -/
/-  D6. widCmp 恒 0（:565-568）且 instDemux 体内无消费者（:440-517 不出现      -/
/-      widCmp）——死输入，不建模（I-4 报告已记，此处复核确认）。               -/
/-  D7. :366 的 readArbiterIO(j)(k).ready（num_bank 循环 last-connect-wins ⇒   -/
/-      恒为 bank3 标量仲裁器的 in.ready）建模为仲裁器输出之一；消费方核查     -/
/-      见 Q4（结论：无消费者，死逻辑）。                                      -/
/-  D8. 写回地址宽度处理同 CollectorUnit D3：sgpr_base(12 位)>>>2 取低 8 位    -/
/-      后与 reg_idxw(8 位)>>>2 在 8 位内相加（= 数学和的低 8 位，即 :606      -/
/-      赋值给 depth_regBank=8 位 Wire 的截断语义）。bankID（:603/:605）为     -/
/-      2 位截断加法（mod 4，与读侧 :103-105 同式）。vgpr_base 11 位 >>>2      -/
/-      取低 8 位同理（:604）。                                               -/
/-  D9. DualIssueIO 的 issueIO 全载荷不重建；inst_is_vec（:634-647）建模为     -/
/-      其触及的控制字段切片 OcExCtrl（tc/fp/mul/sfu/mem/csr(2 位)/barrier/    -/
/-      isvec，字段类型 scoreboard.scala:19-65，已核实 csr 为 UInt(2.W)）。    -/
/-  D10. bank 读数据（scalarBank(i).rs / vectorBank(i).rs/v0，:554-556）抽象   -/
/-      为 crossbar 输入；寄存器堆模型见 Arith/RegFile.lean（rf 前缀）。       -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类，I-4 乱序发射收口】instDemux 只按 CU control.ready 分配、不比     -/
/-      较 wid（:566 比较逻辑被注释、:567 恒 0，D6）：同 warp 的后到指令可     -/
/-      占据另一 CU、先集齐操作数而先发射（该 warp 程序序被打乱）。witness     -/
/-      定理 ocI4_*（native_decide，2 CU 缩放，D1）。                         -/
/-  Q2【I 类，I-12 死锁链收口】:362-365 只放行 rsType=1/2 ⇒ mask 读请求       -/
/-      （rsType(3)≡0，CollectorUnit Q1/cuRsTypeWire :214）在全部 8 个仲裁     -/
/-      器上过滤后 valid=false ⇒ 永不授予 ⇒ crossbar 端口 3 对该 CU 永不置    -/
/-      valid ⇒ CU 永不收 regOrder=3 返回 ⇒ cuWmask_deadlock 的前提成为系     -/
/-      统事实，死锁链闭环（ocI12_* 系列，第 4 节）。                           -/
/-  Q3【I 类，I-11 截断收口】:606 wbScaBankAddr 8 位截断：sgpr_base≥1024 的   -/
/-      warp 标量写回回绕别名到 bank 内低 256 项（读侧 :110-125 同公式，       -/
/-      CollectorUnit D3 已按 8 位建模，本文件 ocI11_read_witness 复证）。     -/
/-      定理 ocI11_*（bv_decide）。                                           -/
/-  Q4【I 类，死逻辑】:366 ready 错接无消费方（E2）。证据：collectorUnit 体    -/
/-      内 outArbiterIO 只出现于 :103-137 的 bits/valid 驱动（已对源码逐行     -/
/-      核对）；模型层面 CuInputs 无仲裁 ready 字段——结构性无消费者。即       -/
/-      使被消费也是错值：应为"本 bank 本类型仲裁器"的 in.ready，实际恒为     -/
/-      bank3 标量仲裁器的。                                                  -/
/-  Q5【E1】:545-546 readArbiterOut*.ready 恒 true ⇒ 读仲裁无反压，           -/
/-      rra3_not_stable（RRArbiter 非 Irrevocable）在此无害：out.valid 当拍     -/
/-      即被消费，不存在"反压期间锁存 bits"的用法。DualIssueIO 的 arb_x/       -/
/-      arb_v（:650-663）下游有反压，但 CU 在 s_out 的 issue.valid/bits 稳     -/
/-      定（ocE1_cu_issue_stable：s_out 拍只清 valid/ready 寄存器，            -/
/-      :258-262；rsReg/controlReg 不动）⇒ 仲裁输入 valid 向量与 bits 在反    -/
/-      压期间整体稳定 ⇒ chosen/out.bits 稳定（ocE1_dual_stable）⇒ 满足       -/
/-      Decoupled 契约。结论：两处例化均合法，非 Irrevocable 无实际影响。      -/
/-  Q6【E3】crossbar 标量/向量两个 when 块（:416-429）同拍同写 out(j)(k)       -/
/-      不可能：需要两笔 grant 的 chosen 同为 4j+k（同一请求下标），但该请     -/
/-      求的 rsType 不能既 =1（标量过滤 :363）又 =2（向量过滤 :365）。形式     -/
/-      化：ocE3_no_clash。同 bank 内 :416 与 :423 双写同理排除。              -/
/-  Q7【观察】:499 outReady2 = outReady1 & ~outV_sel_oh：outV_sel_oh 为        -/
/-      one-hot（:497 PriorityEncoderOH），全 0 输入时 oh=0、~后全 1，         -/
/-      outReady2=outReady1=0，与"去掉最低 ready 位"语义一致（模型 ocDemux     -/
/-      按此建模，数值测试覆盖）。                                            -/
/-  Q8【观察】:369-373 readchosen* 直接接仲裁器 chosen（未寄存），:549-552     -/
/-      在顶层做 RegNext 对齐——chosen 跨模块以组合路径穿过，时序上依赖同      -/
/-      级寄存，功能建模无影响，仅记录。                                      -/
/- ========================================================================= -/

import Ventus.Schedule.CollectorUnit
import Ventus.Schedule.RRArbiter
import Ventus.Arith.RegFile
import Std.Tactic.BVDecide

namespace Ventus.Schedule

open Ventus.Arith (rfIMM_I)

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 基础辅助：valid 打包 ocPack、最低置位位 ocPrioLowest、或归约 ocOrR        -/
/- ========================================================================= -/

/-- valid 打包（D3）：`(ocPack f n).getLsbD i = f i`（i < n）。
    用 `2^m` 置位（= `1#n <<< m`，m < n 时等价，取前者便于引理证明）。 -/
def ocPack {n : Nat} (f : Fin n → Bool) : Nat → BitVec n
  | 0 => 0#n
  | m + 1 =>
    if h : m < n then
      (if f ⟨m, h⟩ then ocPack f m ||| BitVec.ofNat n (2 ^ m) else ocPack f m)
    else ocPack f m

/-- 2^m 的位读（m < n 时恰为第 m 位） -/
theorem ocPow2_getLsbD {n m j : Nat} (hm : m < n) :
    (BitVec.ofNat n (2 ^ m)).getLsbD j = decide (j = m) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hjm : j = m
  · subst hjm
    rw [Nat.testBit_two_pow_self]
    simp [hm]
  · rw [Nat.testBit_two_pow_of_ne (by omega : m ≠ j)]
    simp [hjm]

/-- 打包桥接引理（D3）：前 m 位恰好是 f 的前 m 项 -/
theorem ocPack_getLsbD_lt {n : Nat} (f : Fin n → Bool) {m j : Nat} (hm : m ≤ n) :
    (ocPack f m).getLsbD j = (if h : j < m then f ⟨j, by omega⟩ else false) := by
  induction m with
  | zero => simp [ocPack]
  | succ m ih =>
    have hmn : m < n := by omega
    have ihm : m ≤ n := by omega
    simp only [ocPack, dif_pos hmn]
    by_cases hf : f ⟨m, hmn⟩ = true
    · rw [if_pos hf, BitVec.getLsbD_or, ih ihm, ocPow2_getLsbD hmn]
      by_cases hjm : j < m + 1
      · rw [dif_pos hjm]
        by_cases hjm2 : j = m
        · subst j
          rw [dif_neg (by omega : ¬ m < m)]
          simp [hf]
        · rw [dif_pos (by omega : j < m)]
          simp [hjm2]
      · rw [dif_neg hjm, dif_neg (by omega : ¬ j < m)]
        simp [show j ≠ m by omega]
    · rw [if_neg hf, ih ihm]
      by_cases hjm : j < m + 1
      · rw [dif_pos hjm]
        by_cases hjm2 : j = m
        · subst j
          rw [dif_neg (by omega : ¬ m < m)]
          simp at hf
          exact hf.symm
        · rw [dif_pos (by omega : j < m)]
      · rw [dif_neg hjm, dif_neg (by omega : ¬ j < m)]

/-- 打包桥接引理（全宽形式）：bit j = f j -/
theorem ocPack_getLsbD {n : Nat} (f : Fin n → Bool) {j : Nat} (hj : j < n) :
    (ocPack f n).getLsbD j = f ⟨j, hj⟩ := by
  rw [ocPack_getLsbD_lt f (Nat.le_refl n), dif_pos hj]

-- 数值回归：打包语义
example : (ocPack (n := 8) (fun j => decide (j.val = 2 || j.val = 5)) 8) = 0b00100100#8 := by decide
example : (ocPack (n := 32) (fun j => decide (j.val % 4 = 3)) 32).getLsbD 7 = true := by decide
example : (ocPack (n := 32) (fun j => decide (j.val % 4 = 3)) 32).getLsbD 8 = false := by decide
example : (ocPack (n := 4) (fun _ => true) 4) = 0xF#4 := by decide

/-- 优先编码的 Nat 形式（PriorityEncoder/PriorityEncoderOH+OHToUInt 的共同语义：
    最低置位位下标；超出范围按 false 处理） -/
def ocPrioF {n : Nat} (f : Fin n → Bool) (j : Nat) : Bool :=
  if h : j < n then f ⟨j, h⟩ else false

/-- 最低置位位下标；全 false 时默认 0（Chisel PriorityEncoder(0.U)=0、
    OHToUInt(0.U)=0；:498/:500 的结果均被 orR 门控，默认值无害） -/
def ocPrioLowest {n : Nat} (f : Fin n → Bool) : Nat :=
  (rraFindNat (ocPrioF f) 0 n).getD 0

/-- 最低置位位规约：有 valid 时 ocPrioLowest 是首个 valid 的下标 -/
theorem ocPrioLowest_spec {n : Nat} (f : Fin n → Bool) (j : Fin n) (hj : f j = true) :
    ∃ c : Fin n, ocPrioLowest f = c.val ∧ f c = true ∧
      (∀ k : Fin n, k.val < c.val → f k = false) ∧ c.val ≤ j.val := by
  unfold ocPrioLowest
  cases hc : rraFindNat (ocPrioF f) 0 n with
  | none =>
    exfalso
    have hf := rraFindNat_none_spec hc j.val (Nat.zero_le _) (by omega)
    have heq : ocPrioF f j.val = f j := by simp [ocPrioF, j.isLt]
    rw [heq] at hf; simp [hf] at hj
  | some c =>
    obtain ⟨hlo, hhi, hvc, hmin⟩ := rraFindNat_some_spec hc
    have hcn : c < n := by omega
    refine ⟨⟨c, hcn⟩, rfl, ?_, ?_, ?_⟩
    · have heq : ocPrioF f c = f ⟨c, hcn⟩ := by simp [ocPrioF, hcn]
      rw [← heq]; exact hvc
    · intro k hk
      have hf := hmin k.val (by omega) hk
      have heq : ocPrioF f k.val = f k := by simp [ocPrioF, k.isLt]
      rw [heq] at hf; exact hf
    · rcases Nat.lt_or_ge j.val c with hgt | hge
      · have hf := hmin j.val (by omega) hgt
        have heq : ocPrioF f j.val = f j := by simp [ocPrioF, j.isLt]
        rw [heq] at hf; simp [hf] at hj
      · exact hge

/-- 全 false 时取默认值 0 -/
theorem ocPrioLowest_of_none {n : Nat} (f : Fin n → Bool) (h : ∀ j : Fin n, f j = false) :
    ocPrioLowest f = 0 := by
  unfold ocPrioLowest
  rw [rraFindNat_none_of_spec (fun k _ hkn => by
    have hkn' : k < n := by omega
    have heq : ocPrioF f k = f ⟨k, hkn'⟩ := by simp [ocPrioF, hkn']
    rw [heq]; exact h ⟨k, hkn'⟩)]
  rfl

-- 数值回归：优先编码
example : ocPrioLowest (n := 8) (fun j => decide (j.val = 3)) = 3 := by decide
example : ocPrioLowest (n := 8) (fun j => decide (j.val = 3 || j.val = 5)) = 3 := by decide
example : ocPrioLowest (n := 8) (fun _ => false) = 0 := by decide
example : ocPrioLowest (n := 2) (fun j => decide (j.val = 1)) = 1 := by decide

/-- 或归约（:501/:502 的 outReady*.orR） -/
def ocOrR {n : Nat} (f : Fin n → Bool) : Bool := (List.finRange n).any f

theorem ocOrR_eq_true_iff {n : Nat} (f : Fin n → Bool) :
    ocOrR f = true ↔ ∃ j : Fin n, f j = true := by
  constructor
  · intro h
    rw [ocOrR, List.any_eq_true] at h
    obtain ⟨j, -, hj⟩ := h
    exact ⟨j, hj⟩
  · intro ⟨j, hj⟩
    rw [ocOrR, List.any_eq_true]
    exact ⟨j, List.mem_finRange j, hj⟩

theorem ocOrR_eq_false_iff {n : Nat} (f : Fin n → Bool) :
    ocOrR f = false ↔ ∀ j : Fin n, f j = false := by
  constructor
  · intro h j
    by_cases hj : f j = true
    · have h' := (ocOrR_eq_true_iff f).mpr ⟨j, hj⟩
      rw [h'] at h; contradiction
    · cases hf : f j with
      | false => rfl
      | true => exact absurd hf hj
  · intro h
    by_cases h' : ocOrR f = true
    · obtain ⟨j, hj⟩ := (ocOrR_eq_true_iff f).mp h'
      rw [h j] at hj; contradiction
    · cases ho : ocOrR f with
      | false => rfl
      | true => exact absurd ho h'

-- 数值回归：或归约
example : ocOrR (n := 8) (fun j => decide (j.val = 3)) = true := by decide
example : ocOrR (n := 8) (fun _ => false) = false := by decide

/- ========================================================================= -/
/- 2. operandArbiter（:329-378）：valid 过滤、授予、bank 读地址连线             -/
/-    n = 4*num_collectorUnit = 32；in 与全部 CU 的 4 路请求一一连接            -/
/-    （:348-356，下标 p = CU 编号 j*4 + 操作数位 k）                           -/
/- ========================================================================= -/

/-- 过滤条件（:362-365）：bank i 的标量仲裁器只放行 rsType=1 且 bankID 匹配；
    向量仲裁器只放行 rsType=2 且 bankID 匹配。 -/
def ocScaFilt (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) : Fin 32 → Bool :=
  fun p => rv p && ((reqs p).bankID == BitVec.ofNat 2 i.val) && ((reqs p).rsType == 1#2)

def ocVecFilt (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) : Fin 32 → Bool :=
  fun p => rv p && ((reqs p).bankID == BitVec.ofNat 2 i.val) && ((reqs p).rsType == 2#2)

/-- 过滤后 valid 打包（bankArbiterScalar(i)/bankArbiterVector(i) 的 in.valid，:362-365） -/
def ocScaPack (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) : BitVec 32 :=
  ocPack (ocScaFilt reqs rv i) 32

def ocVecPack (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) : BitVec 32 :=
  ocPack (ocVecFilt reqs rv i) 32

/-- bank i 标量/向量仲裁器的 chosen（:372-373 经 rra 模型） -/
def ocScaChoice (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32) : Fin 32 :=
  rraChoice (by decide) (ocScaPack reqs rv i) lg

def ocVecChoice (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32) : Fin 32 :=
  rraChoice (by decide) (ocVecPack reqs rv i) lg

/-- bank i 标量/向量仲裁器的 out.valid（:369-371 经 rra 模型） -/
def ocScaOutValid (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32) : Bool :=
  rraOutValid (by decide) (ocScaPack reqs rv i) lg

def ocVecOutValid (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32) : Bool :=
  rraOutValid (by decide) (ocVecPack reqs rv i) lg

/-- :366 的 ready 错接（D7）：num_bank 循环 last-connect-wins ⇒ i=3 生效，
    所有请求的 ready 恒为 bank3 标量仲裁器的 in.ready（out.ready 恒 true，:545-546）。
    消费方核查结论（Q4）：CU 不读 outArbiterIO.ready（:101-137 只驱动 bits/valid），
    结构性无消费者——死逻辑，且即使被消费也是错值。 -/
def ocArbInReady366 (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (lg : Fin 32) (p : Fin 32) : Bool :=
  rraInReady (by decide) (ocScaPack reqs rv ⟨3, by decide⟩) lg true p

/- ---- A 链第 1 环：过滤（纯组合事实） ---- -/

/-- rsType=0 的请求对所有 bank 的两个仲裁器过滤后 valid=false（:362-365）。
    这是 I-12 死锁链的源头：mask 请求 rsType(3)≡0（:214）。 -/
theorem ocA_filter_rt0 (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (p : Fin 32)
    (h : (reqs p).rsType = 0#2) :
    ocScaFilt reqs rv i p = false ∧ ocVecFilt reqs rv i p = false := by
  simp [ocScaFilt, ocVecFilt, h]

/-- rsType=3（立即数）同样被全部过滤（:362-365 只放行 1/2） -/
theorem ocA_filter_rt3 (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (p : Fin 32)
    (h : (reqs p).rsType = 3#2) :
    ocScaFilt reqs rv i p = false ∧ ocVecFilt reqs rv i p = false := by
  simp [ocScaFilt, ocVecFilt, h]

/-- 标量过滤通过 ⇒ 原 valid 且 bankID 匹配且 rsType=1 -/
theorem ocA_filt_sca_eq_true (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (p : Fin 32) :
    ocScaFilt reqs rv i p = true →
      rv p = true ∧ (reqs p).bankID = BitVec.ofNat 2 i.val ∧ (reqs p).rsType = 1#2 := by
  intro h
  simp only [ocScaFilt, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- 向量过滤通过 ⇒ 原 valid 且 bankID 匹配且 rsType=2 -/
theorem ocA_filt_vec_eq_true (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (p : Fin 32) :
    ocVecFilt reqs rv i p = true →
      rv p = true ∧ (reqs p).bankID = BitVec.ofNat 2 i.val ∧ (reqs p).rsType = 2#2 := by
  intro h
  simp only [ocVecFilt, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/- ---- A 链第 2 环：授予必为过滤通过的请求 ---- -/

theorem ocA_grant_sca (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32)
    (h : ocScaOutValid reqs rv i lg = true) :
    (reqs (ocScaChoice reqs rv i lg)).rsType = 1#2 ∧
      (reqs (ocScaChoice reqs rv i lg)).bankID = BitVec.ofNat 2 i.val ∧
      rv (ocScaChoice reqs rv i lg) = true := by
  have h' : (ocScaPack reqs rv i).getLsbD (ocScaChoice reqs rv i lg).val = true := h
  unfold ocScaPack at h'
  rw [ocPack_getLsbD _ (ocScaChoice reqs rv i lg).isLt] at h'
  obtain ⟨h1, h2, h3⟩ := ocA_filt_sca_eq_true reqs rv i _ h'
  exact ⟨h3, h2, h1⟩

theorem ocA_grant_vec (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool) (i : Fin 4) (lg : Fin 32)
    (h : ocVecOutValid reqs rv i lg = true) :
    (reqs (ocVecChoice reqs rv i lg)).rsType = 2#2 ∧
      (reqs (ocVecChoice reqs rv i lg)).bankID = BitVec.ofNat 2 i.val ∧
      rv (ocVecChoice reqs rv i lg) = true := by
  have h' : (ocVecPack reqs rv i).getLsbD (ocVecChoice reqs rv i lg).val = true := h
  unfold ocVecPack at h'
  rw [ocPack_getLsbD _ (ocVecChoice reqs rv i lg).isLt] at h'
  obtain ⟨h1, h2, h3⟩ := ocA_filt_vec_eq_true reqs rv i _ h'
  exact ⟨h3, h2, h1⟩

/-- A 链第 3 环（Q2 关键）：slot-3 请求 rsType≡0 ⇒ 任何 bank 的两个仲裁器都
    不会授予 slot-3（chosen 落在 4j+3 时 out.valid=false）。 -/
theorem ocA_no_grant3 (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool)
    (hrt : ∀ p : Fin 32, p.val % 4 = 3 → (reqs p).rsType = 0#2)
    (i : Fin 4) (lg : Fin 32) :
    ((ocScaChoice reqs rv i lg).val % 4 = 3 → ocScaOutValid reqs rv i lg = false) ∧
      ((ocVecChoice reqs rv i lg).val % 4 = 3 → ocVecOutValid reqs rv i lg = false) := by
  constructor
  · intro h3
    by_cases hv : ocScaOutValid reqs rv i lg = true
    · obtain ⟨hrt1, -, -⟩ := ocA_grant_sca reqs rv i lg hv
      have hrt0 := hrt (ocScaChoice reqs rv i lg) h3
      rw [hrt1] at hrt0
      exact absurd hrt0 (by decide)
    · cases hvo : ocScaOutValid reqs rv i lg with
      | false => rfl
      | true => exact absurd hvo hv
  · intro h3
    by_cases hv : ocVecOutValid reqs rv i lg = true
    · obtain ⟨hrt2, -, -⟩ := ocA_grant_vec reqs rv i lg hv
      have hrt0 := hrt (ocVecChoice reqs rv i lg) h3
      rw [hrt2] at hrt0
      exact absurd hrt0 (by decide)
    · cases hvo : ocVecOutValid reqs rv i lg with
      | false => rfl
      | true => exact absurd hvo hv

/- ---- bank 读地址连线（:543-546） ---- -/

/-- bank 读地址（:543-544）：rsidx = 仲裁 out.bits.rsAddr（:56 组合直通） -/
def ocBankReadAddr (reqs : Fin 32 → CuArbReq) (pack : BitVec 32) (lg : Fin 32) : BitVec 8 :=
  (rraOutBits (by decide) reqs pack lg).rsAddr

/-- D-连线恒等：bank 读地址就是被选中请求的 rsAddr；且 out.valid 时该请求必获
    grant（rra1_choice_granted），即读的就是被仲裁授予的那笔请求的地址。 -/
theorem ocD_bank_addr_wiring (reqs : Fin 32 → CuArbReq) (pack : BitVec 32) (lg : Fin 32)
    (h : rraOutValid (by decide) pack lg = true) :
    ocBankReadAddr reqs pack lg = (reqs (rraChoice (by decide) pack lg)).rsAddr ∧
      rraGrant pack lg (rraChoice (by decide) pack lg) = true :=
  ⟨rfl, rra1_choice_granted (by decide) pack lg h⟩

/-- E1（Q5）：读仲裁 out.ready 恒 true（:545-546）⇒ out.valid 当拍即 fire，
    反压不存在，RRArbiter 非 Irrevocable（rra3_not_stable）在读侧无影响面。 -/
theorem ocE1_read_fire_of_valid (v : BitVec 32) (lg : Fin 32)
    (h : rraOutValid (by decide) v lg = true) :
    rraStep (by decide) v true lg = rraChoice (by decide) v lg :=
  rra4_step_of_fire (by decide) v lg h

/- ---- 数值回归：过滤与授予 ---- -/

section OcArbTests

/-- 测试请求阵列：全部 32 路同 bankID/rsType -/
def ocTReqs (rsType : BitVec 2) (bankID : BitVec 2) : Fin 32 → CuArbReq :=
  fun _ => ⟨0, bankID, rsType⟩

-- 标量请求被匹配 bank 的标量仲裁器授予
example : ocScaOutValid (ocTReqs 1#2 2#2) (fun p => decide (p.val = 5)) ⟨2, by decide⟩ ⟨0, by decide⟩ = true := by decide
example : (ocScaChoice (ocTReqs 1#2 2#2) (fun p => decide (p.val = 5)) ⟨2, by decide⟩ ⟨0, by decide⟩).val = 5 := by decide
-- bankID 不匹配 → 不授予
example : ocScaOutValid (ocTReqs 1#2 2#2) (fun p => decide (p.val = 5)) ⟨1, by decide⟩ ⟨0, by decide⟩ = false := by decide
-- rsType=1 不被向量仲裁器授予；rsType=0（mask）不被任何仲裁器授予（Q2）
example : ocVecOutValid (ocTReqs 1#2 2#2) (fun p => decide (p.val = 5)) ⟨2, by decide⟩ ⟨0, by decide⟩ = false := by decide
example : ocScaOutValid (ocTReqs 0#2 2#2) (fun p => decide (p.val = 5)) ⟨2, by decide⟩ ⟨0, by decide⟩ = false := by decide
example : ocVecOutValid (ocTReqs 0#2 2#2) (fun p => decide (p.val = 5)) ⟨2, by decide⟩ ⟨0, by decide⟩ = false := by decide
-- 向量请求；slot-3（p=31）的向量请求可授予、rsType=0 的 slot-3 不可
example : ocVecOutValid (ocTReqs 2#2 3#2) (fun p => decide (p.val = 31)) ⟨3, by decide⟩ ⟨0, by decide⟩ = true := by decide
example : ocScaOutValid (ocTReqs 0#2 3#2) (fun p => decide (p.val = 31)) ⟨3, by decide⟩ ⟨0, by decide⟩ = false := by decide
-- bank 读地址 = 选中请求的 rsAddr
example : ocBankReadAddr (fun p => ⟨BitVec.ofNat 8 p.val, 0, 1#2⟩)
    (ocScaPack (fun p => ⟨BitVec.ofNat 8 p.val, 0, 1#2⟩) (fun p => decide (p.val = 7)) ⟨0, by decide⟩) ⟨0, by decide⟩ = 7#8 := by decide

end OcArbTests

/- ========================================================================= -/
/- 3. crossBar（:380-435）：纯组合路由。CUId=chosen>>2（:403/:405）、          -/
/-    regOrder=chosen%4（:404/:406）；默认全无效（:408-412），按 bank 序        -/
/-    0→3 扫描命中即覆盖（:413-434，last-connect-wins；E3/Q6 证明并发不可能） -/
/- ========================================================================= -/

/-- crossbar 输入（:382-392 + 顶层 :549-556 的 RegNext/读数据线） -/
structure OcXbarIn where
  chosenS : Fin 4 → BitVec 5    -- :382（RegNext 后的 readchosenScalar）
  chosenV : Fin 4 → BitVec 5    -- :383
  validS  : Fin 4 → Bool        -- :384（RegNext 后的 out.valid）
  validV  : Fin 4 → Bool        -- :385
  dataS   : Fin 4 → BitVec 32   -- :386-388,:554 scalarBank(i).rs
  dataV   : Fin 4 → CuRow       -- :389-392,:555 vectorBank(i).rs
  dataV0  : Fin 4 → CuRow       -- :391,:556 vectorBank(i).v0

/-- crossbar2CU 输出（:24-29 + :393 的 valid） -/
structure OcXbarOut where
  valid : Bool
  regOrder : BitVec 2
  data : CuRow
  v0 : CuRow

/-- 标量命中条件（:416）：CUIdScalar(i)=j 且 valid 且 regOrderScalar(i)=k。
    （regOrderScalar 是 2 位截断，chosen%4<4 截断无损，等价于 chosen%4=k） -/
def ocXHitS (x : OcXbarIn) (i : Fin 4) (j k : Nat) : Bool :=
  (x.chosenS i >>> 2 == BitVec.ofNat 5 j) && x.validS i &&
    ((x.chosenS i % 4#5) == BitVec.ofNat 5 k)

/-- 向量命中条件（:423） -/
def ocXHitV (x : OcXbarIn) (i : Fin 4) (j k : Nat) : Bool :=
  (x.chosenV i >>> 2 == BitVec.ofNat 5 j) && x.validV i &&
    ((x.chosenV i % 4#5) == BitVec.ofNat 5 k)

theorem ocXHitS_eq_true (x : OcXbarIn) (i : Fin 4) (j k : Nat) :
    ocXHitS x i j k = true →
      x.chosenS i >>> 2 = BitVec.ofNat 5 j ∧ x.validS i = true ∧
        (x.chosenS i % 4#5) = BitVec.ofNat 5 k := by
  intro h
  simp only [ocXHitS, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ocXHitV_eq_true (x : OcXbarIn) (i : Fin 4) (j k : Nat) :
    ocXHitV x i j k = true →
      x.chosenV i >>> 2 = BitVec.ofNat 5 j ∧ x.validV i = true ∧
        (x.chosenV i % 4#5) = BitVec.ofNat 5 k := by
  intro h
  simp only [ocXHitV, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- 命中时写入的 regOrder = k（:404/:421；chosen%4 的低 2 位 = chosen 的低 2 位） -/
theorem ocXHitS_regOrder (x : OcXbarIn) (i : Fin 4) (j k : Nat) (hk : k < 4) :
    ocXHitS x i j k = true → (x.chosenS i).extractLsb' 0 2 = BitVec.ofNat 2 k := by
  intro h
  obtain ⟨-, -, h3⟩ := ocXHitS_eq_true x i j k h
  have he : (x.chosenS i).extractLsb' 0 2 = (x.chosenS i % 4#5).extractLsb' 0 2 := by bv_decide
  rw [he, h3]
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem ocXHitV_regOrder (x : OcXbarIn) (i : Fin 4) (j k : Nat) (hk : k < 4) :
    ocXHitV x i j k = true → (x.chosenV i).extractLsb' 0 2 = BitVec.ofNat 2 k := by
  intro h
  obtain ⟨-, -, h3⟩ := ocXHitV_eq_true x i j k h
  have he : (x.chosenV i).extractLsb' 0 2 = (x.chosenV i % 4#5).extractLsb' 0 2 := by bv_decide
  rw [he, h3]
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- 标量命中的写入（:417-421：data/valid/regOrder；v0 不动） -/
def ocXUpdS (acc : OcXbarOut) (ro : BitVec 2) (d : CuRow) : OcXbarOut :=
  { acc with valid := true, regOrder := ro, data := d }

/-- 向量命中的写入（:424-429：data/v0/valid/regOrder） -/
def ocXUpdV (acc : OcXbarOut) (ro : BitVec 2) (d v0 : CuRow) : OcXbarOut :=
  { acc with valid := true, regOrder := ro, data := d, v0 := v0 }

/-- 单端口路由的 bank 折叠（:408-434）：初值全无效；bank m 的处理 = 先标量
    when 块（:416-422）后向量 when 块（:423-430）——同 bank 双命中时向量覆盖
    标量（E3/Q6 证明系统内不可达）。m ≥ 4 的部分不用（ocXbar 只取 m=4）。 -/
def ocXbarGo (x : OcXbarIn) (j k : Nat) : Nat → OcXbarOut
  | 0 => ⟨false, 0#2, cuRow0, cuRow0⟩
  | m + 1 =>
    if h : m < 4 then
      (if ocXHitV x ⟨m, h⟩ j k = true then
        ocXUpdV (if ocXHitS x ⟨m, h⟩ j k = true then
                   ocXUpdS (ocXbarGo x j k m) ((x.chosenS ⟨m, h⟩).extractLsb' 0 2)
                     (cuBcast (x.dataS ⟨m, h⟩))
                 else ocXbarGo x j k m)
          ((x.chosenV ⟨m, h⟩).extractLsb' 0 2) (x.dataV ⟨m, h⟩) (x.dataV0 ⟨m, h⟩)
      else (if ocXHitS x ⟨m, h⟩ j k = true then
              ocXUpdS (ocXbarGo x j k m) ((x.chosenS ⟨m, h⟩).extractLsb' 0 2)
                (cuBcast (x.dataS ⟨m, h⟩))
            else ocXbarGo x j k m))
    else ocXbarGo x j k m

/-- `= false` 转 `¬ = true`（if_neg 用） -/
theorem ocNotTrue {b : Bool} (h : b = false) : ¬ b = true := by simp [h]

/-- CU j 的端口 k 的输出（:393 的 out(j)(k)） -/
def ocXbar (x : OcXbarIn) (j k : Nat) : OcXbarOut := ocXbarGo x j k 4

/-- 折叠的 valid 刻画：置位当且仅当某个已扫描 bank 命中 -/
theorem ocXbarGo_valid (x : OcXbarIn) (j k : Nat) {m : Nat} (hm : m ≤ 4) :
    (ocXbarGo x j k m).valid = true ↔
      ∃ i : Fin 4, i.val < m ∧ (ocXHitS x i j k = true ∨ ocXHitV x i j k = true) := by
  induction m with
  | zero =>
    constructor
    · intro h; simp [ocXbarGo] at h
    · intro h
      obtain ⟨i, hi, -⟩ := h
      omega
  | succ m ih =>
    have hm4 : m < 4 := by omega
    have ihm : m ≤ 4 := by omega
    simp only [ocXbarGo]
    rw [dif_pos hm4]
    by_cases hV : ocXHitV x ⟨m, hm4⟩ j k = true
    · rw [if_pos hV]
      exact ⟨fun _ => ⟨⟨m, hm4⟩, Nat.lt_succ_self m, Or.inr hV⟩, fun _ => rfl⟩
    · rw [if_neg hV]
      by_cases hS : ocXHitS x ⟨m, hm4⟩ j k = true
      · rw [if_pos hS]
        exact ⟨fun _ => ⟨⟨m, hm4⟩, Nat.lt_succ_self m, Or.inl hS⟩, fun _ => rfl⟩
      · rw [if_neg hS, ih ihm]
        constructor
        · intro ⟨i, hi, hh⟩; exact ⟨i, by omega, hh⟩
        · intro ⟨i, hi, hh⟩
          have hne : i.val ≠ m := by
            intro he
            have heq : i = ⟨m, hm4⟩ := Fin.ext he
            rw [heq] at hh
            cases hh with
            | inl hh => rw [hh] at hS; contradiction
            | inr hh => rw [hh] at hV; contradiction
          exact ⟨i, by omega, hh⟩

/-- 端口 valid 的存在刻画（:416-429 是置 valid 的唯一途径） -/
theorem ocXbar_valid_iff (x : OcXbarIn) (j k : Nat) :
    (ocXbar x j k).valid = true ↔
      ∃ i : Fin 4, ocXHitS x i j k = true ∨ ocXHitV x i j k = true := by
  have h := ocXbarGo_valid x j k (m := 4) (Nat.le_refl 4)
  unfold ocXbar
  rw [h]
  constructor
  · intro h
    obtain ⟨i, -, hh⟩ := h
    exact ⟨i, hh⟩
  · intro ⟨i, hh⟩; exact ⟨i, by omega, hh⟩

/-- valid 端口的 regOrder ≡ k（路由条件 :404/:406/:421/:429 的直接推论） -/
theorem ocXbar_regOrder_of_valid (x : OcXbarIn) (j k : Nat) (hk : k < 4)
    (h : (ocXbar x j k).valid = true) : (ocXbar x j k).regOrder = BitVec.ofNat 2 k := by
  have key : ∀ m : Nat, m ≤ 4 → (ocXbarGo x j k m).valid = true →
      (ocXbarGo x j k m).regOrder = BitVec.ofNat 2 k := by
    intro m hm
    induction m with
    | zero => intro hv; simp [ocXbarGo] at hv
    | succ m ih2 =>
      have hm4 : m < 4 := by omega
      have ihm : m ≤ 4 := by omega
      intro hv
      simp only [ocXbarGo] at hv ⊢
      rw [dif_pos hm4] at hv ⊢
      by_cases hV : ocXHitV x ⟨m, hm4⟩ j k = true
      · rw [if_pos hV] at hv ⊢
        show (x.chosenV ⟨m, hm4⟩).extractLsb' 0 2 = BitVec.ofNat 2 k
        exact ocXHitV_regOrder x ⟨m, hm4⟩ j k hk hV
      · rw [if_neg hV] at hv ⊢
        by_cases hS : ocXHitS x ⟨m, hm4⟩ j k = true
        · rw [if_pos hS] at hv ⊢
          show (x.chosenS ⟨m, hm4⟩).extractLsb' 0 2 = BitVec.ofNat 2 k
          exact ocXHitS_regOrder x ⟨m, hm4⟩ j k hk hS
        · rw [if_neg hS] at hv ⊢
          exact ih2 ihm hv
  exact key 4 (Nat.le_refl 4) h

/-- 归纳主键（唯一标量命中 ⇒ 折叠结果）：b 之前无命中、b 处置位、b 之后保持 -/
theorem ocXbarGo_of_uniq_sca (x : OcXbarIn) (b : Fin 4) (j k : Nat) (hk : k < 4)
    (hhit : ocXHitS x b j k = true) (hnoV : ocXHitV x b j k = false)
    (huniq : ∀ m : Fin 4, m ≠ b → ocXHitS x m j k = false ∧ ocXHitV x m j k = false) :
    ∀ m : Nat, m ≤ 4 → ocXbarGo x j k m =
      if b.val < m then
        ⟨true, BitVec.ofNat 2 k, cuBcast (x.dataS b), cuRow0⟩
      else ⟨false, 0#2, cuRow0, cuRow0⟩ := by
  intro m hm
  induction m with
  | zero => rw [ocXbarGo, if_neg (by omega : ¬ b.val < 0)]
  | succ m ih2 =>
    have hm4 : m < 4 := by omega
    have ihm : m ≤ 4 := by omega
    have ihv := ih2 ihm
    simp only [ocXbarGo]
    rw [dif_pos hm4]
    by_cases hbm : b.val = m
    · have hS : ocXHitS x ⟨m, hm4⟩ j k = true := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]; exact hhit
      have hV : ocXHitV x ⟨m, hm4⟩ j k = false := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]; exact hnoV
      rw [if_neg (ocNotTrue hV), if_pos hS, ihv, if_neg (by omega : ¬ b.val < m)]
      have hro : (x.chosenS ⟨m, hm4⟩).extractLsb' 0 2 = BitVec.ofNat 2 k := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]
        exact ocXHitS_regOrder x b j k hk hhit
      rw [if_pos (by omega : b.val < m + 1)]
      have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
      show (⟨true, (x.chosenS ⟨m, hm4⟩).extractLsb' 0 2, cuBcast (x.dataS ⟨m, hm4⟩),
             cuRow0⟩ : OcXbarOut) = _
      rw [hro, ← hb]
    · have hne : ⟨m, hm4⟩ ≠ b := by
        intro he
        exact hbm (congrArg Fin.val he).symm
      obtain ⟨hS, hV⟩ := huniq ⟨m, hm4⟩ hne
      rw [if_neg (ocNotTrue hV), if_neg (ocNotTrue hS), ihv]
      by_cases hlt : b.val < m
      · rw [if_pos hlt, if_pos (by omega : b.val < m + 1)]
      · rw [if_neg hlt, if_neg (by omega : ¬ b.val < m + 1)]

/-- D-crossbar 路由正确性（标量，:417）：唯一命中时端口收到该 bank 标量数据
    的广播（:417 VecInit.fill），regOrder=k，valid=1 -/
theorem ocXbar_route_sca (x : OcXbarIn) (b : Fin 4) (j k : Nat) (hk : k < 4)
    (hhit : ocXHitS x b j k = true) (hnoV : ocXHitV x b j k = false)
    (huniq : ∀ m : Fin 4, m ≠ b → ocXHitS x m j k = false ∧ ocXHitV x m j k = false) :
    ocXbar x j k = ⟨true, BitVec.ofNat 2 k, cuBcast (x.dataS b), cuRow0⟩ := by
  have h := ocXbarGo_of_uniq_sca x b j k hk hhit hnoV huniq 4 (Nat.le_refl 4)
  show ocXbarGo x j k 4 = _
  rw [h, if_pos b.isLt]

/-- 归纳主键（唯一向量命中 ⇒ 折叠结果） -/
theorem ocXbarGo_of_uniq_vec (x : OcXbarIn) (b : Fin 4) (j k : Nat) (hk : k < 4)
    (hhit : ocXHitV x b j k = true) (hnoS : ocXHitS x b j k = false)
    (huniq : ∀ m : Fin 4, m ≠ b → ocXHitS x m j k = false ∧ ocXHitV x m j k = false) :
    ∀ m : Nat, m ≤ 4 → ocXbarGo x j k m =
      if b.val < m then
        ⟨true, BitVec.ofNat 2 k, x.dataV b, x.dataV0 b⟩
      else ⟨false, 0#2, cuRow0, cuRow0⟩ := by
  intro m hm
  induction m with
  | zero => rw [ocXbarGo, if_neg (by omega : ¬ b.val < 0)]
  | succ m ih2 =>
    have hm4 : m < 4 := by omega
    have ihm : m ≤ 4 := by omega
    have ihv := ih2 ihm
    simp only [ocXbarGo]
    rw [dif_pos hm4]
    by_cases hbm : b.val = m
    · have hV : ocXHitV x ⟨m, hm4⟩ j k = true := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]; exact hhit
      have hS : ocXHitS x ⟨m, hm4⟩ j k = false := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]; exact hnoS
      rw [if_pos hV]
      have hro : (x.chosenV ⟨m, hm4⟩).extractLsb' 0 2 = BitVec.ofNat 2 k := by
        have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
        rw [← hb]
        exact ocXHitV_regOrder x b j k hk hhit
      rw [if_pos (by omega : b.val < m + 1)]
      have hb : b = ⟨m, hm4⟩ := Fin.ext hbm
      show (⟨true, (x.chosenV ⟨m, hm4⟩).extractLsb' 0 2, x.dataV ⟨m, hm4⟩,
             x.dataV0 ⟨m, hm4⟩⟩ : OcXbarOut) = _
      rw [hro, ← hb]
    · have hne : ⟨m, hm4⟩ ≠ b := by
        intro he
        exact hbm (congrArg Fin.val he).symm
      obtain ⟨hS, hV⟩ := huniq ⟨m, hm4⟩ hne
      rw [if_neg (ocNotTrue hV), if_neg (ocNotTrue hS), ihv]
      by_cases hlt : b.val < m
      · rw [if_pos hlt, if_pos (by omega : b.val < m + 1)]
      · rw [if_neg hlt, if_neg (by omega : ¬ b.val < m + 1)]

/-- D-crossbar 路由正确性（向量，:424-425）：唯一命中时端口收到该 bank 的
    向量数据与 v0，regOrder=k，valid=1 -/
theorem ocXbar_route_vec (x : OcXbarIn) (b : Fin 4) (j k : Nat) (hk : k < 4)
    (hhit : ocXHitV x b j k = true) (hnoS : ocXHitS x b j k = false)
    (huniq : ∀ m : Fin 4, m ≠ b → ocXHitS x m j k = false ∧ ocXHitV x m j k = false) :
    ocXbar x j k = ⟨true, BitVec.ofNat 2 k, x.dataV b, x.dataV0 b⟩ := by
  have h := ocXbarGo_of_uniq_vec x b j k hk hhit hnoS huniq 4 (Nat.le_refl 4)
  show ocXbarGo x j k 4 = _
  rw [h, if_pos b.isLt]

/-- 命中条件的 Nat 分解：chosen < 32、j < 8、k < 4 时，命中 ⟺ chosen = 4j+k -/
theorem ocHit_chosen_eq (c : BitVec 5) (j k : Nat) (hj : j < 8) (hk : k < 4)
    (h1 : c >>> 2 = BitVec.ofNat 5 j) (h2 : c % 4#5 = BitVec.ofNat 5 k) :
    c.toNat = 4 * j + k := by
  have h1' := congrArg BitVec.toNat h1
  have h2' := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 5),
      Nat.shiftRight_eq_div_pow] at h1'
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (4 : Nat) % 2 ^ 5 = 4 by decide,
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 5)] at h2'
  have hc := c.isLt
  omega

/-- E3（Q6）：crossbar 标量/向量两个 when 块（:416/:423）同拍同写 out(j)(k)
    不可能——同 (j,k) 命中要求两笔 grant 的 chosen 同为 4j+k（同一请求下标），
    但该请求的 rsType 不能既 =1（:363 标量过滤）又 =2（:365 向量过滤）。
    推论：ocXbarGo 折叠里的覆盖分支系统内不可达，路由行为等价于唯一命中。 -/
theorem ocE3_no_clash (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool)
    (i m : Fin 4) (lgS lgV : Fin 32) (j k : Nat) (hj : j < 8) (hk : k < 4)
    (hvs : ocScaOutValid reqs rv i lgS = true)
    (hvv : ocVecOutValid reqs rv m lgV = true)
    (hS : (BitVec.ofNat 5 (ocScaChoice reqs rv i lgS).val) >>> 2 = BitVec.ofNat 5 j ∧
          (BitVec.ofNat 5 (ocScaChoice reqs rv i lgS).val) % 4#5 = BitVec.ofNat 5 k)
    (hV : (BitVec.ofNat 5 (ocVecChoice reqs rv m lgV).val) >>> 2 = BitVec.ofNat 5 j ∧
          (BitVec.ofNat 5 (ocVecChoice reqs rv m lgV).val) % 4#5 = BitVec.ofNat 5 k) :
    False := by
  obtain ⟨hrt1, -, -⟩ := ocA_grant_sca reqs rv i lgS hvs
  obtain ⟨hrt2, -, -⟩ := ocA_grant_vec reqs rv m lgV hvv
  have hceS : (BitVec.ofNat 5 (ocScaChoice reqs rv i lgS).val).toNat = 4 * j + k :=
    ocHit_chosen_eq _ j k hj hk hS.1 hS.2
  have hceV : (BitVec.ofNat 5 (ocVecChoice reqs rv m lgV).val).toNat = 4 * j + k :=
    ocHit_chosen_eq _ j k hj hk hV.1 hV.2
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ocScaChoice reqs rv i lgS).isLt] at hceS
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ocVecChoice reqs rv m lgV).isLt] at hceV
  have hce : ocScaChoice reqs rv i lgS = ocVecChoice reqs rv m lgV := Fin.ext (by omega)
  rw [hce] at hrt1
  rw [hrt1] at hrt2
  exact absurd hrt2 (by decide)

/-- I-12 链第 4 环（crossbar 段）：没有 bank 授予 slot-3（chosen%4=3）时，
    任何 CU 的端口 3 永不置 valid。 -/
theorem ocXbar_port3_never_valid (x : OcXbarIn)
    (hS : ∀ i : Fin 4, x.validS i = true → (x.chosenS i % 4#5) ≠ 3#5)
    (hV : ∀ i : Fin 4, x.validV i = true → (x.chosenV i % 4#5) ≠ 3#5)
    (j : Nat) :
    (ocXbar x j 3).valid = false := by
  by_cases hv : (ocXbar x j 3).valid = true
  · obtain ⟨i, hh⟩ := (ocXbar_valid_iff x j 3).mp hv
    cases hh with
    | inl hh =>
      obtain ⟨-, hvi, h3⟩ := ocXHitS_eq_true x i j 3 hh
      exact absurd h3 (hS i hvi)
    | inr hh =>
      obtain ⟨-, hvi, h3⟩ := ocXHitV_eq_true x i j 3 hh
      exact absurd h3 (hV i hvi)
  · cases hvo : (ocXbar x j 3).valid with
    | false => rfl
    | true => exact absurd hvo hv

/- ---- 数值回归：crossbar 路由 ---- -/

section OcXbarTests

/-- 测试输入：bank 1 标量命中 CU3 端口 2（chosen=3*4+2=14） -/
def ocTX : OcXbarIn :=
  { chosenS := fun i => if i.val = 1 then 14#5 else 0#5
  , chosenV := fun _ => 0#5
  , validS := fun i => decide (i.val = 1)
  , validV := fun _ => false
  , dataS := fun i => 0xA0#32 + BitVec.ofNat 32 i.val
  , dataV := fun _ => cuRowA
  , dataV0 := fun _ => cuRowB }

example : ocXHitS ocTX ⟨1, by decide⟩ 3 2 = true := by decide
example : ocXHitS ocTX ⟨0, by decide⟩ 3 2 = false := by decide
-- 路由：CU3 端口 2 收到 bank1 标量数据广播（0xA1）
example : (ocXbar ocTX 3 2).valid = true := by native_decide
example : (ocXbar ocTX 3 2).regOrder = 2#2 := by native_decide
example : (ocXbar ocTX 3 2).data ⟨7, by decide⟩ = 0xA1#32 := by native_decide
-- 未命中端口保持无效
example : (ocXbar ocTX 3 1).valid = false := by native_decide
example : (ocXbar ocTX 2 2).valid = false := by native_decide
-- slot-3 无 grant ⇒ 端口 3 恒无效（I-12 的数值见证）
example : (ocXbar ocTX 0 3).valid = false := by native_decide
example : (ocXbar ocTX 7 3).valid = false := by native_decide

/-- 测试输入：bank 2 向量命中 CU1 端口 0（chosen=1*4+0=4） -/
def ocTXV : OcXbarIn :=
  { chosenS := fun _ => 0#5
  , chosenV := fun i => if i.val = 2 then 4#5 else 0#5
  , validS := fun _ => false
  , validV := fun i => decide (i.val = 2)
  , dataS := fun _ => 0#32
  , dataV := fun _ => cuRowC
  , dataV0 := fun _ => cuRowA }

example : (ocXbar ocTXV 1 0).valid = true := by native_decide
example : (ocXbar ocTXV 1 0).data ⟨5, by decide⟩ = 0x3005#32 := by native_decide
example : (ocXbar ocTXV 1 0).v0 ⟨5, by decide⟩ = 0x1005#32 := by native_decide

end OcXbarTests

/- ========================================================================= -/
/- 4. I-12 系统死锁链闭环（Q2）                                                -/
/-    链：CU 的 slot-3 请求 rsType≡0（:214，本节第 0 环）                      -/
/-      ⇒ 全 8 仲裁器过滤后 valid=false（ocA_filter_rt0，第 1 环）            -/
/-      ⇒ 永不授予 slot-3（ocA_no_grant3，第 2/3 环）                         -/
/-      ⇒ crossbar 端口 3 永不置 valid（ocXbar_port3_never_valid，第 4 环）   -/
/-      ⇒ sourced 输入满足 cuWmask_deadlock 前提（ocI12_closure，第 5 环）    -/
/-      ⇒ masked 指令死锁（ocI12_deadlock_system，闭环）                       -/
/- ========================================================================= -/

/-- cuBankPort 不改 rsType3（:264-318 只写 rsReg/mask/ready） -/
theorem ocCuBankPort_rsType3 (pre : CuState) (inp : CuInputs) (st : CuState) (k : Nat) :
    (cuBankPort pre inp st k).rsType3 = st.rsType3 := by
  by_cases hf : cuBankFireK pre inp k = true
  · rcases cuBv2_plain (inp.bankB k).regOrder with h0|h0|h0|h0 <;> simp_all [cuBankPort]
  · simp [cuBankPort, hf]

/-- cuAccept 的 rsType3：接受拍置 0（:219），否则保持 -/
theorem ocCuAccept_rsType3 (s : CuState) (inp : CuInputs) :
    (cuAccept s inp).rsType3 = (if cuControlFire s inp then 0#2 else s.rsType3) := by
  unfold cuAccept; split <;> rfl

/-- 单拍保持：rsType3 = 0 是不变式 -/
theorem ocCuStep_rsType3 (s : CuState) (inp : CuInputs) (h : s.rsType3 = 0#2) :
    (cuStep s inp).rsType3 = 0#2 := by
  simp only [cuStep]
  rw [ocCuBankPort_rsType3, ocCuBankPort_rsType3, ocCuBankPort_rsType3,
      ocCuBankPort_rsType3]
  have hacc : (cuAccept s inp).rsType3 = 0#2 := by
    rw [ocCuAccept_rsType3]
    split
    · rfl
    · exact h
  unfold cuPreBank
  split
  · exact hacc
  · exact hacc

/-- I-12 链第 0 环（CU 侧不变式）：任何从 cuInit 可达的状态下 rsType(3)≡0
    （:214 的 rsTypeWire(3)=0 经 :219 写入，此后无改写路径） -/
theorem ocI12_cu_rsType3_run_aux (s : CuState) (h : s.rsType3 = 0#2) (ins : List CuInputs) :
    (cuRun s ins).rsType3 = 0#2 := by
  induction ins generalizing s with
  | nil => exact h
  | cons j js ih => exact ih (cuStep s j) (ocCuStep_rsType3 s j h)

theorem ocI12_cu_rsType3_run (ins : List CuInputs) :
    (cuRun cuInit ins).rsType3 = 0#2 :=
  ocI12_cu_rsType3_run_aux cuInit rfl ins

/-- slot-3 请求（:101-127 的 k=3 端口）的 rsType 恒 0：接受拍取 rsTypeWire(3)=0
    （:214），保持期取 rsType(3) 寄存器（可达状态下恒 0，见上） -/
theorem ocI12_slot3_rt0 (s : CuState) (inp : CuInputs) (h : s.rsType3 = 0#2) :
    (cuOutArbBits s inp 3).rsType = 0#2 := by
  unfold cuOutArbBits
  simp [cuRsTypeWire, CuState.rsTypeAt, h]

/-- 仲裁 ⇒ crossbar 输入事实（RegNext 保值，:549-552）：crossbar 的
    valid/chosen 是仲裁 out.valid/chosen 的寄存版，"不授予 slot-3"逐拍传递。 -/
theorem ocI12_xbar_hyp_of_arb (reqs : Fin 32 → CuArbReq) (rv : Fin 32 → Bool)
    (hrt : ∀ p : Fin 32, p.val % 4 = 3 → (reqs p).rsType = 0#2)
    (x : OcXbarIn) (lgS lgV : Fin 4 → Fin 32)
    (hxS : ∀ i, x.validS i = ocScaOutValid reqs rv i (lgS i) ∧
                x.chosenS i = BitVec.ofNat 5 (ocScaChoice reqs rv i (lgS i)).val)
    (hxV : ∀ i, x.validV i = ocVecOutValid reqs rv i (lgV i) ∧
                x.chosenV i = BitVec.ofNat 5 (ocVecChoice reqs rv i (lgV i)).val)
    (i : Fin 4) :
    (x.validS i = true → (x.chosenS i % 4#5) ≠ 3#5) ∧
      (x.validV i = true → (x.chosenV i % 4#5) ≠ 3#5) := by
  obtain ⟨hgS, -⟩ := ocA_no_grant3 reqs rv hrt i (lgS i)
  obtain ⟨-, hgV⟩ := ocA_no_grant3 reqs rv hrt i (lgV i)
  obtain ⟨hvS, hcS⟩ := hxS i
  obtain ⟨hvV, hcV⟩ := hxV i
  constructor
  · intro hvi hmod
    have hov : ocScaOutValid reqs rv i (lgS i) = true := by rw [← hvS]; exact hvi
    have h3 : (ocScaChoice reqs rv i (lgS i)).val % 4 = 3 := by
      have hmod' : (BitVec.ofNat 5 (ocScaChoice reqs rv i (lgS i)).val) % 4#5 = 3#5 := by
        rw [← hcS]; exact hmod
      have hto := congrArg BitVec.toNat hmod'
      rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (ocScaChoice reqs rv i (lgS i)).isLt,
          show (4 : Nat) % 2 ^ 5 = 4 by decide, show (3 : Nat) % 2 ^ 5 = 3 by decide] at hto
      exact hto
    rw [hgS h3] at hov
    contradiction
  · intro hvi hmod
    have hov : ocVecOutValid reqs rv i (lgV i) = true := by rw [← hvV]; exact hvi
    have h3 : (ocVecChoice reqs rv i (lgV i)).val % 4 = 3 := by
      have hmod' : (BitVec.ofNat 5 (ocVecChoice reqs rv i (lgV i)).val) % 4#5 = 3#5 := by
        rw [← hcV]; exact hmod
      have hto := congrArg BitVec.toNat hmod'
      rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (ocVecChoice reqs rv i (lgV i)).isLt,
          show (4 : Nat) % 2 ^ 5 = 4 by decide, show (3 : Nat) % 2 ^ 5 = 3 by decide] at hto
      exact hto
    rw [hgV h3] at hov
    contradiction

/-- CU 的 bankIn 由 crossbar 驱动（:559）：sourced 输入端口的 valid 即 crossbar
    输出 valid，valid 时 regOrder 即 crossbar 输出 regOrder -/
def ocXSourced (x : OcXbarIn) (inp : CuInputs) (j : Nat) : Prop :=
  ∀ k, k ≤ 3 → inp.bankV k = (ocXbar x j k).valid ∧
    ((ocXbar x j k).valid = true → (inp.bankB k).regOrder = (ocXbar x j k).regOrder)

/-- I-12 链第 5 环（闭环）：sourced 输入满足 cuWmask_deadlock 的"无 regOrder=3
    返回"前提——k=3（含 k>3，CuInputs.bankV/bankB 对 k≥3 归到端口 3）时
    crossbar 端口 3 恒无效；k≤2 时命中端口的 regOrder≡k≠3（:404/:406）。 -/
theorem ocI12_closure (x : OcXbarIn) (j : Nat)
    (hS : ∀ i : Fin 4, x.validS i = true → (x.chosenS i % 4#5) ≠ 3#5)
    (hV : ∀ i : Fin 4, x.validV i = true → (x.chosenV i % 4#5) ≠ 3#5)
    (inp : CuInputs) (hs : ocXSourced x inp j) :
    ∀ k, inp.bankV k = true → (inp.bankB k).regOrder ≠ 3#2 := by
  intro k hbk
  have hP3 : (ocXbar x j 3).valid = false := ocXbar_port3_never_valid x hS hV j
  by_cases h01 : k = 0 ∨ k = 1 ∨ k = 2
  · rcases h01 with rfl | rfl | rfl
    · obtain ⟨hv, hr⟩ := hs 0 (by omega)
      have hport : (ocXbar x j 0).valid = true := by rw [← hv]; exact hbk
      have hro := hr hport
      rw [hro, ocXbar_regOrder_of_valid x j 0 (by omega) hport]
      decide
    · obtain ⟨hv, hr⟩ := hs 1 (by omega)
      have hport : (ocXbar x j 1).valid = true := by rw [← hv]; exact hbk
      have hro := hr hport
      rw [hro, ocXbar_regOrder_of_valid x j 1 (by omega) hport]
      decide
    · obtain ⟨hv, hr⟩ := hs 2 (by omega)
      have hport : (ocXbar x j 2).valid = true := by rw [← hv]; exact hbk
      have hro := hr hport
      rw [hro, ocXbar_regOrder_of_valid x j 2 (by omega) hport]
      decide
  · have hk3 : k ≥ 3 := by omega
    have hbv : inp.bankV k = inp.bankV 3 := by
      have h1 : k ≠ 0 := by omega
      have h2 : k ≠ 1 := by omega
      have h3 : k ≠ 2 := by omega
      simp [CuInputs.bankV, h1, h2, h3]
    obtain ⟨hv, -⟩ := hs 3 (by omega)
    rw [hbv, hv, hP3] at hbk
    contradiction

/-- **I-12 系统死锁链（完整闭环定理）**：masked 指令（control.mask=1）被 CU
    接受后，若系统内 bankIn 全部由 crossbar 驱动（ocXSourced，:559）且所有
    bank 的仲裁器不授予 slot-3（由 ocI12_slot3_rt0 + ocA_no_grant3 +
    ocI12_xbar_hyp_of_arb 保证的"slot-3 请求 rsType≡0"事实），则 CU 永久滞留
    s_add、control.ready 永不恢复——该 warp 的 CU 死锁，instDemux 亦不再向它
    分配新指令。定理即 cuWmask_deadlock 在系统事实下的实例化。 -/
theorem ocI12_deadlock_system (i0 : CuInputs) (ins : List CuInputs)
    (hv0 : i0.controlValid = true) (hm : i0.ctrl.mask = true)
    (hx : ∀ c ∈ (i0 :: ins), ∃ (x : OcXbarIn) (j : Nat),
      (∀ i : Fin 4, x.validS i = true → (x.chosenS i % 4#5) ≠ 3#5) ∧
      (∀ i : Fin 4, x.validV i = true → (x.chosenV i % 4#5) ≠ 3#5) ∧
      ocXSourced x c j) :
    (cuRun (cuStep cuInit i0) ins).state = cuSAdd ∧
      cuControlRdy (cuRun (cuStep cuInit i0) ins) = false := by
  apply cuWmask_deadlock i0 ins hv0 hm
  intro c hc k hbk
  obtain ⟨x, j, hS, hV, hs⟩ := hx c hc
  exact ocI12_closure x j hS hV c hs k hbk

/- ========================================================================= -/
/- 5. instDemux（:440-517，num_warp=8>1 ⇒ :495-512 分支）                      -/
/-    outV_sel=最低 ready CU（:497-498）；outReady2=去掉 outV_sel（:499）；     -/
/-    outX_sel=outReady2 的最低置位位（:500）；bits 默认广播 in(0)（:452），    -/
/-    :505/:509 覆盖选中端口                                                    -/
/- ========================================================================= -/

/-- demux 组合输出 -/
structure OcDemuxRes (n : Nat) where
  valid : Fin n → Bool     -- out(j).valid（:453,:506,:510）
  bits  : Fin n → CuCtrl   -- out(j).bits（:452,:505,:509）
  in0Rdy : Bool            -- in(0).ready（:501）
  in1Rdy : Bool            -- in(1).ready（:502）

/-- outReady2（:499）：outReady1 去掉 outV_sel 位（Q7：outV_sel_oh 为 one-hot） -/
def ocRdy2 {n : Nat} (outRdy : Fin n → Bool) : Fin n → Bool :=
  fun j => outRdy j && !decide (j.val = ocPrioLowest outRdy)

/-- instDemux（:495-512 分支；widCmp 死输入不建模，D6） -/
def ocDemux {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool) (b0 b1 : CuCtrl) : OcDemuxRes n :=
  { valid := fun j =>
      (ocOrR outRdy && decide (j.val = ocPrioLowest outRdy) && in0V) ||
        (ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) && in1V)
  , bits := fun j =>
      if ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) then b1 else b0
  , in0Rdy := ocOrR outRdy
  , in1Rdy := ocOrR (ocRdy2 outRdy) }

/-- outV_sel 与 outX_sel 互异（anyX 时）——:504 与 :508 不写同一端口 -/
theorem ocRdy2_prio_ne {n : Nat} (outRdy : Fin n → Bool)
    (h : ocOrR (ocRdy2 outRdy) = true) :
    ocPrioLowest (ocRdy2 outRdy) ≠ ocPrioLowest outRdy := by
  obtain ⟨jj, hjj⟩ := (ocOrR_eq_true_iff _).mp h
  obtain ⟨c2, hce2, hcf2, -, -⟩ := ocPrioLowest_spec (ocRdy2 outRdy) jj hjj
  rw [hce2]
  intro heq
  have h1 : ocRdy2 outRdy c2 = true := hcf2
  unfold ocRdy2 at h1
  rw [← heq] at h1
  simp at h1

/-- D-demux（:497/:504-507）：j 是最低 ready CU 时 controlV 落到 out(j)——
    valid=in(0).valid、bits=in(0).bits；:509 不写它（ocRdy2_prio_ne） -/
theorem ocDemux_controlV_lowest {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool) (b0 b1 : CuCtrl)
    (j : Fin n) (hj : outRdy j = true) (hmin : ∀ k : Fin n, k.val < j.val → outRdy k = false) :
    (ocDemux outRdy in0V in1V b0 b1).valid j = in0V ∧
      (ocDemux outRdy in0V in1V b0 b1).bits j = b0 := by
  obtain ⟨c, hce, hcf, hcmin, hcj⟩ := ocPrioLowest_spec outRdy j hj
  have hcj_eq : c = j := by
    apply Fin.ext
    rcases Nat.lt_or_ge c.val j.val with hlt | hge
    · have hf := hmin c hlt
      rw [hcf] at hf; contradiction
    · exact Nat.le_antisymm hcj hge
  have hvSel : ocPrioLowest outRdy = j.val := by rw [hce, hcj_eq]
  have hanyV : ocOrR outRdy = true := (ocOrR_eq_true_iff _).mpr ⟨j, hj⟩
  have hnotX : (ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy))) = false := by
    by_cases hX : ocOrR (ocRdy2 outRdy) = true
    · have hne := ocRdy2_prio_ne outRdy hX
      rw [hvSel] at hne
      have hd : decide (j.val = ocPrioLowest (ocRdy2 outRdy)) = false := by
        rw [decide_eq_false_iff_not]
        intro heq
        exact hne heq.symm
      rw [hd]; simp
    · have ho : ocOrR (ocRdy2 outRdy) = false := by
        cases hoo : ocOrR (ocRdy2 outRdy) with
        | false => rfl
        | true => exact absurd hoo hX
      rw [ho]; simp
  have hvalid : (ocDemux outRdy in0V in1V b0 b1).valid j =
      ((ocOrR outRdy && decide (j.val = ocPrioLowest outRdy) && in0V) ||
        (ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) && in1V)) := rfl
  have hbits : (ocDemux outRdy in0V in1V b0 b1).bits j =
      if ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) then b1 else b0 := rfl
  constructor
  · rw [hvalid]
    simp [hanyV, hvSel, hnotX]
  · rw [hbits]
    simp [hnotX]

/-- D-demux（:500/:508-511）：l 最低、j 次低 ready CU 时 controlX 落到 out(j)——
    valid=in(1).valid、bits=in(1).bits（:509 覆盖 :452 的默认广播，E4 关键） -/
theorem ocDemux_controlX_second {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool) (b0 b1 : CuCtrl)
    (l j : Fin n) (hl : outRdy l = true) (hlmin : ∀ k : Fin n, k.val < l.val → outRdy k = false)
    (hj : outRdy j = true) (hjl : j ≠ l)
    (hjmin : ∀ k : Fin n, k.val < j.val → k ≠ l → outRdy k = false) :
    (ocDemux outRdy in0V in1V b0 b1).valid j = in1V ∧
      (ocDemux outRdy in0V in1V b0 b1).bits j = b1 := by
  obtain ⟨c, hce, hcf, hcmin, hcj⟩ := ocPrioLowest_spec outRdy l hl
  have hcl : c = l := by
    apply Fin.ext
    rcases Nat.lt_or_ge c.val l.val with hlt | hge
    · have hf := hlmin c hlt
      rw [hcf] at hf; contradiction
    · exact Nat.le_antisymm hcj hge
  have hvSel : ocPrioLowest outRdy = l.val := by rw [hce, hcl]
  have hjl' : j.val ≠ l.val := fun he => hjl (Fin.ext he)
  have hrdy2j : ocRdy2 outRdy j = true := by
    unfold ocRdy2
    rw [hvSel]
    simp [hj, hjl']
  have hrdy2min : ∀ k : Fin n, k.val < j.val → ocRdy2 outRdy k = false := by
    intro k hkj
    unfold ocRdy2
    rw [hvSel]
    by_cases hkl : k = l
    · have hne : k.val = l.val := congrArg Fin.val hkl
      simp [hne]
    · have hf := hjmin k hkj hkl
      simp [hf]
  obtain ⟨c2, hce2, hcf2, hc2min, hc2j⟩ := ocPrioLowest_spec (ocRdy2 outRdy) j hrdy2j
  have hc2 : c2 = j := by
    apply Fin.ext
    rcases Nat.lt_or_ge c2.val j.val with hlt | hge
    · have hf := hrdy2min c2 hlt
      rw [hcf2] at hf; contradiction
    · exact Nat.le_antisymm hc2j hge
  have hxSel : ocPrioLowest (ocRdy2 outRdy) = j.val := by rw [hce2, hc2]
  have hanyX : ocOrR (ocRdy2 outRdy) = true := (ocOrR_eq_true_iff _).mpr ⟨j, hrdy2j⟩
  have hvalid : (ocDemux outRdy in0V in1V b0 b1).valid j =
      ((ocOrR outRdy && decide (j.val = ocPrioLowest outRdy) && in0V) ||
        (ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) && in1V)) := rfl
  have hbits : (ocDemux outRdy in0V in1V b0 b1).bits j =
      if ocOrR (ocRdy2 outRdy) && decide (j.val = ocPrioLowest (ocRdy2 outRdy)) then b1 else b0 := rfl
  constructor
  · rw [hvalid, hvSel]
    simp [hjl', hanyX, hxSel]
  · rw [hbits]
    simp [hanyX, hxSel]

/-- in(0).ready（:501）= 存在 ready CU -/
theorem ocDemux_in0Rdy {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool) (b0 b1 : CuCtrl) :
    (ocDemux outRdy in0V in1V b0 b1).in0Rdy = ocOrR outRdy := rfl

/-- in(1).ready（:502）= 存在 outV_sel 之外的 ready CU -/
theorem ocDemux_in1Rdy {n : Nat} (outRdy : Fin n → Bool) (in0V in1V : Bool) (b0 b1 : CuCtrl) :
    (ocDemux outRdy in0V in1V b0 b1).in1Rdy = ocOrR (ocRdy2 outRdy) := rfl

/-- E4（:452/:505/:509 的 bits 广播审查）：in(1) 有效而 in(0) 无效时，controlX
    的 bits 不被 in(0).bits 污染——(a) 存在次低 ready CU 时 :509 把 out(xSel)
    覆盖为 in(1).bits（ocDemux_controlX_second，不依赖 in0V）；(b) 只有一个
    ready CU 时 outReady2=0、in(1).ready=0（:502），in(1) 不 fire，全部端口
    valid=0（:452 的默认 bits=in(0).bits 是死值，无消费者）。本定理钉死 (b)。 -/
theorem ocDemux_E4_single_ready {n : Nat} (j : Fin n) (in1V : Bool) (b0 b1 : CuCtrl) :
    (ocDemux (fun k => decide (k = j)) false in1V b0 b1).in1Rdy = false ∧
      ∀ k : Fin n, (ocDemux (fun k => decide (k = j)) false in1V b0 b1).valid k = false := by
  have hvSel : ocPrioLowest (fun k => decide (k = j)) = j.val := by
    obtain ⟨c, hce, hcf, -, -⟩ := ocPrioLowest_spec (fun k => decide (k = j)) j (by simp)
    have hcje : c = j := by
      have h : decide (c = j) = true := hcf
      rw [decide_eq_true_eq] at h
      exact h
    rw [hce, hcje]
  have hrdy2 : ∀ k : Fin n, ocRdy2 (fun kk => decide (kk = j)) k = false := by
    intro k
    unfold ocRdy2
    rw [hvSel]
    by_cases hkj : k = j
    · have h : k.val = j.val := congrArg Fin.val hkj
      simp [h]
    · have h : decide (k = j) = false := by
        rw [decide_eq_false_iff_not]; exact hkj
      simp [h]
  have hanyX : ocOrR (ocRdy2 (fun k => decide (k = j))) = false :=
    (ocOrR_eq_false_iff _).mpr hrdy2
  have h1 : (ocDemux (fun k => decide (k = j)) false in1V b0 b1).in1Rdy = false := hanyX
  refine ⟨h1, fun k => ?_⟩
  have hvalid : (ocDemux (fun k => decide (k = j)) false in1V b0 b1).valid k =
      ((ocOrR (fun kk => decide (kk = j)) && decide (k.val = ocPrioLowest (fun kk => decide (kk = j))) && false) ||
        (ocOrR (ocRdy2 (fun kk => decide (kk = j))) &&
          decide (k.val = ocPrioLowest (ocRdy2 (fun kk => decide (kk = j)))) && in1V)) := rfl
  rw [hvalid, hanyX]
  simp

/- ---- 数值回归：demux 分配 ---- -/

section OcDemuxTests

def ocDC1 : CuCtrl := { cuCtrl0 with tag := 1#8 }
def ocDC2 : CuCtrl := { cuCtrl0 with tag := 2#8 }

-- 全 ready（8 CU）：controlV→CU0、controlX→CU1，其余端口无效
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).valid ⟨0, by decide⟩ = true := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).bits ⟨0, by decide⟩ = ocDC1 := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).valid ⟨1, by decide⟩ = true := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).bits ⟨1, by decide⟩ = ocDC2 := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).valid ⟨2, by decide⟩ = false := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).in0Rdy = true := by decide
example : (ocDemux (n := 8) (fun _ => true) true true ocDC1 ocDC2).in1Rdy = true := by decide
-- 只有 CU1 ready：controlV→CU1，controlX 无去处
example : (ocDemux (n := 8) (fun k => decide (k.val = 1)) true true ocDC1 ocDC2).valid ⟨1, by decide⟩ = true := by decide
example : (ocDemux (n := 8) (fun k => decide (k.val = 1)) true true ocDC1 ocDC2).bits ⟨1, by decide⟩ = ocDC1 := by decide
example : (ocDemux (n := 8) (fun k => decide (k.val = 1)) true true ocDC1 ocDC2).in1Rdy = false := by decide
-- E4(b)：单 ready + in(0) 无效 ⇒ in(1) 不接、全端口 valid=0
example : (ocDemux (n := 8) (fun k => decide (k.val = 3)) false true ocDC1 ocDC2).in1Rdy = false := by decide
example : ∀ k : Fin 8, (ocDemux (n := 8) (fun kk => decide (kk.val = 3)) false true ocDC1 ocDC2).valid k = false := by decide
-- E4(a)：in(0) 无效 + 两个 ready ⇒ controlX 到次低 CU5 且 bits 未被 in(0) 污染
example : (ocDemux (n := 8) (fun k => decide (k.val = 3 || k.val = 5)) false true ocDC1 ocDC2).bits ⟨5, by decide⟩ = ocDC2 := by decide
example : (ocDemux (n := 8) (fun k => decide (k.val = 3 || k.val = 5)) false true ocDC1 ocDC2).valid ⟨5, by decide⟩ = true := by decide
-- 无 ready：两输入都不接
example : (ocDemux (n := 8) (fun _ => false) true true ocDC1 ocDC2).in0Rdy = false := by decide
example : (ocDemux (n := 8) (fun _ => false) true true ocDC1 ocDC2).in1Rdy = false := by decide
-- 2 CU 缩放（I-4 witness 配置，D1）
example : (ocDemux (n := 2) (fun _ => true) true false ocDC1 ocDC2).valid ⟨0, by decide⟩ = true := by decide
example : (ocDemux (n := 2) (fun k => decide (k.val = 1)) true false ocDC1 ocDC2).valid ⟨1, by decide⟩ = true := by decide

end OcDemuxTests

/- ========================================================================= -/
/- 6. 写回地址/bank 计算（:593-624）与 I-11 截断定理（Q3）                     -/
/- ========================================================================= -/

/-- 写回 bank 号（:603/:605）：reg_idxw(1,0) + warp_id(widSliceHigh=1,0)，
    2 位截断加法（mod num_bank，与读侧 :103-105 同式，CollectorUnit Q4 一致） -/
def ocWbScaBankId (regIdx : BitVec 8) (wid : BitVec 3) : BitVec 2 :=
  regIdx.extractLsb' 0 2 + wid.extractLsb' 0 2

def ocWbVecBankId (regIdx : BitVec 8) (wid : BitVec 3) : BitVec 2 :=
  regIdx.extractLsb' 0 2 + wid.extractLsb' 0 2

/-- 写回标量 bank 内地址（:606，D8）：(sgpr_base(w)>>2) + (reg_idxw>>2)，
    赋值给 depth_regBank=8 位 Wire 的截断语义 = 低 8 位相加 -/
def ocWbScaAddr (sgpr : BitVec 12) (regIdx : BitVec 8) : BitVec 8 :=
  ((sgpr >>> 2).extractLsb' 0 8) + (regIdx >>> 2)

/-- 写回向量 bank 内地址（:604）：vgpr_base 11 位 >>>2 取低 8 位 -/
def ocWbVecAddr (vgpr : BitVec 11) (regIdx : BitVec 8) : BitVec 8 :=
  ((vgpr >>> 2).extractLsb' 0 8) + (regIdx >>> 2)

/-- 标量写使能（:622）：wxd & valid & reg_idxw.orR（x0 不写） -/
def ocScaWen (wxd valid : Bool) (regIdx : BitVec 8) : Bool :=
  wxd && valid && (regIdx != 0#8)

/-- **I-11 见证**（Q3）：sgpr_base=1792、reg_idxw=0 时数学地址 (1792>>2)+0=448，
    但 8 位的 wbScaBankAddr 只写向 192——bank 内地址回绕（寄存器堆侧 SyncReadMem
    深度 512 而索引只有 8 位，RegFile.lean Q3 同根因）。 -/
theorem ocI11_witness :
    ocWbScaAddr 1792#12 0#8 = 192#8 ∧ (1792 / 4 + 0 / 4 : Nat) = 448 ∧ (448 : Nat) ≠ 192 :=
  ⟨by decide, by decide, by decide⟩

/-- **I-11 别名定理**：sgpr_base 相差 1024 的两个 warp，同号寄存器的写回 bank
    内地址相同（(b+1024)>>2 ≡ b>>2 (mod 256)）——写回落到同一物理表项。 -/
theorem ocI11_alias (b : BitVec 12) (r : BitVec 8) :
    ocWbScaAddr (b + 1024#12) r = ocWbScaAddr b r := by
  unfold ocWbScaAddr
  bv_decide

/-- **I-11 完全别名**：sgpr_base 差 1024 且 warp 号差 4（wid(1,0) 相同）的两个
    warp，同号寄存器的写回 bank 号与 bank 内地址完全相同——两 warp 的写回
    串扰同一物理寄存器。 -/
theorem ocI11_full_alias (b : BitVec 12) (r : BitVec 8) (w : BitVec 3) :
    ocWbScaAddr (b + 1024#12) r = ocWbScaAddr b r ∧
      ocWbScaBankId r (w + 4#3) = ocWbScaBankId r w := by
  constructor
  · unfold ocWbScaAddr
    bv_decide
  · unfold ocWbScaBankId
    bv_decide

/-- I-11 读侧复证（:110-125 与 :606 同公式，CollectorUnit D3 已按 8 位建模）：
    sgpr_base=1792、reg_idx1=0 的标量读请求 rsAddr=192（数学值 448 的回绕）——
    同一别名同时影响读侧（操作数收集读到别 warp 的寄存器）。 -/
def ocI11ReadCtrl : CuCtrl :=
  { cuCtrl0 with sel_alu1 := cuA1_RS1, reg_idx1 := 0#8, wid := 0#3 }

theorem ocI11_read_witness :
    (cuOutArbBits cuInit
      { cuInNop with controlValid := true, ctrl := ocI11ReadCtrl, sgprBase := fun _ => 1792#12 }
      0).rsAddr = 192#8 := by decide

/-- 向量侧 base 无截断（vgpr_base<1024 ⇒ >>>2 < 256，取低 8 位无损；
    RegFile.lean Q3：向量 bank 深度 256 与 8 位索引恰好匹配） -/
theorem ocD_vec_base_no_trunc (v : BitVec 11) (h : v < 1024#11) :
    ((v >>> 2).extractLsb' 0 8).zeroExtend 11 = v >>> 2 := by bv_decide

/-- D-写回 x0 抑制（:622 的 reg_idxw.orR）：reg_idxw=0 时标量写使能恒 0 -/
theorem ocD_wb_x0_suppress (wxd valid : Bool) :
    ocScaWen wxd valid 0#8 = false := by
  cases wxd <;> cases valid <;> decide

/-- 正向：reg_idxw≠0 时写使能 = wxd && valid -/
theorem ocD_wb_wen_of_ne0 (wxd valid : Bool) (r : BitVec 8) (h : r ≠ 0#8) :
    ocScaWen wxd valid r = (wxd && valid) := by
  have h' : (r == 0#8) = false := by simp [h]
  show (wxd && valid && !(r == 0#8)) = (wxd && valid)
  rw [h']
  simp

-- 数值回归：写回计算
example : ocWbScaBankId 5#8 3#3 = 0#2 := by decide   -- 5(1,0)=1 + 3(1,0)=3 = 4 mod 4
example : ocWbScaBankId 5#8 2#3 = 3#2 := by decide
example : ocWbScaAddr 64#12 8#8 = 18#8 := by decide   -- 16+2
example : ocWbVecAddr 512#11 4#8 = 129#8 := by decide -- 128+1
example : ocWbScaAddr 1792#12 0#8 = 192#8 := by decide
example : ocScaWen true true 5#8 = true := by decide
example : ocScaWen true false 5#8 = false := by decide

/- ========================================================================= -/
/- 7. DualIssueIO（:627-664）与 E1：非 Irrevocable 的影响面（Q5）              -/
/- ========================================================================= -/

/-- inst_is_vec 触及的控制字段切片（D9；字段类型 scoreboard.scala:19-65，csr
    为 UInt(2.W) 已核实） -/
structure OcExCtrl where
  tc      : Bool
  fp      : Bool
  mul     : Bool
  sfu     : Bool
  mem     : Bool
  csr     : BitVec 2
  barrier : Bool
  isvec   : Bool

/-- inst_is_vec（:634-647）：tc|fp|mul|sfu|mem → 向量；csr.orR|barrier → 标量；
    isvec → 向量；否则标量 -/
def ocInstIsVec (c : OcExCtrl) : Bool :=
  if c.tc || c.fp || c.mul || c.sfu || c.mem then true
  else if (c.csr != 0#2) || c.barrier then false
  else c.isvec

/-- bankIn 不 fire 时 cuBankPort 恒等 -/
theorem ocCuBankPort_of_not_fire (pre : CuState) (i : CuInputs) (st : CuState) (k : Nat)
    (h : cuBankFireK pre i k = false) : cuBankPort pre i st k = st := by
  simp [cuBankPort, h]

/-- CU 在 s_out 反压滞留时 issue.bits 与 issue.valid 稳定（:155-158 状态保持、
    :258-262 只清 valid/ready 寄存器、rsReg/controlReg/mask 不动）——
    DualIssueIO 的 arb_x/arb_v 输入（:657-660）在反压期间整体稳定的来源。 -/
theorem ocE1_cu_issue_stable (s : CuState) (i : CuInputs)
    (hs : s.state = cuSOut) (hr : i.issueReady = false) :
    cuIssueBits (cuStep s i) = cuIssueBits s ∧
      cuIssueValid (cuStep s i) = true := by
  have hso : (s.state == cuSOut) = true := by simp [hs]
  have hsi : (s.state == cuSIdle) = false := by rw [hs]; decide
  have hsa : (s.state == cuSAdd) = false := by rw [hs]; decide
  have hcf : cuControlFire s i = false :=
    cuControlFire_false_of_not_idle s i (by rw [hs]; decide)
  have hif : cuIssueFire s i = false := by simp [cuIssueFire, hr]
  have hst : cuStateTrans s i = cuSOut := by
    simp [cuStateTrans, hsi, hsa, hso, hif]
  have hbf : ∀ k, cuBankFireK s i k = false :=
    fun k => cuBankFireK_false s i k (by rw [hs]; decide) hcf
  have hacc : cuAccept s i = s := by
    unfold cuAccept
    rw [if_neg (by simp [hcf])]
  have hpre : cuPreBank s i = { s with state := cuSOut, valid := 0#4, ready := 0#4 } := by
    unfold cuPreBank
    rw [if_pos hso, hacc, hst]
  have hstep : cuStep s i = cuPreBank s i := by
    simp only [cuStep]
    rw [ocCuBankPort_of_not_fire s i _ 3 (hbf 3),
        ocCuBankPort_of_not_fire s i _ 2 (hbf 2),
        ocCuBankPort_of_not_fire s i _ 1 (hbf 1),
        ocCuBankPort_of_not_fire s i _ 0 (hbf 0)]
  rw [hstep, hpre]
  constructor
  · rfl
  · simp [cuIssueValid]

/-- E1 结论（Q5）：DualIssueIO 的 arb_x/arb_v 下游有反压，但反压期间
    （ready=false）lastGrant 不变（rra3_step_not_ready），且 CU 侧 issue
    valid/bits 稳定（ocE1_cu_issue_stable；inst_is_vec 只依赖 bits，:654）
    ⇒ 过滤后 valid 向量不变 ⇒ chosen/out.bits 不变——满足 Decoupled 契约，
    RRArbiter 非 Irrevocable（rra3_not_stable）在此无实际影响。
    （读侧仲裁 out.ready 恒 true，:545-546，无反压，见 ocE1_read_fire_of_valid。） -/
theorem ocE1_dual_stable {n : Nat} (hn : 0 < n) (v v' : BitVec n) (lg : Fin n)
    (h : v' = v) :
    rraChoice hn v' (rraStep hn v false lg) = rraChoice hn v lg := by
  rw [rra3_step_not_ready, h]

-- 数值回归：inst_is_vec 优先链（:638-646）
example : ocInstIsVec ⟨false, false, false, false, false, 0#2, false, true⟩ = true := by decide
example : ocInstIsVec ⟨false, false, false, false, false, 0#2, false, false⟩ = false := by decide
example : ocInstIsVec ⟨true, false, false, false, false, 0#2, false, false⟩ = true := by decide
example : ocInstIsVec ⟨false, true, false, false, false, 1#2, false, true⟩ = true := by decide  -- fp 优先
example : ocInstIsVec ⟨false, false, false, false, false, 1#2, false, true⟩ = false := by decide -- csr 压过 isvec
example : ocInstIsVec ⟨false, false, false, false, false, 0#2, true, true⟩ = false := by decide  -- barrier 压过 isvec

/- ========================================================================= -/
/- 8. I-4 同 warp 乱序发射 witness（Q1；2 CU 缩放配置，机制与规模无关，D1）    -/
/-    轨迹：拍 T：warp5 的指令 B（含向量读操作数）经 controlV 进 CU0（最低     -/
/-    ready CU），B 的 bankIn 不返回 ⇒ CU0 停 s_add；拍 T+1：warp5 的指令 C    -/
/-    （全立即数）经 controlV 进 CU1；拍 T+2：C 到 s_out 可 issue 而 B 仍      -/
/-    在 s_add ⇒ C 先于 B 发射。                                               -/
/- ========================================================================= -/

/-- witness 系统状态：2 个 CU -/
structure OcWitState where
  cu0 : CuState
  cu1 : CuState

/-- witness 单拍输入：controlV 提供 + 共享 issue.ready（bankIn 全无效 =
    "bank 暂不返回"；controlX 不提供） -/
structure OcWitIn where
  cvValid : Bool
  cvBits  : CuCtrl
  issueRdy : Bool

/-- witness 单拍：demux（:495-512，in(0)=controlV 对应 :570）按两个 CU 的
    control.ready 分配，再各走一步 CU 状态机 -/
def ocWitStep (s : OcWitState) (i : OcWitIn) : OcWitState :=
  let rdy : Fin 2 → Bool := fun j => if j.val = 0 then cuControlRdy s.cu0 else cuControlRdy s.cu1
  let d := ocDemux rdy i.cvValid false i.cvBits cuCtrl0
  let mkIn (j : Fin 2) : CuInputs :=
    ⟨d.valid j, d.bits j, false, false, false, false, cuBI0, cuBI0, cuBI0, cuBI0,
     i.issueRdy, cuSgprB, cuVgprB⟩
  ⟨cuStep s.cu0 (mkIn ⟨0, by decide⟩), cuStep s.cu1 (mkIn ⟨1, by decide⟩)⟩

/-- 指令 B（warp 5）：sel_alu1=VRS1 向量读（:205），其余操作数走捷径——
    接受后 readyWire=1110 停 s_add 等端口 0 的向量返回（本 witness 不返回） -/
def ocI4ctrlB : CuCtrl :=
  { cuCtrl0 with wid := 5#3, sel_alu1 := cuA1_VRS1, reg_idx1 := 3#8, isvec := true, tag := 6#8 }

/-- 指令 C（warp 5，同 warp 后到）：全立即数——readyWire=0xF，接受拍直进
    s_out（:146） -/
def ocI4ctrlC : CuCtrl :=
  { cuCtrl0 with wid := 5#3, sel_alu1 := cuA1_IMM, sel_alu2 := cuA2_IMM, sel_imm := rfIMM_I, inst := 0x00530293#32, pc := 0x2000#32, tag := 7#8 }

def ocI4T0 : OcWitIn := ⟨true, ocI4ctrlB, false⟩   -- 拍 T：B 到达
def ocI4T1 : OcWitIn := ⟨true, ocI4ctrlC, false⟩   -- 拍 T+1：C 到达
def ocI4T2 : OcWitIn := ⟨false, cuCtrl0, true⟩     -- 拍 T+2：下游 issue ready

def ocI4s0 : OcWitState := ⟨cuInit, cuInit⟩
def ocI4s1 := ocWitStep ocI4s0 ocI4T0
def ocI4s2 := ocWitStep ocI4s1 ocI4T1
def ocI4s3 := ocWitStep ocI4s2 ocI4T2

/-- 拍 T 的 demux 决策：两 CU 均 ready ⇒ B 给 CU0（:497 最低 ready） -/
theorem ocI4_demux_T :
    (ocDemux (n := 2) (fun _ => true) true false ocI4ctrlB cuCtrl0).valid ⟨0, by decide⟩ = true ∧
      (ocDemux (n := 2) (fun _ => true) true false ocI4ctrlB cuCtrl0).valid ⟨1, by decide⟩ = false := by
  decide

/-- 拍 T+1 的 demux 决策：CU0 忙 ⇒ C 给 CU1 -/
theorem ocI4_demux_T1 :
    (ocDemux (n := 2) (fun j => decide (j.val = 1)) true false ocI4ctrlC cuCtrl0).valid ⟨1, by decide⟩ = true := by
  decide

/-- 拍 T 后：CU0 接受 B 并滞留 s_add（等端口 0 向量返回），CU1 保持空闲 -/
theorem ocI4_T_alloc_B :
    ocI4s1.cu0.state = cuSAdd ∧ ocI4s1.cu0.controlReg = ocI4ctrlB ∧
      ocI4s1.cu1.state = cuSIdle := by native_decide

/-- 拍 T+1 后：CU0 忙 ⇒ demux 把 C 分给 CU1；C 全立即数接受拍直进 s_out（:146）；
    CU0 仍持 B 滞留 s_add -/
theorem ocI4_T1_alloc_C :
    ocI4s2.cu1.state = cuSOut ∧ ocI4s2.cu1.controlReg = ocI4ctrlC ∧
      ocI4s2.cu0.state = cuSAdd ∧ ocI4s2.cu0.controlReg = ocI4ctrlB := by native_decide

/-- **I-4 核心 witness（Q1）**：B、C 同 warp（wid=5）且 B 先到达（拍 T 先于
    拍 T+1），但拍 T+2 时 C 已在 s_out 可发射（issue.valid=1）而 B 仍滞留
    s_add；拍 T+2 末 C 完成发射回 s_idle，B 依然滞留——同 warp 程序序被
    operandCollector 的分配策略打乱（:566 wid 比较被注释、:567 widCmp 恒 0
    死代码，instDemux 只看 CU ready）。机制与 CU 数量无关（分配定理
    ocDemux_controlV_lowest 对任意 n 成立），此处按 2 CU 缩放（D1）。 -/
theorem ocI4_C_issues_before_B :
    ocI4ctrlB.wid = ocI4ctrlC.wid ∧
      cuIssueValid ocI4s2.cu1 = true ∧ ocI4s2.cu1.controlReg = ocI4ctrlC ∧
      ocI4s2.cu0.state = cuSAdd ∧ ocI4s2.cu0.controlReg = ocI4ctrlB ∧
      ocI4s3.cu1.state = cuSIdle ∧ ocI4s3.cu0.state = cuSAdd ∧
      ocI4s3.cu0.controlReg = ocI4ctrlB := by native_decide

/- ========================================================================= -/
/- 9. 公理审计（bv_decide 引入每定理私有的 LRAT trust 公理                      -/
/-    `…._native.bv_decide.ax_…`；native_decide 引入 Lean.ofReduceBool，      -/
/-    按 AGENTS.md 归档注明）                                                 -/
/- ========================================================================= -/

#print axioms ocA_filter_rt0
#print axioms ocA_grant_sca
#print axioms ocA_no_grant3
#print axioms ocD_bank_addr_wiring
#print axioms ocE1_read_fire_of_valid
#print axioms ocXbar_valid_iff
#print axioms ocXbar_route_sca
#print axioms ocXbar_route_vec
#print axioms ocXbar_port3_never_valid
#print axioms ocE3_no_clash
#print axioms ocI12_slot3_rt0
#print axioms ocI12_cu_rsType3_run
#print axioms ocI12_xbar_hyp_of_arb
#print axioms ocI12_closure
#print axioms ocI12_deadlock_system
#print axioms ocRdy2_prio_ne
#print axioms ocDemux_controlV_lowest
#print axioms ocDemux_controlX_second
#print axioms ocDemux_E4_single_ready
#print axioms ocI11_witness
#print axioms ocI11_alias
#print axioms ocI11_full_alias
#print axioms ocI11_read_witness
#print axioms ocD_wb_x0_suppress
#print axioms ocD_wb_wen_of_ne0
#print axioms ocE1_cu_issue_stable
#print axioms ocE1_dual_stable
#print axioms ocI4_demux_T
#print axioms ocI4_demux_T1
#print axioms ocI4_T_alloc_B
#print axioms ocI4_T1_alloc_C
#print axioms ocI4_C_issues_before_B

end Ventus.Schedule
