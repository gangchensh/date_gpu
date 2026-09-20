/- ========================================================================= -/
/-                     SIMT/PcReconv.lean                                    -/
/-  bug 报告 I-31 的裁决：pc_reconv valid 直通是否导致 simt_rpc 重复入队      -/
/-                                                                           -/
/-  背景（03 报告 I-31【待确认】）：                                          -/
/-    pipe.scala:389-390                                                     -/
/-      simt_stack.io.pc_reconv.bits  := csrfile.io.simt_rpc                 -/
/-      simt_stack.io.pc_reconv.valid := issueV.io.out_SIMT.valid  //todo check this -/
/-    pc_reconv 下游是 PC_reconv_buf = Queue(io.pc_reconv, 1, flow = true)    -/
/-    （branch_join.scala:86）。疑点：若 out_SIMT 反压期间 valid 持续高，      -/
/-    flow 队列每腾出空位就重复入队同一 simt_rpc ⇒ 汇合点重复。                -/
/-                                                                           -/
/- ======================== 源码事实核查（本文件的前提） ==================== -/
/-  F1. out_SIMT 的生产者是 issueV = Module(new Issue)（pipe.scala:75）。      -/
/-      issue.scala:120-124：opcode=0（vbranch）时                            -/
/-        out_SIMT.valid := inputBuf.valid & out_SIMT.ready & out_vALU.ready  -/
/-      —— valid 被 ready **组合门控**，反压期间 valid 当即撤低，             -/
/-      "反压期间 valid 持续高"对 vbranch 结构性不可能。                      -/
/-      issue.scala:126-127：opcode=1（join）时 out_SIMT.valid := inputBuf.valid -/
/-      —— valid 可持续高（反压可达）。                                       -/
/-  F2. 两个缓冲队列同参数同复位：branch_ctl_buf = Queue(io.branch_ctl,1,flow=true) -/
/-      （branch_join.scala:84），PC_reconv_buf = Queue(io.pc_reconv,1,flow=true) -/
/-      （:86）。enq.valid 同源：io.branch_ctl.valid 与 io.pc_reconv.valid 都是 -/
/-      issueV.io.out_SIMT.valid（pipe.scala:382 `issueV.io.out_SIMT<>simt_stack.io.branch_ctl` -/
/-      与 :390）。                                                           -/
/-  F3. deq.ready 同值：branch_join.scala:124-138 的全部四个分支里            -/
/-      branch_ctl_buf.ready 与 PC_reconv_buf.ready 被赋同一个表达式           -/
/-      （if_mask_buf.fire / true.B / false.B / false.B）。                   -/
/-  F4. chisel 6.4.0 Queue 语义（依赖版本见 build.sc:32；源码                 -/
/-      src/main/scala/chisel3/util/Decoupled.scala:243-307，已逐行核对）：    -/
/-      entries=1 ⇒ Counter(1) 指针恒 0、ptr_match 恒真 ⇒ empty = !maybe_full, -/
/-      full = maybe_full；enq.ready = !full（:286，pipe=false 故无 :306 补丁）； -/
/-      deq.valid = !empty，flow 补丁 enq.valid 时 deq.valid := true（:297）；  -/
/-      deq.bits = empty ? enq.bits : ram（:293, :298-299）；                  -/
/-      do_enq 默认 enq.fire，flow 补丁 empty ∧ deq.ready 时取消（:300-301）； -/
/-      do_deq 默认 deq.fire，flow 补丁 empty 时取消（:300）；                -/
/-      do_enq ≠ do_deq 时 maybe_full := do_enq（:276-278）。                  -/
/-      关键：full ∧ deq.ready 的一拍里 do_enq = false（enq.ready = !full），  -/
/-      腾出的空位**当拍不接收**新项——producer 须再等一拍（此时队空，新项      -/
/-      flow-through 被消费恰好一次，见见证 pcrW3/pcrW4）。                   -/
/-                                                                           -/
/- ======================== 结论：I-31【已排除】 =========================== -/
/-  两条相互独立的结构性理由（均机器证明）：                                   -/
/-  R1 双队列锁步（pcrT_lockstep + pcrT_count_equal + pcrT_pending_stable）：  -/
/-     同 enq.valid、同 deq.ready、同参数、同复位 ⇒ full 状态恒等 ⇒ 入队/出队  -/
/-     点火 1:1，且挂起项不被覆盖。"同一 rpc 重复入队"要求 pc_reconv 的入队    -/
/-     点火多于 branch_ctl，被计数相等定理否定。                               -/
/-  R2 vbranch 的 valid 被 ready 门控（pcrT_vbranch_valid_gated，F1）：        -/
/-     对唯一消费 rpc 值的 opcode=0 情形，反压期间 valid 根本不持续高。        -/
/-  join（opcode=1）的 valid 可持续高，但其 rpc 值本就不被使用（PC_reconv 仅   -/
/-  用于 pushentry.reconPC，branch_join.scala:149），且由 R1 无重复入队。      -/
/-  残余脆弱性（非 bug，健壮性备注）：锁步依赖 F3 的"同值赋值"；若未来改动使   -/
/-  两队列 deq.ready 分叉（如 :119 注释掉的独立驱动被恢复且与                 -/
/-  branch_ctl_buf.ready 不同步），重复/丢失会立即出现。建议加断言。          -/
/- ========================================================================= -/

import Ventus.Base.Defs

namespace Ventus.SIMT

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. Queue(1, flow = true) 精确模型（chisel 6.4.0，Decoupled.scala:243-307） -/
/- ========================================================================= -/

/-- 队列状态：maybe_full 寄存器 + 单槽 ram。entries=1 时指针恒 0（ptr_match 恒真），
    故 empty = !full、full = maybe_full。 -/
structure PcrQ1F (α : Type) where
  full : Bool
  data : α
deriving DecidableEq

/-- 同拍输入：enq valid/bits + deq ready。 -/
structure PcrQ1FIn (α : Type) where
  enqV : Bool
  enqB : α
  deqR : Bool

/-- enq.ready = !full（:286；pipe = false 故无 :306 的 `when(deq.ready){enq.ready := true}`）。 -/
def pcrEnqReady (q : PcrQ1F α) : Bool := !q.full

/-- deq.valid = !empty，flow 补丁：enq.valid 时亦为真（:285, :297）。 -/
def pcrDeqValid (q : PcrQ1F α) (enqV : Bool) : Bool := q.full || enqV

/-- deq.bits = empty ? enq.bits : ram(0)（:293, :298-299）。 -/
def pcrDeqBits (q : PcrQ1F α) (enqB : α) : α := if q.full then q.data else enqB

/-- 消费者可见的 deq.fire = deq.valid ∧ deq.ready。 -/
def pcrDeqFire (q : PcrQ1F α) (enqV deqR : Bool) : Bool := (q.full || enqV) && deqR

/-- 内部 do_enq（:263 默认 io.enq.fire = enqV ∧ !full；
    flow 补丁 :300-301：empty ∧ deq.ready 时 do_enq := false）。 -/
def pcrDoEnq (q : PcrQ1F α) (enqV deqR : Bool) : Bool := enqV && !q.full && !deqR

/-- 内部 do_deq（:264 默认 io.deq.fire；flow 补丁 :300：empty 时 do_deq := false）。 -/
def pcrDoDeq (q : PcrQ1F α) (deqR : Bool) : Bool := q.full && deqR

/-- 单拍转移（:269-278）：do_enq 写 ram；do_enq ≠ do_deq 时 maybe_full := do_enq。
    合并化简得 full' = !deqR ∧ (full ∨ enqV)（8 种组合与原文逐分支语义的一致性
    由 pcrQ1FStep_correct 全枚举核对）。 -/
def pcrQ1FStep (q : PcrQ1F α) (i : PcrQ1FIn α) : PcrQ1F α :=
  { full := !i.deqR && (q.full || i.enqV),
    data := if pcrDoEnq q i.enqV i.deqR then i.enqB else q.data }

/-- 参考实现：直接按原文 do_enq/do_deq 与 maybe_full 更新规则（:269-278）。 -/
def pcrQ1FStepRef (q : PcrQ1F α) (i : PcrQ1FIn α) : PcrQ1F α :=
  let doEnq := pcrDoEnq q i.enqV i.deqR
  let doDeq := pcrDoDeq q i.deqR
  { full := if doEnq != doDeq then doEnq else q.full,
    data := if doEnq then i.enqB else q.data }

/-- 化简式 ≡ 参考实现（8 种 full/enqV/deqR 组合全枚举，data 任意）。 -/
theorem pcrQ1FStep_correct (q : PcrQ1F α) (i : PcrQ1FIn α) :
    pcrQ1FStep q i = pcrQ1FStepRef q i := by
  obtain ⟨f, d⟩ := q
  obtain ⟨ev, eb, dr⟩ := i
  cases f <;> cases ev <;> cases dr <;> rfl

/- ---- 数值回归测试（decide） ---- -/

-- 空队列 flow-through：enqV ∧ deqR ⇒ 不落槽（full 保持 false），deq 直通有效
theorem pcrSan_flowthrough :
    let q : PcrQ1F (BitVec 8) := ⟨false, 0⟩
    let q' := pcrQ1FStep q ⟨true, 7, true⟩
    q'.full = false ∧ q'.data = 0 ∧ pcrDeqValid q true = true ∧ pcrDeqBits q 7 = 7 := by
  decide
-- 空队列无下游：落槽
theorem pcrSan_store :
    let q : PcrQ1F (BitVec 8) := ⟨false, 0⟩
    let q' := pcrQ1FStep q ⟨true, 7, false⟩
    q'.full = true ∧ q'.data = 7 := by
  decide
-- 满队列无下游：保持，enq 被拒（数据不被覆盖）
theorem pcrSan_full_hold :
    let q : PcrQ1F (BitVec 8) := ⟨true, 5⟩
    let q' := pcrQ1FStep q ⟨true, 9, false⟩
    q'.full = true ∧ q'.data = 5 ∧ pcrEnqReady q = false := by
  decide
-- 满队列腾出空位当拍不接收新项（flow ≠ pipe）：deq 发生、full 撤、enq 被拒
theorem pcrSan_full_drain_no_enq :
    let q : PcrQ1F (BitVec 8) := ⟨true, 5⟩
    let q' := pcrQ1FStep q ⟨true, 9, true⟩
    q'.full = false ∧ q'.data = 5 ∧ pcrDoEnq q true true = false ∧
    pcrDeqFire q true true = true ∧ pcrDeqBits q 9 = 5 := by
  decide

/- ========================================================================= -/
/- 2. Issue 的 out_SIMT.valid 模型（issue.scala:118-128）与 R2               -/
/- ========================================================================= -/

/-- out_SIMT.valid：opcode=0（vbranch）时 valid = inputValid ∧ outSIMTready ∧ outVALUready
    （:121-124，valid 被 ready 组合门控）；opcode=1（join）时 valid = inputValid
    （:126-127，可持续高）。 -/
def pcrOutSIMTValid (opcode0 : Bool) (inputV simtR valuR : Bool) : Bool :=
  if opcode0 then inputV && simtR && valuR else inputV

/-- R2：vbranch（opcode=0）反压期间 valid 不可能持续高 —— ready = false ⇒ valid = false。
    因此 pc_reconv.valid（= out_SIMT.valid，pipe.scala:390）同样当即撤低。 -/
theorem pcrT_vbranch_valid_gated (inputV simtR valuR : Bool) :
    pcrOutSIMTValid true inputV simtR valuR = true → simtR = true := by
  cases simtR <;> simp [pcrOutSIMTValid]

/-- 对照：join（opcode=1）的 valid 不被门控（反压可达）——这是 I-31 疑点唯一
    可能成立的情形，其安全性由 R1（双队列锁步）覆盖。 -/
theorem pcrT_join_valid_ungated (inputV simtR valuR : Bool) :
    pcrOutSIMTValid false inputV simtR valuR = inputV := rfl

/- ========================================================================= -/
/- 3. 双队列锁步（R1）                                                       -/
/-    branch_ctl_buf 与 PC_reconv_buf：同 enq.valid（F2）、同 deq.ready（F3）、 -/
/-    同参数同复位（F2）⇒ full 状态恒等。                                     -/
/- ========================================================================= -/

/-- 双队列：ctl = branch_ctl_buf，rpc = PC_reconv_buf。 -/
structure PcrPair (α : Type) (β : Type) where
  ctl : PcrQ1F α
  rpc : PcrQ1F β

/-- 同拍共享输入：enqV = out_SIMT.valid，deqR = 共同的就绪信号（F3）。 -/
def pcrPairStep (p : PcrPair α β) (enqV : Bool) (cb : α) (rb : β) (deqR : Bool) :
    PcrPair α β :=
  { ctl := pcrQ1FStep p.ctl ⟨enqV, cb, deqR⟩, rpc := pcrQ1FStep p.rpc ⟨enqV, rb, deqR⟩ }

/-- 锁步不变量：两队列 full 状态恒等。 -/
def pcrLockstep (p : PcrPair α β) : Prop := p.ctl.full = p.rpc.full

/-- 锁步保持（全证）：任意共享输入下不变量保持。 -/
theorem pcrT_lockstep (p : PcrPair α β) (enqV : Bool) (cb : α) (rb : β) (deqR : Bool)
    (h : pcrLockstep p) : pcrLockstep (pcrPairStep p enqV cb rb deqR) := by
  have h' : p.ctl.full = p.rpc.full := h
  simp [pcrLockstep, pcrPairStep, pcrQ1FStep, h']

/-- 入队点火 1:1（全证）：锁步下两队列 do_enq 相同 —— 每个 rpc 入队都有唯一
    对应的 branch_ctl 入队，反之亦然。 -/
theorem pcrT_enqFire_eq (p : PcrPair α β) (h : pcrLockstep p) (enqV deqR : Bool) :
    pcrDoEnq p.ctl enqV deqR = pcrDoEnq p.rpc enqV deqR := by
  have h' : p.ctl.full = p.rpc.full := h
  simp [pcrDoEnq, h']

/-- 出队点火 1:1（全证）：锁步下两队列 deq.fire 相同 —— 消费也 1:1。 -/
theorem pcrT_deqFire_eq (p : PcrPair α β) (h : pcrLockstep p) (enqV deqR : Bool) :
    pcrDeqFire p.ctl enqV deqR = pcrDeqFire p.rpc enqV deqR := by
  have h' : p.ctl.full = p.rpc.full := h
  simp [pcrDeqFire, h']

/-- 挂起项不被覆盖（全证）：full 期间 do_enq = false，data 保持不变 ——
    反压期间持续高的 valid 不会导致重复写入。 -/
theorem pcrT_pending_stable (q : PcrQ1F α) (i : PcrQ1FIn α) (h : q.full = true) :
    (pcrQ1FStep q i).data = q.data := by
  simp [pcrQ1FStep, pcrDoEnq, h]

/-- 带计数轨迹：c1/c2 = 两队列各自的入队点火累计数。 -/
def pcrRunC (p : PcrPair α β) (c1 c2 : Nat) : List (Bool × α × β × Bool) → Nat × Nat
  | [] => (c1, c2)
  | (enqV, cb, rb, dr) :: t =>
      pcrRunC (pcrPairStep p enqV cb rb dr)
        (c1 + (if pcrDoEnq p.ctl enqV dr then 1 else 0))
        (c2 + (if pcrDoEnq p.rpc enqV dr then 1 else 0)) t

/-- 计数相等（全证）：任意轨迹、任意起点，两队列入队点火次数恒等。 -/
theorem pcrT_count_equal (p : PcrPair α β) (t : List (Bool × α × β × Bool)) (n : Nat)
    (h : pcrLockstep p) : (pcrRunC p n n t).1 = (pcrRunC p n n t).2 := by
  induction t generalizing p n with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨enqV, cb, rb, dr⟩ := hd
    have hfire := pcrT_enqFire_eq p h enqV dr
    have hstep := pcrT_lockstep p enqV cb rb dr h
    simp only [pcrRunC]
    rw [hfire]
    exact ih _ _ hstep

/-- 双队列从空（复位）初始化。 -/
def pcrPairInit (cd : α) (rd : β) : PcrPair α β := ⟨⟨false, cd⟩, ⟨false, rd⟩⟩

theorem pcrPairInit_lockstep (cd : α) (rd : β) : pcrLockstep (pcrPairInit cd rd) := rfl

/-- I-31 主结论（已排除）：从复位状态出发的任意输入轨迹下，pc_reconv 与 branch_ctl
    的入队点火次数恒相等。"同一 simt_rpc 被重复入队"要求 pc_reconv 点火次数严格更多，
    与本定理矛盾；结合 pcrT_pending_stable（挂起不覆盖），重复入队/重复弹出的机制
    不成立。 -/
theorem pcrMain_i31_excluded (cd : α) (rd : β) (t : List (Bool × α × β × Bool)) (n : Nat) :
    (pcrRunC (pcrPairInit cd rd) n n t).1 = (pcrRunC (pcrPairInit cd rd) n n t).2 :=
  pcrT_count_equal _ t n (pcrPairInit_lockstep cd rd)

/- ========================================================================= -/
/- 4. 见证轨迹（native_decide）：join 反压 4 拍——疑点场景真实走完一遍       -/
/-    A = 第一个 join（c1 入缓冲），B = 第二个 join（反压期间 producer 持有）。 -/
/-    结论：B 被消费恰好一次（c4 flow-through），A 恰好一次（c3 从 ram），     -/
/-    反压拍（c2）无任何入队。                                                -/
/- ========================================================================= -/

section PcrWitness

def wA : BitVec 32 := 0xAAAA0000   -- A 的 branch_ctl 标签
def wAr : BitVec 32 := 0xAAAA0008  -- A 对应的 simt_rpc
def wB : BitVec 32 := 0xBBBB0000
def wBr : BitVec 32 := 0xBBBB0008

def wS0 : PcrPair (BitVec 32) (BitVec 32) := pcrPairInit 0 0
def wS1 := pcrPairStep wS0 true wA wAr false   -- c1: 下游不就绪，A 落槽
def wS2 := pcrPairStep wS1 true wB wBr false   -- c2: 反压，valid 持续高，B 被持有
def wS3 := pcrPairStep wS2 true wB wBr true    -- c3: 下游消费 A；full 故 B 当拍不被接收
def wS4 := pcrPairStep wS3 true wB wBr true    -- c4: 队空，B flow-through 被消费

def wTrace : List (Bool × BitVec 32 × BitVec 32 × Bool) :=
  [(true, wA, wAr, false), (true, wB, wBr, false), (true, wB, wBr, true), (true, wB, wBr, true)]

-- c1：A 同时落入两队列（锁步）
theorem pcrW1_store :
    wS1.ctl.full = true ∧ wS1.rpc.full = true ∧
    wS1.ctl.data = wA ∧ wS1.rpc.data = wAr := by
  native_decide
-- c2（关键反压拍）：valid 持续高但无入队点火、挂起的 rpc 不被覆盖
theorem pcrW2_stall_no_dup :
    pcrDoEnq wS1.rpc true false = false ∧ pcrDoEnq wS1.ctl true false = false ∧
    wS2.rpc.full = true ∧ wS2.rpc.data = wAr ∧ wS2.ctl.data = wA := by
  native_decide
-- c3：A 被两队列同时消费（deq.fire 1:1、读出的是 ram 里的 A/wAr）；
--     B 因 enq.ready = !full = false 当拍仍不被接收（producer 继续持有）
theorem pcrW3_drain_A :
    pcrDeqFire wS2.ctl true true = true ∧ pcrDeqFire wS2.rpc true true = true ∧
    pcrDeqBits wS2.ctl wB = wA ∧ pcrDeqBits wS2.rpc wBr = wAr ∧
    pcrDoEnq wS2.ctl true true = false ∧ pcrDoEnq wS2.rpc true true = false ∧
    wS3.ctl.full = false ∧ wS3.rpc.full = false := by
  native_decide
-- c4：B flow-through 被消费恰好一次（deq.bits 直通为 wB/wBr，不落槽、无残留）
theorem pcrW4_flow_B_once :
    pcrDeqFire wS3.ctl true true = true ∧ pcrDeqFire wS3.rpc true true = true ∧
    pcrDeqBits wS3.ctl wB = wB ∧ pcrDeqBits wS3.rpc wBr = wBr ∧
    pcrDoEnq wS3.rpc true true = false ∧ wS4.ctl.full = false ∧ wS4.rpc.full = false := by
  native_decide
-- 整条轨迹：两队列入队点火各恰好 1 次（A 的那一次）
theorem pcrW5_count :
    (pcrRunC wS0 0 0 wTrace).1 = 1 ∧ (pcrRunC wS0 0 0 wTrace).2 = 1 := by
  native_decide

end PcrWitness

/- ---- 公理审计（全证定理应仅剩 Lean 标准公理；witness 为 native_decide，
       公理含 Lean.ofReduceBool，属预期，见 AGENTS.md 已知踩坑） ---- -/

#print axioms pcrQ1FStep_correct
#print axioms pcrT_lockstep
#print axioms pcrT_enqFire_eq
#print axioms pcrT_deqFire_eq
#print axioms pcrT_pending_stable
#print axioms pcrT_count_equal
#print axioms pcrT_vbranch_valid_gated
#print axioms pcrMain_i31_excluded
-- native_decide 见证的审计（预期含 Lean.ofReduceBool）
#print axioms pcrW2_stall_no_dup
#print axioms pcrW5_count

end Ventus.SIMT
