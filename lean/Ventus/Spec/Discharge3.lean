/- ========================================================================= -/
/-                      Spec/Discharge3.lean                                 -/
/-  契约核销第三波：Contracts.lean 登记册两个残余缺口的收口                     -/
/-  （BJB-1 的 B1 前提 / WB-A1 的 (a)(b)(c) 三缺口）                          -/
/-                                                                           -/
/-  纪律：namespace Ventus.Spec；辅助名一律 dcg3 前缀；只新建本文件。          -/
/-                                                                           -/
/- ======================== 核销结论一览（详见各节头注） ======================-/
/-  1. BJB-1 的 B1 缺口（wid/bits 传输完整性：exe_dataV→issueV→out_SIMT→      -/
/-     branch_ctl_buf）——**核销（组合链全闭合 + 队列保真在抽象层闭合）**：      -/
/-     (i) 无状态段全部为组合直通，逐段 rfl 钉死：exe_dataV 匿名模块            -/
/-         （pipe.scala:122-128，deq<>enq）、:371/:382 两段 <>（pipeConn）、    -/
/-         Issue 的 Queue(in,0) 零深度直通（issue.scala:57，Issue.lean D1）、   -/
/-         out_SIMT bits 五字段装配（issue.scala:70-74）——                      -/
/-         dcg3Bjb1CombChain + dcg3_bjb1_chain_*；                              -/
/-         :293 input_wid 与 :362 ctrl 同源（dcg3_bjb1_inputWid_same_source）。 -/
/-     (ii) 唯一的状态环节 branch_ctl_buf（branch_join.scala:84，                -/
/-         Queue(1,flow=true)）的 bits 保真在 QueueModel 抽象层闭合：           -/
/-         dcg3_queue_hist_fidelity（deqHist 是 enqHist 前缀的逐点形式）+        -/
/-         dcg3_bjb1_flow_through（flow 直通拍 = 先入后出）。                  -/
/-     (iii) 配对门（branch_join.scala:125）：beqv 双发使 SIMT 侧与 vALU 侧     -/
/-         wid 同源（issue.scala:64 vs :72，iss_dual_valid_coupled 保证同拍     -/
/-         消费同一 inputBuf 事务；execution.scala:467/:562 的 wid 直通）——     -/
/-         dcg3_bjb1_wid_pair_gate。                                            -/
/-     主定理 dcg3_bjb1_end_to_end：在 B2（读-消费窗口掩码不变，Discharge2      -/
/-     既有前提，由 beq 门控支撑）下掩码纪律闭合。                              -/
/-     **残余义务**（降级为连线/精化级，非逻辑缺口）：具体 Chisel               -/
/-     Queue(1,flow=true) ⇒ QueueModel AQueue cap1 的 Simulates 精化未证        -/
/-     （同 H-IB2I 一类的方法论降级）；if_mask 侧 result2simt（Queue(1,pipe)）  -/
/-     同理。                                                                   -/
/-  2. WB-A1(a)（CSR vgpr_base_dispatch 写入点，CSR.scala:300-301）——**核销**： -/
/-     写时机：仅 CTA 派发拍（ctaValid ∧ ctaWid 命中该 warp），其余节拍/其余    -/
/-     warp 不变（dcg3_wba1_csrExe_write_point + csrExe_untouched 既有定理）；  -/
/-     写值 = zext11(splitVgpr) = zext11(vgprBase + wf_id×perWf) 且             -/
/-     wfTagDispatch = wf_id 同拍配对（dcg3_wba1_capstone，组合                 -/
/-     dcg2_cuif_split_base）。派发链四段组合直通（GPGPU_top.scala:94、         -/
/-     CTA2warp.scala:82-83 同拍、warp_schedule.scala:58-59 转发、              -/
/-     pipe.scala:163）以 hsrcV/hsrcT 接线前提显式化——CTA2warp 的 I-25        -/
/-     tag 迟读污染不影响本链（:82-83 是同拍组合赋值，不经 data 寄存器阵列）。  -/
/-  3. WB-A1(b)（对齐前提 k | vgprBase ∧ k | perWf）——**核实结论：分配侧不    -/
/-     保证 4 对齐，这是真发现**：resource_table 分配粒度 = 1 个寄存器          -/
/-     （基址 = 空段起点，无取整；resource_table.scala:305-311），              -/
/-     num_vgpr/num_vgpr_per_wf 均为 host 直传参数（GPGPU_top.scala:76-79），   -/
/-     全链路无任何对齐检查/取整。                                              -/
/-     正面闭合（条件形式）：dcg3_wba1_rt_run_aligned +                           -/
/-     dcg3_wba1_next_alloc_aligned——**若 host 保证每个 WG 的 num_vgpr          -/
/-     k-对齐，则所有分配基址 k-对齐**（归纳于分配/回收步进）；perWf 的          -/
/-     k-对齐是纯 host 契约（dcg3_wba1_perWf_unaligned_breaks）。               -/
/-     反例 witness：dcg3RtMisalign（首 WG 尺寸 5 ⇒ 下一基址 5，4∤5）+          -/
/-     dcg3_wba1_misalign_collision（非对齐基址下 rsAddr 公式失真：寄存器 8      -/
/-     与寄存器 4 撞同一 bank 地址 1）——即 dcg2_wba1_bank_disjoint 的 halB     -/
/-     前提被违反时 bank 不交结论确实有洞。宿主纪律（4 | num_vgpr ∧            -/
/-     4 | num_vgpr_per_wf）是该前提的唯一支撑。                               -/
/-  4. WB-A1(c)（尺寸关系 numWf×perWf ≤ vgprSize）——**核实结论：纯 host        -/
/-     契约，硬件无检查**：numWf 与 perWf 都源于 host（GPGPU_top.scala:72-79），-/
/-     cu_interface.scala:96 的仿真断言只挡「越出整个 1024 寄存器堆」、不挡     -/
/-     「越出本 WG 分配区间」（dcg3_wba1_hw_assert_too_weak：S=32/numWf=8/      -/
/-     perWf=32 时断言全程通过而区间越界 7 倍）。破洞形式：                     -/
/-     dcg3_wba1_fit_violation（numWf×perWf > vgprSize ⇒ 末 WF 区间与相邻 WG    -/
/-     相交，specIntervalDisjoint 被破坏）。                                    -/
/- ========================================================================= -/

import Ventus.Spec.Discharge2
import Ventus.Schedule.Issue
import Ventus.Arith.CSR
import Ventus.Base.QueueModel

namespace Ventus.Spec

open Ventus.Schedule Ventus.SIMT Ventus.CTA Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. BJB-1 的 B1 缺口：wid/bits 传输完整性链                                  -/
/-    链：pipe.scala:362-366（exe_dataV enq 装配）→ exe_dataV（:122-128        -/
/-    deq<>enq 直通）→ :371 issueV.io.in → issue.scala:57（Queue(in,0) 直通）  -/
/-    → :70-74（out_SIMT bits 装配）→ pipe.scala:382（<> branch_ctl）→         -/
/-    branch_join.scala:84（branch_ctl_buf = Queue(1,flow=true)）→ :114-117    -/
/-    （warp_id := branch_ctl_buf.bits.wid 等）。                               -/
/- ========================================================================= -/

/-- issue.scala out_SIMT bits 装配的输入侧子集（vExeData 相关字段）：
    wid = ctrl.wid；op = ctrl.simt_stack_op；pc = ctrl.pc；in30 = in3(0)；
    mask = mask.asUInt（pipe.scala:366 已为 instrMask ∧ out_mask） -/
structure Dcg3VExeBits where
  wid : BitVec 3
  op : BitVec 1
  pc : BitVec 32
  in30 : BitVec 32
  mask : BitVec 32
deriving DecidableEq, Repr

/-- simtExeData（SIMT_STACK.scala:374-380 的活版本字段集；spike_info 不建模） -/
structure Dcg3SimtExe where
  opcode : BitVec 1
  wid : BitVec 3
  pcBranch : BitVec 32
  pcExecute : BitVec 32
  maskInit : BitVec 32
deriving DecidableEq, Repr

/-- L1（pipe.scala:362-366）：exe_dataV.io.enq 装配——ctrl 逐字段直通
    （wid/simt_stack_op/pc/in3(0)），mask = 指令掩码 ∧ simt_stack.out_mask -/
def dcg3ExeDataVEnq (wid : BitVec 3) (op : BitVec 1) (pc in30 : BitVec 32)
    (instrMask outMask : BitVec 32) : Dcg3VExeBits where
  wid := wid
  op := op
  pc := pc
  in30 := in30
  mask := pipeExeDataVMask instrMask outMask

/-- L2（pipe.scala:122-128）：exe_dataV 匿名模块 deq<>enq——纯组合直通 -/
def dcg3ExeDataVPass (x : Dcg3VExeBits) : Dcg3VExeBits := x

/-- L4（issue.scala:57）：inputBuf = Queue.apply(io.in, 0) 零深度 = 组合直通
    （Issue.lean D1） -/
def dcg3IssueInputBuf (x : Dcg3VExeBits) : Dcg3VExeBits := x

/-- L5（issue.scala:70-74）：out_SIMT.bits 的字段装配 -/
def dcg3IssueOutSimtBits (x : Dcg3VExeBits) : Dcg3SimtExe where
  opcode := x.op
  wid := x.wid
  pcBranch := x.in30
  pcExecute := x.pc
  maskInit := x.mask

/-- **B1 组合链（无状态段全闭合）**：:362-366 装配 → exe_dataV 直通 →
    :371（pipeConn）→ inputBuf → out_SIMT bits → :382（pipeConn）→
    simt_stack.io.branch_ctl 入口。 -/
def dcg3Bjb1CombChain (wid : BitVec 3) (op : BitVec 1) (pc in30 : BitVec 32)
    (instrMask outMask : BitVec 32) : Dcg3SimtExe :=
  pipeConn (dcg3IssueOutSimtBits (dcg3IssueInputBuf (pipeConn (dcg3ExeDataVPass
    (dcg3ExeDataVEnq wid op pc in30 instrMask outMask)))))

/-- 链保真（wid）：出口 wid = 源指令 ctrl.wid -/
theorem dcg3_bjb1_chain_wid (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    (dcg3Bjb1CombChain w o pc i3 im om).wid = w := rfl

/-- 链保真（mask_init）：= :366 的执行掩码（instrMask ∧ outMask） -/
theorem dcg3_bjb1_chain_maskInit (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    (dcg3Bjb1CombChain w o pc i3 im om).maskInit = pipeExeDataVMask im om := rfl

/-- 链保真（opcode） -/
theorem dcg3_bjb1_chain_opcode (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    (dcg3Bjb1CombChain w o pc i3 im om).opcode = o := rfl

/-- 链保真（PC_branch = in3(0)，issue.scala:70） -/
theorem dcg3_bjb1_chain_pcBranch (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    (dcg3Bjb1CombChain w o pc i3 im om).pcBranch = i3 := rfl

/-- 链保真（PC_execute = ctrl.pc，issue.scala:71） -/
theorem dcg3_bjb1_chain_pcExecute (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    (dcg3Bjb1CombChain w o pc i3 im om).pcExecute = pc := rfl

/-- B1 读拍同源（pipe.scala:293 vs :362）：simt_stack.io.input_wid 与 exe_dataV
    enq 的 ctrl.wid 是同一个 out(0).bits.control.wid——:366 掩码计算所用的
    warp 索引恰是被传输指令自身的 wid（消费拍 warp_id 经队列保真后同值） -/
theorem dcg3_bjb1_inputWid_same_source (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32)
    (im om : BitVec 32) :
    dcg2BjInputWid w = (dcg3Bjb1CombChain w o pc i3 im om).wid := rfl

/-- vALU 侧 if_mask 的 wid 来源（execution.scala:467/:562
    result2simt.enq.bits.wid := in.bits.ctrl.wid；in = issueV.out_vALU，
    其 bits = 同一 inputBuf.bits，issue.scala:64） -/
def dcg3ValuSimtWid (x : Dcg3VExeBits) : BitVec 3 := x.wid

/-- **B1 配对面**（branch_join.scala:125 的 wid 配对门）：beqv 双发下 SIMT 侧
    与 vALU 侧的 wid 同源（同一 inputBuf 事务；iss_dual_valid_coupled 保证两路
    同拍消费），两侧队列保真（dcg3_queue_hist_fidelity 型）时配对门恒成立 -/
theorem dcg3_bjb1_wid_pair_gate (x : Dcg3VExeBits) :
    ((dcg3IssueOutSimtBits x).wid == dcg3ValuSimtWid x) = true := beq_self_eq_true _

/- ---- B1 的状态环节：branch_ctl_buf 的队列保真（QueueModel 抽象层） ---- -/

/-- 队列保真（QueueModel Hist 的逐点形式）：任意操作历史下，第 i 个出队元素
    = 第 i 个入队元素（i 在已出队范围内）——FIFO 顺序保持（Hist.run_prefix）
    的逐点推论。 -/
theorem dcg3_queue_hist_fidelity {α : Type} {cap : Nat} (h0 : Hist α cap)
    (ops : List (AOp α)) (hf : Hist α cap) (hrun : h0.run ops = some hf)
    (i : Nat) (hi : i < hf.deqHist.length) :
    hf.deqHist[i]? = hf.enqHist[i]? := by
  obtain ⟨t, ht⟩ := (Hist.run_prefix h0 ops hf hrun).1
  rw [← ht, List.getElem?_append_left hi]

/-- branch_ctl_buf（Queue(1,flow=true)，branch_join.scala:84）的 flow 直通拍
    在抽象操作序列上映射为「先入后出」：空队列同拍出入的输出 bits = 入队 bits -/
theorem dcg3_bjb1_flow_through {α : Type} (x : α) :
    aSteps (AQueue.empty : AQueue α 1) [.enq x, .deq] = some ([x], AQueue.empty) := by
  obtain ⟨q', henq, hdeq⟩ := AQueue.fifo_single x Nat.zero_lt_one
  have hs1 := aStep_enq henq
  have hs2 := aStep_deq hdeq
  simp only [aSteps, hs1, hs2, Option.toList, List.append_nil, List.nil_append]

/-- **B1 队列段（定位形式）**：第 i 个被消费的 branch_ctl 事务逐字段等于
    第 i 个入队事务（= 源指令经组合链的输出） -/
theorem dcg3_bjb1_consumed_entry (h0 : Hist Dcg3SimtExe 1)
    (ops : List (AOp Dcg3SimtExe)) (hf : Hist Dcg3SimtExe 1)
    (hrun : h0.run ops = some hf)
    (w : BitVec 3) (o : BitVec 1) (pc i3 : BitVec 32) (im om : BitVec 32)
    (i : Nat) (hi : i < hf.deqHist.length)
    (henq : hf.enqHist[i]? = some (dcg3Bjb1CombChain w o pc i3 im om)) :
    hf.deqHist[i]? = some (dcg3Bjb1CombChain w o pc i3 im om) := by
  rw [dcg3_queue_hist_fidelity h0 ops hf hrun i hi, henq]

/-- 前缀的隶属传递：出队历史的元素都是入队历史的元素 -/
theorem dcg3_deq_mem_enq {α : Type} {cap : Nat} (h0 : Hist α cap)
    (ops : List (AOp α)) (hf : Hist α cap) (hrun : h0.run ops = some hf)
    (e : α) (he : e ∈ hf.deqHist) : e ∈ hf.enqHist := by
  obtain ⟨t, ht⟩ := (Hist.run_prefix h0 ops hf hrun).1
  rw [← ht]
  exact List.mem_append_left _ he

/-- **BJB-1 的 B1 前提核销（端到端形）**：设被消费的 branch_ctl_buf 表项 e
    来自某个操作历史（h0/ops/hf），且每个入队事务都是某条源指令经组合链的
    输出（hsrc，由 dcg3Bjb1CombChain 各段 rfl 闭合；outMask 取读拍的
    tm (wsFin w)，:366+:293 同源连线），消费拍 bi.maskInit 取自 e（:141-142）、
    B2 时序前提（htm：读-消费窗口该 warp 活跃掩码不变，由 beq 门控支撑，
    见 Discharge2 头注与 pipe_i4_gate_chain_beq）——则掩码纪律成立。
    B1（dcg2_bjb1_consume 的 htr）在此完全闭合。 -/
theorem dcg3_bjb1_end_to_end {depth : Nat} [NeZero depth]
    (s : BjSysState depth 32) (bi : BjBranchIn 32)
    (tm : Fin 8 → BitVec 32)
    (h0 : Hist Dcg3SimtExe 1) (ops : List (AOp Dcg3SimtExe)) (hf : Hist Dcg3SimtExe 1)
    (hrun : h0.run ops = some hf)
    (e : Dcg3SimtExe) (he : e ∈ hf.deqHist)
    (hsrc : ∀ x ∈ hf.enqHist, ∃ w o p i3 m,
      x = dcg3Bjb1CombChain w o p i3 m (tm (wsFin w)))
    (hbi : bi.maskInit = e.maskInit)
    (htm : s.tmask = tm (wsFin e.wid)) :
    bjbMaskDiscipline s bi := by
  obtain ⟨w, o, p, i3, m, hx⟩ := hsrc e (dcg3_deq_mem_enq h0 ops hf hrun e he)
  subst hx
  exact dcg2_bjb1_consume s bi tm w _ m hbi rfl htm

/-- dcg2_bjb1_consume 的前提 B1 实例化形：bufWid 取组合链出口（= 源 wid，rfl） -/
theorem dcg3_bjb1_consume_closed {depth : Nat} [NeZero depth]
    (s : BjSysState depth 32) (bi : BjBranchIn 32)
    (tm : Fin 8 → BitVec 32) (w : BitVec 3) (instrMask : BitVec 32)
    (hmi : bi.maskInit = pipeExeDataVMask instrMask (tm (wsFin w)))
    (htm : s.tmask = tm (wsFin w)) :
    bjbMaskDiscipline s bi :=
  dcg2_bjb1_consume s bi tm w w instrMask hmi rfl htm

/- ---- B1 数值回归 ---- -/

section Dcg3Bjb1Tests

-- 具体指令经组合链：五字段逐一对应（mask = 0xFF00FF00 ∧ 0x0F0F0F0F = 0x0F000F00）
example : dcg3Bjb1CombChain 5#3 1#1 0x100#32 0x200#32 0xFF00FF00#32 0x0F0F0F0F#32 =
    ⟨1#1, 5#3, 0x200#32, 0x100#32, 0x0F000F00#32⟩ := by decide

-- 队列保真数值镜像（cap 1，flow 配置）：先通后入
example : ((Hist.empty : Hist (BitVec 8) 1).run [.enq 5, .deq, .enq 7]).map
    (fun h => (h.enqHist, h.deqHist)) = some ([5#8, 7#8], [5#8]) := by decide

-- 满队列同拍出入（enqDeq）：出旧入新
example : ((Hist.empty : Hist (BitVec 8) 1).run [.enq 5, .enqDeq 7]).map
    (fun h => (h.enqHist, h.deqHist, h.q.items)) = some ([5#8, 7#8], [5#8], [7#8]) := by decide

end Dcg3Bjb1Tests

/- ========================================================================= -/
/- 2. WB-A1(a)：CSR vgpr_base_dispatch 写入点（CSR.scala:296-313 的 CTA 链，   -/
/-    :300-301 的 sgpr/vgpr 基址写入；CSRexe 路由 :338-355）                    -/
/- ========================================================================= -/

/-- CTA 派发拍的 vgprBase 写入（:301）：ctaValid 时无条件覆盖为该拍
    dispatch2cu_vgpr_base_dispatch（与写链无关，:296-313 与 :257-295 更新
    不相交——CSR.lean Q10） -/
theorem dcg3_wba1_csr_vgpr_of_cta (s : Ventus.Arith.CsrState) (i : Ventus.Arith.CsrInputs)
    (h : i.ctaValid = true) :
    (Ventus.Arith.csrStep s i).vgprBase = i.ctaVgprBase := by
  unfold Ventus.Arith.csrStep
  rw [if_pos h]

/-- CTA 派发拍的 wfTagDispatch 写入（:302）：= wf_tag 的低 depth_warp=3 位
    （= wf_id，cuifWfTag 布局的 wf 半）零扩展回 6 位 -/
theorem dcg3_wba1_csr_tag_of_cta (s : Ventus.Arith.CsrState) (i : Ventus.Arith.CsrInputs)
    (h : i.ctaValid = true) :
    (Ventus.Arith.csrStep s i).wfTagDispatch =
      BitVec.zeroExtend 6 (i.ctaWfTag.extractLsb' 0 3) := by
  unfold Ventus.Arith.csrStep
  rw [if_pos h]

/-- **WB-A1(a) 写入点（CSRexe 级）**：CTA 派发拍且 ctaWid 命中 warp k 时，
    warp k 的 CSRFile 写入新基址与 wf_id；其余 warp 不变
    （Ventus.Arith.csrExe_untouched，独热使能 :354-355）。 -/
theorem dcg3_wba1_csrExe_write_point (f : Fin 8 → Ventus.Arith.CsrState) (fire : Bool)
    (wid ctaWid : BitVec 3) (i : Ventus.Arith.CsrInputs) (k : Fin 8)
    (hcta : i.ctaValid = true) (hk : (ctaWid == BitVec.ofNat 3 k.val) = true) :
    (Ventus.Arith.csrExeStep f fire wid ctaWid i k).vgprBase = i.ctaVgprBase ∧
    (Ventus.Arith.csrExeStep f fire wid ctaWid i k).wfTagDispatch =
      BitVec.zeroExtend 6 (i.ctaWfTag.extractLsb' 0 3) := by
  have hsel : (Ventus.Arith.csrPerWarpInput i fire wid ctaWid
      (BitVec.ofNat 3 k.val)).ctaValid = true := by
    show (i.ctaValid && (ctaWid == BitVec.ofNat 3 k.val)) = true
    rw [Bool.and_eq_true]
    exact ⟨hcta, hk⟩
  have hv := dcg3_wba1_csr_vgpr_of_cta (f k) _ hsel
  have ht := dcg3_wba1_csr_tag_of_cta (f k) _ hsel
  exact ⟨hv, ht⟩

/-- WB-A1(a) 派发链的宽度衔接（10b → 11b 零扩展）：cu_wf_new.bits.vgpr_base
    （splitter_vgpr_addr，10b，cu_interface.scala:74,105）→ CTAreqData 的
    dispatch2cu_vgpr_base_dispatch（11b，GPGPU_top.scala:94）→ CTA2warp 同拍
    直通（CTA2warp.scala:82-83：warpReq.bits.CTAdata := CTAreq.bits，与
    warpReq.valid := CTAreq.fire 同拍——不经 data 寄存器阵列，I-25 的迟读
    污染与本链无关）→ warp_sche 纯转发（warp_schedule.scala:58-59）→
    csrfile（pipe.scala:163）。四段全组合直通，唯一变换是零扩展。 -/
def dcg3CtaVgprPath (v : BitVec 10) : BitVec 11 := BitVec.zeroExtend 11 v

theorem dcg3_cta_vgpr_path_eq (v : BitVec 10) :
    dcg3CtaVgprPath v = BitVec.zeroExtend 11 v := rfl

/-- **WB-A1(a) 派发侧一致性**：cuif 拆发中第 k = numWf - splitCnt 个 WF 的
    下发值 = zext11(splitVgpr) = zext11(vgprBase + k×perWf)，且与 wf_tag 的
    wf_id 同源配对（dcg2_cuif_split_base，补 G3 vgpr 半边的既有核销） -/
theorem dcg3_wba1_dispatch_consistent (s : CuifState) (h : CuifInv s)
    (hv : dcg2CuifSplitVgprInv s) (hc : s.splitCnt ≠ 0#4) :
    ∃ h' t, s.fifo = h' :: t ∧
      cuifWfNewTag s = cuifWfTag h'.wgSlotId ((h'.numWf - s.splitCnt).extractLsb' 0 3) ∧
      dcg3CtaVgprPath s.splitVgpr = BitVec.zeroExtend 11
        (h'.vgprBase + (h'.numWf - s.splitCnt).zeroExtend 10 *
          h'.numVgprPerWf.extractLsb' 0 10) := by
  obtain ⟨h', t, hfifo, htag, hbase⟩ := dcg2_cuif_split_base s h hv hc
  refine ⟨h', t, hfifo, htag, ?_⟩
  show BitVec.zeroExtend 11 s.splitVgpr = BitVec.zeroExtend 11 _
  rw [hbase]

/-- WB-A1(a) 写入值 = 派发值（接线前提 hsrc 下的直接组合） -/
theorem dcg3_wba1_csr_gets_split_base (f : Fin 8 → Ventus.Arith.CsrState) (fire : Bool)
    (wid ctaWid : BitVec 3) (i : Ventus.Arith.CsrInputs) (k : Fin 8) (v : BitVec 10)
    (hcta : i.ctaValid = true) (hk : (ctaWid == BitVec.ofNat 3 k.val) = true)
    (hsrc : i.ctaVgprBase = dcg3CtaVgprPath v) :
    (Ventus.Arith.csrExeStep f fire wid ctaWid i k).vgprBase = BitVec.zeroExtend 11 v := by
  rw [(dcg3_wba1_csrExe_write_point f fire wid ctaWid i k hcta hk).1, hsrc,
    dcg3_cta_vgpr_path_eq]

/-- **WB-A1(a) 总核销**：cuif 拆发状态（dcg2_cuif_split_base 配对）+ 四段组合
    直通接线前提（hsrcV/hsrcT）下，CTA 派发拍写入 hw slot k 的 CSR 表项满足
    vgprBase = zext11(vgprBase_wg + wf_id×perWf) 且 wfTagDispatch = wf_id——
    「写入点 = CTA 派发拍（且仅此时），写入值与 CTA 派发逐拍一致」。 -/
theorem dcg3_wba1_capstone (s : CuifState) (hinv : CuifInv s)
    (hv : dcg2CuifSplitVgprInv s) (hc : s.splitCnt ≠ 0#4)
    (f : Fin 8 → Ventus.Arith.CsrState) (fire : Bool) (wid ctaWid : BitVec 3)
    (i : Ventus.Arith.CsrInputs) (k : Fin 8)
    (hcta : i.ctaValid = true) (hk : (ctaWid == BitVec.ofNat 3 k.val) = true)
    (hsrcV : i.ctaVgprBase = dcg3CtaVgprPath s.splitVgpr)
    (hsrcT : i.ctaWfTag = cuifWfNewTag s) :
    ∃ h' t, s.fifo = h' :: t ∧
      (Ventus.Arith.csrExeStep f fire wid ctaWid i k).vgprBase =
        BitVec.zeroExtend 11 (h'.vgprBase + (h'.numWf - s.splitCnt).zeroExtend 10 *
          h'.numVgprPerWf.extractLsb' 0 10) ∧
      (Ventus.Arith.csrExeStep f fire wid ctaWid i k).wfTagDispatch =
        BitVec.zeroExtend 6 ((h'.numWf - s.splitCnt).extractLsb' 0 3) := by
  obtain ⟨h', t, hfifo, htag, hbase⟩ := dcg2_cuif_split_base s hinv hv hc
  obtain ⟨hw, htw⟩ := dcg3_wba1_csrExe_write_point f fire wid ctaWid i k hcta hk
  refine ⟨h', t, hfifo, ?_, ?_⟩
  · rw [hw, hsrcV]
    show BitVec.zeroExtend 11 s.splitVgpr = BitVec.zeroExtend 11 _
    rw [hbase]
  · rw [htw, hsrcT, htag]
    have hrt : (cuifWfTag h'.wgSlotId
        ((h'.numWf - s.splitCnt).extractLsb' 0 3)).extractLsb' 0 3
        = (h'.numWf - s.splitCnt).extractLsb' 0 3 :=
      (cuif_tag_roundtrip _ _).2
    rw [hrt]

/- ---- WB-A1(a) 数值回归 ---- -/

section Dcg3Wba1Tests

/-- CTA 派发输入装配（其余字段取空拍值） -/
def dcg3CsrCtaIn (vgpr : BitVec 11) (wfTag : BitVec 6) : Ventus.Arith.CsrInputs :=
  { Ventus.Arith.csrInNop with ctaValid := true, ctaVgprBase := vgpr, ctaWfTag := wfTag }

-- 选中 warp 写入：ctaWid=3 → warp3 的 vgprBase = 0x25
example : (Ventus.Arith.csrExeStep (fun _ => Ventus.Arith.csrInit) false 0#3 3#3
    (dcg3CsrCtaIn 0x25#11 0x0B#6) ⟨3, by decide⟩).vgprBase = 0x25#11 := by native_decide
-- wfTagDispatch = wf_tag 低 3 位（0x0B 的低 3 位 = 3）
example : (Ventus.Arith.csrExeStep (fun _ => Ventus.Arith.csrInit) false 0#3 3#3
    (dcg3CsrCtaIn 0x25#11 0x0B#6) ⟨3, by decide⟩).wfTagDispatch = 0x03#6 := by native_decide
-- 未命中 warp 不变
example : (Ventus.Arith.csrExeStep (fun _ => Ventus.Arith.csrInit) false 0#3 3#3
    (dcg3CsrCtaIn 0x25#11 0x0B#6) ⟨4, by decide⟩).vgprBase = 0#11 := by native_decide

end Dcg3Wba1Tests

/- ========================================================================= -/
/- 3. WB-A1(b)：对齐前提 k | vgprBase ∧ k | perWf 的核实（k = num_bank = 4）   -/
/-                                                                           -/
/-  核实结论（源码证据）：                                                    -/
/-  - resource_table 分配粒度 = 1 个寄存器：FIND 选空段（:305-311，             -/
/-    found_addr = 段起点），WRITE 插入 [base, base+size-1]（:364-369），      -/
/-    全程无取整/对齐逻辑；尺寸 wgsize = host 的 num_vgpr。                    -/
/-  - num_vgpr / num_vgpr_per_wf 均为 host 直传（GPGPU_top.scala:76-79），     -/
/-    cu_interface 拆分只做多发累加（:83-90），CSR 写入只透传（:301）——        -/
/-    全链路无对齐检查。                                                       -/
/-  ⇒ WB-A1 主定理（dcg2_wba1_vgpr_bank_addr_unique）的 halB/halp 前提的       -/
/-    唯一支撑是 host 纪律。本节给出：正面条件闭合（host 尺寸全 k-对齐 ⇒       -/
/-    所有基址 k-对齐，归纳证）+ 反例 witness（非对齐尺寸 ⇒ 非对齐基址 ⇒       -/
/-    bank 地址公式失真）。                                                    -/
/- ========================================================================= -/

/-- WB-A1(b) 的对齐不变式：链表所有在驻节点的基址与末址+1 均 k-对齐
    （即所有段边界 k-对齐）。初始空表 vacuous 成立；维护它只需 alloc 尺寸
    k-对齐（dealloc 不动地址）。 -/
def dcg3RtAligned (ram : RtRam) (k : Nat) : Prop :=
  ∀ i, i < ram.cnt → k ∣ ram.addr1 (ram.walk i) ∧ k ∣ (ram.addr2 (ram.walk i) + 1)

/-- 整除辅助（core 无现成 dvd_add 的 Nat 形式保障，手工见证） -/
theorem dcg3_dvd_add {k a b : Nat} (ha : k ∣ a) (hb : k ∣ b) : k ∣ a + b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨x + y, by rw [hx, hy, Nat.mul_add]⟩

/-- 零被任意 k 整除 -/
theorem dcg3_dvd_zero (k : Nat) : k ∣ 0 := ⟨0, by rw [Nat.mul_zero]⟩

/-- 空表 vacuous 对齐 -/
theorem dcg3_rtEmpty_aligned (k : Nat) : dcg3RtAligned rtEmpty k := by
  intro i hi
  have hc : rtEmpty.cnt = 0 := rfl
  rw [hc] at hi
  exact absurd hi (Nat.not_lt_zero i)

/-- 段基址对齐：段 0 为 0（k-对齐），段 i+1 为前节点末址+1（不变式给） -/
theorem dcg3_rt_gapLo_aligned (ram : RtRam) (k : Nat) (hal : dcg3RtAligned ram k)
    (i : Nat) (hi : i ≤ ram.cnt) : k ∣ rtGapLo ram i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [rtGapLo_zero]
    exact dcg3_dvd_zero k
  · have him1 : i - 1 < ram.cnt := by omega
    have e : i - 1 + 1 = i := by omega
    rw [← e, rtGapLo_succ]
    exact (hal (i - 1) him1).2

/-- **WB-A1(b)  alloc 基址对齐（条件形式）**：对齐不变式 + 契约内 alloc ⇒
    输出基址 k-对齐 -/
theorem dcg3_rt_alloc_base_aligned (ram : RtRam) (N k : Nat) (hwf : RtWf ram N)
    (hal : dcg3RtAligned ram k) (slot : Fin 8) (wgsize : Nat)
    (hok : rtEventOk ram N (.alloc slot wgsize)) :
    k ∣ rtAllocBase ram N slot wgsize := by
  obtain ⟨hcnt8, hnew, hfit⟩ := hok
  unfold rtAllocBase
  by_cases h0 : wgsize = 0
  · rw [if_pos h0]
    exact dcg3_dvd_zero k
  · rw [if_neg h0]
    by_cases hc : ram.cnt = 0
    · rw [rtFind_empty ram N wgsize hc]
      exact dcg3_dvd_zero k
    · obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left h0
      have hup := rtFind_success ram N wgsize hwf (by omega) ⟨i, hi0, hi1⟩
      obtain ⟨hfk, haddr, _, _⟩ := rtFind_upd ram N wgsize hwf hup
      rw [haddr]
      exact dcg3_rt_gapLo_aligned ram k hal _ hfk

/-- **WB-A1(b)  alloc 步进保持对齐**：对齐不变式 + 契约内 alloc + 尺寸
    k-对齐 ⇒ 步进后仍对齐 -/
theorem dcg3_rt_alloc_step_aligned (ram : RtRam) (N k : Nat) (hwf : RtWf ram N)
    (hal : dcg3RtAligned ram k) (slot : Fin 8) (wgsize : Nat)
    (hok : rtEventOk ram N (.alloc slot wgsize)) (hsize : k ∣ wgsize) :
    dcg3RtAligned (rtStep ram N (.alloc slot wgsize)) k := by
  rw [rtStep_alloc]
  by_cases h0 : wgsize = 0
  · rw [if_pos h0]
    exact hal
  · rw [if_neg h0]
    have hbase0 : k ∣ rtAllocBase ram N slot wgsize :=
      dcg3_rt_alloc_base_aligned ram N k hwf hal slot wgsize hok
    obtain ⟨hcnt8, hnew, hfit⟩ := hok
    generalize hfb : (rtFind ram N wgsize).faddr = fb
    generalize hfk : (rtFind ram N wgsize).fk = fk
    have hbase : k ∣ fb := by
      have he : rtAllocBase ram N slot wgsize = fb := by
        unfold rtAllocBase
        rw [if_neg h0]
        exact hfb
      rwa [he] at hbase0
    have hfkle : fk ≤ ram.cnt := by
      by_cases hc : ram.cnt = 0
      · rw [← hfk, rtFind_empty ram N wgsize hc]
        exact Nat.zero_le _
      · obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left h0
        have hup := rtFind_success ram N wgsize hwf (by omega) ⟨i, hi0, hi1⟩
        obtain ⟨hfk', _, _, _⟩ := rtFind_upd ram N wgsize hwf hup
        rw [← hfk]
        exact hfk'
    intro i hi
    rw [rtInsert_cnt] at hi
    rcases Nat.lt_trichotomy i fk with h | h | h
    · rw [rtInsert_walk_lt (slot := slot) (base := fb) (size := wgsize) ram N hwf hfkle hnew i h,
        rtInsert_addr1_ne ram (hnew i (by omega)) fb wgsize fk,
        rtInsert_addr2_ne ram (hnew i (by omega)) fb wgsize fk]
      exact hal i (by omega)
    · subst h
      rw [rtInsert_walk_eq (slot := slot) (base := fb) (size := wgsize) ram N hwf hfkle hnew,
        rtInsert_addr1_eq, rtInsert_addr2_eq]
      refine ⟨hbase, ?_⟩
      have hwg : 1 ≤ wgsize := Nat.pos_of_ne_zero h0
      have e : fb + wgsize - 1 + 1 = fb + wgsize := by omega
      rw [e]
      exact dcg3_dvd_add hbase hsize
    · have hd : fk + (i - 1 - fk) < ram.cnt := by omega
      have e := rtInsert_walk_gt (slot := slot) (base := fb) (size := wgsize)
        ram N hwf hfkle hnew (i - 1 - fk) hd
      have e1 : fk + 1 + (i - 1 - fk) = i := by omega
      have e2 : fk + (i - 1 - fk) = i - 1 := by omega
      rw [e1, e2] at e
      rw [e, rtInsert_addr1_ne ram (hnew (i-1) (by omega)) fb wgsize fk,
        rtInsert_addr2_ne ram (hnew (i-1) (by omega)) fb wgsize fk]
      exact hal (i-1) (by omega)

/-- WB-A1(b)  dealloc 步进保持对齐（地址数组不动，节点子列） -/
theorem dcg3_rt_dealloc_step_aligned (ram : RtRam) (N k : Nat) (hwf : RtWf ram N)
    (hal : dcg3RtAligned ram k) (slot : Fin 8)
    (hok : rtEventOk ram N (.dealloc slot)) :
    dcg3RtAligned (rtStep ram N (.dealloc slot)) k := by
  obtain ⟨kk, hkk, hslot⟩ := hok
  rw [rtStep_dealloc]
  cases hfs : rtFindSlot ram slot with
  | none =>
    exact absurd hslot (rtFindSlot_none ram slot hfs kk hkk)
  | some k' =>
    obtain ⟨hk', hslot'⟩ := rtFindSlot_spec ram slot hfs
    intro i hi
    rw [rtRemove_cnt] at hi
    by_cases hik : i < k'
    · rw [rtRemove_walk_lt ram N hwf hk' hslot' i hik, rtRemove_addr1, rtRemove_addr2]
      exact hal i (by omega)
    · have hd : k' + (i - k') < ram.cnt - 1 := by omega
      have e := rtRemove_walk_ge ram N hwf hk' hslot' (i - k') hd
      have e1 : k' + (i - k') = i := by omega
      rw [e1] at e
      rw [e, rtRemove_addr1, rtRemove_addr2]
      exact hal (i + 1) (by omega)

/-- rt 事件序列演化 -/
def dcg3RtRun (ram : RtRam) (N : Nat) (es : List RtEvent) : RtRam :=
  es.foldl (fun r e => rtStep r N e) ram

/-- 对齐不变式的多拍保持（归纳主定理，初始状态任意） -/
theorem dcg3_rt_run_aligned_aux (N k : Nat) :
    ∀ (l : List RtEvent) (ram : RtRam), RtWf ram N → dcg3RtAligned ram k →
      (∀ e ∈ l, ∀ s z, e = .alloc s z → k ∣ z) →
      (∀ pre e, List.IsPrefix (pre ++ [e]) l →
        rtEventOk (dcg3RtRun ram N pre) N e) →
      dcg3RtAligned (dcg3RtRun ram N l) k ∧ RtWf (dcg3RtRun ram N l) N := by
  intro l
  induction l with
  | nil => intro ram hwf hal _ _; exact ⟨hal, hwf⟩
  | cons x xs ih =>
    intro ram hwf hal hsizes hok
    have hokx : rtEventOk ram N x := hok [] x ⟨xs, rfl⟩
    have hszx : ∀ s z, x = .alloc s z → k ∣ z :=
      hsizes x (List.mem_cons_self : x ∈ x :: xs)
    have hwf' : RtWf (rtStep ram N x) N := rt_step_wf ram N hwf x hokx
    have hal' : dcg3RtAligned (rtStep ram N x) k := by
      cases x with
      | alloc s z => exact dcg3_rt_alloc_step_aligned ram N k hwf hal s z hokx (hszx s z rfl)
      | dealloc s => exact dcg3_rt_dealloc_step_aligned ram N k hwf hal s hokx
    have e2 : dcg3RtRun ram N (x :: xs) = dcg3RtRun (rtStep ram N x) N xs := by
      simp only [dcg3RtRun, List.foldl_cons]
    rw [e2]
    apply ih (rtStep ram N x) hwf' hal'
    · intro e he s z hz
      exact hsizes e (List.mem_cons_of_mem x he) s z hz
    · intro pre e hpre
      obtain ⟨t, ht⟩ := hpre
      have h1 : List.IsPrefix ((x :: pre) ++ [e]) (x :: xs) :=
        ⟨t, congrArg (x :: ·) ht⟩
      have h2 := hok (x :: pre) e h1
      have heq : dcg3RtRun ram N (x :: pre) = dcg3RtRun (rtStep ram N x) N pre := by
        simp only [dcg3RtRun, List.foldl_cons]
      rwa [heq] at h2

/-- **WB-A1(b) 正面闭合（host 契约 ⇒ 全链对齐）**：从空表出发、事件序列满足
    逐前缀契约（rtEventOk）且所有 alloc 尺寸 k-对齐，则任意演化后链表中所有
    在驻 WG 的基址与末址+1 都 k-对齐。 -/
theorem dcg3_wba1_rt_run_aligned (N k : Nat) (hN : 0 < N) (es : List RtEvent)
    (hsizes : ∀ e ∈ es, ∀ s z, e = .alloc s z → k ∣ z)
    (hok : ∀ pre e, List.IsPrefix (pre ++ [e]) es →
      rtEventOk (dcg3RtRun rtEmpty N pre) N e) :
    dcg3RtAligned (dcg3RtRun rtEmpty N es) k ∧ RtWf (dcg3RtRun rtEmpty N es) N :=
  dcg3_rt_run_aligned_aux N k es rtEmpty (rtEmpty_wf N hN) (dcg3_rtEmpty_aligned k)
    hsizes hok

/-- WB-A1(b) 闭环的使用形态：对齐演化后的下一次契约内 alloc，其输出基址
    必 k-对齐——即「host 保证每个 WG 的 num_vgpr k-对齐」是 halB 前提的
    充分闭合条件（必要性由下方 witness 给出：尺寸非对齐即可产生非对齐基址） -/
theorem dcg3_wba1_next_alloc_aligned (N k : Nat) (hN : 0 < N) (es : List RtEvent)
    (hsizes : ∀ e ∈ es, ∀ s z, e = .alloc s z → k ∣ z)
    (hok : ∀ pre e, List.IsPrefix (pre ++ [e]) es →
      rtEventOk (dcg3RtRun rtEmpty N pre) N e)
    (slot : Fin 8) (wgsize : Nat)
    (hok' : rtEventOk (dcg3RtRun rtEmpty N es) N (.alloc slot wgsize)) :
    k ∣ rtAllocBase (dcg3RtRun rtEmpty N es) N slot wgsize :=
  dcg3_rt_alloc_base_aligned _ _ _
    (dcg3_wba1_rt_run_aligned N k hN es hsizes hok).2
    (dcg3_wba1_rt_run_aligned N k hN es hsizes hok).1 slot wgsize hok'

/-- **WB-A1(b) 反例 witness（真发现）**：分配粒度 = 1 个寄存器，无任何对齐
    约束——首个 WG 尺寸 5（host 参数 num_vgpr=5，硬件不检查），下一个 WG 的
    基址 = 5，4 ∤ 5。 -/
def dcg3RtMisalign : RtRam := rtStep rtEmpty rtNUM_VGPR (.alloc 2 5)

/-- witness 的基址计算（best-fit：段 [5,1024) 胜出段 [0,0)） -/
theorem dcg3T_misalign_base : rtAllocBase dcg3RtMisalign rtNUM_VGPR 3 4 = 5 := by decide
/-- 5 不是 4 的倍数 -/
theorem dcg3T_misalign_not_aligned : ¬ (4 : Nat) ∣ 5 := by decide

/-- **WB-A1(b) 公式失真 witness**：非对齐基址下 bank 地址公式失真——
    warp A（base=5）的寄存器 r=3（真实寄存器 8）与 warp B（base=4）的 r=0
    （真实寄存器 4）算出同一 rsAddr = 1，而真实 bank 地址应为 2 与 1——
    两个不同物理位置映射到同 bank 同地址 ⟹ 写回互踩。这正是
    dcg2_wba1_bank_disjoint 的 hb1（k | b1）前提被违反的直接后果。 -/
theorem dcg3_wba1_misalign_collision :
    (5 / 4 + 3 / 4 : Nat) = (4 / 4 + 0 / 4 : Nat) ∧ (5 + 3 : Nat) / 4 ≠ (4 + 0) / 4 := by
  decide

/-- WB-A1(b) perWf 半：perWf 的 k-对齐是纯 host 契约（cu_interface.scala:88-89
    只做多发累加，无取整）——即使基址对齐，perWf=5 也使 WF1 基址失对齐 -/
theorem dcg3_wba1_perWf_unaligned_breaks (B : Nat) (hB : 4 ∣ B) : ¬ 4 ∣ B + 5 := by
  omega

/- ---- WB-A1(b) 数值回归 ---- -/

section Dcg3Wba1bTests

/-- 对齐演化镜像：alloc 8 → alloc 4 → dealloc → alloc 4；基址 0/8/回收后重用 0，
    全 4 对齐（dealloc 不清 addr 阵列，slot2 的 0 是残留值） -/
def dcg3RtTrace : List RtEvent := [.alloc 2 8, .alloc 5 4, .dealloc 2, .alloc 7 4]

example : (dcg3RtRun rtEmpty rtNUM_VGPR dcg3RtTrace).addr1 2 = 0 ∧
    (dcg3RtRun rtEmpty rtNUM_VGPR dcg3RtTrace).addr1 5 = 8 ∧
    (dcg3RtRun rtEmpty rtNUM_VGPR dcg3RtTrace).addr1 7 = 0 := by decide

end Dcg3Wba1bTests

/- ========================================================================= -/
/- 4. WB-A1(c)：尺寸关系 numWf×perWf ≤ vgprSize 的核实                         -/
/-                                                                           -/
/-  核实结论（源码证据）：numWf 与 perWf 均源于 host（GPGPU_top.scala:72-79： -/
/-  host_wg_new.bits.num_vgpr := host_vgpr_size_total、num_vgpr_per_wf :=      -/
/-  host_vgpr_size_per_wf），cu_interface 拆分按 numWf 次累加 perWf            -/
/-  （:83-90），全程无「numWf×perWf ≤ 本 WG 的 vgprSize」检查——                -/
/-  cu_interface.scala:96 的仿真断言只对 NUM_VGPR=1024（整个寄存器堆）挡        -/
/-  溢出，不挡「越出本 WG 分配区间」。dcg2_wba1_vgpr_bank_addr_unique 的        -/
/-  hfit1/hfit2 前提由此只能来自 host 契约。                                   -/
/- ========================================================================= -/

/-- **WB-A1(c) 破洞形式**：numWf×perWf > vgprSize 时，末 WF 的寄存器区间
    [B+(numWf-1)·p, B+numWf·p) 越出本 WG 分配区间 [B, B+S)——地址 B+S
    （本 WG 之外的第一个寄存器，必属于某个相邻/后续 WG）落在末 WF 区间内，
    任何覆盖 B+S 的 WG 都与末 WF 撞区间。 -/
theorem dcg3_wba1_fit_violation (B S p nw : Nat)
    (hfit : S < nw * p) (hlast : (nw - 1) * p < S) :
    B + (nw - 1) * p < B + S ∧ B + S < B + nw * p := by
  have hmul : nw * p = (nw - 1) * p + p := by
    cases nw with
    | zero => simp at hfit
    | succ m => rw [Nat.succ_mul, Nat.succ_sub_one]
  omega

/-- 破洞的数值镜像（p=32、numWf=2、S=40：末 WF 区间 [B+32,B+64) 越出 [B,B+40)，
    覆盖 B+40 的相邻 WG（如 [40,64)）与之相交——specIntervalDisjoint 不成立） -/
example : (0 + 1 * 32 < 0 + 40 ∧ 0 + 40 < 0 + 2 * 32) ∧
    ¬ specIntervalDisjoint (0 + 1 * 32) 32 (0 + 40) 24 := by decide

/-- **WB-A1(c) 佐证：硬件断言过弱**：cu_interface.scala:96 的仿真断言
    （splitter_cnt > 1 ⇒ NUM_VGPR - splitVgpr > perWf）在上述越界场景全程通过
    （基址最大 6×32=192，192+32=224 < 1024），而 numWf×perWf=256 > 32=S。
    即该断言不构成 hfit 的硬件支撑。 -/
theorem dcg3_wba1_hw_assert_too_weak :
    (∀ k, k < 7 → 0 + k * 32 + 32 < rtNUM_VGPR) ∧ ¬ (8 * 32 ≤ 32) := by
  have hN : rtNUM_VGPR = 1024 := rfl
  refine ⟨?_, by decide⟩
  intro k hk
  omega

/- ========================================================================= -/
/- 5. 核销证据交叉引用与公理审计                                               -/
/- ========================================================================= -/

/-- 【B1 队列保真的抽象层证据（QueueModel 顺序保持）】 -/
def dcg3XrefQueueRunPrefix := @Ventus.Base.Hist.run_prefix
/-- 【B1 队列保真：flow 直通拍的 FIFO 基元】 -/
def dcg3XrefFifoSingle := @Ventus.Base.AQueue.fifo_single
/-- 【B1 消费形态（Discharge2 既有组合主定理）】 -/
def dcg3XrefBjb1Consume := @dcg2_bjb1_consume
/-- 【B1 读拍同源（Discharge2 既有连线）】 -/
def dcg3XrefBjb1InputWid := @dcg2BjInputWid
/-- 【B1 配对面的双发耦合证据（Issue.lean）】 -/
def dcg3XrefDualCoupled := @Ventus.Schedule.iss_dual_valid_coupled
/-- 【WB-A1(a) 派发侧配对证据（Discharge2 既有，补 G3 vgpr 半边）】 -/
def dcg3XrefCuifSplitBase := @dcg2_cuif_split_base
/-- 【WB-A1(a) 写入点的独热性证据（CSR.lean 既有：未选中 warp 不变）】 -/
def dcg3XrefCsrUntouched := @Ventus.Arith.csrExe_untouched
/-- 【WB-A1(b) 前提的消费点（Discharge2 既有 bank 不交引理）】 -/
def dcg3XrefWba1BankDisjoint := @dcg2_wba1_bank_disjoint
/-- 【WB-A1(b/c) 的分配在界证据（ResourceTable.lean 既有）】 -/
def dcg3XrefRtAllocBounds := @Ventus.CTA.rt_alloc_base_bounds

-- 公理审计（归档注明：dcg3_bjb1_end_to_end 经 dcg2_bjb1_consume 继承其
-- bv_decide 的 LRAT trust 公理；dcg3_wba1_capstone 经 cuif_tag_roundtrip
-- 同理；native_decide 测试带 Lean.ofReduceBool；纯 Nat/List/组合引理仅
-- 标准公理；本文件无 sorry）
#print axioms dcg3_bjb1_chain_wid
#print axioms dcg3_bjb1_inputWid_same_source
#print axioms dcg3_bjb1_wid_pair_gate
#print axioms dcg3_queue_hist_fidelity
#print axioms dcg3_bjb1_flow_through
#print axioms dcg3_bjb1_consumed_entry
#print axioms dcg3_bjb1_end_to_end
#print axioms dcg3_wba1_csrExe_write_point
#print axioms dcg3_wba1_dispatch_consistent
#print axioms dcg3_wba1_capstone
#print axioms dcg3_rt_alloc_base_aligned
#print axioms dcg3_rt_alloc_step_aligned
#print axioms dcg3_rt_dealloc_step_aligned
#print axioms dcg3_wba1_rt_run_aligned
#print axioms dcg3_wba1_next_alloc_aligned
#print axioms dcg3_wba1_fit_violation
#print axioms dcg3_wba1_hw_assert_too_weak

end Ventus.Spec
