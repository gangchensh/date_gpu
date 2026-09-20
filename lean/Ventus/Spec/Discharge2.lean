/- ========================================================================= -/
/-                      Spec/Discharge2.lean                                 -/
/-  契约核销第二波：Contracts.lean 登记册 5 条 pending 契约的组合核销            -/
/-  （WB-A2 / BJB-1 / H-BB / WB-A1 / CTA-A1+E1）                              -/
/-                                                                           -/
/-  纪律：namespace Ventus.Spec；辅助名一律 dcg2 前缀；只新建本文件。          -/
/-                                                                           -/
/- ======================== 核销结论一览（详见各节头注） ======================-/
/-  1. WB-A2（warp 内发射顺序 = 程序序）——**核销**（前缀精化形式）：            -/
/-     ibuffer 每 warp FIFO 保序（IBuffer.lean ibTop_warp_prefix）             -/
/-     + pipe.scala:223-224 门控同拍同事务（Pipe.lean pipe_ib2i_fire_eq）       -/
/-     ⇒ dcg2_wba2_prefix / dcg2_wba2_getElem / dcg2_wba2_take /               -/
/-       dcg2_wba2_chain。边界：flush（分支重定向）重启程序序（前提 hf）；      -/
/-     "接受序 = 取指序"由 accepted 按输入轨迹顺序构造而立即可见（每 warp       -/
/-     icache_rsp 按序到达属 icache 侧环境）；ibuffer2issue 的跨 warp RR 仲裁   -/
/-     不引入 per-warp 重排（单通道串行，IBuffer.lean D5 的仲裁未建模但只       -/
/-     交织 warp 间顺序）。scoreboard delay 读 _r 视图已由 Scoreboard.lean      -/
/-     D3 建模（sbRead/sbDelay），与本链正交。                                  -/
/-  2. BJB-1（掩码纪律的 wid 时序一致性）——**核销（条件形式，两前提显式化）**： -/
/-     读拍（pipe.scala:366+:293 同源）mask_init ⊆ thread_masks(指令自身 wid)   -/
/-     = dcg2_bjb1_read_submask；消费拍（branch_join.scala:141-142,:260）       -/
/-     dcg2_bjb1_consume：前提 B1（wid 传输完整性：exe_dataV→issueV→out_SIMT→   -/
/-     branch_ctl_buf 链路 bits 保真，队列直通/未建模）+ 前提 B2（读拍→消费拍    -/
/-     该 warp 活跃掩码不变；由 beq 门控支撑——同 warp 有未决分支时不能发射，    -/
/-     pipe_i4_gate_chain_beq，见 dcg2XrefBjbGateBeq）⇒ bjbMaskDiscipline。     -/
/-  3. H-BB（branch_back 固定优先级 Arbiter 终将授予 in1(fetch_ctl) 且          -/
/-     warp_sche 接受）——**核销（单拍授权 + 有界等待条件形式）**：               -/
/-     branch_back = Writeback.lean wbArb（n=2 固定优先级，无状态）：            -/
/-     in0 无效的当拍 in1 必获授权（dcg2_hbb_grant），warp_sche 接受条件         -/
/-     branchReady = !flushCacheValid（warp_schedule.scala:51，dcg2_hbb_accept）；-/
/-     合成 dcg2_hbb_fire（0 拍等待）、饿死刻画 dcg2_hbb_no_fire_iff、           -/
/-     有界等待 dcg2_hbb_bounded_wait。**降级前提清单**（活性闭环所需，           -/
/-     系统侧事实，未建模）：(i) in0（alu.out2br）不持续 valid；                 -/
/-     (ii) flushCacheValid（icache miss 响应）不持续 valid。                    -/
/-  4. WB-A1（同物理 bank 地址 ⟹ 同 warp）——**核销（组合链 + 缺口显式化）**：   -/
/-     已证链：WG 级区间不交（CtaScheduler CtasInv 的 ctasPairOk，               -/
/-     dcg2_wba1_wg_vgpr_disjoint；其归纳保持由 ctas_step_inv 保证）             -/
/-     + WG 内 WF 步长不交（dcg2_wba1_stride_disjoint）                          -/
/-     + 对齐区间的 bank 映射保持不交（dcg2_wba1_bank_disjoint，                 -/
/-       operandCollector.scala:110-124 的 rsAddr=(base+r)/k 形式，k=num_bank=4）-/
/-     ⇒ 主定理 dcg2_wba1_vgpr_bank_addr_unique。                                -/
/-     cuif 拆发基址递推（cu_interface.scala:83-90）的"第 k 个 WF 基址 =         -/
/-     vgprBase + k×perWf 且与 wf_tag 的 wf_id 同序"由 dcg2_cuif_splitVgpr_inv  -/
/-     不变式 + dcg2_cuif_split_base 钉死——补登记册缺口 G3（cuif_split_wfid      -/
/-     定理缺失）的 vgpr 半边。                                                 -/
/-     **残余缺口**（明示）：(a) CSR vgpr_base_dispatch 写入点（CSR.scala:300-301）-/
/-     与 CTA2warp 透传、operandCollector 的 rsAddr 映射未建模（本定理以对齐     -/
/-     前提 halB/halp + 线性地址形式给出，bank 交织的正确性依赖 k|base∧k|perWf）-/
/-     (b) 分配尺寸关系 numWf×perWf ≤ vgprSize（hfit 前提）来自 host/allocator -/
/-     参数语义，工程内未建模；(c) sgpr/lds 版本为同一实例化（略）。             -/
/-  5. CTA-A1 / CTA-E1（环境契约组合闭环）——**核销（条件形式，对应关系显式化）**：-/
/-     dcg2_ctaA1：cuif dealloc 源（H-CUIF-DEALLOC 已核销四定理打包               -/
/-     dcg2_ctaA1_source）+ 簿记对应 dcg2Agree ⇒ AlcEnvOk（A1）；                -/
/-     dcg2_ctaE1：H-ALLOC-SLOT（alc_h_alloc_slot，已核销）+ dcg2Agree +         -/
/-     H-WF（axiomatic）⇒ CuifEnvOk 的 enq 半。                                  -/
/-     **残余缺口**：C1 = dcg2Agree（allocator 的 wgslot/wfslot 簿记与            -/
/-     cu_interface 的 liveMem/fifo/gather 状态的逐点对应）——需要 alloc×cuif     -/
/-     联合状态机的归纳证明，当前两模型未联合例化；numWf ≥ 1 依赖 H-WF            -/
/-     （host 契约，axiomatic，与 Q-CUIF1 同源）。                               -/
/- ========================================================================= -/

import Ventus.Spec.Contracts
import Ventus.Schedule.IBuffer

namespace Ventus.Spec

open Ventus.Schedule Ventus.SIMT Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. WB-A2：warp 内发射顺序 = 入队序 = 取指序                                  -/
/-    链：icache_rsp 入队（pipe.scala:187,216）→ ibuffer 每 warp FIFO           -/
/-    （InstrBufferV2，IBuffer.lean ibTop_warp_prefix）→ :223-224 门控          -/
/-    （pipe_ib2i_fire_eq / pipe_ib2i_gated）→ ibuffer2issue 入口。             -/
/- ========================================================================= -/

/-- warp w 在整机输入轨迹下的发射序列（ibuffer 出口 = ibuffer2issue 入口） -/
def dcg2EmitSeq (t : IbTop) (is : List IbTopIn) (w : Fin 8) : List IbInsn :=
  ((t.lanes w).run (is.map fun i => ibTopLaneIn i w)).2

/-- warp w 的接受序列（= 入队序；accepted 按输入轨迹顺序逐拍展开，故亦 = 取指序） -/
def dcg2AcceptSeq (t : IbTop) (is : List IbTopIn) (w : Fin 8) : List IbInsn :=
  (t.lanes w).accepted (is.map fun i => ibTopLaneIn i w)

/-- **WB-A2 主定理（前缀精化）**：无 flush 轨迹下，warp w 的发射序列是接受
    （入队/取指）序列的前缀——发射顺序与程序序一致，且不重排、不插队。 -/
theorem dcg2_wba2_prefix (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false) :
    List.IsPrefix (dcg2EmitSeq t is w) (dcg2AcceptSeq t is w) := by
  obtain ⟨tl, htl⟩ := ibTop_warp_prefix t is w he hf
  exact ⟨tl, htl⟩

/-- 发射序列不长于接受序列（前缀的长度半） -/
theorem dcg2_wba2_accept_length_le (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false) :
    (dcg2EmitSeq t is w).length ≤ (dcg2AcceptSeq t is w).length := by
  obtain ⟨tl, htl⟩ := dcg2_wba2_prefix t is w he hf
  rw [← htl]
  simp

/-- **WB-A2 逐条形式**：第 k 条发射的指令 = 第 k 条入队的指令（k 在已发射范围内）。
    即"同 warp 发射序 = 入队序"的逐元素陈述。 -/
theorem dcg2_wba2_getElem (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false)
    (k : Nat) (hk : k < (dcg2EmitSeq t is w).length) :
    (dcg2EmitSeq t is w)[k]? = (dcg2AcceptSeq t is w)[k]? := by
  obtain ⟨tl, htl⟩ := dcg2_wba2_prefix t is w he hf
  rw [← htl, List.getElem?_append_left hk]

/-- WB-A2 的 take 形式：发射序列 = 接受序列的前缀截取 -/
theorem dcg2_wba2_take (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false) :
    dcg2EmitSeq t is w = (dcg2AcceptSeq t is w).take (dcg2EmitSeq t is w).length := by
  obtain ⟨tl, htl⟩ := dcg2_wba2_prefix t is w he hf
  rw [← htl]
  exact List.take_left.symm

/-- **WB-A2 总链**：(1) 发射序 ⊑ 入队序（本文件）；(2) ibuffer 出口 fire ⟺
    ibuffer2issue 入口 fire（pipe.scala:223-224，同拍同一事务，两侧视图一致，
    门控不引入重排——Pipe.lean pipe_ib2i_fire_eq）；(3) warp_ready=0 时两侧
    同停（pipe_ib2i_gated：反压只停不排）。 -/
theorem dcg2_wba2_chain (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false) :
    List.IsPrefix (dcg2EmitSeq t is w) (dcg2AcceptSeq t is w) ∧
    (∀ v r wr, pipeIb2iInFire v r wr = pipeIbOutFire v r wr) ∧
    (∀ v r, pipeIb2iInFire v r false = false ∧ pipeIbOutFire v r false = false) :=
  ⟨dcg2_wba2_prefix t is w he hf,
   fun v r wr => pipe_ib2i_fire_eq v r wr,
   fun v r => pipe_ib2i_gated v r⟩

/-- 核销证据交叉引用（同 Contracts.lean 第 5 节惯例：同名同型别名） -/
def dcg2XrefIbTopWarpPrefix := @Ventus.Schedule.ibTop_warp_prefix
/-- 记分板 delay 组合读出（Scoreboard.lean D3：读 _r 非旁路视图）——WB-A2 前提的另一半 -/
def dcg2XrefSbDelay := @Ventus.Schedule.sbDelay

/- ---- WB-A2 数值回归：反压交织下发射序 = 接受序 ---- -/

section Dcg2WbA2Tests

/-- 反压下的 warp0 轨迹：拍0 入队 [10,11]（无 ready），拍2 入队 [12] 并开始排空，
    中间反压一拍——发射序必须仍是 [10,11,12]（= 接受序，不含 13：mask=1 只取 c0） -/
def dcg2IbStall : List IbTopIn :=
  [ ibTopIn true (ibGrpW 0 10 11 3#2) false 0 0b00000000#8   -- 拍0：入队组[10,11]，下游反压
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000000#8    -- 拍1：反压（SlowDown 未装入，Q3）
  , ibTopIn true (ibGrpW 0 12 13 1#2) false 0 0b00000001#8   -- 拍2：装入 SlowDown + 入队[12]
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000000#8    -- 拍3：反压
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000001#8    -- 拍4：发 10
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000001#8    -- 拍5：发 11 + 装入[12]
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000001#8 ]  -- 拍6：发 12

theorem dcg2T_stall_emit :
    (dcg2EmitSeq ibTopEmpty dcg2IbStall ⟨0, by decide⟩).map IbInsn.tag = [10, 11, 12] := by
  native_decide

theorem dcg2T_stall_accept :
    (dcg2AcceptSeq ibTopEmpty dcg2IbStall ⟨0, by decide⟩).map IbInsn.tag = [10, 11, 12] := by
  native_decide

end Dcg2WbA2Tests

/- ========================================================================= -/
/- 2. BJB-1：掩码纪律的 wid 时序一致性（pipe.scala:366,293 +                    -/
/-    branch_join.scala:260,141-142）                                          -/
/- ========================================================================= -/

/-- pipe.scala:293 的连线：simt_stack.io.input_wid = operand_collector.io.out(0)
    .bits.control.wid——即"正在 :366 被计算掩码的那条指令自己的 wid"（恒等连线）。 -/
def dcg2BjInputWid (ctrlWid : BitVec 3) : BitVec 3 := ctrlWid

theorem dcg2_bjb1_inputWid_eq (wid : BitVec 3) : dcg2BjInputWid wid = wid := rfl

/-- **BJB-1 读拍**：:366 计算的 mask_init = 指令掩码 ∧ out_mask，而 out_mask =
    thread_masks(input_wid)（branch_join.scala:260 组合读出）且 input_wid =
    该指令自身 wid（:293）——故 mask_init ⊆ 该 warp 读拍的活跃掩码。 -/
theorem dcg2_bjb1_read_submask (instrMask : BitVec 32) (tm : Fin 8 → BitVec 32)
    (wid : BitVec 3) :
    pipeExeDataVMask instrMask (tm (wsFin (dcg2BjInputWid wid))) &&& ~~~(tm (wsFin wid)) = 0#32 :=
  pipe_vmask_sub_outMask _ _

/-- **BJB-1 消费拍（组合主定理）**：若 (B1) branch_ctl_buf.bits.wid 就是该 vbranch
    的 wid（队列/路由传输完整性，缺口 B1）且 (B2) 该 warp 的活跃掩码从读拍到消费拍
    未变（时序稳定性，缺口 B2），则 branch_join 消费（branch_join.scala:141-142，
    warp_id := branch_ctl_buf.bits.wid 索引 thread_masks，:249-259）时掩码纪律
    bjbMaskDiscipline 成立。
    B2 的正当性：同 warp 有未决分支（beqReg）时不能发射
    （pipe_i4_gate_chain_beq），故本 vbranch 发射前同 warp 前序分支已结算、
    发射后同 warp 后续指令被阻塞——thread_masks(wid) 在读-消费窗口内不变。 -/
theorem dcg2_bjb1_consume {depth : Nat} [NeZero depth]
    (s : BjSysState depth 32) (bi : BjBranchIn 32)
    (tm : Fin 8 → BitVec 32) (wid bufWid : BitVec 3) (instrMask : BitVec 32)
    (hmi : bi.maskInit = pipeExeDataVMask instrMask (tm (wsFin wid)))
    (htr : bufWid = wid)
    (htm : s.tmask = tm (wsFin bufWid)) :
    bjbMaskDiscipline s bi := by
  rw [htr] at htm
  unfold bjbMaskDiscipline
  rw [htm, hmi]
  show (instrMask &&& tm (wsFin wid)) &&& tm (wsFin wid) = instrMask &&& tm (wsFin wid)
  bv_decide

/-- 核销证据交叉引用：B2 的门控支撑（beq 未决 ⇒ 同 warp 不发射） -/
def dcg2XrefBjbGateBeq := @pipe_i4_gate_chain_beq
/-- 核销证据交叉引用：BJB-1 已证的 popcount 半边（BranchJoinBounds.lean） -/
def dcg2XrefBjbDisciplinePopcount := @Ventus.SIMT.bjbDiscipline_popcount

/- ========================================================================= -/
/- 3. H-BB：branch_back（writeback.scala:18-36，n=2 固定优先级 Arbiter，        -/
/-    in0=alu.out2br、in1=simt_stack.fetch_ctl）活性 + warp_sche 接受           -/
/-    （pipe.scala:130,148；warp_schedule.scala:51）                            -/
/- ========================================================================= -/

/-- branch_back 的 valid 向量装配（bit0 = in0 alu.out2br.valid，bit1 = in1 fetch_ctl） -/
def dcg2BbVal (in0v in1v : Bool) : BitVec 2 :=
  (BitVec.ofBool in0v).zeroExtend 2 ||| ((BitVec.ofBool in1v).zeroExtend 2 <<< 1)

theorem dcg2BbVal_0 (a b : Bool) : (dcg2BbVal a b).getLsbD 0 = a := by
  cases a <;> cases b <;> decide

theorem dcg2BbVal_1 (a b : Bool) : (dcg2BbVal a b).getLsbD 1 = b := by
  cases a <;> cases b <;> decide

/-- **H-BB 仲裁半**：固定优先级下，in0 无效的当拍 in1（fetch_ctl）必获授权。
    （wbArbGrant 语义：grant(i) ⟺ i 之前无 valid，Writeback.lean wbArbGrant_eq_true_iff） -/
theorem dcg2_hbb_grant (in0v : Bool) (h0 : in0v = false) :
    wbArbGrant (dcg2BbVal in0v true) ⟨1, by decide⟩ = true := by
  rw [wbArbGrant_eq_true_iff]
  intro j hj
  have hv : (⟨1, by decide⟩ : Fin 2).val = 1 := rfl
  rw [hv] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [dcg2BbVal_0]
  exact h0

/-- H-BB 压制的反向刻画：in0 有效时 in1 必不获授权（固定优先级的饿死面，Q3） -/
theorem dcg2_hbb_blocked (in1v : Bool) :
    wbArbGrant (dcg2BbVal true in1v) ⟨1, by decide⟩ = false := by
  have hiff := wbArbGrant_eq_true_iff (dcg2BbVal true in1v) ⟨1, by decide⟩
  cases hg : wbArbGrant (dcg2BbVal true in1v) ⟨1, by decide⟩ with
  | false => rfl
  | true =>
    rw [hiff] at hg
    have h0 := hg 0 (by
      have hv : (⟨1, by decide⟩ : Fin 2).val = 1 := rfl
      rw [hv]; omega)
    rw [dcg2BbVal_0] at h0
    exact absurd h0 (by decide)

/-- **H-BB 接受半**：warp_sche 的 branch.ready = !flushCache.valid
    （warp_schedule.scala:51）；flushCache.valid = pc_rsp.valid && pc_rsp.status(0)
    （miss 响应，wsOut）。 -/
theorem dcg2_hbb_accept (s : WsState) (i : WsInputs) :
    (wsOut s i).branchReady = !(i.pcRspValid && i.pcRspMiss) := rfl

/-- 接受半的另一形式：branchReady 与当拍 flushCacheValid 互补 -/
theorem dcg2_hbb_accept_iff_no_flushCache (s : WsState) (i : WsInputs) :
    (wsOut s i).branchReady = !(wsOut s i).flushCacheValid := rfl

/-- 授权+就绪的合成（供 dcg2_hbb_fire / dcg2_hbb_bounded_wait 复用） -/
theorem dcg2_hbb_fire1 (in0v : Bool) (h0 : in0v = false) (r : Bool) (hr : r = true) :
    wbArbInFire (dcg2BbVal in0v true) r ⟨1, by decide⟩ = true := by
  have hg : wbArbGrant (dcg2BbVal in0v true) ⟨1, by decide⟩ = true := dcg2_hbb_grant in0v h0
  have hv1 : (dcg2BbVal in0v true).getLsbD (⟨1, by decide⟩ : Fin 2).val = true := by
    have hv : (⟨1, by decide⟩ : Fin 2).val = 1 := rfl
    rw [hv]; exact dcg2BbVal_1 in0v true
  simp only [wbArbInFire, wbArbInReady]
  rw [hv1, hg, hr]
  rfl

/-- **H-BB 主定理（单拍授权+接受，0 拍等待）**：fetch_ctl valid、in0 无效、
    warp_sche 可接受（无 icache miss 响应）⟹ branch_back.in1 当拍 fire。 -/
theorem dcg2_hbb_fire (s : WsState) (i : WsInputs) (in0v : Bool)
    (h0 : in0v = false) (hfc : (i.pcRspValid && i.pcRspMiss) = false) :
    wbArbInFire (dcg2BbVal in0v true) (wsOut s i).branchReady ⟨1, by decide⟩ = true :=
  dcg2_hbb_fire1 in0v h0 _ (by rw [dcg2_hbb_accept, hfc]; rfl)

/-- **H-BB 饿死刻画（充要）**：fetch_ctl valid 而不 fire ⟺ in0 同拍有效（被压）
    或 warp_sche 拒收（flushCacheValid）。 -/
theorem dcg2_hbb_no_fire_iff (in0v : Bool) (r : Bool) :
    wbArbInFire (dcg2BbVal in0v true) r ⟨1, by decide⟩ = false ↔
      in0v = true ∨ r = false := by
  constructor
  · intro hnf
    cases h0 : in0v with
    | true => exact Or.inl rfl
    | false =>
      cases hr : r with
      | false => exact Or.inr rfl
      | true =>
        have hf : wbArbInFire (dcg2BbVal false true) true ⟨1, by decide⟩ = true :=
          dcg2_hbb_fire1 false rfl true rfl
        rw [h0, hr] at hnf
        rw [hf] at hnf
        exact absurd hnf (by decide)
  · intro h
    rcases h with h0 | hr
    · subst h0
      have hb := dcg2_hbb_blocked true
      simp only [wbArbInFire, wbArbInReady]
      rw [hb]
      simp
    · subst hr
      simp [wbArbInFire, wbArbInReady]

/-- **H-BB 有界等待（条件形式）**：窗口 [t0, t0+B] 内若存在一拍"in0 无效 ∧
    warp_sche 可接受"，则持续 valid 的 fetch_ctl 在该拍被授予——等待上界 =
    该拍到来的距离。**残余前提**（活性闭环缺环，系统侧事实）：in0（alu 分支回传）
    不持续有效 ∧ flushCacheValid（icache miss）不持续有效。 -/
theorem dcg2_hbb_bounded_wait (in0v fcv : Nat → Bool) (t0 B : Nat)
    (hex : ∃ t, t0 ≤ t ∧ t ≤ t0 + B ∧ in0v t = false ∧ fcv t = false) :
    ∃ t, t0 ≤ t ∧ t ≤ t0 + B ∧
      wbArbInFire (dcg2BbVal (in0v t) true) (!fcv t) ⟨1, by decide⟩ = true := by
  obtain ⟨t, ht0, htB, h0, hfc⟩ := hex
  exact ⟨t, ht0, htB, dcg2_hbb_fire1 (in0v t) h0 (!fcv t) (by simp [hfc])⟩

/- ---- H-BB 数值回归 ---- -/

section Dcg2HbbTests

-- in1 单独有效 → 授权并 fire
example : wbArbInFire (dcg2BbVal false true) true ⟨1, by decide⟩ = true := by native_decide
-- in0 优先：in1 被压
example : wbArbInFire (dcg2BbVal true true) true ⟨1, by decide⟩ = false := by native_decide
example : wbArbInFire (dcg2BbVal true true) true ⟨0, by decide⟩ = true := by native_decide
-- 下游拒收：无 fire
example : wbArbInFire (dcg2BbVal false true) false ⟨1, by decide⟩ = false := by native_decide
-- out.valid 只看是否有有效输入
example : wbArbOutValid (dcg2BbVal false true) = true := by native_decide
example : wbArbOutValid (dcg2BbVal false false) = false := by native_decide

end Dcg2HbbTests

/- ========================================================================= -/
/- 4. WB-A1：同物理 bank 地址 ⟹ 同 warp                                        -/
/-    链：CtasInv（WG 级三类资源区间两两不交，CtaScheduler ctasPairOk；          -/
/-    归纳保持 ctas_step_inv，事件契约由 H-RT-DISJOINT 的 rt_alloc_disjoint /     -/
/-    rt_wf_disjoint 核销）→ WG 内 WF 步长不交（cu_interface.scala:83-94 的      -/
/-    base + k×perWf 递推）→ bank 交织映射保持不交（operandCollector.scala:94,   -/
/-    110-124：rsAddr = (base >> log2Ceil k) + (r >> log2Ceil k)，k | base 时    -/
/-    = (base + r) / k，k = num_bank = 4，top/parameters.scala:18）。            -/
/- ========================================================================= -/

/-- num_bank（top/parameters.scala:18） -/
def dcg2NumBank : Nat := 4

/-- WB-A1 抽象引理（WG 内步长不交）：同 WG 两个不同 WF 的寄存器子区间
    [B + k·p, B + (k+1)·p) 不相交（cu_interface 拆发递推的 Nat 形式）。 -/
theorem dcg2_wba1_stride_disjoint (B p : Nat) {w1 w2 : Nat} (hw : w1 ≠ w2) (hp : 0 < p) :
    (B + w1 * p) + p ≤ B + w2 * p ∨ (B + w2 * p) + p ≤ B + w1 * p := by
  rcases Nat.lt_or_gt_of_ne hw with h | h
  · left
    have hle : (w1 + 1) * p ≤ w2 * p := Nat.mul_le_mul (Nat.succ_le_of_lt h) (Nat.le_refl p)
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega
  · right
    have hle : (w2 + 1) * p ≤ w1 * p := Nat.mul_le_mul (Nat.succ_le_of_lt h) (Nat.le_refl p)
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega

/-- bank 映射的代数事实：k | b 时 (b >> log2Ceil k) + (r >> log2Ceil k) = (b + r) / k
    （operandCollector.scala:110-124 的求和式在基址对齐时等价于整体除） -/
theorem dcg2_wba1_bank_map_eq (k b r : Nat) (hk : 0 < k) (hb : k ∣ b) :
    b / k + r / k = (b + r) / k := by
  obtain ⟨q, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left q hk, Nat.mul_add_div hk]

/-- 线性收尾（除法抽象为原子后 omega 稳态）：区间错开则商和不等 -/
theorem dcg2_wba1_linear_sep {x1 y1 x2 y2 q1 q2 : Nat}
    (hq1 : q1 < y1) (hq2 : q2 < y2)
    (h : x1 + y1 ≤ x2 ∨ x2 + y2 ≤ x1) :
    x1 + q1 ≠ x2 + q2 := by
  rcases h with h | h <;> omega

/-- WB-A1 抽象引理（bank 映射保持不交）：两段按 k 对齐的不相交区间，各自内部
    地址的 bank 号（地址 / k）也不同。 -/
theorem dcg2_wba1_bank_disjoint (k : Nat) (hk : 0 < k) {b1 s1 b2 s2 : Nat}
    (hb1 : k ∣ b1) (hs1 : k ∣ s1) (hb2 : k ∣ b2) (hs2 : k ∣ s2)
    (hdisj : b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1)
    {r1 r2 : Nat} (hr1 : r1 < s1) (hr2 : r2 < s2) :
    b1 / k + r1 / k ≠ b2 / k + r2 / k := by
  obtain ⟨x1, rfl⟩ := hb1
  obtain ⟨y1, rfl⟩ := hs1
  obtain ⟨x2, rfl⟩ := hb2
  obtain ⟨y2, rfl⟩ := hs2
  have hd1 : r1 / k < y1 := by
    rcases Nat.eq_zero_or_pos y1 with hy | hy
    · subst hy; simp at hr1
    · rcases Nat.lt_or_ge (r1 / k) y1 with h | h
      · exact h
      · exfalso
        have h1 := Nat.mul_le_mul h (Nat.le_refl k)
        have h2 := Nat.div_mul_le_self r1 k
        rw [Nat.mul_comm y1 k] at h1
        omega
  have hd2 : r2 / k < y2 := by
    rcases Nat.eq_zero_or_pos y2 with hy | hy
    · subst hy; simp at hr2
    · rcases Nat.lt_or_ge (r2 / k) y2 with h | h
      · exact h
      · exfalso
        have h1 := Nat.mul_le_mul h (Nat.le_refl k)
        have h2 := Nat.div_mul_le_self r2 k
        rw [Nat.mul_comm y2 k] at h1
        omega
  rw [Nat.mul_div_cancel_left x1 hk, Nat.mul_div_cancel_left x2 hk]
  rcases hdisj with h | h
  · have hx : x1 + y1 ≤ x2 := by
      have h' : k * (x1 + y1) ≤ k * x2 := by rw [Nat.mul_add]; exact h
      exact Nat.le_of_mul_le_mul_left h' hk
    exact dcg2_wba1_linear_sep hd1 hd2 (Or.inl hx)
  · have hx : x2 + y2 ≤ x1 := by
      have h' : k * (x2 + y2) ≤ k * x1 := by rw [Nat.mul_add]; exact h
      exact Nat.le_of_mul_le_mul_left h' hk
    exact dcg2_wba1_linear_sep hd1 hd2 (Or.inr hx)

/-- 整除辅助：k | B 且 k | p ⇒ k | B + w·p（core 无 dvd_mul_of_dvd_right，手工见证） -/
theorem dcg2_dvd_add_wf {k B p w : Nat} (hB : k ∣ B) (hp : k ∣ p) : k ∣ B + w * p := by
  obtain ⟨xB, rfl⟩ := hB
  obtain ⟨q, rfl⟩ := hp
  refine ⟨xB + w * q, ?_⟩
  rw [Nat.mul_add]
  have e : w * (k * q) = k * (w * q) := Nat.mul_left_comm w k q
  rw [e]

/-- WB-A1 抽象引理（同 WG 内）：不同 WF 的 bank 地址不同 -/
theorem dcg2_wba1_within_wg (k : Nat) (hk : 1 ≤ k) {B p : Nat}
    {w1 w2 : Nat} (hw : w1 ≠ w2) (hp : 0 < p)
    (halB : k ∣ B) (halp : k ∣ p)
    {ridx1 ridx2 : Nat} (hr1 : ridx1 < p) (hr2 : ridx2 < p) :
    (B + w1 * p) / k + ridx1 / k ≠ (B + w2 * p) / k + ridx2 / k := by
  have hdisj := dcg2_wba1_stride_disjoint B p hw hp
  have hb1 : k ∣ B + w1 * p := dcg2_dvd_add_wf halB halp
  have hb2 : k ∣ B + w2 * p := dcg2_dvd_add_wf halB halp
  exact dcg2_wba1_bank_disjoint k hk hb1 halp hb2 halp hdisj hr1 hr2

/-- WB-A1 抽象引理（跨 WG）：WG 级区间不交 + 各 WF 子区间在 WG 区间内 +
    对齐 ⟹ 两个 WF 的 bank 地址不同 -/
theorem dcg2_wba1_across_wg (k : Nat) (hk : 1 ≤ k)
    {B1 S1 B2 S2 p : Nat}
    (hdisj0 : B1 + S1 ≤ B2 ∨ B2 + S2 ≤ B1)
    {w1 w2 : Nat} (hle1 : w1 * p + p ≤ S1) (hle2 : w2 * p + p ≤ S2)
    (hal1 : k ∣ B1) (hal2 : k ∣ B2) (halp : k ∣ p)
    {ridx1 ridx2 : Nat} (hr1 : ridx1 < p) (hr2 : ridx2 < p) :
    (B1 + w1 * p) / k + ridx1 / k ≠ (B2 + w2 * p) / k + ridx2 / k := by
  have hdisj : (B1 + w1 * p) + p ≤ B2 + w2 * p ∨ (B2 + w2 * p) + p ≤ B1 + w1 * p := by
    rcases hdisj0 with h | h
    · left; omega
    · right; omega
  have hb1 : k ∣ B1 + w1 * p := dcg2_dvd_add_wf hal1 halp
  have hb2 : k ∣ B2 + w2 * p := dcg2_dvd_add_wf hal2 halp
  exact dcg2_wba1_bank_disjoint k hk hb1 halp hb2 halp hdisj hr1 hr2

/-- **WB-A1 WG 级环（具体化）**：CtasInv 下同 CU 不同槽的 vgpr 区间不交
    （ctasPairOk 的 vgpr 分量；不变式的归纳保持由 CtaScheduler.lean
    ctas_step_inv 给出，底层区间不交由 ResourceTable.lean rt_alloc_disjoint /
    rt_wf_disjoint 核销——H-RT-DISJOINT）。 -/
theorem dcg2_wba1_wg_vgpr_disjoint (s : CtasState) (h : CtasInv s) (cu : Fin 2)
    {sl1 sl2 : Fin 8} (hne : sl1 ≠ sl2) {r1 r2 : CtasWgRec}
    (h1 : s.live cu sl1 = some r1) (h2 : s.live cu sl2 = some r2) :
    r1.vgprBase + r1.vgprSize ≤ r2.vgprBase ∨ r2.vgprBase + r2.vgprSize ≤ r1.vgprBase := by
  have hp : ctasPairOk (s.live cu sl1) (s.live cu sl2) := h.2.2.1 cu sl1 sl2 hne
  rw [h1, h2] at hp
  have hp' : ctasDisjoint r1 r2 := hp
  exact hp'.2.1

/-- **WB-A1 主定理（组合链闭环）**：同一 CU 内两个 warp（WG 槽 sl、WG 内 WF 序号 w）
    的 vgpr 访问打到同一物理 bank 地址 ⟹ 两 warp 相同（sl₁ = sl₂ ∧ w₁ = w₂）。
    前提（残余缺口显式化）：
    (a) 每 WF 基址 = WG vgprBase + w×p 且寄存器号 ridx < p——cuif 侧由
        dcg2_cuif_split_base（下方）钉死递推与 wf_id 的配对；CSR vgpr_base_dispatch
        写入点（CSR.scala:300-301）与 operandCollector rsAddr 映射未建模；
    (b) 对齐 k | vgprBase ∧ k | p（bank 交织正确的条件，k = num_bank = 4）；
    (c) numWf×p ≤ vgprSize（分配尺寸关系，host/allocator 参数语义）。
    不同 CU 属不同 SM 的物理寄存器堆，地址天然不同（不计入同一物理地址）。 -/
theorem dcg2_wba1_vgpr_bank_addr_unique (s : CtasState) (h : CtasInv s) (cu : Fin 2)
    (k : Nat) (hk : 1 ≤ k)
    {sl1 sl2 : Fin 8} {r1 r2 : CtasWgRec}
    (h1 : s.live cu sl1 = some r1) (h2 : s.live cu sl2 = some r2)
    {w1 w2 : Nat} (hw1 : w1 < r1.numWf) (hw2 : w2 < r2.numWf)
    {p : Nat} (hp0 : 0 < p)
    (hfit1 : r1.numWf * p ≤ r1.vgprSize) (hfit2 : r2.numWf * p ≤ r2.vgprSize)
    (halB1 : k ∣ r1.vgprBase) (halB2 : k ∣ r2.vgprBase) (halp : k ∣ p)
    {ridx1 ridx2 : Nat} (hr1 : ridx1 < p) (hr2 : ridx2 < p)
    (haddr : (r1.vgprBase + w1 * p) / k + ridx1 / k =
             (r2.vgprBase + w2 * p) / k + ridx2 / k) :
    sl1 = sl2 ∧ w1 = w2 := by
  by_cases hslot : sl1 = sl2
  · subst hslot
    have hrr : r2 = r1 := Option.some.inj (h2.symm.trans h1)
    subst hrr
    refine ⟨rfl, ?_⟩
    by_cases hw : w1 = w2
    · exact hw
    · exact absurd haddr (dcg2_wba1_within_wg k hk hw hp0 halB1 halp hr1 hr2)
  · have hdisj := dcg2_wba1_wg_vgpr_disjoint s h cu hslot h1 h2
    have hle1 : w1 * p + p ≤ r1.vgprSize := by
      have hle : (w1 + 1) * p ≤ r1.numWf * p :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hw1) (Nat.le_refl p)
      rw [Nat.add_mul, Nat.one_mul] at hle
      omega
    have hle2 : w2 * p + p ≤ r2.vgprSize := by
      have hle : (w2 + 1) * p ≤ r2.numWf * p :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hw2) (Nat.le_refl p)
      rw [Nat.add_mul, Nat.one_mul] at hle
      omega
    exact absurd haddr (dcg2_wba1_across_wg k hk hdisj hle1 hle2 halB1 halB2 halp hr1 hr2)

/- ---- WB-A1 的 cuif 侧缺环补齐：拆发基址递推不变式（补登记册缺口 G3 的 ----
   ---- vgpr 半边：第 k 个 WF 的 vgpr 基址 = vgprBase + k×perWf 且与 wf_tag    ----
   ---- 的 wf_id 是同一个 k）                                                 ---- -/

/-- cu_interface 拆发基址不变式（增量于 CuifInv）：拆发中（splitCnt ≠ 0）队首 WG
    的当前 vgpr 基址 = vgprBase +（已发序号 = numWf - splitCnt）× numVgprPerWf
    （mod 2^10，cu_interface.scala:83-90 的累加递推）。 -/
def dcg2CuifSplitVgprInv (s : CuifState) : Prop :=
  s.splitCnt ≠ 0#4 → ∃ h t, s.fifo = h :: t ∧
    s.splitVgpr = h.vgprBase +
      (h.numWf - s.splitCnt).zeroExtend 10 * h.numVgprPerWf.extractLsb' 0 10

theorem dcg2_cuif_splitVgpr_init : dcg2CuifSplitVgprInv cuifInit := by
  intro h; exact absurd rfl h

/-- 拆发递推的位级一步（vgpr：10b 基址 + 11b 步长，截断回 10b） -/
theorem dcg2_split_step_bv10 (base : BitVec 10) (n c : BitVec 4) (p : BitVec 11)
    (hc2 : 2#4 ≤ c) (hle : c ≤ n) :
    ((base + (n - c).zeroExtend 10 * p.extractLsb' 0 10).zeroExtend 11 + p).extractLsb' 0 10 =
      base + (n - (c - 1#4)).zeroExtend 10 * p.extractLsb' 0 10 := by
  bv_decide

/-- 装入拍的基址：已发序号 0 ⇒ 基址 = vgprBase -/
theorem dcg2_split_zero_bv10 (base : BitVec 10) (n : BitVec 4) (p : BitVec 11) :
    base + (n - n).zeroExtend 10 * p.extractLsb' 0 10 = base := by
  bv_decide

/-- 不变式单拍保持（在 CuifInv 下；注意本不变式只增量于 CuifInv，step 证明
    不需要 CuifEnvOk——splitVgpr 的更新不依赖环境契约）。 -/
theorem dcg2_cuif_splitVgpr_step (s : CuifState) (i : CuifInputs)
    (hinv : CuifInv s) (h : dcg2CuifSplitVgprInv s) :
    dcg2CuifSplitVgprInv (cuifStep s i) := by
  intro hne
  by_cases hc0 : s.splitCnt = 0#4
  · -- 装入拍：fifo 必非空（否则 splitCnt' = 0 与 hne 矛盾），loadNew 生效
    obtain ⟨h0, t0, hfifo⟩ : ∃ h0 t0, s.fifo = h0 :: t0 := by
      have hsc := cuif_splitCnt_step s i
      rw [hsc, if_neg (by simp [hc0])] at hne
      cases hf : s.fifo with
      | nil => rw [hf] at hne; simp at hne
      | cons h0 t0 => exact ⟨h0, t0, rfl⟩
    have hload : cuifLoadNew s = true := by
      unfold cuifLoadNew
      simp [hc0, hfifo]
    have hdeq : cuifDeqFire s i = false := cuif_no_deq_of_cnt0 s i hc0
    have hfifo' := cuif_fifo_step_cons s i h0 t0 hfifo hdeq
    have hsc : (cuifStep s i).splitCnt = h0.numWf := by
      rw [cuif_splitCnt_step, if_neg (by simp [hc0]), hfifo]
    have hv : (cuifStep s i).splitVgpr = h0.vgprBase := by
      have e : (cuifStep s i).splitVgpr =
          (if cuifLoadNew s then (cuifHead s).vgprBase
           else if cuifWfFire s i then
             (s.splitVgpr.zeroExtend 11 + (cuifHead s).numVgprPerWf).extractLsb' 0 10
           else s.splitVgpr) := rfl
      rw [e, if_pos hload, cuifHead_of_cons hfifo]
    refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), hfifo', ?_⟩
    rw [hv, hsc]
    exact (dcg2_split_zero_bv10 h0.vgprBase h0.numWf h0.numVgprPerWf).symm
  · obtain ⟨h0, t0, hfifo, hbase⟩ := h hc0
    obtain ⟨_, _, _, _, hsplit, _⟩ := hinv
    obtain ⟨h0', t0', hfifo', hle⟩ := hsplit hc0
    rw [hfifo] at hfifo'
    cases hfifo'
    have hleBV : s.splitCnt ≤ h0.numWf := hle
    have hload : cuifLoadNew s = false := by unfold cuifLoadNew; simp [hc0]
    by_cases hfire : cuifWfFire s i = true
    · have hsc : (cuifStep s i).splitCnt = s.splitCnt - 1#4 := cuif_split_countdown s i hfire
      have hc1ne : s.splitCnt ≠ 1#4 := by
        intro h1
        apply hne
        rw [hsc, h1]
        decide
      have hc2 : 2#4 ≤ s.splitCnt := by bv_decide
      have hdeq : cuifDeqFire s i = false := by
        unfold cuifDeqFire
        simp [hc1ne]
      have hfifo'' := cuif_fifo_step_cons s i h0 t0 hfifo hdeq
      have hhead : cuifHead s = h0 := cuifHead_of_cons hfifo
      have hv : (cuifStep s i).splitVgpr =
          (s.splitVgpr.zeroExtend 11 + h0.numVgprPerWf).extractLsb' 0 10 := by
        have e : (cuifStep s i).splitVgpr =
            (if cuifLoadNew s then (cuifHead s).vgprBase
             else if cuifWfFire s i then
               (s.splitVgpr.zeroExtend 11 + (cuifHead s).numVgprPerWf).extractLsb' 0 10
             else s.splitVgpr) := rfl
        rw [e]
        simp [hload, hfire, hhead]
      refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), hfifo'', ?_⟩
      rw [hv, hsc, hbase]
      exact dcg2_split_step_bv10 h0.vgprBase h0.numWf s.splitCnt h0.numVgprPerWf hc2 hleBV
    · have hfire' : cuifWfFire s i = false := (Bool.not_eq_true _).mp hfire
      have hsc : (cuifStep s i).splitCnt = s.splitCnt := by
        rw [cuif_splitCnt_step, if_pos hc0]
        simp [hfire']
      have hdeq : cuifDeqFire s i = false := cuif_no_fire_no_deq s i hc0 hfire'
      have hfifo'' := cuif_fifo_step_cons s i h0 t0 hfifo hdeq
      have hv : (cuifStep s i).splitVgpr = s.splitVgpr := by
        have e : (cuifStep s i).splitVgpr =
            (if cuifLoadNew s then (cuifHead s).vgprBase
             else if cuifWfFire s i then
               (s.splitVgpr.zeroExtend 11 + (cuifHead s).numVgprPerWf).extractLsb' 0 10
             else s.splitVgpr) := rfl
        rw [e]
        simp [hload, hfire']
      refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), hfifo'', ?_⟩
      rw [hv, hsc]
      exact hbase

/-- 不变式多拍保持（CuifInv 由 cuifInv_run 提供） -/
theorem dcg2_cuif_splitVgpr_run (ins : List CuifInputs)
    (henv : ∀ (pre : List CuifInputs) (i : CuifInputs), CuifEnvOk (cuifRun cuifInit pre) i) :
    dcg2CuifSplitVgprInv (cuifRun cuifInit ins) := by
  have key : ∀ l : List CuifInputs, dcg2CuifSplitVgprInv (cuifRun cuifInit l.reverse) := by
    intro l
    induction l with
    | nil => exact dcg2_cuif_splitVgpr_init
    | cons x xs ih =>
      have e2 : cuifRun cuifInit ((x :: xs).reverse) = cuifStep (cuifRun cuifInit xs.reverse) x := by
        simp [cuifRun, List.reverse_cons, List.foldl_append]
      rw [e2]
      exact dcg2_cuif_splitVgpr_step _ _ (cuifInv_run _ henv) ih
  have h := key ins.reverse
  rwa [List.reverse_reverse] at h

/-- **WB-A1 cuif 环（配对定理）**：拆发中第 k = numWf - splitCnt 个待/正发 WF 的
    wf_tag 低位序号（H-CUIF-SPLIT，cuif_split_tag）与其 vgpr 基址偏移（本不变式）
    是同一个 k——wf_id 与基址配对，warp 级分配"逐 WF 等距切分 WG 区间"成立。 -/
theorem dcg2_cuif_split_base (s : CuifState) (h : CuifInv s) (hv : dcg2CuifSplitVgprInv s)
    (hc : s.splitCnt ≠ 0#4) :
    ∃ h' t, s.fifo = h' :: t ∧
      cuifWfNewTag s = cuifWfTag h'.wgSlotId ((h'.numWf - s.splitCnt).extractLsb' 0 3) ∧
      s.splitVgpr = h'.vgprBase + (h'.numWf - s.splitCnt).zeroExtend 10 *
        h'.numVgprPerWf.extractLsb' 0 10 := by
  obtain ⟨h1, t1, hf1, htag, _⟩ := cuif_split_tag s h hc
  obtain ⟨h2, t2, hf2, hbase⟩ := hv hc
  rw [hf1] at hf2
  cases hf2
  exact ⟨h1, t1, hf1, htag, hbase⟩

/- ---- WB-A1 数值回归（先测试：拆发基址递推的数值镜像） ---- -/

section Dcg2WbA1Tests

/-- WG V：cu0 slot4，3 WF，vgprBase=5，numVgprPerWf=32 -/
def dcg2WgV : CuifWg :=
  ⟨0#1, 4#3, 3#4, 0x11#32, 0#12, 32#11, 0#18, 0#11, 5#10, 0#17, 0#32, false, false, false⟩

def dcg2TsplitV : List CuifInputs := [
  { enqValid := true, enqWg := dcg2WgV },   -- 拍0：enq
  { cuRdy0 := true },                        -- 拍1：loadNew（cnt←3，splitVgpr←5）
  { cuRdy0 := true },                        -- 拍2：发 wf0（基址 5）→ 37
  { cuRdy0 := true },                        -- 拍3：发 wf1（基址 37）→ 69
  { cuRdy0 := true }                         -- 拍4：发 wf2（基址 69）+ deq
]

-- 装入拍后：splitVgpr = 5 = 5 + 0×32
theorem dcg2T_split_load : (cuifRun cuifInit (dcg2TsplitV.take 2)).splitVgpr = 5#10 := by
  native_decide
-- 发 wf0 后：37 = 5 + 1×32
theorem dcg2T_split_f0 : (cuifRun cuifInit (dcg2TsplitV.take 3)).splitVgpr = 37#10 := by
  native_decide
-- 发 wf1 后：69 = 5 + 2×32
theorem dcg2T_split_f1 : (cuifRun cuifInit (dcg2TsplitV.take 4)).splitVgpr = 69#10 := by
  native_decide
-- tag 配对：拍2（wf0）tag = {slot4, 0}，拍3（wf1）tag = {slot4, 1}
theorem dcg2T_split_tag0 :
    cuifWfNewTag (cuifRun cuifInit (dcg2TsplitV.take 2)) = cuifWfTag 4#3 0#3 := by
  native_decide
theorem dcg2T_split_tag1 :
    cuifWfNewTag (cuifRun cuifInit (dcg2TsplitV.take 3)) = cuifWfTag 4#3 1#3 := by
  native_decide

-- 步长不交（具体实例：perWf=32、wf0 与 wf2 的 vgpr 区间 [5,37) 与 [69,101)）
example : (5 + 0 * 32) + 32 ≤ 5 + 2 * 32 := by decide
-- bank 映射保持（k=4，对齐基址 64：(64>>2)+(37>>2) = 16+9 = 25 = 101/4）
example : (64 : Nat) / 4 + 37 / 4 = (64 + 37) / 4 := by decide

end Dcg2WbA1Tests

/- ========================================================================= -/
/- 5. CTA-A1 / CTA-E1：Allocator/CuInterface 环境契约的组合闭环                 -/
/- ========================================================================= -/

/-- cuif 侧"该 (cu, slot) 有 WG 占驻"：在驻（liveMem）或正在 dealloc 上报中
    （gfsm=dealloc 且寄存器指向该槽——此时 live 已在 finish 拍清除，但 dealloc
    事务尚未被 allocator 消费，簿记上该槽仍占）。 -/
def dcg2CuifOccupied (cs : CuifState) (cu : BitVec 1) (slot : BitVec 3) : Prop :=
  cs.liveMem (cuifGaddr cu slot) = true ∨
    (cs.gfsm = .dealloc ∧ cs.cuReg = cu ∧ cs.slotReg = slot)

/-- **CTA-A1/E1 的跨模块簿记对应（残余缺口 C1，显式前提）**：allocator 的
    wgslot 位图 / wfslot 计数与 cu_interface 的 liveMem/fifo/gather 状态一致。
    正当性论证（未归纳验证——需要 alloc×cuif 联合状态机，当前两模型未联合例化）：
    alloc 生效拍同拍置 wgslot 位（allocator.scala:295）并经 cuinterface_buf enq
    （:330），cuif loadNew 置 liveMem（cu_interface.scala:132）；dealloc 由 cuif
    发起（:204，H-CUIF-DEALLOC：仅在驻 WG 计数恰好完成才发）经 allocator 的
    rt_dealloc 端口（:289）同拍清位——同一事务的两端视图。 -/
def dcg2Agree (as : AlcState) (cs : CuifState) : Prop :=
  (∀ cu slot, ((as.wgslot (alcCuFin cu) >>> slot.zeroExtend 8) &&& 1#8 = 1#8) ↔
      (dcg2CuifOccupied cs cu slot ∨
        ∃ w, w ∈ cs.fifo ∧ w.cuId = cu ∧ w.wgSlotId = slot)) ∧
  (cuifRtDeallocValid cs = true → cs.infoRd.numWf ≤ as.wfslot (alcCuFin cs.cuReg))

/-- 位辅助：补字的该位为 1 ⟹ 原字该位为 0（供 alc_h_alloc_slot 的补位形式转换） -/
theorem dcg2_bit_clear_of_compl (w : BitVec 8) (id : BitVec 3)
    (h : (~~~w >>> id.zeroExtend 8) &&& 1#8 = 1#8) :
    (w >>> id.zeroExtend 8) &&& 1#8 = 0#8 := by
  bv_decide

/-- **CTA-A1（闭环）**：dealloc 事务来自 cuif 的完成上报（H-CUIF-DEALLOC），
    其 numWf 取自该槽在驻记录（dcg2_ctaA1_source）；在簿记对应 dcg2Agree 下，
    扣减量不超过该 CU 当前 wfslot 占用——AlcEnvOk（A1）成立，:296 的 4 位减法
    不回绕。接线前提 hwire：cu_interface.scala:205-211 的 dealloc bits 接到
    allocator 的 io.rt_dealloc（:284-289）。 -/
theorem dcg2_ctaA1 (as : AlcState) (cs : CuifState) (i : AlcInputs)
    (hagree : dcg2Agree as cs)
    (hvalid : cuifRtDeallocValid cs = true)
    (hwire : i.deallocV = true ∧ i.deallocCu = cs.cuReg ∧ i.deallocSlot = cs.slotReg ∧
             i.deallocNumWf = cs.infoRd.numWf) :
    AlcEnvOk as i := by
  intro _
  obtain ⟨_, hcu, _, hnum⟩ := hwire
  rw [hnum, hcu]
  exact hagree.2 hvalid

/-- **CTA-A1 源端事实打包**：UPDATE 拍 finish 时（dealloc 首发拍），该槽在驻、
    infoRd 即该槽 gather ram 记录、计数恰好达到 numWf（H-CUIF-DEALLOC 三定理组合）；
    DEALLOC 状态的重发由 cuif_dealloc_no_double 保证至多被消费一次。 -/
theorem dcg2_ctaA1_source (s : CuifState) (h : CuifInv s)
    (hg : s.gfsm = .update) (hf : cuifFinish s = true) :
    s.liveMem (cuifGaddr s.cuReg s.slotReg) = true ∧
    s.infoRd = s.infoMem (cuifGaddr s.cuReg s.slotReg) ∧
    s.cntRd.toNat + 1 = s.infoRd.numWf.toNat := by
  have hval : cuifRtDeallocValid s = true :=
    (cuif_dealloc_valid_iff s).mpr (Or.inl ⟨hg, hf⟩)
  exact ⟨(h.2.2.2.2.2.2.2.2.1 hg).2.2, cuif_dealloc_wgId s h hg, cuif_dealloc_exact s h hval⟩

/-- **CTA-E1（闭环）**：allocator 在 ALLOC 首拍只选空闲槽（H-ALLOC-SLOT 已核销，
    alc_h_alloc_slot）；在簿记对应 dcg2Agree 下，cuif 侧同槽既不在驻也无排队
    （¬ cuifSlotBusy）；numWf ∈ [1,8] 由 host 契约（H-WF，axiomatic；numWf ≥ 1
    与 Q-CUIF1 同源）经接线传入。即 CuifEnvOk 的 enq 半成立。 -/
theorem dcg2_ctaE1 (as : AlcState) (cs : CuifState) (i : CuifInputs)
    (hinv : AlcInv as) (hagree : dcg2Agree as cs)
    (h1 : as.fsm = .alloc) (h2 : as.fsmR1 ≠ .alloc)
    (hwire : i.enqWg.cuId = as.cu ∧ i.enqWg.wgSlotId = as.wgslotId ∧
             i.enqWg.numWf = as.wg.numWf)
    (hwf : 1 ≤ as.wg.numWf.toNat ∧ as.wg.numWf.toNat ≤ 8) :
    cuifEnqFire cs i = true →
      1 ≤ i.enqWg.numWf.toNat ∧ i.enqWg.numWf.toNat ≤ 8 ∧
        ¬ cuifSlotBusy cs i.enqWg.cuId i.enqWg.wgSlotId := by
  intro _
  obtain ⟨hcu, hslot, hnum⟩ := hwire
  refine ⟨by rw [hnum]; exact hwf.1, by rw [hnum]; exact hwf.2, ?_⟩
  obtain ⟨_, _, hbit⟩ := alc_h_alloc_slot as hinv h1 h2
  have hclear : (as.wgslot (alcCuFin as.cu) >>> as.wgslotId.zeroExtend 8) &&& 1#8 = 0#8 :=
    dcg2_bit_clear_of_compl _ _ hbit
  intro hbusy
  rw [hcu, hslot] at hbusy
  unfold cuifSlotBusy at hbusy
  have hoc : dcg2CuifOccupied cs as.cu as.wgslotId ∨
      ∃ w, w ∈ cs.fifo ∧ w.cuId = as.cu ∧ w.wgSlotId = as.wgslotId := by
    rcases hbusy with hl | hf
    · exact Or.inl (Or.inl hl)
    · exact Or.inr hf
  have hset := (hagree.1 as.cu as.wgslotId).mpr hoc
  exact absurd (hset.symm.trans hclear) (by decide)

/- ========================================================================= -/
/- 6. 汇总与公理审计                                                           -/
/-    预期：纯 Nat/List 组合引理仅 [propext, Quot.sound(, Classical.choice)]； -/
/-    bv_decide 引理（dcg2_split_step_bv10 / dcg2_split_zero_bv10 /            -/
/-    dcg2_bit_clear_of_compl / dcg2_bjb1_consume）带每定理私有 LRAT trust      -/
/-    公理；native_decide 测试带 Lean.ofReduceBool（仅测试定理）。              -/
/- ========================================================================= -/

#print axioms dcg2_wba2_prefix
#print axioms dcg2_wba2_getElem
#print axioms dcg2_wba2_chain
#print axioms dcg2_bjb1_consume
#print axioms dcg2_hbb_grant
#print axioms dcg2_hbb_fire
#print axioms dcg2_hbb_no_fire_iff
#print axioms dcg2_hbb_bounded_wait
#print axioms dcg2_wba1_stride_disjoint
#print axioms dcg2_wba1_bank_disjoint
#print axioms dcg2_wba1_vgpr_bank_addr_unique
#print axioms dcg2_cuif_splitVgpr_step
#print axioms dcg2_cuif_splitVgpr_run
#print axioms dcg2_cuif_split_base
#print axioms dcg2_ctaA1
#print axioms dcg2_ctaE1

end Ventus.Spec
