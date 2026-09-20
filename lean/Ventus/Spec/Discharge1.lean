/- ========================================================================= -/
/-                     Spec/Discharge1.lean                                   -/
/-  Contracts.lean 登记册 6 条 pending 契约的核销（第一波）                     -/
/-                                                                           -/
/-  核销对象与结论（登记册翻转由主会话统一做，本文件不动 Contracts.lean）：      -/
/-                                                                           -/
/-  1. H-IB2I（pipe.scala:223-224，ibuffer2issue 不引入额外反压扭曲）：         -/
/-     【已核销】granted warp 的 ibuffer 出队 ready = out.ready && warp_ready   -/
/-     （dcg1_hIb2i_ready_closed），仲裁器不附加第三项；fire 一致性             -/
/-     （dcg1_hIb2i_fire_eq）与 bits 归属（dcg1_hIb2i_bits_closed）组合闭环。 -/
/-     链：Issue.lean ISS11/ISS12 + RRArbiter rraInReady + Pipe.lean W5。     -/
/-  2. H-DELAY（pipe.scala:161,237 + scoreboard.scala:142，delay 连线恒等）： -/
/-     【已核销】pipeScoreboardBusy_bit 在逐 warp 记分板实例化下给出           -/
/-     bit i = sbDelay（dcg1_hDelay_wire）；pipe_i4_gate_chain 的 hd 前提      -/
/-     由定义性等式 rfl 闭合（dcg1_hDelay_gate_closed 不再含 delay 连线假设）。-/
/-  3. H-WID（branch_join.scala:115,121,183，fetch_ctl/complete 的 wid =       -/
/-     所属 warp）：【已核销（模型范围内）】wid 连线是恒等（branch_ctl_buf.bits -/
/-     .wid → warp_id → complete.bits / fetch_ctl.wid），dcg1_hWid_*；          -/
/-     BranchJoin.lean 为单 warp 模型（D2：各 warp 栈完全独立、无交互），      -/
/-     故 wid 不变性 = 恒等连线 + 模型侧无跨 warp 混淆通道。                    -/
/-     残留缺口（记录）：bjstack(warp_id) 的实例选择（:111-112）与             -/
/-     io.out_mask 的 wid mux（:260）在 D2 抽象中被省略，多 warp 分发正确性    -/
/-     不在本模型覆盖范围（不在本契约语义内，本契约只约束事件 wid 的传递）。   -/
/-  4. WB-A3（OpCol 串行化）：【已核销】独立陈述 dcg1WbA3Serialized 并证明      -/
/-     （dcg1_wbA3_serialization = i4f_no_two_busy_orig 的命题化）；机制半：    -/
/-     占用位置位当拍后继指令被门控拦截、不进入任何 CU（dcg1_wbA3_blocked_     -/
/-     while_busy / dcg1_wbA3_next_blocked）；占用位语义（原版）               -/
/-     dcg1_wbA3_occ_tracks_busy_orig。                                       -/
/-  5. H-ALLOC-PENDING（allocator.scala:187-188，alloc ⟹ pending>0）：          -/
/-     【已核销（WgbEnvOk 环境契约条件下）】取件当拍缓冲非空                   -/
/-     （dcg1_hAllocPending_rdAct）；alloc 输出寄存器有效 ⟹ pending>0          -/
/-     （不变式 dcg1AllocRegInv + dcg1_allocRegInv_step/run 归纳保持 +         -/
/-     dcg1_hAllocPending_offer/fire）；accept 半 dcg1_hAllocPending_accept。 -/
/-     条件说明：不变式保持依赖 WgbEnvOk（D6：alloc_result 只指在驻已移交槽， -/
/-     由 allocator「每请求恰一响应」纪律保证），该纪律本身是 CTA 侧环境契约。 -/
/-  6. WS-M7（warp_schedule.scala:55 "warpRsp always ready"）：【已证伪】       -/
/-     I-6 的契约化结论：CTA2warp 的 Queue(16) 满时 warpRsp.ready=0 且         -/
/-     valid 响应被静默丢弃（dcg1_wsM7_counterexample，反例状态从复位可达：   -/
/-     dcg1_wsM7_fifo_full 轨迹 = 8 派发 + c2wFillIns）；假设的全称形式被      -/
/-     否定（dcg1_wsM7_assumption_false）。登记册该条应改"已证伪"。           -/
/-  7. IC-D8 拆分（ICache.scala:185 / ICacheMSHR.scala:163）：                  -/
/-     (a) coreReq 地址 num_fetch=2 对齐：【已核销】PCcontrol 的 pout 8B 对齐  -/
/-         单拍保持（dcg1_pcc_step_aligned）+ run 归纳（dcg1_pcc_run_aligned） -/
/-         + 对接 :185 断言条件（dcg1_icD8_align_assert）。前提仅 src3         -/
/-         （miss 重放）回填地址对齐——该地址即上次请求地址，归纳闭环。        -/
/-     (b) memRsp 只回已分配已发 entry：【保持 axiomatic，补强理由】           -/
/-         陈述为 dcg1IcRspEnvOk；消费闭环 dcg1_icD8_rsp_consumes_env          -/
/-         （icMshr_rsp_fire 的 hvalid 前提由环境纪律供给）。不可内证：        -/
/-         响应来自片外内存子系统（L2/DRAM/互联不在本工程范围），d_source      -/
/-         索引由对端回填，ICache 侧无任何机制约束其指向；:163 的 assert       -/
/-         正是源码作者对此环境纪律的仿真期检查。                             -/
/-                                                                           -/
/-  公理说明：bv_decide 定理带每定理私有的 LRAT trust 公理（…._native.        -/
/-  bv_decide.ax_*）；WS-M7 反例的轨迹求值用 native_decide（多                 -/
/-  Lean.ofReduceBool）。按 AGENTS.md 归档注明。                              -/
/- ========================================================================= -/

import Ventus.Pipe
import Ventus.Schedule.Issue
import Ventus.Schedule.IBuffer
import Ventus.Schedule.I4Fix
import Ventus.CTA.WgBuffer
import Ventus.CTA.CTA2warp
import Ventus.Mem.ICache
import Ventus.SIMT.PCcontrol
import Std.Tactic.BVDecide

namespace Ventus.Spec

open Ventus Ventus.CTA Ventus.Schedule Ventus.SIMT Ventus.Mem

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. H-IB2I：ibuffer2issue 不引入额外反压扭曲（pipe.scala:223-224）            -/
/-                                                                           -/
/-  链：ibuffer lane 的出队 ready（IBuffer.lean IbLaneIn.outRdy，字段注释即     -/
/-  指向 pipe.scala:224）= pipeIbOutReady（Pipe.lean W5b：:224 的连线）        -/
/-  ∘ ibuffer2issue.io.in(i).ready（= chisel RRArbiter count=1 的               -/
/-  rraInReady = grant(i) && out.ready，ibuffer.scala:64-65 的 rrarbit_x/v）。 -/
/-  ISS11（iss_ib2iss_fire_integrity）：fire 时 granted 输入的 ready 恰为       -/
/-  out.ready——仲裁器对 granted 通道不加任何额外反压项。                        -/
/- ========================================================================= -/

/-- 【H-IB2I 半环：arbiter 侧】granted（chosen 且 valid）输入的 in.ready 恰等于
    仲裁器 out.ready（grant(chosen)=true，rra1_choice_granted）——
    iss_ib2iss_fire_integrity 的 ready 半的独立陈述 -/
theorem dcg1_hIb2i_no_distortion {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (outRdy : Bool) (hv : rraOutValid hn v lg = true) :
    rraInReady hn v lg outRdy (rraChoice hn v lg) = outRdy := by
  have hv' : v.getLsbD (rraChoice hn v lg).val = true := hv
  have h := iss_ib2iss_fire_integrity hn v lg outRdy hv
  -- 注意：ISS11 的陈述按 "`&&` 优先级低于 `=`" 解析（见 AGENTS.md 踩坑），
  -- h 的实际形态为 (v.getLsbD ... && decide (rraInReady ... = outRdy)) = true
  rw [hv', Bool.true_and] at h
  exact of_decide_eq_true h

/-- 【H-IB2I 闭环】granted warp 的 ibuffer 出队 ready（= IbLaneIn.outRdy 的
    实际驱动值，pipe.scala:224）：= 仲裁器 out.ready && warp_sche 的
    warp_ready(i)，无第三项——"不引入额外反压扭曲"的精确形式 -/
theorem dcg1_hIb2i_ready_closed {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (outRdy warpRdy : Bool) (hv : rraOutValid hn v lg = true) :
    pipeIbOutReady (rraInReady hn v lg outRdy (rraChoice hn v lg)) warpRdy =
      (outRdy && warpRdy) := by
  rw [dcg1_hIb2i_no_distortion hn v lg outRdy hv]
  rfl

/-- 【H-IB2I fire 一致性】pipe.scala:223-224 两侧（ibuffer 出队 / arbiter 入队）
    的 fire 刻画相同（Pipe.lean W5 既有定理 pipe_ib2i_fire_eq 的登记形态） -/
theorem dcg1_hIb2i_fire_eq (v r w : Bool) :
    pipeIb2iInFire v r w = pipeIbOutFire v r w := pipe_ib2i_fire_eq v r w

/-- 【H-IB2I bits 归属】fire 拍被消费的 bits = granted 输入的 bits
    （组合直通，ISS12 的登记形态） -/
theorem dcg1_hIb2i_bits_closed {n : Nat} (hn : 0 < n) {α : Type} (bits : Fin n → α)
    (v : BitVec n) (lg : Fin n) :
    rraOutBits hn bits v lg = bits (rraChoice hn v lg) :=
  iss_ib2iss_bits_of_fire hn bits v lg

-- 数值佐证（num_warp=8 实例，v=0b00000101、lastGrant=0 → chosen=2）
example : pipeIbOutReady (rraInReady (by decide : 0 < 8) 0b00000101#8 ⟨0, by decide⟩ true
    (rraChoice (by decide) 0b00000101#8 ⟨0, by decide⟩)) true = true := by decide
example : pipeIbOutReady (rraInReady (by decide : 0 < 8) 0b00000101#8 ⟨0, by decide⟩ false
    (rraChoice (by decide) 0b00000101#8 ⟨0, by decide⟩)) true = false := by decide
example : pipeIbOutReady (rraInReady (by decide : 0 < 8) 0b00000101#8 ⟨0, by decide⟩ true
    (rraChoice (by decide) 0b00000101#8 ⟨0, by decide⟩)) false = false := by decide

/- ========================================================================= -/
/- 2. H-DELAY：delay 连线 = 该 warp 的 delay                                    -/
/-    （pipe.scala:161 装配 + :237 接 ibuffer 头指令 + scoreboard.scala:142）   -/
/- ========================================================================= -/

/-- 【H-DELAY 连线恒等】scoreboard_busy 的第 i 位 = 第 i 个记分板实例的 delay
    （sb 为逐 warp 记分板状态，cc 为逐 warp 的 ibuffer 头指令控制字，
    即 pipe.scala:237 的 scoreb(i).ibuffer_if_ctrl := ibuffer.io.out(i).bits）。
    pipeScoreboardBusy_bit（Pipe.lean W3）在"连线忠实"实例化下的形态 -/
theorem dcg1_hDelay_wire (sb : Fin 8 → SbState) (cc : Fin 8 → SbCtrl) (i : BitVec 3) :
    ((pipeScoreboardBusy (fun j => sbDelay (sb j) (cc j)) >>> i.zeroExtend 8) &&& 1#8 = 1#8) ↔
      sbDelay (sb (wsFin i)) (cc (wsFin i)) = true :=
  pipeScoreboardBusy_bit _ _

/-- 【H-DELAY 闭环】I-4 门控链在逐 warp 记分板实例化下的完整形式：
    OpColV 占用位置位 ⟹ 该 warp 当拍不可能从 ibuffer 向 ibuffer2issue 发射。
    pipe_i4_gate_chain 的前提 `d (wsFin i) = sbDelay s c` 由实例化后的定义性
    等式（rfl）闭合——本定理不再含"delay 连线"假设，H-DELAY 核销 -/
theorem dcg1_hDelay_gate_closed (sb : Fin 8 → SbState) (cc : Fin 8 → SbCtrl)
    (bar exe act : BitVec 8) (i : BitVec 3)
    (hocc : sbReadOpColV (sb (wsFin i)) = true) (ibValid ib2iRdy : Bool) :
    pipeIb2iInFire ibValid ib2iRdy
      (pipeWarpReadyBit bar (pipeScoreboardBusy (fun j => sbDelay (sb j) (cc j))) exe act i) =
        false :=
  pipe_i4_gate_chain (fun j => sbDelay (sb j) (cc j)) bar exe act i _ _ rfl hocc _ _

/- ========================================================================= -/
/- 3. H-WID：fetch_ctl/complete 事件的 wid = 该 vbranch/join 所属 warp          -/
/-    （branch_join.scala:115,121,183）                                        -/
/- ========================================================================= -/

/-- 【H-WID 连线模型】warp_id := branch_ctl_buf.bits.wid（:115） -/
def dcg1BjWarpId (ctrlWid : BitVec 3) : BitVec 3 := ctrlWid
/-- 【H-WID 连线模型】io.complete.bits := branch_ctl_buf.bits.wid（:121） -/
def dcg1BjCompleteWid (ctrlWid : BitVec 3) : BitVec 3 := ctrlWid
/-- 【H-WID 连线模型】fetch_ctl.wid := warp_id（:183，覆盖 :179-182 的默认 0.U） -/
def dcg1BjFetchCtlWid (ctrlWid : BitVec 3) : BitVec 3 := dcg1BjWarpId ctrlWid

/-- 【H-WID 核销】complete 事件 wid = 受理该 vbranch 的 warp -/
theorem dcg1_hWid_complete (w : BitVec 3) : dcg1BjCompleteWid w = w := rfl
/-- 【H-WID 核销】fetch_ctl 事件 wid = 受理该 vbranch/join 的 warp -/
theorem dcg1_hWid_fetchCtl (w : BitVec 3) : dcg1BjFetchCtlWid w = w := rfl
/-- 【H-WID 同源】两路输出的 wid 逐位相同（同一 wire，:115 单源） -/
theorem dcg1_hWid_same_source (w : BitVec 3) :
    dcg1BjCompleteWid w = dcg1BjFetchCtlWid w := rfl

/-- 带 wid 的事件输出：bjSysStep 的 complete/fetchValid 配上 :121/:183 的 wid 连线 -/
def dcg1BjOutWid {nT : Nat} (o : BjOut nT) (w : BitVec 3) :
    (Bool × BitVec 3) × (Bool × BitVec 3) :=
  ((o.complete, dcg1BjCompleteWid w), (o.fetchValid, dcg1BjFetchCtlWid w))

/-- 【H-WID 事件形式】branch/join/nop 任意事件、任意栈状态：complete 与
    fetch_ctl 携带的 wid 都是所属 warp 的 wid。模型侧依据：BranchJoin.lean D2
    （单 warp 建模——各 warp 的 branch_join_stack 与 thread_masks 项完全独立、
    无交互），不存在跨 warp 的 wid 混淆通道；连线侧即上述三条恒等 -/
theorem dcg1_hWid_event (s : BjSysState 32 32) (e : BjEvent 32) (w : BitVec 3) :
    let o := (bjSysStep s e).2
    (dcg1BjOutWid o w).1.2 = w ∧ (dcg1BjOutWid o w).2.2 = w := ⟨rfl, rfl⟩

/- ========================================================================= -/
/- 4. WB-A3：OpCol 串行化（同 warp 前序指令离开 collector 前后续被阻塞）        -/
/-    （scoreboard.scala:115-118 + pipe.scala:262-268；基于 I4Fix.lean）        -/
/- ========================================================================= -/

/-- 【WB-A3 命题】串行化谓词：同一时刻至多一个 collectorUnit 持有该 warp 的
    指令（2-CU 缩放系统的形式，I4Fix.lean 第 4 节） -/
def dcg1WbA3Serialized (s : I4fSysState) : Prop :=
  ¬(i4fCuBusy s.cu0 = true ∧ i4fCuBusy s.cu1 = true)

/-- 【WB-A3 核销主定理（原版门控）】任意输入序列后串行化保持——
    i4f_no_two_busy_orig 的命题化重述（原版记分板语义下同样成立：
    门控使"同拍 in+out"竞态不可自举，见 I4Fix.lean 头注 ★ 段） -/
theorem dcg1_wbA3_serialization (ins : List I4fSysIn) :
    dcg1WbA3Serialized (i4fSysRunG i4fSbOpColOrig i4fSysInit ins) :=
  i4f_no_two_busy_orig ins

/-- 【WB-A3 机制半】前序指令在 collector 内（占用位置位）当拍，后继指令被
    门控拦截：任何 CU 的 controlV.valid 均为 false（pipe.scala:223 的
    warp_ready 门控经 :161、scoreboard.scala:131,142 由占用位驱动） -/
theorem dcg1_wbA3_blocked_while_busy (s : I4fSysState) (i : I4fSysIn)
    (hocc : s.occ = 1#1) (j : Fin 2) :
    (i4fDemuxD s i).valid j = false := by
  unfold i4fDemuxD
  rw [i4f_demux_valid_def]
  have hg : (i.offer && (s.occ == 0#1)) = false := by
    rw [hocc]; cases i.offer <;> decide
  simp [hg]

/-- 【WB-A3 串行化（run 形式）】前序指令离开 collector 之前（任意轨迹后
    占用位=1），同 warp 的后继 offer 不可能进入任何 CU -/
theorem dcg1_wbA3_next_blocked (ins : List I4fSysIn) (i : I4fSysIn)
    (hocc : (i4fSysRunG i4fSbOpColOrig i4fSysInit ins).occ = 1#1) (j : Fin 2) :
    (i4fDemuxD (i4fSysRunG i4fSbOpColOrig i4fSysInit ins) i).valid j = false :=
  dcg1_wbA3_blocked_while_busy _ _ hocc j

/-- 【WB-A3 占用位语义（原版）】门控下原版本的占用位同样精确跟踪
    "该 warp 有指令在 collector 内"（经逐步等价 i4fSys_run_eq_orig 从修复版
    转移）——"前序离开"即占用位清除，与 CU 空闲同步 -/
theorem dcg1_wbA3_occ_tracks_busy_orig (ins : List I4fSysIn) :
    ((i4fSysRunG i4fSbOpColOrig i4fSysInit ins).occ == 1#1) =
      (i4fCuBusy (i4fSysRunG i4fSbOpColOrig i4fSysInit ins).cu0 ||
        i4fCuBusy (i4fSysRunG i4fSbOpColOrig i4fSysInit ins).cu1) := by
  rw [← i4fSys_run_eq_orig i4fSysInit ins i4fSys_init_inv]
  exact i4f_occ_tracks_busy ins

/- ========================================================================= -/
/- 5. H-ALLOC-PENDING：alloc ⟹ pending > 0（allocator.scala:187-188；          -/
/-    wg_buffer → allocator 取件链路，基于 WgBuffer.lean）                      -/
/- ========================================================================= -/

/-- 【H-ALLOC-PENDING 不变式】alloc 输出寄存器有效 ⟹ 其登记槽位仍在驻
    （供给与消费之间，valid 位只能被 accept 清除；WgbEnvOk 禁止清除在途项） -/
def dcg1AllocRegInv (s : WgbState) : Prop :=
  s.allocValidR = true → wgbBit s.valid s.allocAddrR = true

/-- 不变式奠基：复位态 allocValidR = false（虚真） -/
theorem dcg1_allocRegInv_init : dcg1AllocRegInv wgbInit := by
  intro h
  simp [wgbInit] at h

/-- 不变式单拍保持（环境契约 WgbEnvOk 下） -/
theorem dcg1_allocRegInv_step (s : WgbState) (i : WgbInputs)
    (henv : WgbEnvOk s i) (h0 : dcg1AllocRegInv s) :
    dcg1AllocRegInv (wgbStep s i) := by
  intro hv
  by_cases hact : wgbRdAct s i = true
  · -- 本拍新供给：登记槽 = wgbRdAddr s，其 valid 位置位、alloc 位未置位
    have hcand : wgbRdCand s ≠ 0#8 := (wgb_bne0 _).1 (wgb_and_true hact).1
    have hpick : wgbBit (s.valid &&& ~~~s.alloc) (wgbRdAddr s) = true :=
      wgb_rrPick_mem _ _ hcand
    have hbitV : wgbBit s.valid (wgbRdAddr s) = true := wgbBit_and_true _ _ _ hpick
    have hbitA : wgbBit s.alloc (wgbRdAddr s) = false := by
      -- 候选位 = valid ∧ ¬alloc 置位 ⟹ alloc 位为 0（bv_decide 位运算；无现成引理）
      unfold wgbBit at hpick ⊢
      generalize s.alloc = w at hpick ⊢
      generalize s.valid = v at hpick
      generalize wgbRdAddr s = a at hpick ⊢
      bv_decide
    have haddr : (wgbStep s i).allocAddrR = wgbRdAddr s := by
      show (if wgbRdAct s i = true then wgbRdAddr s else s.allocAddrR) = wgbRdAddr s
      rw [if_pos hact]
    rw [haddr]
    apply wgb_valid_persists s i _ hbitV
    intro hclr
    -- 供给槽 alloc=0，被清槽（若 clearAct）alloc=1（WgbEnvOk）→ 不同槽
    exact (wgbBit_ne_of hbitA (henv (wgbClearAct_resValid hclr)).2.1).symm
  · -- 本拍无新供给：寄存器保持有效 ⟹ allocReady=false 且原已有效
    have haddr : (wgbStep s i).allocAddrR = s.allocAddrR := by
      show (if wgbRdAct s i = true then wgbRdAddr s else s.allocAddrR) = s.allocAddrR
      rw [if_neg hact]
    have hvr : s.allocValidR = true := by
      by_cases hr : i.allocReady = true
      · have hf : (wgbStep s i).allocValidR = false := by
          show (if wgbRdAct s i = true then true
                else if i.allocReady = true then false else s.allocValidR) = false
          rw [if_neg hact, if_pos hr]
        rw [hf] at hv; exact absurd hv (by decide)
      · have he : (wgbStep s i).allocValidR = s.allocValidR := by
          show (if wgbRdAct s i = true then true
                else if i.allocReady = true then false else s.allocValidR) = s.allocValidR
          rw [if_neg hact, if_neg hr]
        rw [he] at hv; exact hv
    rw [haddr]
    apply wgb_valid_persists s i _ (h0 hvr)
    intro hclr
    -- WgbEnvOk 第三项：在途寄存器中的槽不会被本拍 accept 清除
    exact ((henv (wgbClearAct_resValid hclr)).2.2 hvr).symm

/-- 环境逐拍满足 WgbEnvOk 的轨迹（D6 环境契约的归纳承载） -/
inductive dcg1WgbTraceOk : WgbState → List WgbInputs → Prop where
  | nil (s : WgbState) : dcg1WgbTraceOk s []
  | cons (s : WgbState) (i : WgbInputs) (rest : List WgbInputs) :
      WgbEnvOk s i → dcg1WgbTraceOk (wgbStep s i) rest → dcg1WgbTraceOk s (i :: rest)

/-- 【H-ALLOC-PENDING 不变式 run 形式】环境契约逐拍成立的轨迹上不变式保持 -/
theorem dcg1_allocRegInv_run (s : WgbState) (ins : List WgbInputs)
    (ht : dcg1WgbTraceOk s ins) :
    dcg1AllocRegInv s → dcg1AllocRegInv (wgbRun s ins) := by
  induction ht with
  | nil s => exact id
  | cons s i rest henv _ ih =>
    intro h0
    show dcg1AllocRegInv (wgbRun (wgbStep s i) rest)
    exact ih (dcg1_allocRegInv_step _ _ henv h0)

/-- 从复位态出发的封闭形式 -/
theorem dcg1_allocRegInv_run_init (ins : List WgbInputs)
    (ht : dcg1WgbTraceOk wgbInit ins) : dcg1AllocRegInv (wgbRun wgbInit ins) :=
  dcg1_allocRegInv_run wgbInit ins ht dcg1_allocRegInv_init

/-- 【H-ALLOC-PENDING 核销：取件当拍】wg_buffer 向 allocator 供给生效
    （wgbRdAct）⟹ 缓冲非空：候选集非空 ⟹ RR 选中位在驻 ⟹ pending > 0 -/
theorem dcg1_hAllocPending_rdAct (s : WgbState) (i : WgbInputs) (h : wgbRdAct s i = true) :
    0 < wgbPending s := by
  have hcand : wgbRdCand s ≠ 0#8 := (wgb_bne0 _).1 (wgb_and_true h).1
  have hpick : wgbBit (s.valid &&& ~~~s.alloc) (wgbRdAddr s) = true :=
    wgb_rrPick_mem _ _ hcand
  exact wgbCount_pos_of_bit _ _ (wgbBit_and_true _ _ _ hpick)

/-- 【H-ALLOC-PENDING 核销：offer 半】alloc 输出寄存器有效（allocator 可消费的
    前提）⟹ pending > 0（不变式的直接读出） -/
theorem dcg1_hAllocPending_offer (s : WgbState) (h : dcg1AllocRegInv s)
    (hv : s.allocValidR = true) : 0 < wgbPending s :=
  wgbCount_pos_of_bit _ _ (h hv)

/-- 【H-ALLOC-PENDING 核销：fire 半】allocator 取件 fire
    （allocValidR && allocReady，wgbuffer_wg_new.fire）⟹ pending > 0 -/
theorem dcg1_hAllocPending_fire (s : WgbState) (i : WgbInputs) (h : dcg1AllocRegInv s)
    (hfire : (s.allocValidR && i.allocReady) = true) : 0 < wgbPending s :=
  dcg1_hAllocPending_offer s h (wgb_and_true hfire).1

/-- 【H-ALLOC-PENDING 核销：accept 半】分配结果接受（alloc_result.fire && accept，
    CtaScheduler 抽象模型的 .alloc 事件的具体化）当拍被回收槽仍在驻
    ⟹ pending > 0 -/
theorem dcg1_hAllocPending_accept (s : WgbState) (i : WgbInputs)
    (henv : WgbEnvOk s i) (h : wgbClearAct s i = true) : 0 < wgbPending s :=
  wgbCount_pos_of_bit _ _ (wgbClearAct_bit_valid henv h)

/- ========================================================================= -/
/- 6. WS-M7 的处置：warpRsp "always ready" 假设已被 I-6 证伪                    -/
/-    （warp_schedule.scala:55 注释级假设 vs CTA2warp 的 Queue(16)）            -/
/- ========================================================================= -/

/-- WS-M7 反例轨迹（从复位态可达）：8 个 CTAreq 占满 8 个 warp 槽
    （idxUsing=0xFF），接 c2wFillIns（8 个 endprg 入队 + 8 个复用派发 +
    8 个 endprg，CTArsp 全程不消费）——CTA2warp.lean T6 的完整可达版 -/
def dcg1WsM7Trace : List C2wInputs :=
  List.replicate 8 (c2wInReq 0x30#6) ++ c2wFillIns

/-- 反例终态：Queue(16) 填满 -/
def dcg1WsM7Full : C2wState := c2wRun c2wInit dcg1WsM7Trace

/-- 反例状态确实填满 FIFO（native_decide：多拍轨迹求值，AGENTS.md 惯例） -/
theorem dcg1_wsM7_fifo_full : dcg1WsM7Full.fifo.length = 16 := by native_decide

/-- 【WS-M7 证伪：反例】FIFO 满时 warpRsp.ready = false，且 valid 的
    warp_end 响应被静默丢弃（c2w6_rsp_dropped_iff_full 的实例化）——
    "always ready" 在该（复位可达）状态上不成立 -/
theorem dcg1_wsM7_counterexample :
    (c2wOut dcg1WsM7Full (c2wInRsp 0#3 false)).warpRspReady = false ∧
    c2wEnqFire dcg1WsM7Full (c2wInRsp 0#3 false) = false := by
  have hfull : dcg1WsM7Full.fifo.length = 16 := dcg1_wsM7_fifo_full
  have hb : dcg1WsM7Full.fifo.length ≤ 16 := by omega
  have hv : (c2wInRsp 0#3 false).warpRspValid = true := rfl
  have hdrop := (c2w6_rsp_dropped_iff_full dcg1WsM7Full (c2wInRsp 0#3 false) hb hv).mpr
    hfull
  refine ⟨?_, hdrop⟩
  native_decide

/-- 【WS-M7 证伪：假设的否定】"warpRsp 下游 always ready" 作为全称命题在
    模型上不成立（反例状态复位可达，非病态构造）——登记册 WS-M7 应改
    "已证伪"，后果链见 CTA2warp.lean Q2（响应丢弃 → idx_using 槽位泄漏 →
    派发死锁）与 bug 报告 I-6 -/
theorem dcg1_wsM7_assumption_false :
    ¬ (∀ (s : C2wState) (i : C2wInputs), s.fifo.length ≤ 16 → i.warpRspValid = true →
        (c2wOut s i).warpRspReady = true) := by
  intro h
  have hfull : dcg1WsM7Full.fifo.length = 16 := dcg1_wsM7_fifo_full
  have hb : dcg1WsM7Full.fifo.length ≤ 16 := by omega
  have hrdy := h dcg1WsM7Full (c2wInRsp 0#3 false) hb rfl
  rw [dcg1_wsM7_counterexample.1] at hrdy
  exact Bool.noConfusion hrdy

/- ========================================================================= -/
/- 7. IC-D8 拆分                                                                -/
/- ========================================================================= -/

/- ---- (a) coreReq 地址 num_fetch=2 对齐（ICache.scala:185）——可证部分 ---- -/

/-- 【IC-D8(a) 单拍】PCcontrol 的 pout 保持 8B（num_fetch=2 × 4B）对齐：
    前提仅 src3（icache miss 重放回填，warp_schedule.scala:195-198）的
    New_PC 对齐——该地址即上次请求地址，归纳闭环（dcg1_pcc_run_aligned） -/
theorem dcg1_pcc_step_aligned (s : PccState) (i : PccIn)
    (hs : s.pout &&& 7#32 = 0#32)
    (h3 : i.replay = false → i.src = 3#2 → i.newPC &&& 7#32 = 0#32) :
    (pccStep s i).pout &&& 7#32 = 0#32 := by
  by_cases hr : i.replay = true
  · rw [pccT2_replay s i hr]; exact hs
  · have hr' : i.replay = false := by
      cases h : i.replay with
      | false => rfl
      | true => exact absurd h hr
    by_cases h2 : i.src = 2#2
    · -- 顺序推进：pout += 8（:43-45），对齐保持
      rw [pccT2_seq s i hr' h2]
      show (s.pout + 8#32) &&& 7#32 = 0#32
      generalize s.pout = p at hs ⊢
      bv_decide
    · by_cases h1 : i.src = 1#2
      · -- 分支/初始化：pout ← align(New_PC)，align 本身 8B 对齐（pccT1a）
        rw [pccT2_src1 s i hr' h1]
        show (pccAlign i.newPC).1 &&& 7#32 = 0#32
        exact (pccT1a_align i.newPC).1
      · by_cases h3c : i.src = 3#2
        · rw [pccT2_src3 s i hr' h3c]
          show i.newPC &&& 7#32 = 0#32
          exact h3 hr' h3c
        · rw [pccT2_hold s i hr' h2 h1 h3c]; exact hs

/-- 【IC-D8(a) run 形式】从对齐状态（复位初值 pout=0 满足）出发、
    src3 回填地址全程对齐，则任意轨迹后 pout 恒 8B 对齐 -/
theorem dcg1_pcc_run_aligned (s : PccState) (ins : List PccIn)
    (hs : s.pout &&& 7#32 = 0#32)
    (henv : ∀ j ∈ ins, j.replay = false → j.src = 3#2 → j.newPC &&& 7#32 = 0#32) :
    (pccRun s ins).pout &&& 7#32 = 0#32 := by
  induction ins generalizing s with
  | nil => exact hs
  | cons j js ih =>
    show (pccRun (pccStep s j) js).pout &&& 7#32 = 0#32
    exact ih _ (dcg1_pcc_step_aligned s j hs (henv j List.mem_cons_self))
      (fun k hk => henv k (List.mem_cons_of_mem j hk))

/-- 【IC-D8(a) 对接 ICache.scala:185】coreReq 地址 8B 对齐 ⟹ :185 断言条件
    成立：blockOffset（addr 的 [6:2]）的低 log2Ceil(num_fetch)=1 位全 0。
    coreReq 地址即 PCcontrol 的 pout（pipe.scala:157 pc_req 直通 +
    warp_schedule.scala:96-100 当拍组合读出 PC_next） -/
theorem dcg1_icD8_align_assert (a : BitVec 32) (h : a &&& 7#32 = 0#32) :
    icGetBlockOffset a &&& 1#5 = 0#5 := by
  unfold icGetBlockOffset
  bv_decide

-- 数值佐证：对齐地址的 blockOffset 低位为 0；非对齐（bit2=1）时为 1
example : icGetBlockOffset 0x100#32 &&& 1#5 = 0#5 := by decide
example : icGetBlockOffset 0x104#32 &&& 1#5 = 1#5 := by decide

/- ---- (b) memRsp 环境纪律（ICacheMSHR.scala:163）——不可内证，保持 axiomatic -/

/-- 【IC-D8(b) 环境纪律陈述】memRsp 只回"已分配且已发访存请求"的 entry：
    响应 valid 时目标 entry 已分配（icEntryValid）且已向内存发出请求
    （hasSend）。
    不可内证的理由（补强）：响应来自片外内存子系统（L2/DRAM/互联不在
    本工程建模范围）；响应的 entry 索引（d_source，icRspEntryIdx）由对端
    回填，ICache 侧没有任何机制约束其指向已分配/已发 entry——
    ICacheMSHR.scala:163 的 assert 正是源码作者对此环境纪律的仿真期检查。
    消费形态：icMshr_rsp_fire 的 hvalid 前提（Contracts.lean 的
    specXrefIcMshrRspFire）。 -/
def dcg1IcRspEnvOk (s : IcMshrState) (i : IcMshrIn) : Prop :=
  i.rspValid = true → icEntryValid s i.rspIdx = true ∧ s.hasSend i.rspIdx = true

/-- 【IC-D8(b) 消费闭环】环境纪律下 MSHR 响应处理契约成立：rspOut 当拍
    有效、blockAddr 正确、目标 subentry 被清（icMshr_rsp_fire 的 hvalid
    前提由环境纪律供给） -/
theorem dcg1_icD8_rsp_consumes_env (s : IcMshrState) (i : IcMshrIn)
    (hrv : i.rspValid = true) (hb : s.busy = false) (henv : dcg1IcRspEnvOk s i) :
    icRspOutValid s i = true ∧ icRspOutBA s i = s.blockAddr i.rspIdx ∧
      (icMshrStep s i).subValid i.rspIdx (icNext2Cancel s i) = false :=
  icMshr_rsp_fire (s := s) (i := i) hrv hb (henv hrv).1

/- ========================================================================= -/
/- 8. 公理审计                                                                  -/
/- ========================================================================= -/

#print axioms dcg1_hIb2i_ready_closed
#print axioms dcg1_hDelay_gate_closed
#print axioms dcg1_hWid_event
#print axioms dcg1_wbA3_serialization
#print axioms dcg1_wbA3_next_blocked
#print axioms dcg1_allocRegInv_run
#print axioms dcg1_hAllocPending_fire
#print axioms dcg1_wsM7_counterexample
#print axioms dcg1_wsM7_assumption_false
#print axioms dcg1_pcc_run_aligned
#print axioms dcg1_icD8_align_assert
#print axioms dcg1_icD8_rsp_consumes_env

end Ventus.Spec
