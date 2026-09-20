/- ========================================================================= -/
/-                     Spec/FlushOrdering.lean                                -/
/-  跨模块风险链核查：WG 完成上报 host（host_wg_done）是否排序在 flushDCache  -/
/-  完成之后。结论：**否**——上报链与 flush 链无交叉（结构性，§4），上报严格   -/
/-  先于 flush 完成（native_decide witness，§5），修复方向为上报门控（§6）。  -/
/-  本文件是 EndprgInflight.lean 头注"附带观察"（I-46 附）的展开核销。        -/
/-                                                                           -/
/-  ======================== 机制链（Chisel 源码行号证据） =================== -/
/-  链 A（完成上报；全链无任何 flush 输入）：                                 -/
/-    warp_schedule.scala:47    warp_end = warp_control.fire & simt_stack_op； -/
/-    warp_schedule.scala:55    warpRsp.valid := warp_end（当拍发出，不等任何   -/
/-      访存状态）；                                                           -/
/-    CTA2warp.scala:63,73      warpRsp.fire 清 idx_using 并入 CTArsp_fifo；   -/
/-    CTA2warp.scala:76-78      CTArsp = FIFO 出队（tag = data(队首 wid)）；    -/
/-    GPGPU_top.scala:175       sm_wrapper.CTArsp <> cta.warp2CTA；            -/
/-    GPGPU_top.scala:111-113   warp2CTA 直通 cu_wf_done（valid/bits/ready     -/
/-      纯连线，无寄存、无门控）；                                             -/
/-    cu_interface.scala:156    arb ready = (fsm == GET_WF)——FIFO 非空即被      -/
/-      接收；:178-186 gather 计数；:179 wf_gather_finish；                    -/
/-    cu_interface.scala:221    host_wg_done.valid = UPDATE && finish；        -/
/-    cta_scheduler.scala:131   host_wg_done 直通顶层（cta_scheduler 全文无     -/
/-      flush 相关逻辑）；GPGPU_top.scala:84-86 → CTA2host → host。            -/
/-  链 B（flushDCache；单向发起、无完成信号）：                                -/
/-    warp_schedule.scala:158-163  warp_endprg_cnt（寄存器）：warpReq.fire 置   -/
/-      位、warpRsp.fire 清位；:159 warp_wg_valid 在派发时置位；               -/
/-    warp_schedule.scala:164-167  mask_0(g) = cnt(g) 空 && valid(g)；          -/
/-      need_flush = mask_0.orR——读**寄存器旧值**，故 flushDCache.valid 最早    -/
/-      在最后一个 warpRsp.fire 的**下一拍**才拉起（发起即晚一拍）；           -/
/-    warp_schedule.scala:169-170  簿记清除条件 = mask_0(entry) &&             -/
/-      flushDCache.ready——**发出即完事**，DCache 实际刷写不在任何簿记内；     -/
/-    pipe.scala:169-171          flushDCache <> lsu.io.flush_dcache；          -/
/-    LSU.scala:137               flush_dcache.ready = (state == s_idle)；     -/
/-    LSU.scala:294               fire → s_dcache；:371-374 接受拍 reg_save     -/
/-      清零、mem_cmd=1；:262-265 is_flush → to_dcache opcode=3, param=0；     -/
/-    DCache.scala:73-75          opcode=3,param=0 → isInvalidate（注意：实际   -/
/-      是 **invalidate**，LSU.scala:262 注释 "invalidate L1D instead of        -/
/-      flush"）；                                                             -/
/-    DCache.scala:488-503        脏行逐行 PutPartialData 写回 L2               -/
/-      （InvOrFluMemReq，单 memReq 端口，每拍至多一行）；                     -/
/-    DCache.scala:464-466        invalidate 完成条件 = !hasDirty &&           -/
/-      MSHR empty && WSHR empty && !flushstall（之后 coreRsp，:484-486）；    -/
/-    DCache.scala:413,516        无脏行时也要等 L2 hintAck（d_opcode=2）。     -/
/-  **关键事实：全硬件不存在"flush 完成"信号**——DCache 对 invalidate 的       -/
/-  coreRsp 回到 LSU 后无人消费为"完成"事件（LSU.scala:405-411 只清            -/
/-  is_flush），不回 warp_scheduler、不进 CTA 链。host_wg_done 不可能等待一    -/
/-  个不存在的事件。                                                           -/
/-                                                                           -/
/-  ======================== 结论 =========================================== -/
/-  (1) 结构性：§4 floRun_report_indep——上报链（c2w+cuif）的任意长演化与       -/
/-      flush 链状态（相位/脏行数/完成标志）完全无关；                         -/
/-  (2) witness：§5 floW 系列——上报拍（拍 3）严格先于 flush 完成拍（≥ 拍 5，   -/
/-      零脏行、零 L2 延迟的最有利抽象；每多一行脏行再晚 ≥1 拍）；             -/
/-  (3) 修复方向：§6 门控机器——host_wg_done.ready &&= flush_done 后，          -/
/-      上报必不早于 flush 完成（flo_guarded_report_safe + 轨迹复核）。        -/
/-  危害与可容忍性分析：见文件尾注。                                           -/
/-                                                                           -/
/-  ======================== 建模决策 ======================================= -/
/-  F1. 复用既有逐拍模型：wsStep/wsOut（Schedule/WarpScheduler.lean，          -/
/-      warp_schedule.scala 逐行翻译）、c2wStep/c2wOut（CTA/CTA2warp.lean）、  -/
/-      cuifStep（CTA/CuInterface.lean）。本文件只做连线装配                   -/
/-      （floWsIn/floC2wIn/floCuifIn，对应 pipe.scala:166-171、                -/
/-      GPGPU_top.scala:111-113,175 的连线）与 flush 链抽象，不重建模块。      -/
/-  F2. flush 链抽象 FloFlush{phase,dirty,done}（处处取对 flush 侧最有利，     -/
/-      使"上报更早"的结论更保守）：phase 0→1 = LSU 接受（fire 当拍，          -/
/-      LSU.scala:137,294）；1→2 = LSU s_dcache 发出 DCache invalidate 请求    -/
/-      （LSU.scala:322,405-411，一拍，忽略 to_dcache 反压）；phase=2 每拍     -/
/-      至多清 1 行脏行（DCache.scala:488-503 单 memReq 端口逐行写回）；       -/
/-      dirty=0 的 phase=2 拍后 done（DCache.scala:464-466 完成条件；L2        -/
/-      hintAck 延迟 :413,:516 按 0 拍计）。                                   -/
/-  F3. dirty 在受理拍由环境输入 dcDirty 载入（= 当拍 L1D 脏行数，属 DCache    -/
/-      内部状态，不在本组合机内建模；主 witness 取 0——最小可能值）。          -/
/-  F4. 上报链环境取最快配置：host 恒 ready、rt_dealloc 恒 ready、单 CU、      -/
/-      CTArsp FIFO 空、cuif 在 GET_WF 空转——上报越早越凸显先于 flush。       -/
/-  F5. cuif 的 WG 在驻状态由 floCuifLoaded 经合法轨迹（enq→loadNew→wf 发      -/
/-      出）构造，非手构非法状态；wg_slot=1、num_wf=1、wf_tag=0x08。           -/
/- ========================================================================= -/

import Ventus.Schedule.WarpScheduler
import Ventus.CTA.CTA2warp
import Ventus.CTA.CuInterface

namespace Ventus.Spec

open Ventus.Base Ventus.Schedule Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. flush 链抽象（F2）                                                      -/
/- ========================================================================= -/

/-- flush 链抽象状态。
    phase：0 = LSU s_idle（可接受，LSU.scala:137）；1 = 已接受（LSU 在
    s_dcache，:294）；2 = 已进入 DCache 处理（DCache.scala:464-503）。
    dirty：剩余待写回脏行数（受理拍采样，F3）。done：invalidate 完成
    （:464-466）。硬件中无此信号（见文件头"关键事实"），此处为分析而建。 -/
structure FloFlush where
  phase : BitVec 2
  dirty : BitVec 10
  done : Bool
deriving DecidableEq

def floFlushInit : FloFlush := ⟨0#2, 0#10, false⟩

/-- flush 链单拍（F2 的逐步语义；fire = flushDCache.valid && LSU s_idle，
    newDirty = 受理拍 L1D 脏行数） -/
def floFlushStep (f : FloFlush) (fire : Bool) (newDirty : BitVec 10) : FloFlush :=
  if f.phase == 0#2 then
    if fire then { phase := 1#2, dirty := newDirty, done := false } else f
  else if f.phase == 1#2 then
    { f with phase := 2#2 }
  else
    { f with
        dirty := if f.dirty == 0#10 then f.dirty else f.dirty - 1#10
        done := f.done || (f.dirty == 0#10) }

/-- FLO-F1 flush 完成条件：done 置位当且仅当此前已完成，或已在 DCache 处理
    相位（phase=2）且脏行清零（DCache.scala:464-466）。接受拍（fire）本身
    永远不可能当拍完成。 -/
theorem flo_flush_done_src (f : FloFlush) (fire : Bool) (d : BitVec 10) :
    (floFlushStep f fire d).done = true →
      f.done = true ∨
      ((f.phase == 0#2) = false ∧ (f.phase == 1#2) = false ∧
        (f.dirty == 0#10) = true) := by
  intro h
  unfold floFlushStep at h
  by_cases h0 : (f.phase == 0#2) = true
  · rw [if_pos h0] at h
    by_cases hf : fire = true
    · rw [if_pos hf] at h; simp at h
    · rw [if_neg hf] at h; exact Or.inl h
  · rw [if_neg h0] at h
    by_cases h1 : (f.phase == 1#2) = true
    · rw [if_pos h1] at h; exact Or.inl h
    · rw [if_neg h1] at h
      have h' : (f.done || (f.dirty == 0#10)) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with hd | hd
      · exact Or.inl hd
      · exact Or.inr ⟨(Bool.not_eq_true _).mp h0, (Bool.not_eq_true _).mp h1, hd⟩

/-- FLO-F2 flush 延迟下界：从空闲干净态出发，两拍之内不可能完成
    （0 → 1 接受 → 2 进 DCache，逐级至少一拍，done 最早第三拍出现） -/
theorem flo_flush_two_steps (d0 d1 : BitVec 10) (f0 f1 : Bool) :
    (floFlushStep (floFlushStep ⟨0#2, 0#10, false⟩ f0 d0) f1 d1).done = false := by
  cases f0 <;> cases f1 <;> rfl

/- ========================================================================= -/
/- 2. 组合机器：上报链（ws+c2w+cuif 忠实模型拼装）+ flush 链抽象              -/
/- ========================================================================= -/

/-- 组合机器状态 -/
structure FloState where
  ws : WsState        -- warp_scheduler（endprg 簿记 + flushDCache 发起）
  c2w : C2wState      -- CTA2warp（CTArsp_fifo）
  cuif : CuifState    -- cu_interface（gather + host_wg_done）
  flu : FloFlush      -- flush 链抽象（F2）

/-- 每拍环境输入 -/
structure FloOp where
  disValid : Bool := false       -- CTA 派发（CTA2warp.io.CTAreq.valid）
  disTag : BitVec 6 := 0         -- wf_tag = {wg_slot, wf_id}
  disCnt : BitVec 4 := 0         -- dispatch2cu_wg_wf_count
  endValid : Bool := false       -- warp_control.fire & simt_stack_op（endprg）
  endWid : BitVec 3 := 0         -- 结束 warp 的 wid
  hostRdy : Bool := false        -- host_wg_done.ready（GPGPU_top.scala:86）
  dcDirty : BitVec 10 := 0       -- flush 受理拍 L1D 脏行数（F3）

/-- c2w 输入装配：ctaRspReady = cu_interface arb ready（cu_interface.scala:156
    经 GPGPU_top.scala:113 反传）；wgIdLookup = 结束 warp（warp_schedule.scala:103
    的 wg_id_lookup := warp_end_id，用于查 wg_id_tag，CTA2warp.scala:51,58） -/
def floC2wIn (s : FloState) (op : FloOp) : C2wInputs :=
  { c2wInNop with
    ctaReqValid := op.disValid
    ctaReqTag := op.disTag
    warpRspValid := op.endValid
    warpRspWid := op.endWid
    wgIdLookup := op.endWid
    ctaRspReady := decide (s.cuif.gfsm = .getWf) }

/-- ws 输入装配：warpReq 来自 c2w 分配输出（CTA2warp.scala:67-69 →
    warp_schedule 的 warpReq）；wg_id_tag 来自 c2w 的 data 查表（真实数据通路）；
    warpRspReady = c2w FIFO 非满（CTA2warp.scala:73）；
    flushDCacheReady = LSU s_idle（LSU.scala:137，经 pipe.scala:171 反传） -/
def floWsIn (s : FloState) (op : FloOp) (c2wO : C2wOutputs) : WsInputs :=
  { wsInNop with
    warpReqFire := c2wO.warpReqValid
    reqWid := c2wO.warpReqWid
    newWgId := cuifTagSlot op.disTag
    newWfCount := op.disCnt
    warpControlFire := op.endValid
    simtStackOp := op.endValid
    wcWid := op.endWid
    wgIdTag := c2wO.wgIdTag
    warpRspReady := c2wO.warpRspReady
    flushDCacheReady := s.flu.phase == 0#2 }

/-- cuif 输入装配：done = CTArsp 直通（GPGPU_top.scala:111-113）；F4：
    rt_dealloc 恒 ready -/
def floCuifIn (c2wO : C2wOutputs) (op : FloOp) : CuifInputs :=
  { doneV0 := c2wO.ctaRspValid
    doneTag0 := c2wO.ctaRspTag
    rtRdy := true
    hostRdy := op.hostRdy : CuifInputs }

/-- 单拍转移。flushFire = flushDCache.valid && LSU s_idle（pipe.scala:169-171 +
    LSU.scala:137,294 的握手） -/
def floStep (s : FloState) (op : FloOp) : FloState :=
  let c2wI := floC2wIn s op
  let c2wO := c2wOut s.c2w c2wI
  let wsI := floWsIn s op c2wO
  let flushFire := (wsOut s.ws wsI).flushDCacheValid && (s.flu.phase == 0#2)
  { ws := wsStep s.ws wsI
    c2w := c2wStep s.c2w c2wI
    cuif := cuifStep s.cuif (floCuifIn c2wO op)
    flu := floFlushStep s.flu flushFire op.dcDirty }

/-- 多拍运行 -/
def floRun (s : FloState) (ops : List FloOp) : FloState := ops.foldl floStep s

/-- 当拍 host_wg_done.fire（cu_interface.scala:221 && host ready） -/
def floReportFire (s : FloState) (op : FloOp) : Bool :=
  cuifHostFire s.cuif (floCuifIn (c2wOut s.c2w (floC2wIn s op)) op)

/- ========================================================================= -/
/- 3. 结构性事实：上报链不读 flush 链状态                                     -/
/- ========================================================================= -/

/-- c2w 单拍只读 (s.c2w, s.cuif.gfsm, op)：与 ws/flu 无关 -/
theorem floStep_c2w_of_eq (s t : FloState) (op : FloOp)
    (hc : s.c2w = t.c2w) (hu : s.cuif = t.cuif) :
    (floStep s op).c2w = (floStep t op).c2w := by
  have e1 : floC2wIn s op = floC2wIn t op := by
    unfold floC2wIn
    rw [hu]
  show c2wStep s.c2w (floC2wIn s op) = c2wStep t.c2w (floC2wIn t op)
  rw [hc, e1]

/-- cuif 单拍只读 (s.cuif, s.c2w 经 CTArsp, op)：与 ws/flu 无关 -/
theorem floStep_cuif_of_eq (s t : FloState) (op : FloOp)
    (hc : s.c2w = t.c2w) (hu : s.cuif = t.cuif) :
    (floStep s op).cuif = (floStep t op).cuif := by
  have e1 : floC2wIn s op = floC2wIn t op := by
    unfold floC2wIn
    rw [hu]
  show cuifStep s.cuif (floCuifIn (c2wOut s.c2w (floC2wIn s op)) op) =
       cuifStep t.cuif (floCuifIn (c2wOut t.c2w (floC2wIn t op)) op)
  rw [hc, e1, hu]

/-- **FLO-S1 结构性主定理**：任意长轨迹下，上报链（CTA2warp FIFO +
    cu_interface gather/host 上报）的演化只依赖 (c2w, cuif) 与输入序列——
    与 warp_scheduler 的 flush 簿记、flush 链相位/脏行/完成标志完全无关。
    硬件对应：cu_interface.scala 与 cta_scheduler.scala 的端口表中没有任何
    flush 相关信号（全文件 grep 无 flush）。 -/
theorem floRun_report_indep (ops : List FloOp) (s t : FloState)
    (hc : s.c2w = t.c2w) (hu : s.cuif = t.cuif) :
    (floRun s ops).c2w = (floRun t ops).c2w ∧
    (floRun s ops).cuif = (floRun t ops).cuif := by
  induction ops generalizing s t with
  | nil => exact ⟨hc, hu⟩
  | cons op ops ih =>
      exact ih (floStep s op) (floStep t op)
        (floStep_c2w_of_eq s t op hc hu) (floStep_cuif_of_eq s t op hc hu)

/-- 推论：flush 链状态换成任意值，上报链轨迹逐字不变 -/
theorem flo_report_chain_no_flush_input (ops : List FloOp) (s : FloState) (f : FloFlush) :
    (floRun s ops).c2w = (floRun { s with flu := f } ops).c2w ∧
    (floRun s ops).cuif = (floRun { s with flu := f } ops).cuif :=
  floRun_report_indep ops s { s with flu := f } rfl rfl

/-- dcDirty（flush 受理拍采样的脏行数）不影响上报链单拍 -/
theorem floStep_c2w_dcDirty (s : FloState) (op : FloOp) (d : BitVec 10) :
    (floStep s op).c2w = (floStep s { op with dcDirty := d }).c2w := rfl

theorem floStep_cuif_dcDirty (s : FloState) (op : FloOp) (d : BitVec 10) :
    (floStep s op).cuif = (floStep s { op with dcDirty := d }).cuif := rfl

/- ========================================================================= -/
/- 4. witness：上报先于 flush 完成                                             -/
/- ========================================================================= -/

/-- witness 的 WG：cu0、wg_slot 1、num_wf 1、wg_id 0xCAFE -/
def floWgA : CuifWg :=
  ⟨0#1, 1#3, 1#4, 0xCAFE#32, 0#12, 0#11, 0#18, 0#11, 0#10, 0#17, 0#32,
    false, false, false⟩

/-- cuif 合法在驻态（F5）：enq → loadNew（live 置位、info 写入）→ wf 发出 -/
def floCuifLoaded : CuifState :=
  cuifRun cuifInit [
    { enqValid := true, enqWg := floWgA : CuifInputs },
    ({} : CuifInputs),
    { cuRdy0 := true : CuifInputs }]

/-- 在驻态健全性：slot(cu0,1) live、numWf=1、cnt=0、FSM 在 GET_WF -/
theorem floCuifLoaded_ok :
    floCuifLoaded.liveMem (cuifGaddr 0#1 1#3) = true ∧
    (floCuifLoaded.infoMem (cuifGaddr 0#1 1#3)).numWf = 1#4 ∧
    floCuifLoaded.cntMem (cuifGaddr 0#1 1#3) = 0#4 ∧
    floCuifLoaded.gfsm = .getWf := by native_decide

/-- 拍 0：派发（tag=0x08 = {slot 1, wf 0}，wf_count=1） -/
def floOpDispatch : FloOp := { disValid := true, disTag := 0x08#6, disCnt := 1#4 }
/-- 拍 1：该 wg 唯一 warp endprg -/
def floOpEndprg : FloOp := { endValid := true, endWid := 0#3, hostRdy := true }
/-- 拍 2：flush 受理 + CTArsp 出队 + cuif 仲裁（dcDirty 由参数给出） -/
def floOpFlushFire (d : BitVec 10) : FloOp := { hostRdy := true, dcDirty := d }
/-- 拍 3：host 消费上报 -/
def floOpHost : FloOp := { hostRdy := true }
/-- 空拍 -/
def floOpNop : FloOp := {}

def floW0 : FloState := ⟨wsInit, c2wInit, floCuifLoaded, floFlushInit⟩
def floW1 : FloState := floStep floW0 floOpDispatch          -- 拍 0：派发
def floW2 : FloState := floStep floW1 floOpEndprg            -- 拍 1：endprg
def floW3 : FloState := floStep floW2 (floOpFlushFire 0#10)  -- 拍 2：flush 受理
def floW4 : FloState := floStep floW3 floOpHost              -- 拍 3：上报 fire
def floW5 : FloState := floStep floW4 floOpNop               -- 拍 4：进 DCache

/-- 拍 0 后：ws 簿记建立（cnt(1)={warp0}、valid(1)）、warp0 active、c2w 分得
    slot 0 且 tag 落表 -/
theorem floW1_dispatch :
    floW1.ws.endprgCnt (wsFin 1#3) = 1#8 ∧
    floW1.ws.wgValid (wsFin 1#3) = true ∧
    (floW1.ws.warpActive &&& 1#8) = 1#8 ∧
    floW1.c2w.idxUsing = 1#8 ∧
    floW1.c2w.data (c2wFin 0#3) = 0x08#6 := by native_decide

/-- **发起时机**：endprg 当拍（拍 1）flushDCache.valid 仍为 false——
    need_flush 读寄存器旧值（warp_schedule.scala:164-167），最早下一拍拉起 -/
theorem floW_flush_starts_after_endprg :
    (wsOut floW1.ws wsInNop).flushDCacheValid = false ∧
    (wsOut floW2.ws wsInNop).flushDCacheValid = true := by native_decide

/-- 拍 1 后：cnt(1) 清零、warp0 active 清除、响应已入 CTArsp_fifo -/
theorem floW2_endprg :
    floW2.ws.endprgCnt (wsFin 1#3) = 0#8 ∧
    floW2.ws.warpActive = 0#8 ∧
    floW2.c2w.fifo = [0#3] := by native_decide

/-- 拍 2 后：flush 被 LSU 接受（phase=1，尚未进 DCache，done=false）、ws 簿记
    清除（valid(1)：warp_schedule.scala:169-170 发出即完事）、CTArsp 出队、
    cuif 进入 UPDATE 且采样到正确的 wg 信息 -/
theorem floW3_flush_accepted :
    floW3.flu.phase = 1#2 ∧ floW3.flu.done = false ∧
    floW3.ws.wgValid (wsFin 1#3) = false ∧
    floW3.c2w.fifo = [] ∧
    floW3.cuif.gfsm = .update ∧ floW3.cuif.slotReg = 1#3 ∧
    floW3.cuif.infoRd.numWf = 1#4 ∧ floW3.cuif.infoRd.wgId = 0xCAFE#32 := by
  native_decide

/-- **witness 主定理**：零脏行、零 L2 延迟的最有利情形下——
    拍 3 host_wg_done.fire（上报发出），同拍 flush 才刚被 LSU 接受
    （phase=1，连 DCache 请求都还没发出）；拍 4 done 仍为 false；
    拍 5 flush 才完成。上报严格先于 flush 完成 ≥ 2 拍。 -/
theorem floW_report_precedes_flush :
    floReportFire floW3 floOpHost = true ∧
    floW3.flu.done = false ∧ floW3.flu.phase = 1#2 ∧
    floW4.flu.done = false ∧
    (floStep floW4 floOpNop).flu.done = true := by native_decide

/-- 上报拍不依赖脏行数：dcDirty 取任意值，拍 3 的上报逐字不变
    （结构性独立于 flush 链，§3 的轨迹级表现；rfl = 定义展开后 dcDirty
    只流入未被观测的 flu 字段） -/
theorem floW_report_any_dirty (d : BitVec 10) :
    floReportFire (floStep floW2 (floOpFlushFire d)) floOpHost = true := by
  have h : floReportFire (floStep floW2 (floOpFlushFire d)) floOpHost =
      floReportFire floW3 floOpHost := rfl
  rw [h]
  exact floW_report_precedes_flush.1

/-- 有脏行时差距更大：受理 1 行脏行，拍 5（最优情形下的完成拍）flush 仍未
    完成——每行脏行至少再晚 1 拍（DCache.scala:488-503 单端口逐行写回），
    实际还要加上 512 组 × 2 路的扫描与 L2 往返 -/
theorem floW_dirty_delays_flush :
    let s3 := floStep floW2 (floOpFlushFire 1#10)
    s3.flu.dirty = 1#10 ∧ s3.flu.done = false ∧
    (floStep (floStep s3 floOpHost) floOpNop).flu.done = false := by native_decide

/- ========================================================================= -/
/- 5. 修复方向：host_wg_done 门控到 flush 完成                                 -/
/-    （硬件对应：cu_interface.scala:221 的 host_wg_done.valid 增加             -/
/-    "本 CU flush 已完成"条件；完成点取 DCache invCOreRsp_st1，               -/
/-    DCache.scala:484-486 是现成信号）                                       -/
/- ========================================================================= -/

/-- 门控版 cuif 输入：host_wg_done.ready &&= flush_done -/
def floCuifInG (s : FloState) (c2wO : C2wOutputs) (op : FloOp) : CuifInputs :=
  { floCuifIn c2wO op with hostRdy := op.hostRdy && s.flu.done }

/-- 门控版单拍 -/
def floStepG (s : FloState) (op : FloOp) : FloState :=
  let c2wI := floC2wIn s op
  let c2wO := c2wOut s.c2w c2wI
  let wsI := floWsIn s op c2wO
  let flushFire := (wsOut s.ws wsI).flushDCacheValid && (s.flu.phase == 0#2)
  { ws := wsStep s.ws wsI
    c2w := c2wStep s.c2w c2wI
    cuif := cuifStep s.cuif (floCuifInG s c2wO op)
    flu := floFlushStep s.flu flushFire op.dcDirty }

/-- 门控版上报观测 -/
def floReportFireG (s : FloState) (op : FloOp) : Bool :=
  cuifHostFire s.cuif (floCuifInG s (c2wOut s.c2w (floC2wIn s op)) op)

/-- **防护定理**：门控机器里，上报 fire 蕴含 flush 已完成 -/
theorem flo_guarded_report_safe (s : FloState) (op : FloOp) :
    floReportFireG s op = true → s.flu.done = true := by
  intro h
  by_cases hd : s.flu.done = true
  · exact hd
  · exfalso
    have hdf : s.flu.done = false := (Bool.not_eq_true _).mp hd
    have h0 : floReportFireG s op = false := by
      unfold floReportFireG floCuifInG cuifHostFire
      simp [hdf]
    rw [h0] at h
    exact absurd h (by decide)

/-- 门控机器轨迹（同一 witness 输入序列；host 恒 ready） -/
def floWG3 : FloState := floStepG floW2 (floOpFlushFire 0#10)
def floWG4 : FloState := floStepG floWG3 floOpHost
def floWG5 : FloState := floStepG floWG4 floOpHost
def floWG6 : FloState := floStepG floWG5 floOpHost

/-- 门控轨迹复核：拍 3、拍 4 上报被阻断（done=false），拍 5 flush 完成后
    上报才放行——防护在轨迹上成立，且只晚 2 拍（最有利情形） -/
theorem floWG_blocked_then_safe :
    floReportFireG floWG3 floOpHost = false ∧
    floReportFireG floWG4 floOpHost = false ∧
    floWG5.flu.done = true ∧
    floReportFireG floWG5 floOpHost = true := by native_decide

/- ========================================================================= -/
/- 尾注：危害与可容忍性分析（随 witness 归档）                                 -/
/-                                                                           -/
/- 危害：host 收到 host_wg_done（GPGPU_top.scala:84-86 → CTA2host）后若立即   -/
/- 读该 wg 的结果缓冲区（标准 OpenCL 流程：kernel/wg 完成事件 → 读回           -/
/- 结果），而读路径不经 GPU L1D（host 侧 AXI/DMA 直读 DDR），则读到 flush     -/
/- 完成前的陈旧数据。触发条件：(a) wg 有全局写且脏行残留 L1D（结果写是常态，  -/
/- 非边角）；(b) host "完成即读"。上报比 flush 完成早 ≥2 拍（零脏行最优）+    -/
/- 每脏行 ≥1 拍（实际为 512×2 组扫描 × L2 往返，数十至数百拍量级）——          -/
/- 系统性竞争，非时序边角。                                                   -/
/- 可容忍性：(1) flush 实为 invalidate（LSU.scala:262 注释、DCache.scala:      -/
/- 73-75），脏行**先写回 L2 再失效**（DCache.scala:488-503），故是排序问题    -/
/- 而非丢数据问题——数据最终一致；(2) 若 host 读路径与 GPU 共享 L2 且 L2 是    -/
/- coherence point，则窗口缩小为"L1D→L2 写回在途"，但上报仍不等待写回完成，   -/
/- 竞争依旧存在；(3) 驱动层若在读结果前插入显式 flush/延迟可掩盖，但代码与    -/
/- 文档中未见此契约；(4) 与 I-5（mask_0 非 one-hot 时 flush 卡死）、I-6       -/
/- （warpRsp 丢失则 flush 永不发出）叠加时，flush 可能**永远不发生**，危害    -/
/- 从"读到陈旧"升级为"永远读到陈旧"。                                         -/
/- 修复建议（最小改动）：host_wg_done.valid 门控"本 CU flush 已完成"——        -/
/- 完成点取 DCache 的 invCOreRsp_st1（DCache.scala:484-486，现成信号），       -/
/- 经 LSU 回传至 cu_interface（cu_interface.scala:221）。注意 rt_dealloc       -/
/- （:204）与 host_wg_done 同拍配对，但资源回收与全局内存可见性无关，可只     -/
/- 门控上报一路，避免拖慢 warp 槽周转。                                       -/
/- ========================================================================= -/

/- 公理审计（native_decide 定理带 Lean.ofReduceBool；无 bv_decide，无 sorry） -/
#print axioms flo_flush_done_src
#print axioms flo_flush_two_steps
#print axioms floRun_report_indep
#print axioms flo_report_chain_no_flush_input
#print axioms floW_report_precedes_flush
#print axioms floW_report_any_dirty
#print axioms floW_dirty_delays_flush
#print axioms flo_guarded_report_safe
#print axioms floWG_blocked_then_safe

end Ventus.Spec
