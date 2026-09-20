/- ========================================================================= -/
/-                       CTA/CuInterface.lean                                 -/
/-  CU 接口（cu_interface）的 Lean 4 逐拍模型：WG→WF 拆分 + WF 完成聚集        -/
/-  + dealloc/host 上报                                                       -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/cu_interface.scala       -/
/-    （class cu_interface，全文 237 行）                                      -/
/-  参数：NUM_CU=2、NUM_WG_SLOT=8、NUM_WF_MAX=8、WF_TAG=6b{slot3,wf3}、        -/
/-    fifo=Queue(2)（:46）、wf_gather_cnt/wf_gather_ram 各 16 项（:127,:165）、-/
/-    DEBUG=true ⇒ wf_gather_ram_valid 存在（:128）。                          -/
/-                                                                           -/
/-  验证目标（CtasEventOk 黑盒契约核销，见 CtaScheduler.lean 第 3 节）：        -/
/-    H-CUIF-SPLIT  （wg→warp 拆分正确：wf_tag 分配、数量一致，:71-113）：      -/
/-      定理 cuif_split_tag / cuif_split_deq_last /                            -/
/-      cuif_split_countdown                                                  -/
/-    H-CUIF-DONE   （完成计数恰好，:161-186）：定理 cuif_done_read /           -/
/-      cuif_cnt_update / cuif_finish_exact                                   -/
/-    H-CUIF-DEALLOC（回收时机 + wgId 一致，:179,:200-223）：定理               -/
/-      cuif_dealloc_valid_iff / cuif_dealloc_exact / cuif_dealloc_bits /      -/
/-      cuif_dealloc_wgId                                                     -/
/-    I-25 后果见证：测试 cuifT_i25_leak（永缺 1 + 提前完成）与                 -/
/-      cuifT_i25_residue（计数残留 → 下一个 WG 少收 1 个 done 即"完成"）       -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 逐拍建模：状态 = 全部寄存器 + fifo + 两块 SyncReadMem；寄存器读旧值。   -/
/-  D2. init 阶段（:166-168 清零 wf_gather_cnt，16 拍）不建模：cta_scheduler   -/
/-      顶层以 init_ok 门控 host 入口（cta_scheduler.scala:122-125），本模型    -/
/-      从 init 完成态起步（cntMem=0、liveMem=false、init_ok=1）。              -/
/-  D3. RRArbiter（:154）建模为固定优先级（CU0 优先）。仲裁顺序只影响处理      -/
/-      顺序，不改变单条 done 的处理语义；活性公平性不在本文件范围。            -/
/-  D4. 3-to-1 握手（:55-58）合并为单输入 enqValid+enqWg：DEBUG 断言           -/
/-      :50-51 保证三源 wg_id 一致，字段合并建模为一个 CuifWg。                 -/
/-  D5. wf_gather_ram 读出保持寄存器（:172-176）建模为"fire 拍采样、其后        -/
/-      保持"的 infoRd 寄存器——与 Mux(tmp, data, RegEnable(data,tmp)) 等价。    -/
/-  D6. SyncReadMem 1 拍读延迟：GET_WF 的 fire 拍发起读，UPDATE 拍消费          -/
/-      cntRd/infoRd（模型在 fire 拍采样进寄存器，语义等价）。                  -/
/-  D7. 环境契约 CuifEnvOk：                                                   -/
/-      E1 enq：num_wf ∈ [1,8] 且目标槽不忙（¬live ∧ fifo 中无同槽项）——        -/
/-         系统侧由 H-ALLOC-SLOT 保证（allocator 只分配空闲槽）；               -/
/-      E2 done：cu_wf_done 的 wf_tag 指向在驻（live）槽——**这正是 I-25         -/
/-         被违反的前提**（CTA2warp 的 tag 迟读污染，03 报告 I-25）。            -/
/-                                                                           -/
/- ======================== 源码审查疑点（Q 区，上报主会话） ================== -/
/-  Q-CUIF1. :79-82：num_wf=0 的 WG 使 splitter_cnt 载入 0，fifo 永不弹出，     -/
/-      后续 WG 全部堵死。依赖 host 契约 num_wf ≥ 1（并入 E1）。                -/
/-  Q-CUIF2. :161 按 tag 取 (cu, wg_slot)——I-25 受害点；本文件给出两条          -/
/-      状态机层面 witness（cuifT_i25_*）。                                     -/
/-  Q-CUIF3. :172-176 的保持寄存器是正确性关键：finish 当拍 live 即清           -/
/-      （:192），DEALLOC 期间同槽新 WG 合法入队甚至 load（覆盖                 -/
/-      wf_gather_ram），但 infoRd 保持旧记录，dealloc bits 不受影响。          -/
/-      机制验证正确，记录在案。                                                -/
/-  Q-CUIF4. :131-136 load 时**不清** wf_gather_cnt，只写 info/valid：cnt       -/
/-      的清零只在 finish 拍（:181-182）。正常流程 cnt 必为 0（由不变式          -/
/-      cuifInv 的 live=false → cnt=0 保证）；但任何绕过 valid 的错误 done      -/
/-      （I-25 污染 tag 打到空闲槽）会留下 cnt 残留，且**不会被下一次 load      -/
/-      清除**——这是 I-25 后果的放大器（见 cuifT_i25_residue）。                -/
/-      建议上游：load 时顺手清零对应 cnt 项（成本为零，堵死残留通道）。        -/
/-  Q-CUIF5. :95-96 的 sgpr/vgpr 地址不回绕断言依赖 rt 分配的基址契约           -/
/-      （H-RT-BOUNDS），本文件不核销（资源区间正确性属 resource_table 波次）。 -/
/-  Q-CUIF6. :190-194：UPDATE 拍对 valid 的写是无条件的；若 done 打到空闲槽     -/
/-      （E2 被违反），valid 被置 true（finish=false 时）——空闲槽变"幽灵在驻"。  -/
/-      DEBUG 配置下 :191 的 assert 会在仿真中先触发；综合后完全静默。           -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

open Ventus.Base

/- ========================================================================= -/
/- 1. 常量、wf_tag 布局、FSM、数据结构                                          -/
/- ========================================================================= -/

/-- wf_tag = cat(wg_slot_id, wf_id)（:35-37,:108-112）；
    与 CtaScheduler.lean:83-89 的 ctasWfTag/ctasTagSlot/ctasTagWf 同一定义 -/
def cuifWfTag (slot wf : BitVec 3) : BitVec 6 := (slot.zeroExtend 6 <<< 3) ||| wf.zeroExtend 6
def cuifTagSlot (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 3 3
def cuifTagWf (tag : BitVec 6) : BitVec 3 := tag.extractLsb' 0 3

/-- TAG 布局往返正确（:161 按 tag 取 slot 的位级基础） -/
theorem cuif_tag_roundtrip (slot wf : BitVec 3) :
    cuifTagSlot (cuifWfTag slot wf) = slot ∧ cuifTagWf (cuifWfTag slot wf) = wf := by
  unfold cuifWfTag cuifTagSlot cuifTagWf
  bv_decide

/-- gather FSM（:142-146） -/
inductive CuifG where
  | getWf | update | dealloc
  deriving DecidableEq, Repr

/-- fifo 元素（cta_data，:43-45；只建模本模块消费的字段） -/
structure CuifWg where
  cuId : BitVec 1
  wgSlotId : BitVec 3
  numWf : BitVec 4
  wgId : BitVec 32
  numSgprPerWf : BitVec 12
  numVgprPerWf : BitVec 11
  numPdsPerWf : BitVec 18
  sgprBase : BitVec 11
  vgprBase : BitVec 10
  ldsBase : BitVec 17
  pdsBase : BitVec 32
  ldsDeallocEn : Bool
  sgprDeallocEn : Bool
  vgprDeallocEn : Bool
  deriving DecidableEq

/-- wf_gather_ram 元素（cta_data_1，:120-126） -/
structure CuifWgInfo where
  numWf : BitVec 4
  wgId : BitVec 32
  ldsDeallocEn : Bool
  sgprDeallocEn : Bool
  vgprDeallocEn : Bool
  deriving DecidableEq

/-- :133-134 从 fifo 元素生成 gather ram 记录 -/
def cuifInfoOf (w : CuifWg) : CuifWgInfo :=
  ⟨w.numWf, w.wgId, w.ldsDeallocEn, w.sgprDeallocEn, w.vgprDeallocEn⟩

/-- cu_interface 全部状态 -/
structure CuifState where
  fifo : List CuifWg                 -- :46 Queue(2)，队首 = head
  splitCnt : BitVec 4                -- :71
  splitSgpr : BitVec 11              -- :73
  splitVgpr : BitVec 10              -- :74
  splitPds : BitVec 32               -- :75
  gfsm : CuifG                       -- :147
  cuReg : BitVec 1                   -- :160
  slotReg : BitVec 3                 -- :162
  cntMem : Fin 16 → BitVec 4         -- :165 wf_gather_cnt
  infoMem : Fin 16 → CuifWgInfo      -- :127 wf_gather_ram
  liveMem : Fin 16 → Bool            -- :128 wf_gather_ram_valid（DEBUG=true）
  cntRd : BitVec 4                   -- :171 读出（D6）
  infoRd : CuifWgInfo                -- :172-176 读出保持（D5）
  rtOk : Bool                        -- :200-203
  hostOk : Bool                      -- :217-220

/-- 每拍输入（平坦字段；D3 仲裁固定 CU0 优先） -/
structure CuifInputs where
  enqValid : Bool := false           -- 三源 valid 同拍（D4）
  enqWg : CuifWg := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩
  cuRdy0 : Bool := false             -- cu_wf_new(0).ready
  cuRdy1 : Bool := false             -- cu_wf_new(1).ready
  doneV0 : Bool := false             -- cu_wf_done(0).valid
  doneV1 : Bool := false
  doneTag0 : BitVec 6 := 0
  doneTag1 : BitVec 6 := 0
  rtRdy : Bool := false              -- rt_dealloc.ready
  hostRdy : Bool := false            -- host_wg_done.ready

/-- init 完成态（D2） -/
def cuifInit : CuifState where
  fifo := []
  splitCnt := 0#4
  splitSgpr := 0#11
  splitVgpr := 0#10
  splitPds := 0#32
  gfsm := .getWf
  cuReg := 0#1
  slotReg := 0#3
  cntMem := fun _ => 0#4
  infoMem := fun _ => ⟨0#4, 0#32, false, false, false⟩
  liveMem := fun _ => false
  cntRd := 0#4
  infoRd := ⟨0#4, 0#32, false, false, false⟩
  rtOk := false
  hostOk := false

/- ========================================================================= -/
/- 2. 索引、地址与组合信号                                                      -/
/- ========================================================================= -/

def cuifCuFin (c : BitVec 1) : Fin 2 := ⟨c.toNat, by have h := c.isLt; omega⟩

/-- 全局槽地址（:129）：cu * NUM_WG_SLOT + wgslot -/
def cuifGaddr (cu : BitVec 1) (slot : BitVec 3) : Fin 16 :=
  ⟨cu.toNat * 8 + slot.toNat, by have h1 := cu.isLt; have h2 := slot.isLt; omega⟩

/-- Fin 16 函数写更新 -/
def cuifUpd (f : Fin 16 → α) (g : Fin 16) (v : α) : Fin 16 → α :=
  fun x => if x = g then v else f x

/-- fifo 非空时取头；空时读出不可观测，建模为全 0（同 CTA2warp D2 惯例） -/
def cuifHead (s : CuifState) : CuifWg :=
  match s.fifo with
  | [] => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩
  | h :: _ => h

/-- 入队（:55-58 + Queue enq.ready：length < 2） -/
def cuifEnqFire (s : CuifState) (i : CuifInputs) : Bool :=
  i.enqValid && decide (s.fifo.length < 2)

/-- splitter_load_new（:76） -/
def cuifLoadNew (s : CuifState) : Bool :=
  decide (s.splitCnt = 0#4) && !s.fifo.isEmpty

/-- cu_wf_new(head.cu).fire（:80,:100） -/
def cuifWfFire (s : CuifState) (i : CuifInputs) : Bool :=
  decide (s.splitCnt ≠ 0#4) &&
  (match s.fifo with
   | [] => false
   | h :: _ => if h.cuId = 0#1 then i.cuRdy0 else i.cuRdy1)

/-- fifo 弹出（:77）：最后一个 WF 发出拍 -/
def cuifDeqFire (s : CuifState) (i : CuifInputs) : Bool :=
  decide (s.splitCnt = 1#4) &&
  (match s.fifo with
   | [] => false
   | h :: _ => if h.cuId = 0#1 then i.cuRdy0 else i.cuRdy1)

/-- cu_wf_new 输出（:99-113）：valid 与 wf_tag -/
def cuifWfNewValid (s : CuifState) (c : BitVec 1) : Bool :=
  decide (s.splitCnt ≠ 0#4) &&
  (match s.fifo with | [] => false | h :: _ => decide (h.cuId = c))

def cuifWfNewTag (s : CuifState) : BitVec 6 :=
  match s.fifo with
  | [] => 0#6
  | h :: _ => cuifWfTag h.wgSlotId ((h.numWf - s.splitCnt).extractLsb' 0 3)  -- :108-112

/-- 仲裁（D3：固定 CU0 优先） -/
def cuifChosenCu (i : CuifInputs) : BitVec 1 := if i.doneV0 then 0#1 else 1#1
def cuifChosenTag (i : CuifInputs) : BitVec 6 := if i.doneV0 then i.doneTag0 else i.doneTag1

def cuifArbFire (s : CuifState) (i : CuifInputs) : Bool :=
  decide (s.gfsm = .getWf) && (i.doneV0 || i.doneV1)

/-- :179 完成判定 -/
def cuifFinish (s : CuifState) : Bool := decide (s.cntRd + 1#4 = s.infoRd.numWf)

/-- :204 rt_dealloc.valid 与 bits（:205-211） -/
def cuifRtDeallocValid (s : CuifState) : Bool :=
  (decide (s.gfsm = .update) && cuifFinish s) ||
  (decide (s.gfsm = .dealloc) && !s.rtOk)
def cuifDeallocBits (s : CuifState) : BitVec 1 × BitVec 3 × CuifWgInfo :=
  (s.cuReg, s.slotReg, s.infoRd)

/-- :221 host_wg_done.valid -/
def cuifHostDoneValid (s : CuifState) : Bool :=
  (decide (s.gfsm = .update) && cuifFinish s) ||
  (decide (s.gfsm = .dealloc) && !s.hostOk)

def cuifRtFire (s : CuifState) (i : CuifInputs) : Bool := cuifRtDeallocValid s && i.rtRdy
def cuifHostFire (s : CuifState) (i : CuifInputs) : Bool := cuifHostDoneValid s && i.hostRdy

/-- :200-203 / :217-220 的成功标志寄存器 -/
def cuifRtOkNext (s : CuifState) (i : CuifInputs) : Bool :=
  if s.gfsm = .update then cuifRtFire s i else (s.rtOk || cuifRtFire s i)
def cuifHostOkNext (s : CuifState) (i : CuifInputs) : Bool :=
  if s.gfsm = .update then cuifHostFire s i else (s.hostOk || cuifHostFire s i)

/- ========================================================================= -/
/- 3. 单拍 step 与多拍 run                                                      -/
/- ========================================================================= -/

/-- :229-236 gather FSM 转移 -/
def cuifGfsmNext (s : CuifState) (i : CuifInputs) : CuifG :=
  match s.gfsm with
  | .getWf => if cuifArbFire s i then .update else .getWf
  | .update =>
      if !cuifFinish s then .getWf
      else if cuifRtFire s i && cuifHostFire s i then .getWf else .dealloc
  | .dealloc =>
      if cuifRtOkNext s i && cuifHostOkNext s i then .getWf else .dealloc

def cuifStep (s : CuifState) (i : CuifInputs) : CuifState where
  fifo := (if cuifDeqFire s i then s.fifo.tail else s.fifo) ++
          (if cuifEnqFire s i then [i.enqWg] else [])      -- Queue(2) 语义
  splitCnt :=                                              -- :79-82
    if s.splitCnt ≠ 0#4 then (if cuifWfFire s i then s.splitCnt - 1#4 else s.splitCnt)
    else (match s.fifo with | [] => 0#4 | h :: _ => h.numWf)
  splitSgpr :=                                             -- :83-86（11b + 12b → 截 11b）
    if cuifLoadNew s then (cuifHead s).sgprBase
    else if cuifWfFire s i then (s.splitSgpr.zeroExtend 12 + (cuifHead s).numSgprPerWf).extractLsb' 0 11
    else s.splitSgpr
  splitVgpr :=                                             -- :87-90（10b + 11b → 截 10b）
    if cuifLoadNew s then (cuifHead s).vgprBase
    else if cuifWfFire s i then (s.splitVgpr.zeroExtend 11 + (cuifHead s).numVgprPerWf).extractLsb' 0 10
    else s.splitVgpr
  splitPds :=                                              -- :91-94
    if cuifLoadNew s then (cuifHead s).pdsBase
    else if cuifWfFire s i then s.splitPds + (cuifHead s).numPdsPerWf.zeroExtend 32
    else s.splitPds
  gfsm :=                                                  -- :229-236
    match s.gfsm with
    | .getWf => if cuifArbFire s i then .update else .getWf
    | .update =>
        if !cuifFinish s then .getWf
        else if cuifRtFire s i && cuifHostFire s i then .getWf else .dealloc
    | .dealloc =>
        if cuifRtOkNext s i && cuifHostOkNext s i then .getWf else .dealloc
  cuReg := if cuifArbFire s i then cuifChosenCu i else s.cuReg               -- :160
  slotReg := if cuifArbFire s i then cuifTagSlot (cuifChosenTag i) else s.slotReg  -- :161-162
  cntRd := if cuifArbFire s i then
      s.cntMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) else s.cntRd  -- :171（D6）
  infoRd := if cuifArbFire s i then
      s.infoMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) else s.infoRd -- :174-175（D5）
  cntMem :=                                                -- :180-186（init 已完成，D2）
    if s.gfsm = .update then
      cuifUpd s.cntMem (cuifGaddr s.cuReg s.slotReg)
        (if cuifFinish s then 0#4 else s.cntRd + 1#4)
    else s.cntMem
  infoMem :=                                               -- :131-136
    if cuifLoadNew s then
      cuifUpd s.infoMem (cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId) (cuifInfoOf (cuifHead s))
    else s.infoMem
  liveMem :=                                               -- :132 先置位、:192 后清（源码序）
    let l1 := if cuifLoadNew s then
        cuifUpd s.liveMem (cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId) true
      else s.liveMem
    if s.gfsm = .update then
      cuifUpd l1 (cuifGaddr s.cuReg s.slotReg) (!cuifFinish s)
    else l1
  rtOk := cuifRtOkNext s i
  hostOk := cuifHostOkNext s i

def cuifRun (s : CuifState) (ins : List CuifInputs) : CuifState := ins.foldl cuifStep s

/- ========================================================================= -/
/- 4. 环境契约与不变式                                                          -/
/- ========================================================================= -/

/-- 槽忙：在驻（live）或已有同槽 WG 在 fifo 排队 -/
def cuifSlotBusy (s : CuifState) (cu : BitVec 1) (slot : BitVec 3) : Prop :=
  s.liveMem (cuifGaddr cu slot) = true ∨
  ∃ w, w ∈ s.fifo ∧ w.cuId = cu ∧ w.wgSlotId = slot

/-- 环境契约（D7） -/
def CuifEnvOk (s : CuifState) (i : CuifInputs) : Prop :=
  (cuifEnqFire s i = true →
     1 ≤ i.enqWg.numWf.toNat ∧ i.enqWg.numWf.toNat ≤ 8 ∧
     ¬ cuifSlotBusy s i.enqWg.cuId i.enqWg.wgSlotId) ∧
  (cuifArbFire s i = true →
     s.liveMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) = true)

/-- 不变式 -/
def CuifInv (s : CuifState) : Prop :=
  s.fifo.length ≤ 2 ∧
  (∀ w, w ∈ s.fifo → 1 ≤ w.numWf.toNat ∧ w.numWf.toNat ≤ 8) ∧
  s.fifo.Nodup ∧
  (∀ w1, w1 ∈ s.fifo → ∀ w2, w2 ∈ s.fifo → w1 ≠ w2 →
      ¬ (w1.cuId = w2.cuId ∧ w1.wgSlotId = w2.wgSlotId)) ∧
  (s.splitCnt ≠ 0#4 → ∃ h t, s.fifo = h :: t ∧ s.splitCnt.toNat ≤ h.numWf.toNat) ∧
  (∀ w, w ∈ s.fifo → s.liveMem (cuifGaddr w.cuId w.wgSlotId) = true →
      s.splitCnt ≠ 0#4 ∧ ∃ t, s.fifo = w :: t) ∧
  (∀ g, s.liveMem g = true →
      1 ≤ (s.infoMem g).numWf.toNat ∧ (s.infoMem g).numWf.toNat ≤ 8 ∧
      (s.cntMem g).toNat < (s.infoMem g).numWf.toNat) ∧
  (∀ g, s.liveMem g = false → s.cntMem g = 0#4) ∧
  (s.gfsm = .update →
      s.cntRd = s.cntMem (cuifGaddr s.cuReg s.slotReg) ∧
      s.infoRd = s.infoMem (cuifGaddr s.cuReg s.slotReg) ∧
      s.liveMem (cuifGaddr s.cuReg s.slotReg) = true) ∧
  (s.gfsm = .dealloc → s.cntRd.toNat + 1 = s.infoRd.numWf.toNat)

/- ========================================================================= -/
/- 5. 支撑引理                                                                 -/
/- ========================================================================= -/

theorem cuif_fifo_step (s : CuifState) (i : CuifInputs) :
    (cuifStep s i).fifo =
      (if cuifDeqFire s i then s.fifo.tail else s.fifo) ++
        (if cuifEnqFire s i then [i.enqWg] else []) := rfl

theorem cuif_splitCnt_step (s : CuifState) (i : CuifInputs) :
    (cuifStep s i).splitCnt =
      (if s.splitCnt ≠ 0#4 then (if cuifWfFire s i then s.splitCnt - 1#4 else s.splitCnt)
       else (match s.fifo with | [] => 0#4 | h :: _ => h.numWf)) := rfl

/-- cntMem 逐点方程（:180-186；只在 UPDATE 拍写，init 已完成） -/
theorem cuif_cnt_step_at (s : CuifState) (i : CuifInputs) (g : Fin 16) :
    (cuifStep s i).cntMem g =
      (if s.gfsm = .update ∧ g = cuifGaddr s.cuReg s.slotReg then
         (if cuifFinish s then 0#4 else s.cntRd + 1#4) else s.cntMem g) := by
  show (if s.gfsm = .update then
      cuifUpd s.cntMem (cuifGaddr s.cuReg s.slotReg) (if cuifFinish s then 0#4 else s.cntRd + 1#4)
      else s.cntMem) g = _
  unfold cuifUpd
  by_cases h1 : s.gfsm = .update <;> by_cases h2 : g = cuifGaddr s.cuReg s.slotReg <;>
    simp [h1, h2]

/-- infoMem 逐点方程（:131-136；只在 loadNew 拍写） -/
theorem cuif_info_step_at (s : CuifState) (i : CuifInputs) (g : Fin 16) :
    (cuifStep s i).infoMem g =
      (if cuifLoadNew s = true ∧ g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId then
         cuifInfoOf (cuifHead s) else s.infoMem g) := by
  show (if cuifLoadNew s then
      cuifUpd s.infoMem (cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId) (cuifInfoOf (cuifHead s))
      else s.infoMem) g = _
  unfold cuifUpd
  by_cases h1 : cuifLoadNew s = true <;>
    by_cases h2 : g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId <;> simp [h1, h2]

/-- liveMem 逐点方程（:132 先置位、:192 后清，源码序后者胜） -/
theorem cuif_live_step_at (s : CuifState) (i : CuifInputs) (g : Fin 16) :
    (cuifStep s i).liveMem g =
      (if s.gfsm = .update ∧ g = cuifGaddr s.cuReg s.slotReg then !cuifFinish s
       else if cuifLoadNew s = true ∧ g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId then true
       else s.liveMem g) := by
  show ((if s.gfsm = .update then
      cuifUpd (if cuifLoadNew s then
        cuifUpd s.liveMem (cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId) true else s.liveMem)
        (cuifGaddr s.cuReg s.slotReg) (!cuifFinish s)
      else (if cuifLoadNew s then
        cuifUpd s.liveMem (cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId) true else s.liveMem)) g) = _
  unfold cuifUpd
  by_cases h1 : s.gfsm = .update <;> by_cases h2 : g = cuifGaddr s.cuReg s.slotReg <;>
    by_cases h3 : cuifLoadNew s = true <;>
    by_cases h4 : g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId <;> simp [h1, h2, h3, h4]

theorem cuif_mem_step_fifo {s : CuifState} {i : CuifInputs} {w : CuifWg}
    (h : w ∈ (cuifStep s i).fifo) : w ∈ s.fifo ∨ w = i.enqWg := by
  rw [cuif_fifo_step] at h
  rcases List.mem_append.mp h with h | h
  · by_cases hd : cuifDeqFire s i = true
    · rw [if_pos hd] at h; exact Or.inl (List.mem_of_mem_tail h)
    · simp only [hd, Bool.false_eq_true, if_false] at h; exact Or.inl h
  · by_cases he : cuifEnqFire s i = true
    · rw [if_pos he] at h; exact Or.inr (List.mem_singleton.mp h)
    · simp only [he, Bool.false_eq_true, if_false] at h; simp at h

theorem cuif_mem_step_fifo_old {s : CuifState} {i : CuifInputs} {w : CuifWg}
    (h : w ∈ (cuifStep s i).fifo) (he : cuifEnqFire s i = false) : w ∈ s.fifo := by
  rw [cuif_fifo_step] at h
  simp only [he, Bool.false_eq_true, if_false, List.append_nil] at h
  by_cases hd : cuifDeqFire s i = true
  · rw [if_pos hd] at h; exact List.mem_of_mem_tail h
  · simp only [hd, Bool.false_eq_true, if_false] at h; exact h

/-- 队首保持：无弹出时 step 后队首不变 -/
theorem cuif_fifo_step_cons (s : CuifState) (i : CuifInputs) (h : CuifWg) (t : List CuifWg)
    (hf : s.fifo = h :: t) (hd : cuifDeqFire s i = false) :
    (cuifStep s i).fifo = h :: (t ++ (if cuifEnqFire s i then [i.enqWg] else [])) := by
  rw [cuif_fifo_step]
  simp only [hd, Bool.false_eq_true, if_false]
  rw [hf, List.cons_append]

theorem cuifHead_of_cons {s : CuifState} {h : CuifWg} {t : List CuifWg}
    (hf : s.fifo = h :: t) : cuifHead s = h := by
  unfold cuifHead; rw [hf]

/-- gaddr 单射（:129 的 cu*8+slot 无混叠） -/
theorem cuifGaddr_inj {c1 c2 : BitVec 1} {s1 s2 : BitVec 3}
    (h : cuifGaddr c1 s1 = cuifGaddr c2 s2) : c1 = c2 ∧ s1 = s2 := by
  have e := congrArg Fin.val h
  simp only [cuifGaddr] at e
  have hc1 := c1.isLt; have hc2 := c2.isLt
  have hs1 := s1.isLt; have hs2 := s2.isLt
  refine ⟨BitVec.toNat_inj.mp ?_, BitVec.toNat_inj.mp ?_⟩ <;> omega

/-- 仲裁只在 GET_WF 拍接收 done -/
theorem cuif_arbFire_getWf {s : CuifState} {i : CuifInputs} (h : cuifArbFire s i = true) :
    s.gfsm = .getWf := by
  unfold cuifArbFire at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- deqFire ⇒ 最后一个 WF 在发（cnt=1、fifo 非空、同拍 wfFire） -/
theorem cuif_deqFire_facts (s : CuifState) (i : CuifInputs) (hd : cuifDeqFire s i = true) :
    s.splitCnt = 1#4 ∧ s.fifo ≠ [] ∧ cuifWfFire s i = true := by
  unfold cuifDeqFire at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨h1, hm⟩ := hd
  cases hf : s.fifo with
  | nil => rw [hf] at hm; simp at hm
  | cons h0 t0 =>
    refine ⟨h1, List.cons_ne_nil _ _, ?_⟩
    unfold cuifWfFire
    have hn0 : decide (s.splitCnt ≠ 0#4) = true := by rw [h1]; decide
    rw [hn0, Bool.true_and, hf]
    rw [hf] at hm
    exact hm

/-- wfFire ⇒ cnt ≠ 0 且 fifo 非空 -/
theorem cuif_wfFire_facts (s : CuifState) (i : CuifInputs) (hf : cuifWfFire s i = true) :
    s.splitCnt ≠ 0#4 ∧ s.fifo ≠ [] := by
  unfold cuifWfFire at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨h1, hm⟩ := hf
  refine ⟨h1, ?_⟩
  cases hfc : s.fifo with
  | nil => rw [hfc] at hm; simp at hm
  | cons h0 t0 => exact List.cons_ne_nil _ _

/-- cnt=1 且 wfFire ⇒ deqFire（同一 ready 条件） -/
theorem cuif_deq_of_wfFire_one (s : CuifState) (i : CuifInputs)
    (h1 : s.splitCnt = 1#4) (hf : cuifWfFire s i = true) : cuifDeqFire s i = true := by
  unfold cuifWfFire at hf
  unfold cuifDeqFire
  have d1 : decide (s.splitCnt ≠ 0#4) = true := by rw [h1]; decide
  have d2 : decide (s.splitCnt = 1#4) = true := decide_eq_true h1
  rw [d1, Bool.true_and] at hf
  rw [d2, Bool.true_and]
  exact hf

/-- cnt≠0 且无 wfFire ⇒ 无 deqFire（同一 ready 条件） -/
theorem cuif_no_fire_no_deq (s : CuifState) (i : CuifInputs)
    (hc : s.splitCnt ≠ 0#4) (hf : cuifWfFire s i = false) : cuifDeqFire s i = false := by
  unfold cuifWfFire at hf
  unfold cuifDeqFire
  by_cases h1 : s.splitCnt = 1#4
  · have d1 : decide (s.splitCnt ≠ 0#4) = true := decide_eq_true hc
    have d2 : decide (s.splitCnt = 1#4) = true := decide_eq_true h1
    rw [d1, Bool.true_and] at hf
    rw [d2, Bool.true_and]
    exact hf
  · have d2 : decide (s.splitCnt = 1#4) = false := decide_eq_false h1
    rw [d2, Bool.false_and]

/-- loadNew ⇒ cnt = 0 且 fifo 非空 -/
theorem cuif_loadNew_facts (s : CuifState) (hl : cuifLoadNew s = true) :
    s.splitCnt = 0#4 ∧ s.fifo ≠ [] := by
  unfold cuifLoadNew at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨h1, h2⟩ := hl
  refine ⟨h1, ?_⟩
  cases hf : s.fifo with
  | nil => rw [hf] at h2; simp at h2
  | cons h0 t0 => exact List.cons_ne_nil _ _

/-- cnt=0 ⇒ 无 deqFire -/
theorem cuif_no_deq_of_cnt0 (s : CuifState) (i : CuifInputs) (hc : s.splitCnt = 0#4) :
    cuifDeqFire s i = false := by
  unfold cuifDeqFire; simp [hc]

/-- 位运算辅助 -/
theorem cuif_ne_zero_of_toNat_pos {x : BitVec 4} (h : 1 ≤ x.toNat) : x ≠ 0#4 := by
  intro hx; rw [hx] at h; exact absurd h (by decide)

theorem cuif_sub_one_ne_zero {x : BitVec 4} (h0 : x ≠ 0#4) (h1 : x ≠ 1#4) :
    x - 1#4 ≠ 0#4 := by bv_decide

theorem cuif_sub_one_le {x n : BitVec 4} (h0 : x ≠ 0#4) (h : x ≤ n) : x - 1#4 ≤ n := by bv_decide

theorem cuif_sub_lt_self {n c : BitVec 4} (h1 : 1#4 ≤ c) (h2 : c ≤ n) : n - c < n := by bv_decide

/-- BitVec 4 非零 ⇒ ≥ 1 -/
theorem cuif_one_le_of_ne_zero {x : BitVec 4} (h : x ≠ 0#4) : 1#4 ≤ x := by
  show 1 ≤ x.toNat
  have h2 : x.toNat ≠ 0 := fun hh => h (BitVec.toNat_inj.mp (by simp [hh]))
  omega

theorem cuif_toNat_add_one {x : BitVec 4} (h : x.toNat + 1 < 16) :
    (x + 1#4).toNat = x.toNat + 1 := by
  have e := BitVec.toNat_add x (1#4)
  simp only [BitVec.toNat_ofNat] at e
  omega

/-- 进入 UPDATE 的唯一途径：GET_WF 拍接收 done -/
theorem cuif_step_gfsm_update (s : CuifState) (i : CuifInputs)
    (h : (cuifStep s i).gfsm = .update) : s.gfsm = .getWf ∧ cuifArbFire s i = true := by
  have e : (cuifStep s i).gfsm = cuifGfsmNext s i := rfl
  rw [e] at h
  cases hg : s.gfsm with
  | getWf =>
    simp only [cuifGfsmNext, hg] at h
    by_cases hf : cuifArbFire s i = true
    · exact ⟨rfl, hf⟩
    · rw [if_neg hf] at h; exact absurd h (by decide)
  | update =>
    simp only [cuifGfsmNext, hg] at h
    by_cases hf : cuifFinish s = true
    · simp only [hf, Bool.not_true, Bool.false_eq_true, if_false] at h
      by_cases hc : (cuifRtFire s i && cuifHostFire s i) = true
      · rw [if_pos hc] at h; exact absurd h (by decide)
      · rw [if_neg hc] at h; exact absurd h (by decide)
    · simp only [(Bool.not_eq_true _).mp hf, Bool.not_false, if_true] at h
      exact absurd h (by decide)
  | dealloc =>
    simp only [cuifGfsmNext, hg] at h
    by_cases hc : (cuifRtOkNext s i && cuifHostOkNext s i) = true
    · rw [if_pos hc] at h; exact absurd h (by decide)
    · rw [if_neg hc] at h; exact absurd h (by decide)

/- ========================================================================= -/
/- 6. 主定理：不变式保持                                                        -/
/- ========================================================================= -/

theorem cuifInv_init : CuifInv cuifInit := by
  refine ⟨by decide, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; simp [cuifInit] at hw
  · intro w1 h1; simp [cuifInit] at h1
  · intro h; exact absurd rfl h
  · intro w hw; simp [cuifInit] at hw
  · intro g hg; simp [cuifInit] at hg
  · intro g hg; rfl
  · intro hg; exact CuifG.noConfusion hg
  · intro hg; exact CuifG.noConfusion hg

theorem cuifInv_step (s : CuifState) (i : CuifInputs)
    (hinv : CuifInv s) (henv : CuifEnvOk s i) : CuifInv (cuifStep s i) := by
  obtain ⟨hlen, hnumB, hnodup, hdist, hsplit, hlive6, hcnt, hzero, hupd, hdec⟩ := hinv
  obtain ⟨henqE, hdoneE⟩ := henv
  -- 主情形公共尾：w ∈ s.fifo 且 pre-live 时，I6 结论保持
  have cont_arg : ∀ w : CuifWg, w ∈ s.fifo →
      s.liveMem (cuifGaddr w.cuId w.wgSlotId) = true → w ∈ (cuifStep s i).fifo →
      (cuifStep s i).splitCnt ≠ 0#4 ∧ ∃ t, (cuifStep s i).fifo = w :: t := by
    intro w hold hlv0 hw'
    obtain ⟨hcnt0, t0, hft⟩ := hlive6 w hold hlv0
    by_cases hfire : cuifWfFire s i = true
    · by_cases h1 : s.splitCnt = 1#4
      · -- 最后一个 WF 发出 → 队首弹出 → w ∉ fifo'，矛盾
        exfalso
        have hd : cuifDeqFire s i = true := cuif_deq_of_wfFire_one s i h1 hfire
        rw [cuif_fifo_step, if_pos hd, hft] at hw'
        simp only [List.tail_cons] at hw'
        rcases List.mem_append.mp hw' with hwt | hwe
        · have hnd : (w :: t0).Nodup := hft ▸ hnodup
          rw [List.nodup_cons] at hnd
          exact hnd.1 hwt
        · by_cases he : cuifEnqFire s i = true
          · rw [if_pos he] at hwe
            rw [List.mem_singleton] at hwe
            exact (henqE he).2.2 (Or.inl (hwe ▸ hlv0))
          · rw [if_neg he] at hwe; simp at hwe
      · refine ⟨?_, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), ?_⟩
        · rw [cuif_splitCnt_step, if_pos hcnt0, if_pos hfire]
          exact cuif_sub_one_ne_zero hcnt0 h1
        · have hdf : cuifDeqFire s i = false := by
            unfold cuifDeqFire; simp [h1]
          exact cuif_fifo_step_cons s i w t0 hft hdf
    · refine ⟨?_, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), ?_⟩
      · rw [cuif_splitCnt_step, if_pos hcnt0, if_neg hfire]
        exact hcnt0
      · exact cuif_fifo_step_cons s i w t0 hft (cuif_no_fire_no_deq s i hcnt0 ((Bool.not_eq_true _).mp hfire))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- c1 fifo.length ≤ 2
    rw [cuif_fifo_step]
    by_cases hd : cuifDeqFire s i = true
    · obtain ⟨h1, hfne, _⟩ := cuif_deqFire_facts s i hd
      rw [if_pos hd]
      by_cases he : cuifEnqFire s i = true
      · rw [if_pos he]
        cases hf : s.fifo with
        | nil => exact absurd hf hfne
        | cons h0 t0 =>
          rw [hf] at hlen
          simp at hlen ⊢
          omega
      · rw [if_neg he]
        cases hf : s.fifo with
        | nil => exact absurd hf hfne
        | cons h0 t0 =>
          rw [hf] at hlen
          simp at hlen ⊢
          omega
    · rw [if_neg hd]
      by_cases he : cuifEnqFire s i = true
      · rw [if_pos he]
        have hl : s.fifo.length < 2 := by
          unfold cuifEnqFire at he
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he
          exact he.2
        simp; omega
      · rw [if_neg he]; simp; exact hlen
  · -- c2 fifo 元素 numWf ∈ [1,8]
    intro w hw
    rcases cuif_mem_step_fifo hw with h | h
    · exact hnumB w h
    · subst h
      by_cases he : cuifEnqFire s i = true
      · exact ⟨(henqE he).1, (henqE he).2.1⟩
      · exact hnumB _ (cuif_mem_step_fifo_old hw ((Bool.not_eq_true _).mp he))
  · -- c3a Nodup
    rw [cuif_fifo_step]
    by_cases hd : cuifDeqFire s i = true
    · rw [if_pos hd]
      obtain ⟨h1, hfne, _⟩ := cuif_deqFire_facts s i hd
      cases hf : s.fifo with
      | nil => exact absurd hf hfne
      | cons h0 t0 =>
        have hnd : (h0 :: t0).Nodup := hf ▸ hnodup
        rw [List.nodup_cons] at hnd
        by_cases he : cuifEnqFire s i = true
        · rw [if_pos he, List.nodup_append]
          refine ⟨hnd.2, by simp, ?_⟩
          intro x hx y hy
          rw [List.mem_singleton] at hy; subst hy
          intro hxy
          exact (henqE he).2.2 (Or.inr ⟨x, by rw [hf]; exact List.mem_cons_of_mem _ hx,
            congrArg CuifWg.cuId hxy, congrArg CuifWg.wgSlotId hxy⟩)
        · rw [if_neg he, List.append_nil]
          exact hnd.2
    · rw [if_neg hd]
      by_cases he : cuifEnqFire s i = true
      · rw [if_pos he, List.nodup_append]
        refine ⟨hnodup, by simp, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        intro hxy
        exact (henqE he).2.2 (Or.inr ⟨x, hx,
          congrArg CuifWg.cuId hxy, congrArg CuifWg.wgSlotId hxy⟩)
      · rw [if_neg he, List.append_nil]; exact hnodup
  · -- c3b 槽位互异
    intro w1 hw1 w2 hw2 hne12 hsame
    rcases cuif_mem_step_fifo hw1 with h1 | h1 <;> rcases cuif_mem_step_fifo hw2 with h2 | h2
    · exact hdist w1 h1 w2 h2 hne12 hsame
    · subst h2
      by_cases he : cuifEnqFire s i = true
      · exact (henqE he).2.2 (Or.inr ⟨w1, h1, hsame.1, hsame.2⟩)
      · exact hdist w1 h1 _ (cuif_mem_step_fifo_old hw2 ((Bool.not_eq_true _).mp he)) hne12 hsame
    · subst h1
      by_cases he : cuifEnqFire s i = true
      · exact (henqE he).2.2 (Or.inr ⟨w2, h2, hsame.1.symm, hsame.2.symm⟩)
      · exact hdist _ (cuif_mem_step_fifo_old hw1 ((Bool.not_eq_true _).mp he)) w2 h2 hne12 hsame
    · exact absurd (h1.trans h2.symm) hne12
  · -- c4 splitCnt ≠ 0 ⇒ fifo = h :: t ∧ cnt ≤ numWf
    intro hcnt'
    rw [cuif_splitCnt_step] at hcnt'
    by_cases hc0 : s.splitCnt = 0#4
    · rw [if_neg (fun h => h hc0)] at hcnt'
      cases hf : s.fifo with
      | nil => rw [hf] at hcnt'; simp at hcnt'
      | cons h0 t0 =>
        rw [hf] at hcnt'
        refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), ?_, ?_⟩
        · exact cuif_fifo_step_cons s i h0 t0 hf (cuif_no_deq_of_cnt0 s i hc0)
        · rw [cuif_splitCnt_step, if_neg (fun h => h hc0), hf]
          exact Nat.le_refl _
    · rw [if_pos hc0] at hcnt'
      obtain ⟨h0, t0, hft, hle⟩ := hsplit hc0
      by_cases hfire : cuifWfFire s i = true
      · rw [if_pos hfire] at hcnt'
        by_cases h1 : s.splitCnt = 1#4
        · rw [h1] at hcnt'; simp at hcnt'
        · have hdf : cuifDeqFire s i = false := by
            unfold cuifDeqFire; simp [h1]
          refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []),
            cuif_fifo_step_cons s i h0 t0 hft hdf, ?_⟩
          rw [cuif_splitCnt_step, if_pos hc0, if_pos hfire]
          show (s.splitCnt - 1#4) ≤ h0.numWf
          exact cuif_sub_one_le hc0 hle
      · rw [if_neg hfire] at hcnt'
        refine ⟨h0, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []),
          cuif_fifo_step_cons s i h0 t0 hft (cuif_no_fire_no_deq s i hc0 ((Bool.not_eq_true _).mp hfire)), ?_⟩
        rw [cuif_splitCnt_step, if_pos hc0, if_neg hfire]
        exact hle
  · -- c5（I6）：fifo 成员 live ⇒ 是队首且正在拆发
    intro w hw hlv'
    -- wrapper：先按 live' 来源三分支，再交 cont_arg
    have wrapper : ∀ w : CuifWg, w ∈ s.fifo → w ∈ (cuifStep s i).fifo →
        (cuifStep s i).liveMem (cuifGaddr w.cuId w.wgSlotId) = true →
        (cuifStep s i).splitCnt ≠ 0#4 ∧ ∃ t, (cuifStep s i).fifo = w :: t := by
      intro w hold hw' hlv'
      rw [cuif_live_step_at] at hlv'
      by_cases hua : s.gfsm = .update ∧ cuifGaddr w.cuId w.wgSlotId = cuifGaddr s.cuReg s.slotReg
      · rw [if_pos hua] at hlv'
        obtain ⟨hgu, hg⟩ := hua
        have hlv0 : s.liveMem (cuifGaddr w.cuId w.wgSlotId) = true := by
          rw [hg]; exact (hupd hgu).2.2
        exact cont_arg w hold hlv0 hw'
      · rw [if_neg hua] at hlv'
        by_cases hla : cuifLoadNew s = true ∧
            cuifGaddr w.cuId w.wgSlotId = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
        · rw [if_pos hla] at hlv'
          obtain ⟨hlf, hgg⟩ := hla
          obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
          cases hfc : s.fifo with
          | nil => exact absurd hfc hfne
          | cons h0 t0 =>
            have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
            rw [hhead] at hgg
            have hsame := cuifGaddr_inj hgg
            have hweq : w = h0 := by
              by_cases hne : w = h0
              · exact hne
              · exact absurd hsame (hdist w hold h0 (by rw [hfc]; simp) hne)
            subst hweq
            have hb := hnumB w (by rw [hfc]; simp)
            refine ⟨?_, t0 ++ (if cuifEnqFire s i then [i.enqWg] else []), ?_⟩
            · rw [cuif_splitCnt_step, if_neg (fun h => h hc0), hfc]
              show w.numWf ≠ 0#4
              exact cuif_ne_zero_of_toNat_pos hb.1
            · exact cuif_fifo_step_cons s i w t0 hfc (cuif_no_deq_of_cnt0 s i hc0)
        · rw [if_neg hla] at hlv'
          exact cont_arg w hold hlv' hw'
    rcases cuif_mem_step_fifo hw with hold | hnew
    · exact wrapper w hold hw hlv'
    · -- w = enqWg：env 保证 ¬busy ⇒ live' 必为 false，矛盾
      subst hnew
      by_cases he : cuifEnqFire s i = true
      · exfalso
        have hnb := (henqE he).2.2
        rw [cuif_live_step_at] at hlv'
        by_cases hua : s.gfsm = .update ∧
            cuifGaddr i.enqWg.cuId i.enqWg.wgSlotId = cuifGaddr s.cuReg s.slotReg
        · rw [if_pos hua] at hlv'
          obtain ⟨hgu, hg⟩ := hua
          have hlv0 : s.liveMem (cuifGaddr i.enqWg.cuId i.enqWg.wgSlotId) = true := by
            rw [hg]; exact (hupd hgu).2.2
          exact hnb (Or.inl hlv0)
        · rw [if_neg hua] at hlv'
          by_cases hla : cuifLoadNew s = true ∧
              cuifGaddr i.enqWg.cuId i.enqWg.wgSlotId =
                cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
          · obtain ⟨hlf, hgg⟩ := hla
            obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
            cases hfc : s.fifo with
            | nil => exact absurd hfc hfne
            | cons h0 t0 =>
              have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
              rw [hhead] at hgg
              have hsame := cuifGaddr_inj hgg
              exact hnb (Or.inr ⟨h0, by rw [hfc]; simp, hsame.1.symm, hsame.2.symm⟩)
          · rw [if_neg hla] at hlv'
            exact hnb (Or.inl hlv')
      · exact wrapper _ (cuif_mem_step_fifo_old hw ((Bool.not_eq_true _).mp he)) hw hlv'
  · -- c6：live ⇒ numWf 合法 ∧ cnt < numWf
    intro g hlv'
    rw [cuif_live_step_at] at hlv'
    by_cases hua : s.gfsm = .update ∧ g = cuifGaddr s.cuReg s.slotReg
    · rw [if_pos hua] at hlv'
      obtain ⟨hgu, hg⟩ := hua
      subst hg
      obtain ⟨hcntR, hinfoR, hlv0⟩ := hupd hgu
      obtain ⟨hb1, hb8, hlt⟩ := hcnt _ hlv0
      -- infoMem[gU] 本拍不被 loadNew 覆盖（gHead ≠ gU：gU live 而 loadNew 要求 cnt=0）
      have hinfo : (cuifStep s i).infoMem (cuifGaddr s.cuReg s.slotReg) =
          s.infoMem (cuifGaddr s.cuReg s.slotReg) := by
        rw [cuif_info_step_at]
        by_cases hld : cuifLoadNew s = true ∧
            cuifGaddr s.cuReg s.slotReg = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
        · obtain ⟨hlf, hgg⟩ := hld
          obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
          cases hfc : s.fifo with
          | nil => exact absurd hfc hfne
          | cons h0 t0 =>
            have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
            rw [hhead] at hgg
            have hlvH : s.liveMem (cuifGaddr h0.cuId h0.wgSlotId) = true := by
              rw [← hgg]; exact hlv0
            obtain ⟨hcnt0, _⟩ := hlive6 h0 (by rw [hfc]; simp) hlvH
            exact absurd hc0 hcnt0
        · rw [if_neg hld]
      have hfin : cuifFinish s = false := by
        cases hf : cuifFinish s <;> simp_all
      rw [hinfo]
      refine ⟨hb1, hb8, ?_⟩
      rw [cuif_cnt_step_at, if_pos ⟨hgu, rfl⟩, if_neg ((Bool.not_eq_true _).mpr hfin)]
      have hne : s.cntRd + 1#4 ≠ s.infoRd.numWf := by
        unfold cuifFinish at hfin; rw [decide_eq_false_iff_not] at hfin; exact hfin
      have hlt3 : s.cntRd.toNat < s.infoRd.numWf.toNat := by rw [hcntR, hinfoR]; exact hlt
      have hbw : (s.cntRd + 1#4).toNat = s.cntRd.toNat + 1 := cuif_toNat_add_one (by omega)
      have hne' : s.cntRd.toNat + 1 ≠ s.infoRd.numWf.toNat := by
        intro hcon
        apply hne
        have e1 : (s.cntRd + 1#4).toNat = s.infoRd.numWf.toNat := by rw [hbw]; exact hcon
        exact BitVec.toNat_inj.mp e1
      rw [hbw, ← hinfoR]
      omega
    · rw [if_neg hua] at hlv'
      by_cases hla : cuifLoadNew s = true ∧
          g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
      · rw [if_pos hla] at hlv'
        obtain ⟨hlf, hgg⟩ := hla
        obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
        cases hfc : s.fifo with
        | nil => exact absurd hfc hfne
        | cons h0 t0 =>
          have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
          -- cnt 本拍不被 update 写（gU ≠ g：gU live 而 g 是 ¬live 的 loadNew 目标）
          have hcntM : (cuifStep s i).cntMem g = s.cntMem g := by
            rw [cuif_cnt_step_at]
            by_cases hgu : s.gfsm = .update ∧ g = cuifGaddr s.cuReg s.slotReg
            · obtain ⟨hgu1, hgu2⟩ := hgu
              have hlvU : s.liveMem g = true := by rw [hgu2]; exact (hupd hgu1).2.2
              -- g live 且是 loadNew 目标 → head 同槽 live → cnt ≠ 0 矛盾
              have hlvH : s.liveMem (cuifGaddr h0.cuId h0.wgSlotId) = true := by
                have e1 : cuifGaddr h0.cuId h0.wgSlotId = g := by
                  rw [← hhead]; exact hgg.symm
                rw [e1]; exact hlvU
              obtain ⟨hcnt0, _⟩ := hlive6 h0 (by rw [hfc]; simp) hlvH
              exact absurd hc0 hcnt0
            · rw [if_neg hgu]
          rw [cuif_info_step_at, if_pos ⟨hlf, hgg⟩]
          have hb := hnumB h0 (by rw [hfc]; simp)
          have hlive_g : s.liveMem g = false := by
            -- g = gHead：若 live 则 hlive6 → cnt ≠ 0，与 loadNew 的 cnt=0 矛盾
            cases hgl : s.liveMem g with
            | true =>
              exfalso
              have hlvH : s.liveMem (cuifGaddr h0.cuId h0.wgSlotId) = true := by
                have e1 : cuifGaddr h0.cuId h0.wgSlotId = g := by
                  rw [← hhead]; exact hgg.symm
                rw [e1]; exact hgl
              obtain ⟨hcnt0, _⟩ := hlive6 h0 (by rw [hfc]; simp) hlvH
              exact absurd hc0 hcnt0
            | false => rfl
          have hcnt0 := hzero g hlive_g
          have hinfo : cuifInfoOf (cuifHead s) = cuifInfoOf h0 := by rw [hhead]
          rw [hinfo]
          rw [hcntM, hcnt0]
          refine ⟨?_, ?_, ?_⟩
          · show 1 ≤ h0.numWf.toNat; exact hb.1
          · show h0.numWf.toNat ≤ 8; exact hb.2
          · show (0#4 : BitVec 4).toNat < h0.numWf.toNat
            have hz : (0#4 : BitVec 4).toNat = 0 := by decide
            omega
      · rw [if_neg hla] at hlv'
        -- 无 live 写：infoMem/cntMem 在 g 处都不变
        have hinfo : (cuifStep s i).infoMem g = s.infoMem g := by
          rw [cuif_info_step_at, if_neg hla]
        have hcntM : (cuifStep s i).cntMem g = s.cntMem g := by
          rw [cuif_cnt_step_at, if_neg hua]
        rw [hinfo, hcntM]
        exact hcnt g hlv'
  · -- c7：¬live ⇒ cnt = 0
    intro g hlv'
    rw [cuif_live_step_at] at hlv'
    by_cases hua : s.gfsm = .update ∧ g = cuifGaddr s.cuReg s.slotReg
    · rw [if_pos hua] at hlv'
      obtain ⟨hgu, hg⟩ := hua
      subst hg
      -- !finish = false ⇒ finish = true ⇒ cnt' = 0
      have hfin : cuifFinish s = true := by
        cases hf : cuifFinish s <;> simp_all
      rw [cuif_cnt_step_at, if_pos ⟨hgu, rfl⟩, if_pos hfin]
    · rw [if_neg hua] at hlv'
      by_cases hla : cuifLoadNew s = true ∧
          g = cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
      · rw [if_pos hla] at hlv'; simp at hlv'
      · rw [if_neg hla] at hlv'
        rw [cuif_cnt_step_at, if_neg hua]
        exact hzero g hlv'
  · -- c8：UPDATE 拍的读数一致性
    intro hg'
    obtain ⟨hg, hf⟩ := cuif_step_gfsm_update s i hg'
    have e_cu : (cuifStep s i).cuReg = cuifChosenCu i := by
      show (if cuifArbFire s i then cuifChosenCu i else s.cuReg) = _; rw [if_pos hf]
    have e_slot : (cuifStep s i).slotReg = cuifTagSlot (cuifChosenTag i) := by
      show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
    have e_cntRd : (cuifStep s i).cntRd =
        s.cntMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) := by
      show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
    have e_infoRd : (cuifStep s i).infoRd =
        s.infoMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) := by
      show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
    have hlv : s.liveMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) = true :=
      hdoneE hf
    -- infoMem 在 g' 处不变（loadNew 目标 ≠ g'：g' live 而 loadNew 目标 ¬live）
    have hinfo : (cuifStep s i).infoMem
        (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) =
        s.infoMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) := by
      rw [cuif_info_step_at]
      by_cases hld : cuifLoadNew s = true ∧
          cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i)) =
            cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
      · obtain ⟨hlf, hgg⟩ := hld
        obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
        cases hfc : s.fifo with
        | nil => exact absurd hfc hfne
        | cons h0 t0 =>
          have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
          rw [hhead] at hgg
          have hlvH : s.liveMem (cuifGaddr h0.cuId h0.wgSlotId) = true := by
            rw [← hgg]; exact hlv
          obtain ⟨hcnt0, _⟩ := hlive6 h0 (by rw [hfc]; simp) hlvH
          exact absurd hc0 hcnt0
      · rw [if_neg hld]
    have hcntM : (cuifStep s i).cntMem
        (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) =
        s.cntMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) := by
      rw [cuif_cnt_step_at]
      rw [if_neg (fun h => by simp [hg] at h)]
    have hlv2 : (cuifStep s i).liveMem
        (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) = true := by
      rw [cuif_live_step_at]
      rw [if_neg (fun h => by simp [hg] at h)]
      by_cases hld : cuifLoadNew s = true ∧
          cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i)) =
            cuifGaddr (cuifHead s).cuId (cuifHead s).wgSlotId
      · obtain ⟨hlf, hgg⟩ := hld
        obtain ⟨hc0, hfne⟩ := cuif_loadNew_facts s hlf
        cases hfc : s.fifo with
        | nil => exact absurd hfc hfne
        | cons h0 t0 =>
          have hhead : cuifHead s = h0 := cuifHead_of_cons hfc
          rw [hhead] at hgg
          have hlvH : s.liveMem (cuifGaddr h0.cuId h0.wgSlotId) = true := by
            rw [← hgg]; exact hlv
          obtain ⟨hcnt0, _⟩ := hlive6 h0 (by rw [hfc]; simp) hlvH
          exact absurd hc0 hcnt0
      · rw [if_neg hld]; exact hlv
    refine ⟨?_, ?_, ?_⟩
    · rw [e_cu, e_slot, hcntM, e_cntRd]
    · rw [e_cu, e_slot, hinfo, e_infoRd]
    · rw [e_cu, e_slot, hlv2]
  · -- c9：DEALLOC ⇒ 完成计数恰好达到 numWf
    intro hg'
    have e : (cuifStep s i).gfsm = cuifGfsmNext s i := rfl
    rw [e] at hg'
    -- 进入/停留 DEALLOC 时 gather 寄存器均不变（arbFire 只在 GET_WF）
    have harbf : cuifArbFire s i = false →
        (cuifStep s i).cntRd = s.cntRd ∧ (cuifStep s i).infoRd = s.infoRd := by
      intro hf
      have hf' := (Bool.not_eq_true _).mpr hf
      exact ⟨by show (if cuifArbFire s i then _ else _) = _; rw [if_neg hf'],
             by show (if cuifArbFire s i then _ else _) = _; rw [if_neg hf']⟩
    cases hg : s.gfsm with
    | getWf =>
      simp only [cuifGfsmNext, hg] at hg'
      by_cases hf : cuifArbFire s i = true
      · rw [if_pos hf] at hg'; exact absurd hg' (by decide)
      · rw [if_neg hf] at hg'; exact absurd hg' (by decide)
    | update =>
      simp only [cuifGfsmNext, hg] at hg'
      by_cases hf : cuifFinish s = true
      · rw [hf] at hg'
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at hg'
        -- 寄存器保持（gfsm=update ⇒ ¬arbFire）
        have hf0 : cuifArbFire s i = false := by unfold cuifArbFire; simp [hg]
        obtain ⟨e_cntRd, e_infoRd⟩ := harbf hf0
        rw [e_cntRd, e_infoRd]
        obtain ⟨hcntR, hinfoR, hlv⟩ := hupd hg
        obtain ⟨hb1, hb8, hlt⟩ := hcnt _ hlv
        have hlt' : s.cntRd.toNat < 8 := by rw [hcntR]; omega
        have e2 : (s.cntRd + 1#4).toNat = s.cntRd.toNat + 1 := cuif_toNat_add_one (by omega)
        have hfin : s.cntRd + 1#4 = s.infoRd.numWf := by
          unfold cuifFinish at hf; rw [decide_eq_true_eq] at hf; exact hf
        have e3 := congrArg BitVec.toNat hfin
        rw [e2] at e3
        exact e3
      · rw [(Bool.not_eq_true _).mp hf] at hg'; simp at hg'
    | dealloc =>
      have hf0 : cuifArbFire s i = false := by unfold cuifArbFire; simp [hg]
      obtain ⟨e_cntRd, e_infoRd⟩ := harbf hf0
      rw [e_cntRd, e_infoRd]
      exact hdec hg

/-- 任意守约输入序列下不变式保持 -/
theorem cuifInv_run (ins : List CuifInputs)
    (henv : ∀ (pre : List CuifInputs) (i : CuifInputs), CuifEnvOk (cuifRun cuifInit pre) i) :
    CuifInv (cuifRun cuifInit ins) := by
  have key : ∀ l : List CuifInputs, CuifInv (cuifRun cuifInit l.reverse) := by
    intro l
    induction l with
    | nil => exact cuifInv_init
    | cons x xs ih =>
      have e2 : cuifRun cuifInit ((x :: xs).reverse) = cuifStep (cuifRun cuifInit xs.reverse) x := by
        simp [cuifRun, List.reverse_cons, List.foldl_append]
      rw [e2]
      exact cuifInv_step _ _ ih (henv _ _)
  have h := key ins.reverse
  rwa [List.reverse_reverse] at h

/- ========================================================================= -/
/- 7. 契约核销定理                                                             -/
/- ========================================================================= -/

/-- **H-CUIF-SPLIT（tag 分配 + 不超发）**：拆发中每个 cu_wf_new 的 wf_tag =
    {本 WG 槽位, 已发序号}（:108-112），且已发序号 < num_wf——恰好对应
    CtaScheduler 的 wfSent < numWf。 -/
theorem cuif_split_tag (s : CuifState) (h : CuifInv s) (hc : s.splitCnt ≠ 0#4) :
    ∃ h' t, s.fifo = h' :: t ∧
      cuifWfNewTag s = cuifWfTag h'.wgSlotId ((h'.numWf - s.splitCnt).extractLsb' 0 3) ∧
      (h'.numWf - s.splitCnt) < h'.numWf := by
  obtain ⟨_, _, _, _, hsplit, _⟩ := h
  obtain ⟨h', t, hft, hle⟩ := hsplit hc
  refine ⟨h', t, hft, ?_, ?_⟩
  · unfold cuifWfNewTag; rw [hft]
  · have hle' : s.splitCnt ≤ h'.numWf := hle
    exact cuif_sub_lt_self (cuif_one_le_of_ne_zero hc) hle'

/-- **H-CUIF-SPLIT（数量恰好）**：fifo 弹出拍 = 最后一个 WF 发出拍（:77），
    其 wf_id = num_wf - 1——不多不少正好 num_wf 个。 -/
theorem cuif_split_deq_last (s : CuifState) (i : CuifInputs) (hd : cuifDeqFire s i = true) :
    s.splitCnt = 1#4 ∧ ∃ h' t, s.fifo = h' :: t ∧
      cuifWfNewTag s = cuifWfTag h'.wgSlotId ((h'.numWf - 1#4).extractLsb' 0 3) := by
  unfold cuifDeqFire at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨h1, hm⟩ := hd
  refine ⟨h1, ?_⟩
  cases hf : s.fifo with
  | nil => rw [hf] at hm; simp at hm
  | cons h0 t0 =>
    refine ⟨h0, t0, rfl, ?_⟩
    unfold cuifWfNewTag
    rw [hf, h1]

/-- 计数逐拍递减（:80）：发一个少一个 -/
theorem cuif_split_countdown (s : CuifState) (i : CuifInputs) (hf : cuifWfFire s i = true) :
    (cuifStep s i).splitCnt = s.splitCnt - 1#4 := by
  obtain ⟨hc, _⟩ := cuif_wfFire_facts s i hf
  rw [cuif_splitCnt_step, if_pos hc, if_pos hf]

/-- 无 fire 则计数保持（反压正确回堵，:80） -/
theorem cuif_split_hold (s : CuifState) (i : CuifInputs)
    (hc : s.splitCnt ≠ 0#4) (hf : cuifWfFire s i = false) :
    (cuifStep s i).splitCnt = s.splitCnt := by
  rw [cuif_splitCnt_step, if_pos hc, if_neg ((Bool.not_eq_true _).mpr hf)]

/-- loadNew 装入 num_wf（:81） -/
theorem cuif_split_load (s : CuifState) (i : CuifInputs)
    (hc : s.splitCnt = 0#4) (h0 : CuifWg) (t0 : List CuifWg) (hf : s.fifo = h0 :: t0) :
    (cuifStep s i).splitCnt = h0.numWf := by
  rw [cuif_splitCnt_step, if_neg (fun h => h hc), hf]

/-- **H-CUIF-DONE（计数恰好）**：UPDATE 拍 finish ⟺ 该槽累计 done 数 +1 = num_wf；
    且在驻槽计数严格小于 num_wf（不超收）。 -/
theorem cuif_finish_exact (s : CuifState) (h : CuifInv s) (hg : s.gfsm = .update) :
    (s.cntMem (cuifGaddr s.cuReg s.slotReg)).toNat <
      (s.infoMem (cuifGaddr s.cuReg s.slotReg)).numWf.toNat ∧
    (cuifFinish s = true ↔
      (s.cntMem (cuifGaddr s.cuReg s.slotReg)).toNat + 1 =
        (s.infoMem (cuifGaddr s.cuReg s.slotReg)).numWf.toNat) := by
  obtain ⟨_, _, _, _, _, _, hcnt, _, hupd, _⟩ := h
  obtain ⟨hcntR, hinfoR, hlv⟩ := hupd hg
  obtain ⟨hb1, hb8, hlt⟩ := hcnt _ hlv
  constructor
  · exact hlt
  · unfold cuifFinish
    rw [decide_eq_true_eq]
    rw [← hcntR, ← hinfoR]
    constructor
    · intro hf
      have e := congrArg BitVec.toNat hf
      have e2 : (s.cntRd + 1#4).toNat = s.cntRd.toNat + 1 := by
        have hb : s.cntRd.toNat + 1 < 16 := by rw [hcntR]; omega
        exact cuif_toNat_add_one hb
      rw [e2] at e
      exact e
    · intro hf
      apply BitVec.toNat_inj.mp
      have e2 : (s.cntRd + 1#4).toNat = s.cntRd.toNat + 1 := by
        have hb : s.cntRd.toNat + 1 < 16 := by rw [hcntR]; omega
        exact cuif_toNat_add_one hb
      rw [e2]
      exact hf

/-- done 接收的读数（:160-176）：寄存器捕获 (cu, slot)、读出计数与记录 -/
theorem cuif_done_read (s : CuifState) (i : CuifInputs) (hf : cuifArbFire s i = true) :
    (cuifStep s i).cuReg = cuifChosenCu i ∧
    (cuifStep s i).slotReg = cuifTagSlot (cuifChosenTag i) ∧
    (cuifStep s i).cntRd =
      s.cntMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) ∧
    (cuifStep s i).infoRd =
      s.infoMem (cuifGaddr (cuifChosenCu i) (cuifTagSlot (cuifChosenTag i))) ∧
    (cuifStep s i).gfsm = .update := by
  have hg : s.gfsm = .getWf := cuif_arbFire_getWf hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
  · show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
  · show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
  · show (if cuifArbFire s i then _ else _) = _; rw [if_pos hf]
  · show cuifGfsmNext s i = .update
    unfold cuifGfsmNext; rw [hg]; exact if_pos hf

/-- UPDATE 拍的计数写回（:180-186）：finish 清零、否则 +1 -/
theorem cuif_cnt_update (s : CuifState) (i : CuifInputs) (hg : s.gfsm = .update) :
    (cuifStep s i).cntMem (cuifGaddr s.cuReg s.slotReg) =
      (if cuifFinish s then 0#4 else s.cntRd + 1#4) ∧
    (∀ g, g ≠ cuifGaddr s.cuReg s.slotReg → (cuifStep s i).cntMem g = s.cntMem g) := by
  constructor
  · rw [cuif_cnt_step_at, if_pos ⟨hg, rfl⟩]
  · intro g hne
    rw [cuif_cnt_step_at, if_neg (fun h => hne h.2)]

/-- **H-CUIF-DEALLOC（valid 的精确刻画，:204）** -/
theorem cuif_dealloc_valid_iff (s : CuifState) :
    cuifRtDeallocValid s = true ↔
      (s.gfsm = .update ∧ cuifFinish s = true) ∨ (s.gfsm = .dealloc ∧ s.rtOk = false) := by
  unfold cuifRtDeallocValid
  cases hg : s.gfsm <;> cases cuifFinish s <;> cases s.rtOk <;> simp

/-- **H-CUIF-DEALLOC（时机精确）**：rt_dealloc 有效 ⇒ 该 WG 完成计数恰好达到
    num_wf（既不过早——由 :179 的 finish 判定；也不漏——DEALLOC 状态由
    不变式保证同样性质）。 -/
theorem cuif_dealloc_exact (s : CuifState) (h : CuifInv s)
    (hv : cuifRtDeallocValid s = true) :
    s.cntRd.toNat + 1 = s.infoRd.numWf.toNat := by
  rcases (cuif_dealloc_valid_iff s).mp hv with ⟨hg, hf⟩ | ⟨hg, _⟩
  · obtain ⟨_, _, _, _, _, _, hcnt, _, hupd, _⟩ := h
    obtain ⟨hcntR, hinfoR, hlv⟩ := hupd hg
    obtain ⟨hb1, hb8, hlt⟩ := hcnt _ hlv
    unfold cuifFinish at hf
    rw [decide_eq_true_eq] at hf
    have e := congrArg BitVec.toNat hf
    have e2 : (s.cntRd + 1#4).toNat = s.cntRd.toNat + 1 := cuif_toNat_add_one (by rw [hcntR]; omega)
    rw [e2] at e
    exact e
  · exact h.2.2.2.2.2.2.2.2.2 hg

/-- **H-CUIF-DEALLOC（内容，:205-211）**：dealloc 上报的 (cu, slot, num_wf,
    dealloc_en) 全部取自该槽在驻记录的保持寄存器。 -/
theorem cuif_dealloc_bits (s : CuifState) :
    cuifDeallocBits s = (s.cuReg, s.slotReg, s.infoRd) := rfl

/-- **H-CUIF-DEALLOC（wgId 一致性）**：UPDATE 拍 infoRd 就是该槽 gather ram 的
    在驻记录（:174-175），其 wgId 即 host_wg_done/dealloc 上报的 wgId。 -/
theorem cuif_dealloc_wgId (s : CuifState) (h : CuifInv s) (hg : s.gfsm = .update) :
    s.infoRd = s.infoMem (cuifGaddr s.cuReg s.slotReg) :=
  (h.2.2.2.2.2.2.2.2.1 hg).2.1

/-- host_wg_done.valid 的精确刻画（:221）；与 rt_dealloc 同一 finish 触发 -/
theorem cuif_host_valid_iff (s : CuifState) :
    cuifHostDoneValid s = true ↔
      (s.gfsm = .update ∧ cuifFinish s = true) ∨ (s.gfsm = .dealloc ∧ s.hostOk = false) := by
  unfold cuifHostDoneValid
  cases hg : s.gfsm <;> cases cuifFinish s <;> cases s.hostOk <;> simp

/-- UPDATE 拍 rt_dealloc 与 host_wg_done 配对同发（:204,:221） -/
theorem cuif_host_paired (s : CuifState) (hg : s.gfsm = .update) :
    cuifHostDoneValid s = cuifRtDeallocValid s := by
  unfold cuifHostDoneValid cuifRtDeallocValid
  simp [hg]

/-- DEALLOC 状态重发至多各一次：fire 后 ok 置位、valid 即撤（:200-203,:204） -/
theorem cuif_dealloc_no_double (s : CuifState) (i : CuifInputs) (hg : s.gfsm = .dealloc)
    (hf : cuifRtFire s i = true) : cuifRtDeallocValid (cuifStep s i) = false := by
  have hok : (cuifStep s i).rtOk = true := by
    show cuifRtOkNext s i = true
    unfold cuifRtOkNext
    rw [if_neg (by simp [hg])]
    simp [hf]
  unfold cuifRtDeallocValid
  cases hgf : (cuifStep s i).gfsm with
  | update =>
    exact absurd (hg.symm.trans (cuif_step_gfsm_update s i hgf).1) (by decide)
  | getWf => simp
  | dealloc => simp [hok]

/- ========================================================================= -/
/- 8. 数值回归测试与 I-25 后果见证                                              -/
/- ========================================================================= -/

section CuifRegressionTests

/-- WG S：cu0 slot3，3 个 WF（拆分测试） -/
def cuifWgS : CuifWg := ⟨0#1, 3#3, 3#4, 0x5EED#32, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩
/-- WG D：cu0 slot1，2 个 WF（正常回收测试） -/
def cuifWgD : CuifWg := ⟨0#1, 1#3, 2#4, 0xAB#32, 0, 0, 0, 0, 0, 0, 0, true, true, false⟩
/-- WG A：cu0 slot2，2 个 WF（I-25 受害 WG） -/
def cuifWgA : CuifWg := ⟨0#1, 2#3, 2#4, 0xA0#32, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩
/-- WG B：cu0 slot5，1 个 WF（I-25 中被提前回收的 WG） -/
def cuifWgB : CuifWg := ⟨0#1, 5#3, 1#4, 0xB0#32, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩
/-- WG C：cu0 slot7，2 个 WF（I-25 计数残留的受害者） -/
def cuifWgC : CuifWg := ⟨0#1, 7#3, 2#4, 0xC0#32, 0, 0, 0, 0, 0, 0, 0, false, false, false⟩

-- T1 拆分：tag 恰好枚举 (slot, 0..numWf-1)，随后 fifo 弹出
def cuifTsplit : List CuifInputs := [
  { enqValid := true, enqWg := cuifWgS },   -- enq
  { cuRdy0 := true },                       -- loadNew：cnt ← 3
  { cuRdy0 := true },                       -- fire wf0
  { cuRdy0 := true },                       -- fire wf1
  { cuRdy0 := true }                        -- fire wf2 + deq
]
example : cuifWfNewTag (cuifRun cuifInit (cuifTsplit.take 2)) = 0x18#6 := by native_decide
example : cuifWfNewTag (cuifRun cuifInit (cuifTsplit.take 3)) = 0x19#6 := by native_decide
example : cuifWfNewTag (cuifRun cuifInit (cuifTsplit.take 4)) = 0x1A#6 := by native_decide
example : (cuifRun cuifInit cuifTsplit).splitCnt = 0#4 ∧
    (cuifRun cuifInit cuifTsplit).fifo = [] := by native_decide
example : (cuifRun cuifInit cuifTsplit).liveMem (cuifGaddr 0#1 3#3) = true ∧
    (cuifRun cuifInit cuifTsplit).cntMem (cuifGaddr 0#1 3#3) = 0#4 := by native_decide

-- T2 正常回收：恰好第 numWf 个 done 触发 finish，dealloc+host 同拍上报
def cuifTgather : List CuifInputs := [
  { enqValid := true, enqWg := cuifWgD },
  { cuRdy0 := true },
  { cuRdy0 := true },
  { cuRdy0 := true },                        -- 2 个 WF 发完
  { doneV0 := true, doneTag0 := 0x08#6 },    -- done wf0 → UPDATE
  {},                                        -- UPDATE：cnt 0→1，未 finish → GET_WF
  { doneV0 := true, doneTag0 := 0x09#6 },    -- done wf1 → UPDATE
  { rtRdy := true, hostRdy := true }         -- UPDATE：finish → 配对上报 → GET_WF
]
-- 未完成时不发 dealloc
example : (cuifRun cuifInit (cuifTgather.take 5)).gfsm = .update ∧
    cuifRtDeallocValid (cuifRun cuifInit (cuifTgather.take 5)) = false := by native_decide
-- 恰好第 2 个 done 的 UPDATE 拍：valid 置位、bits 正确
example : (cuifRun cuifInit (cuifTgather.take 7)).gfsm = .update ∧
    cuifRtDeallocValid (cuifRun cuifInit (cuifTgather.take 7)) = true ∧
    cuifHostDoneValid (cuifRun cuifInit (cuifTgather.take 7)) = true ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTgather.take 7))).1 = 0#1 ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTgather.take 7))).2.1 = 1#3 ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTgather.take 7))).2.2.wgId = 0xAB#32 ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTgather.take 7))).2.2.numWf = 2#4 := by
  native_decide
-- 回收后：cnt 清零、live 清除、FSM 回 GET_WF
example : (cuifRun cuifInit cuifTgather).gfsm = .getWf ∧
    (cuifRun cuifInit cuifTgather).cntMem (cuifGaddr 0#1 1#3) = 0#4 ∧
    (cuifRun cuifInit cuifTgather).liveMem (cuifGaddr 0#1 1#3) = false := by native_decide

-- T3 **I-25 见证（永缺 1 + 提前完成）**：A 的第二个 done 的 tag 被 CTA2warp
-- 污染成 B 的槽（CTA2warp.scala:77 迟读，03 报告 I-25）——B 从未有 warp 完成
-- 却被 dealloc，A 的计数永缺 1。
def cuifTi25Leak : List CuifInputs := [
  { enqValid := true, enqWg := cuifWgA },   -- 1
  { cuRdy0 := true },                       -- 2 load A
  { cuRdy0 := true },                       -- 3 fire (2,0)
  { cuRdy0 := true },                       -- 4 fire (2,1) + deq
  { enqValid := true, enqWg := cuifWgB },   -- 5
  { cuRdy0 := true },                       -- 6 load B
  { cuRdy0 := true },                       -- 7 fire (5,0) + deq
  { doneV0 := true, doneTag0 := 0x10#6 },   -- 8 done A wf0（tag 正确）→ UPDATE
  {},                                       -- 9 UPDATE：cnt[2] 0→1 → GET_WF
  { doneV0 := true, doneTag0 := 0x28#6 },   -- 10 A 的第 2 个 done，tag 被污染成槽 5
  { rtRdy := true, hostRdy := true }        -- 11 UPDATE：cnt[13]=0+1=1=numWf(B) → finish!
]
-- B 被提前回收：dealloc 上报的是 B（slot5、wgId=0xB0）
example : (cuifRun cuifInit (cuifTi25Leak.take 10)).gfsm = .update ∧
    cuifRtDeallocValid (cuifRun cuifInit (cuifTi25Leak.take 10)) = true ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTi25Leak.take 10))).2.1 = 5#3 ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTi25Leak.take 10))).2.2.wgId = 0xB0#32 := by
  native_decide
-- 终态：A 永缺 1（cnt=1≠2、live 永驻 → 槽位/资源/host 通知全泄漏），B 已释放
example : (cuifRun cuifInit cuifTi25Leak).cntMem (cuifGaddr 0#1 2#3) = 1#4 ∧
    (cuifRun cuifInit cuifTi25Leak).liveMem (cuifGaddr 0#1 2#3) = true ∧
    (cuifRun cuifInit cuifTi25Leak).liveMem (cuifGaddr 0#1 5#3) = false := by native_decide

-- T4 **I-25 见证（计数残留 → 下一个 WG 提前完成）**：污染 done 打到**空闲**槽
-- 会在 wf_gather_cnt 留下残留（load 不清零，:131-136 只写 info/valid），
-- 下一个分配到该槽的 WG 少收 1 个真实 done 即"完成"。
def cuifTi25Res : List CuifInputs := [
  { doneV0 := true, doneTag0 := 0x38#6 },   -- 1 污染 done 打到空闲槽 7 → UPDATE
  {},                                       -- 2 UPDATE：0+1≠0（初始 numWf=0）→ cnt[15]:=1
  { enqValid := true, enqWg := cuifWgC },   -- 3 C 分配到槽 7
  { cuRdy0 := true },                       -- 4 load C（cnt[15] 残留 1，不清）
  { cuRdy0 := true },                       -- 5 fire (7,0)
  { cuRdy0 := true },                       -- 6 fire (7,1) + deq
  { doneV0 := true, doneTag0 := 0x38#6 },   -- 7 C 的第 1 个真实 done → UPDATE
  { rtRdy := true, hostRdy := true }        -- 8 UPDATE：cntRd=1（残留）+1=2=numWf(C) → 提前完成
]
example : (cuifRun cuifInit (cuifTi25Res.take 2)).cntMem (cuifGaddr 0#1 7#3) = 1#4 := by
  native_decide
-- C 只完成了 1/2 个 warp 即被 dealloc
example : (cuifRun cuifInit (cuifTi25Res.take 7)).gfsm = .update ∧
    cuifRtDeallocValid (cuifRun cuifInit (cuifTi25Res.take 7)) = true ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTi25Res.take 7))).2.1 = 7#3 ∧
    (cuifDeallocBits (cuifRun cuifInit (cuifTi25Res.take 7))).2.2.wgId = 0xC0#32 := by
  native_decide
example : (cuifRun cuifInit cuifTi25Res).liveMem (cuifGaddr 0#1 7#3) = false ∧
    (cuifRun cuifInit cuifTi25Res).cntMem (cuifGaddr 0#1 7#3) = 0#4 := by native_decide

end CuifRegressionTests

/- 公理审计 -/
#print axioms cuif_split_tag
#print axioms cuif_split_deq_last
#print axioms cuif_split_countdown
#print axioms cuif_split_load
#print axioms cuif_finish_exact
#print axioms cuif_done_read
#print axioms cuif_cnt_update
#print axioms cuif_dealloc_exact
#print axioms cuif_dealloc_wgId
#print axioms cuif_dealloc_no_double
#print axioms cuifInv_step
#print axioms cuifInv_run

end Ventus.CTA
