/- ========================================================================= -/
/-                        CTA/Allocator.lean                                  -/
/-  CTA 分配器（allocator，含 rtcache_writer）的 Lean 4 逐拍模型               -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/allocator.scala          -/
/-    （rtcache_writer :61-100；allocator :102-383，全文）                     -/
/-  参数（top/parameters.scala:164-197）：NUM_CU=2 (:167)、NUM_WG_SLOT=8       -/
/-    (:169)、NUM_WF_SLOT=num_warp=8 (:170 经 :173)、NUM_SGPR_MAX=2048、       -/
/-    NUM_VGPR_MAX=1024、NUM_LDS_MAX=131072、RESOURCE_TABLE.NUM_RESULT=2       -/
/-    (:196)、DEBUG=true (:197)。                                              -/
/-  位宽：cu_id=1b、wg_slot_id=3b、num_wf=4b、num_sgpr=12b、num_vgpr=11b、     -/
/-    num_lds=18b、wfslot=4b、cu_cnt=2b、alloc_sel=1b。                        -/
/-                                                                           -/
/-  验证目标（CtasEventOk 黑盒契约核销，见 CtaScheduler.lean 第 3 节）：        -/
/-    H-ALLOC-SLOT（只分配空闲槽位，:270-271,:295）：定理 alc_h_alloc_slot      -/
/-    H-ALLOC-FIT （需求 ≤ 剩余才分配，:251-262；:91 断言不触发）：             -/
/-      定理 alc_h_alloc_fit / alc_assert91                                   -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 逐拍建模：状态 = 全部寄存器；step = 单拍纯函数（Chisel 语义：寄存器    -/
/-      读一律旧值，写当拍生效于下一拍）。                                      -/
/-  D2. RESOURCE_CHECK_CU_STEP=1（:124）且 NUM_CU=2：cu_check（:210-215）       -/
/-      在 STEP=1 时 begin==end，条件恒真（定理 alc_cu_check_always）⇒         -/
/-      resource_check_repeat 化简为"三个 rt_result 任一 fire"。               -/
/-      PriorityEncoder(1 位 resource_check_result) 恒 0 ⇒ 选中 CU = 当前 CU。  -/
/-  D3. 三个 rtcache_writer 的 alloc_en_r1 同驱动同初值，合并为一个寄存器。     -/
/-  D4. cuinterface_buf（:329，Queue entries=1 pipe=true）只以其 enq.ready     -/
/-      影响 allocator，建模为环境输入 cuifRdy；内容正确性属 cu_interface 侧。  -/
/-  D5. wg 号/wgram_addr/wg_id 只透传不影响分配决策，wg 寄存器只建模           -/
/-      num_wf/num_sgpr/num_vgpr/num_lds 四个字段。                           -/
/-  D6. 环境契约 AlcEnvOk（A1）：rt_dealloc 只回收在驻槽，num_wf 不超过该      -/
/-      CU 当前 wfslot 占用（否则 :296 的 4 位减法会回绕）。系统侧由            -/
/-      H-CUIF-DEALLOC + rt 簿记保证。                                        -/
/-                                                                           -/
/- ======================== 源码审查疑点（Q 区，上报主会话） ================== -/
/-  Q-ALC1. :289 dealloc.ready：ALLOC 首拍只允许同 CU 的 dealloc，异 CU 被     -/
/-      反压一拍。decoupled 无丢失，记录在案。                                  -/
/-  Q-ALC2. :295-296 alloc 与 dealloc 同拍同 CU：正确性依赖 dealloc 目标槽 ≠   -/
/-      新分配槽（同槽时 allocMask 经 OR 覆盖 dealloc 清除、wfslot 加减可能     -/
/-      回绕）。系统内由"rt 不会回收未启动 WG"保证，本模型并入 A1 假设。        -/
/-  Q-ALC3. :210-215 cu_check 在 STEP=1 恒真 ⇒ RESOURCE_CHECK 期间任何         -/
/-      rt_result 都重查当前 CU。保守而正确（即 H-ALLOC-FIT 的缓存一致性机制：  -/
/-      转入 ALLOC 的当拍必无 rt_result 写入，cache 与检查结果同源）。          -/
/-  Q-ALC4. :91 断言（alloc_rawdata.size(sel) ≥ alloc_size）只在仿真存在；     -/
/-      其恒成立由 alc_assert91 证明。                                          -/
/-  Q-ALC5. :230 PriorityEncoder(resource_check_result.asUInt)：STEP=1 时      -/
/-      输入仅 1 位，输出恒 0；该表达式在 STEP>1 时才是真的选择器。            -/
/-  Q-ALC6. :372 cuCnt(2b)+1 ≥ 2：cuCnt=1 即触发 REJECT，不会到 3 再回绕。     -/
/-      记录在案，非 bug。                                                      -/
/-  Q-ALC7. rtcache 与 rt 实际链表的时序一致性（缓存高估风险）依赖              -/
/-      resource_table 侧契约（CtaScheduler Q4），不在本文件范围；本文件证明     -/
/-      的是"分配决策相对 rtcache 内容不漏、不超"。                              -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

open Ventus.Base

/- ========================================================================= -/
/- 1. 常量、FSM、数据结构                                                      -/
/- ========================================================================= -/

/-- allocator 主 FSM（:172-174） -/
inductive AlcFsm where
  | idle | cuPrefer | resCheck | alloc | reject
  deriving DecidableEq, Repr

/-- WG 资源请求（io_buffer2alloc 的资源字段，D5；ctainfo_host_to_alloc） -/
structure AlcWgReq where
  numWf   : BitVec 4   -- num_wf，log2Ceil(NUM_WF_MAX+1)
  numSgpr : BitVec 12  -- num_sgpr，log2Ceil(2048+1)
  numVgpr : BitVec 11  -- num_vgpr，log2Ceil(1024+1)
  numLds  : BitVec 18  -- num_lds，log2Ceil(131072+1)
  deriving DecidableEq

/-- allocator 全部寄存器状态 -/
structure AlcState where
  fsm      : AlcFsm                          -- :176
  fsmR1    : AlcFsm                          -- :177
  wg       : AlcWgReq                        -- :187 RegEnable
  cuCnt    : BitVec 2                        -- :191
  cu       : BitVec 1                        -- :206（RegInit NUM_CU-1）
  wgslot   : Fin 2 → BitVec 8                -- :162 每 CU 的 WG 槽位占用位图
  wfslot   : Fin 2 → BitVec 4                -- :163 每 CU 的 WF 槽占用数
  wgslotId : BitVec 3                        -- :165
  wgslot1H : BitVec 8                        -- :166
  ldsSel   : BitVec 1                        -- :278
  sgprSel  : BitVec 1                        -- :279
  vgprSel  : BitVec 1                        -- :280
  rtReg    : Bool                            -- :316 alloc_task_rt_reg
  cuifReg  : Bool                            -- :328 alloc_task_cuinterface_reg
  wgram2Reg : Bool                           -- :344 alloc_task_wgram2_reg
  cacheLds : Fin 2 → Fin 2 → BitVec 18       -- :131 rtcache_lds（CU × 行）
  cacheSgpr : Fin 2 → Fin 2 → BitVec 12      -- :136
  cacheVgpr : Fin 2 → Fin 2 → BitVec 11      -- :141
  allocEnR1 : Bool                           -- :74 alloc_en_r1（三个 writer 合一，D3）

/-- 每拍环境输入（未建模字段取默认） -/
structure AlcInputs where
  wgNewValid : Bool := false                 -- io.wgbuffer_wg_new.valid
  wgNew : AlcWgReq := ⟨0, 0, 0, 0⟩
  resLdsV : Bool := false                    -- io.rt_result_lds.valid
  resLdsCu : BitVec 1 := 0
  resLds0 : BitVec 18 := 0                   -- rt_result.size(0)
  resLds1 : BitVec 18 := 0                   -- rt_result.size(1)
  resSgprV : Bool := false
  resSgprCu : BitVec 1 := 0
  resSgpr0 : BitVec 12 := 0
  resSgpr1 : BitVec 12 := 0
  resVgprV : Bool := false
  resVgprCu : BitVec 1 := 0
  resVgpr0 : BitVec 11 := 0
  resVgpr1 : BitVec 11 := 0
  deallocV : Bool := false                   -- io.rt_dealloc.valid
  deallocCu : BitVec 1 := 0
  deallocSlot : BitVec 3 := 0
  deallocNumWf : BitVec 4 := 0
  rtAllocRdy : Bool := true                  -- io.rt_alloc.ready
  cuifRdy : Bool := true                     -- cuinterface_buf enq.ready（D4）
  wgbufRdy : Bool := true                    -- io.wgbuffer_result.ready

/-- 复位初值（:131-145 每 CU 第 0 行 = MAX、其余 0；:206 cu=NUM_CU-1=1） -/
def alcInit : AlcState where
  fsm := .idle
  fsmR1 := .idle
  wg := ⟨0, 0, 0, 0⟩
  cuCnt := 0#2
  cu := 1#1
  wgslot := fun _ => 0#8
  wfslot := fun _ => 0#4
  wgslotId := 0#3
  wgslot1H := 0#8
  ldsSel := 0#1
  sgprSel := 0#1
  vgprSel := 0#1
  rtReg := false
  cuifReg := false
  wgram2Reg := false
  cacheLds := fun _ j => if j = 0 then 131072#18 else 0#18
  cacheSgpr := fun _ j => if j = 0 then 2048#12 else 0#12
  cacheVgpr := fun _ j => if j = 0 then 1024#11 else 0#11
  allocEnR1 := false

/- ========================================================================= -/
/- 2. 索引与优先编码器                                                         -/
/- ========================================================================= -/

/-- BitVec 1 → Fin 2 -/
def alcCuFin (c : BitVec 1) : Fin 2 := ⟨c.toNat, by have h := c.isLt; omega⟩

/-- alloc_sel（BitVec 1）→ rtcache 行号（Fin 2） -/
def alcSelFin (b : BitVec 1) : Fin 2 := alcCuFin b

theorem alcSelFin_zero : alcSelFin 0#1 = (0 : Fin 2) := by decide
theorem alcSelFin_one : alcSelFin 1#1 = (1 : Fin 2) := by decide

/-- Fin 2 函数写更新 -/
def alcUpd (f : Fin 2 → α) (c : Fin 2) (v : α) : Fin 2 → α :=
  fun x => if x = c then v else f x

/-- PriorityEncoder（:270，8 位）：最低置位位编号；全 0 → 0（此时不被消费）。
    语义同 CTA2warp.lean 的 c2wPriorityEnc（Chisel PriorityEncoder = 最低位）。 -/
def alcPE8 (u : BitVec 8) : BitVec 3 :=
  if (u >>> 0) &&& 1#8 = 1#8 then 0#3 else
  if (u >>> 1) &&& 1#8 = 1#8 then 1#3 else
  if (u >>> 2) &&& 1#8 = 1#8 then 2#3 else
  if (u >>> 3) &&& 1#8 = 1#8 then 3#3 else
  if (u >>> 4) &&& 1#8 = 1#8 then 4#3 else
  if (u >>> 5) &&& 1#8 = 1#8 then 5#3 else
  if (u >>> 6) &&& 1#8 = 1#8 then 6#3 else
  if (u >>> 7) &&& 1#8 = 1#8 then 7#3 else 0#3

/-- PriorityEncoderOH（:271）：最低置位位的 one-hot = u & (-u) -/
def alcPEOH8 (u : BitVec 8) : BitVec 8 := u &&& (0#8 - u)

theorem alcPEOH8_and (u : BitVec 8) : u &&& alcPEOH8 u = alcPEOH8 u := by
  unfold alcPEOH8; bv_decide

theorem alcPEOH8_ne_zero {u : BitVec 8} (h : u ≠ 0#8) : alcPEOH8 u ≠ 0#8 := by
  unfold alcPEOH8; bv_decide

/-- 选中的位在源字中必为 0 的补：u 与 PEOH(~~~u) 不交 -/
theorem alcPEOH8_compl (u : BitVec 8) : u &&& alcPEOH8 (~~~u) = 0#8 := by
  unfold alcPEOH8; bv_decide

/-- 1H 与 id 的一致性：wgslot_id_1H = 1 << wgslot_id（需非零；全 0 时 OH=0 而移位=1） -/
theorem alcPEOH8_eq_shift {u : BitVec 8} (h : u ≠ 0#8) :
    alcPEOH8 u = 1#8 <<< (alcPE8 u).zeroExtend 8 := by
  unfold alcPEOH8 alcPE8; bv_decide

/-- 非全 1 的补非零 -/
theorem alc_compl_ne_zero {u : BitVec 8} (h : u ≠ BitVec.allOnes 8) : ~~~u ≠ 0#8 := by
  bv_decide

/-- 选中位确实是空闲位（对应 :270 从 ~wgslot 选位） -/
theorem alcPE8_bit_set {u : BitVec 8} (h : u ≠ 0#8) :
    (u >>> (alcPE8 u).zeroExtend 8) &&& 1#8 = 1#8 := by
  unfold alcPE8; bv_decide

/-- cu_check（:210-215）在 STEP=1 时恒真（Q-ALC3） -/
theorem alc_cu_check_always (x c : BitVec 1) : x ≤ c ∨ c ≤ x := by bv_decide

/- ========================================================================= -/
/- 3. 组合信号（握手 fire、资源检查、任务完成）                                 -/
/- ========================================================================= -/

def alcAllocEn (s : AlcState) : Bool := decide (s.fsm = .alloc)          -- :299
def alcAllocFirstB (s : AlcState) : Bool :=
  decide (s.fsm = .alloc) && !decide (s.fsmR1 = .alloc)                  -- fsm =/= fsm_r1
def alcAllocWr (s : AlcState) : Bool := alcAllocEn s && !s.allocEnR1     -- :75 posedge

/-- :188 wgbuffer_wg_new.ready = (fsm == IDLE) -/
def alcWgNewFire (s : AlcState) (i : AlcInputs) : Bool :=
  i.wgNewValid && decide (s.fsm = .idle)

/-- :80 rt_result.ready（三个 writer 同一形式） -/
def alcWriterRdy (s : AlcState) (resCu : BitVec 1) : Bool :=
  !alcAllocEn s || (!alcAllocWr s && decide (resCu ≠ s.cu))

def alcResFireLds (s : AlcState) (i : AlcInputs) : Bool :=
  i.resLdsV && alcWriterRdy s i.resLdsCu
def alcResFireSgpr (s : AlcState) (i : AlcInputs) : Bool :=
  i.resSgprV && alcWriterRdy s i.resSgprCu
def alcResFireVgpr (s : AlcState) (i : AlcInputs) : Bool :=
  i.resVgprV && alcWriterRdy s i.resVgprCu

/-- :289 rt_dealloc.ready -/
def alcDeallocRdy (s : AlcState) (i : AlcInputs) : Bool :=
  !alcAllocFirstB s || decide (i.deallocCu = s.cu)
def alcDeallocFire (s : AlcState) (i : AlcInputs) : Bool :=
  i.deallocV && alcDeallocRdy s i

/-- :317,:325 rt_alloc -/
def alcRtAllocFire (s : AlcState) (i : AlcInputs) : Bool :=
  decide (s.fsm = .alloc) && !s.rtReg && i.rtAllocRdy
/-- :330,:338-339 cuinterface_buf enq -/
def alcCuifFire (s : AlcState) (i : AlcInputs) : Bool :=
  decide (s.fsm = .alloc) && !s.cuifReg && i.cuifRdy
/-- :345,:353 wgbuffer_result -/
def alcWgbufFire (s : AlcState) (i : AlcInputs) : Bool :=
  (decide (s.fsm = .alloc) || decide (s.fsm = .reject)) && !s.wgram2Reg && i.wgbufRdy

/-- :283-286 三个 ALLOC 任务全部完成 -/
def alcTaskOk (s : AlcState) (i : AlcInputs) : Bool :=
  (s.rtReg || alcRtAllocFire s i) && (s.wgram2Reg || alcWgbufFire s i) &&
  (s.cuifReg || alcCuifFire s i)

/-- :251-253 单行资源检查 -/
def alcLineOkLds (s : AlcState) (j : Fin 2) : Bool :=
  decide (s.cacheLds (alcCuFin s.cu) j ≥ s.wg.numLds)
def alcLineOkSgpr (s : AlcState) (j : Fin 2) : Bool :=
  decide (s.cacheSgpr (alcCuFin s.cu) j ≥ s.wg.numSgpr)
def alcLineOkVgpr (s : AlcState) (j : Fin 2) : Bool :=
  decide (s.cacheVgpr (alcCuFin s.cu) j ≥ s.wg.numVgpr)

def alcOrLds (s : AlcState) : Bool := alcLineOkLds s 0 || alcLineOkLds s 1
def alcOrSgpr (s : AlcState) : Bool := alcLineOkSgpr s 0 || alcLineOkSgpr s 1
def alcOrVgpr (s : AlcState) : Bool := alcLineOkVgpr s 0 || alcLineOkVgpr s 1

/-- :257-259 PriorityMux（高行优先；都不满足时默认 0，但此时 result=0 不被消费） -/
def alcSelLds (s : AlcState) : BitVec 1 := if alcLineOkLds s 1 then 1#1 else 0#1
def alcSelSgpr (s : AlcState) : BitVec 1 := if alcLineOkSgpr s 1 then 1#1 else 0#1
def alcSelVgpr (s : AlcState) : BitVec 1 := if alcLineOkVgpr s 1 then 1#1 else 0#1

/-- :261-263 资源检查通过（含槽位与 WF 数） -/
def alcResult (s : AlcState) : Bool :=
  alcOrLds s && alcOrSgpr s && alcOrVgpr s &&
  (s.wgslot (alcCuFin s.cu) != BitVec.allOnes 8) &&
  decide ((8#4 - s.wfslot (alcCuFin s.cu)) ≥ s.wg.numWf)

/-- :216-219（STEP=1 化简，Q-ALC3）：任何 rt_result fire 都重查 -/
def alcRepeat (s : AlcState) (i : AlcInputs) : Bool :=
  alcResFireLds s i || alcResFireSgpr s i || alcResFireVgpr s i

/-- :360-381 fsm_next -/
def alcFsmNext (s : AlcState) (i : AlcInputs) : AlcFsm :=
  match s.fsm with
  | .idle => if alcWgNewFire s i then .cuPrefer else .idle
  | .cuPrefer => .resCheck
  | .resCheck =>
      if alcRepeat s i then .resCheck
      else if alcResult s then .alloc
      else if (s.cuCnt + 1#2) ≥ 2#2 then .reject
      else .resCheck
  | .reject => if alcWgbufFire s i then .idle else .reject
  | .alloc => if alcTaskOk s i then .idle else .alloc

/-- :221-239 cu 更新（PE(1 位结果)=0，Q-ALC5；模 2 = 1 位回绕） -/
def alcCuNext (s : AlcState) (i : AlcInputs) : BitVec 1 :=
  match s.fsm with
  | .cuPrefer => s.cu + 1#1
  | .resCheck =>
      if alcFsmNext s i = .alloc then s.cu
      else if alcRepeat s i then s.cu
      else s.cu + 1#1
  | _ => s.cu

/-- :294 cu_tmp -/
def alcCuTmp (s : AlcState) (i : AlcInputs) : Fin 2 :=
  if alcAllocFirstB s then alcCuFin s.cu else alcCuFin i.deallocCu

/-- :290-291 wgslot 更新位掩码 -/
def alcAllocMask (s : AlcState) : BitVec 8 :=
  if alcAllocFirstB s then s.wgslot1H else 0#8
def alcDeallocMask (s : AlcState) (i : AlcInputs) : BitVec 8 :=
  if alcDeallocFire s i then 1#8 <<< i.deallocSlot.zeroExtend 8 else 0#8

/-- :295 wgslot 更新 -/
def alcWgslotNext (s : AlcState) (i : AlcInputs) : Fin 2 → BitVec 8 :=
  alcUpd s.wgslot (alcCuTmp s i)
    ((s.wgslot (alcCuTmp s i) &&& ~~~(alcDeallocMask s i)) ||| alcAllocMask s)

/-- :296 wfslot 更新 -/
def alcWfslotNext (s : AlcState) (i : AlcInputs) : Fin 2 → BitVec 4 :=
  alcUpd s.wfslot (alcCuTmp s i)
    (s.wfslot (alcCuTmp s i) + (if alcAllocFirstB s then s.wg.numWf else 0#4)
      - (if alcDeallocFire s i then i.deallocNumWf else 0#4))

/-- rtcache_writer 主功能（:86-99）：allocWr 优先于 rt_result（互斥，:80） -/
def alcCacheNext (cache : Fin 2 → Fin 2 → BitVec w) (s : AlcState)
    (fire : Bool) (resCu : BitVec 1) (res0 res1 : BitVec w) (size : BitVec w) (sel : BitVec 1) :
    Fin 2 → Fin 2 → BitVec w :=
  if alcAllocWr s then
    alcUpd cache (alcCuFin s.cu)
      (fun j => cache (alcCuFin s.cu) j - (if j = alcSelFin sel then size else 0))
  else if fire then
    alcUpd cache (alcCuFin resCu) (fun j => if j = 0 then res0 else res1)
  else cache

/- ========================================================================= -/
/- 4. 单拍 step 与多拍 run                                                     -/
/- ========================================================================= -/

def alcStep (s : AlcState) (i : AlcInputs) : AlcState where
  fsm := alcFsmNext s i
  fsmR1 := s.fsm
  wg := if alcWgNewFire s i then i.wgNew else s.wg
  cuCnt := match s.fsm with
    | .cuPrefer => 0#2                 -- :195（fsm_next 恒为 RESOURCE_CHECK）
    | .resCheck => s.cuCnt + 1#2       -- :199
    | _ => s.cuCnt
  cu := alcCuNext s i
  wgslot := alcWgslotNext s i
  wfslot := alcWfslotNext s i
  wgslotId := if s.fsm = .resCheck then alcPE8 (~~~(s.wgslot (alcCuFin (alcCuNext s i)))) else s.wgslotId   -- :270
  wgslot1H := if s.fsm = .resCheck then alcPEOH8 (~~~(s.wgslot (alcCuFin (alcCuNext s i)))) else s.wgslot1H -- :271
  ldsSel := if s.fsm = .resCheck then alcSelLds s else s.ldsSel     -- :278
  sgprSel := if s.fsm = .resCheck then alcSelSgpr s else s.sgprSel  -- :279
  vgprSel := if s.fsm = .resCheck then alcSelVgpr s else s.vgprSel  -- :280
  rtReg := if s.fsm = .alloc then s.rtReg || (alcRtAllocFire s i && !alcTaskOk s i) else false     -- :324
  cuifReg := if s.fsm = .alloc then s.cuifReg || (alcCuifFire s i && !alcTaskOk s i) else false    -- :338
  wgram2Reg := if s.fsm = .alloc || s.fsm = .reject then
      s.wgram2Reg || (alcWgbufFire s i && !alcTaskOk s i) else false                               -- :349-352
  cacheLds := alcCacheNext s.cacheLds s (alcResFireLds s i) i.resLdsCu i.resLds0 i.resLds1 s.wg.numLds s.ldsSel
  cacheSgpr := alcCacheNext s.cacheSgpr s (alcResFireSgpr s i) i.resSgprCu i.resSgpr0 i.resSgpr1 s.wg.numSgpr s.sgprSel
  cacheVgpr := alcCacheNext s.cacheVgpr s (alcResFireVgpr s i) i.resVgprCu i.resVgpr0 i.resVgpr1 s.wg.numVgpr s.vgprSel
  allocEnR1 := alcAllocEn s          -- :74 RegNext

def alcRun (s : AlcState) (ins : List AlcInputs) : AlcState := ins.foldl alcStep s

/- ========================================================================= -/
/- 5. 环境契约与不变式                                                          -/
/- ========================================================================= -/

/-- A1（D6/Q-ALC2）：rt_dealloc 只回收在驻槽——扣减的 wf 数不超过该 CU 当前占用 -/
def AlcEnvOk (s : AlcState) (i : AlcInputs) : Prop :=
  alcDeallocFire s i = true → i.deallocNumWf ≤ s.wfslot (alcCuFin i.deallocCu)

/-- 不变式：ALLOC 首拍（分配决策生效拍）槽位空闲 + 资源足够 + wfslot 有界 -/
def AlcInv (s : AlcState) : Prop :=
  (s.allocEnR1 = decide (s.fsmR1 = .alloc)) ∧
  (∀ c, s.wfslot c ≤ 8#4) ∧
  (s.fsm = .alloc → s.fsmR1 ≠ .alloc →
    s.wgslot1H ≠ 0#8 ∧
    (s.wgslot (alcCuFin s.cu)) &&& s.wgslot1H = 0#8 ∧
    s.wgslot1H = 1#8 <<< s.wgslotId.zeroExtend 8 ∧
    s.cacheLds (alcCuFin s.cu) (alcSelFin s.ldsSel) ≥ s.wg.numLds ∧
    s.cacheSgpr (alcCuFin s.cu) (alcSelFin s.sgprSel) ≥ s.wg.numSgpr ∧
    s.cacheVgpr (alcCuFin s.cu) (alcSelFin s.vgprSel) ≥ s.wg.numVgpr ∧
    (8#4 - s.wfslot (alcCuFin s.cu)) ≥ s.wg.numWf)

/- ========================================================================= -/
/- 6. 支撑引理                                                                 -/
/- ========================================================================= -/

/-- 转入 ALLOC 只能来自 RESOURCE_CHECK，且当拍无重查、检查通过 -/
theorem alcFsmNext_eq_alloc (s : AlcState) (i : AlcInputs)
    (h : alcFsmNext s i = .alloc) (hf : s.fsm ≠ .alloc) :
    s.fsm = .resCheck ∧ alcRepeat s i = false ∧ alcResult s = true := by
  cases hfsm : s.fsm with
  | idle =>
    simp only [alcFsmNext, hfsm] at h
    by_cases hw : alcWgNewFire s i = true <;> simp [hw] at h
  | cuPrefer => simp [alcFsmNext, hfsm] at h
  | reject =>
    simp only [alcFsmNext, hfsm] at h
    by_cases hw : alcWgbufFire s i = true <;> simp [hw] at h
  | alloc => exact absurd hfsm hf
  | resCheck =>
    have hrep' : alcRepeat s i = false := by
      cases hr : alcRepeat s i with
      | true => simp [alcFsmNext, hfsm, hr] at h
      | false => rfl
    have hres' : alcResult s = true := by
      cases hr : alcResult s with
      | true => rfl
      | false =>
        simp only [alcFsmNext, hfsm, hrep', hr, Bool.false_eq_true, if_false] at h
        by_cases hc : (s.cuCnt + 1#2) ≥ 2#2 <;> simp [hc] at h
    exact ⟨rfl, hrep', hres'⟩

/-- RESOURCE_CHECK → ALLOC 时 cu 保持（PE=0，Q-ALC5） -/
theorem alcCuNext_of_alloc (s : AlcState) (i : AlcInputs)
    (hrc : s.fsm = .resCheck) (h : alcFsmNext s i = .alloc) : alcCuNext s i = s.cu := by
  simp [alcCuNext, hrc, h]

/-- 非 IDLE 不取新 WG -/
theorem alcWgNewFire_ne_idle {s : AlcState} {i : AlcInputs} (hf : s.fsm ≠ .idle) :
    alcWgNewFire s i = false := by
  unfold alcWgNewFire
  cases h : s.fsm <;> simp_all

/-- 非 ALLOC 无 allocWr -/
theorem alcAllocWr_not_alloc {s : AlcState} (hf : s.fsm ≠ .alloc) : alcAllocWr s = false := by
  unfold alcAllocWr alcAllocEn; simp [hf]

/-- 非 ALLOC 首拍（fsm ≠ alloc）时 allocMask = 0、cuTmp = deallocCu -/
theorem alcAllocMask_not_first {s : AlcState} (hf : s.fsm ≠ .alloc) : alcAllocMask s = 0#8 := by
  unfold alcAllocMask alcAllocFirstB; simp [hf]

theorem alcCuTmp_not_first {s : AlcState} {i : AlcInputs} (hf : s.fsm ≠ .alloc) :
    alcCuTmp s i = alcCuFin i.deallocCu := by
  unfold alcCuTmp alcAllocFirstB; simp [hf]

/-- sel 选择的行必满足检查（PriorityMux 语义，:257-259） -/
theorem alc_sel_lds_ok (s : AlcState) (h : alcOrLds s = true) :
    s.cacheLds (alcCuFin s.cu) (alcSelFin (alcSelLds s)) ≥ s.wg.numLds := by
  unfold alcOrLds at h
  unfold alcSelLds
  by_cases h1 : alcLineOkLds s 1 = true
  · rw [if_pos h1, alcSelFin_one]
    exact of_decide_eq_true h1
  · have h1f : alcLineOkLds s 1 = false := (Bool.not_eq_true _).mp h1
    rw [if_neg h1, alcSelFin_zero]
    have h0 : alcLineOkLds s 0 = true := by
      simp only [h1f, Bool.or_false] at h
      exact h
    exact of_decide_eq_true h0

theorem alc_sel_sgpr_ok (s : AlcState) (h : alcOrSgpr s = true) :
    s.cacheSgpr (alcCuFin s.cu) (alcSelFin (alcSelSgpr s)) ≥ s.wg.numSgpr := by
  unfold alcOrSgpr at h
  unfold alcSelSgpr
  by_cases h1 : alcLineOkSgpr s 1 = true
  · rw [if_pos h1, alcSelFin_one]
    exact of_decide_eq_true h1
  · have h1f : alcLineOkSgpr s 1 = false := (Bool.not_eq_true _).mp h1
    rw [if_neg h1, alcSelFin_zero]
    have h0 : alcLineOkSgpr s 0 = true := by
      simp only [h1f, Bool.or_false] at h
      exact h
    exact of_decide_eq_true h0

theorem alc_sel_vgpr_ok (s : AlcState) (h : alcOrVgpr s = true) :
    s.cacheVgpr (alcCuFin s.cu) (alcSelFin (alcSelVgpr s)) ≥ s.wg.numVgpr := by
  unfold alcOrVgpr at h
  unfold alcSelVgpr
  by_cases h1 : alcLineOkVgpr s 1 = true
  · rw [if_pos h1, alcSelFin_one]
    exact of_decide_eq_true h1
  · have h1f : alcLineOkVgpr s 1 = false := (Bool.not_eq_true _).mp h1
    rw [if_neg h1, alcSelFin_zero]
    have h0 : alcLineOkVgpr s 0 = true := by
      simp only [h1f, Bool.or_false] at h
      exact h
    exact of_decide_eq_true h0

/-- 位运算引理：清更多位仍与 p 不交 -/
theorem alc_and_and_compl {w dm p : BitVec 8} (h : w &&& p = 0#8) :
    (w &&& ~~~dm) &&& p = 0#8 := by bv_decide

theorem alc_or_zero (x : BitVec 8) : x ||| 0#8 = x := by bv_decide

/-- wfslot 拟合保持：dealloc 只腾不占（A1 防回绕） -/
theorem alc_wf_fit_dealloc {old d n : BitVec 4} (h1 : 8#4 - old ≥ n) (h2 : old ≤ 8#4)
    (h3 : d ≤ old) : 8#4 - (old - d) ≥ n := by bv_decide

/-- wfslot 有界保持：ALLOC 首拍加 numWf -/
theorem alc_wf_bound_alloc {old d n : BitVec 4} (h1 : 8#4 - old ≥ n) (h2 : old ≤ 8#4)
    (h3 : d ≤ old) : old + n - d ≤ 8#4 := by bv_decide

/-- wfslot 有界保持：纯 dealloc 拍 -/
theorem alc_wf_bound_sub {old d : BitVec 4} (h2 : old ≤ 8#4) (h3 : d ≤ old) :
    old - d ≤ 8#4 := by bv_decide

theorem alc_add_zero4 (x : BitVec 4) : x + 0#4 = x := by bv_decide

/-- A1 + ready 门控推出当拍扣减量 ≤ cuTmp 占用 -/
theorem alc_dealloc_le (s : AlcState) (i : AlcInputs) (henv : AlcEnvOk s i) :
    (if alcDeallocFire s i then i.deallocNumWf else 0#4) ≤ s.wfslot (alcCuTmp s i) := by
  by_cases hf : alcDeallocFire s i = true
  · rw [if_pos hf]
    by_cases hfirst : alcAllocFirstB s = true
    · -- ALLOC 首拍：fire ⇒ deallocCu = cu（:289）
      have hcu : i.deallocCu = s.cu := by
        unfold alcDeallocFire alcDeallocRdy at hf
        simp [hfirst] at hf
        exact hf.2
      have h2 : alcCuTmp s i = alcCuFin i.deallocCu := by
        unfold alcCuTmp; rw [if_pos hfirst, ← hcu]
      rw [h2]; exact henv hf
    · have h2 : alcCuTmp s i = alcCuFin i.deallocCu := by
        unfold alcCuTmp; rw [if_neg hfirst]
      rw [h2]; exact henv hf
  · rw [if_neg hf]; bv_decide

/- ========================================================================= -/
/- 7. 主定理：不变式保持（H-ALLOC-SLOT / H-ALLOC-FIT 的归纳核心）                -/
/- ========================================================================= -/

theorem alcInv_init : AlcInv alcInit := by
  refine ⟨rfl, ?_, ?_⟩
  · intro c; show (0#4 : BitVec 4) ≤ 8#4; bv_decide
  · intro h; exact absurd h (by decide)

theorem alcInv_step (s : AlcState) (i : AlcInputs)
    (hinv : AlcInv s) (henv : AlcEnvOk s i) : AlcInv (alcStep s i) := by
  obtain ⟨hen1, hbound, hfirst⟩ := hinv
  have hdle := alc_dealloc_le s i henv
  refine ⟨?_, ?_, ?_⟩
  · -- allocEnR1 = decide (fsmR1 = alloc)
    show alcAllocEn s = decide (s.fsm = .alloc)
    rfl
  · -- wfslot ≤ 8 保持
    intro c
    show (alcWfslotNext s i c) ≤ 8#4
    unfold alcWfslotNext alcUpd
    by_cases hc : c = alcCuTmp s i
    · rw [if_pos hc]
      by_cases hfa : alcAllocFirstB s = true
      · -- ALLOC 首拍：old + numWf - d
        have hfa' : s.fsm = .alloc ∧ s.fsmR1 ≠ .alloc := by
          unfold alcAllocFirstB at hfa
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not] at hfa
          exact hfa
        obtain ⟨_, _, _, _, _, _, hwf⟩ := hfirst hfa'.1 hfa'.2
        rw [if_pos hfa]
        have htmp2 : alcCuTmp s i = alcCuFin s.cu := by unfold alcCuTmp; rw [if_pos hfa]
        have hb := hbound (alcCuTmp s i)
        rw [htmp2] at hb hdle ⊢
        exact alc_wf_bound_alloc hwf hb hdle
      · -- 纯 dealloc 拍
        rw [if_neg hfa, alc_add_zero4]
        have hb := hbound (alcCuTmp s i)
        exact alc_wf_bound_sub hb hdle
    · rw [if_neg hc]; exact hbound c
  · -- ALLOC 首拍性质
    intro hfsm hfsmr1
    have hnext : alcFsmNext s i = .alloc := hfsm
    have hfne : s.fsm ≠ .alloc := by
      have : (alcStep s i).fsmR1 = s.fsm := rfl
      rw [this] at hfsmr1; exact hfsmr1
    obtain ⟨hrc, hrep, hres⟩ := alcFsmNext_eq_alloc s i hnext hfne
    -- 当前拍为 RESOURCE_CHECK：无 resFire、无 allocWr、wg/cu 不变
    have hnofire : alcResFireLds s i = false ∧ alcResFireSgpr s i = false ∧
        alcResFireVgpr s i = false := by
      have h := hrep
      unfold alcRepeat at h
      cases h1 : alcResFireLds s i <;> cases h2 : alcResFireSgpr s i <;>
        cases h3 : alcResFireVgpr s i <;> simp_all
    obtain ⟨hfl, hfs, hfv⟩ := hnofire
    have hwr : alcAllocWr s = false := alcAllocWr_not_alloc (by simp [hrc])
    have hcu : alcCuNext s i = s.cu := alcCuNext_of_alloc s i hrc hnext
    have hwg : alcWgNewFire s i = false := alcWgNewFire_ne_idle (by simp [hrc])
    have hnf : s.fsm ≠ .alloc := by simp [hrc]
    have hmask : alcAllocMask s = 0#8 := alcAllocMask_not_first hnf
    have htmp : alcCuTmp s i = alcCuFin i.deallocCu := alcCuTmp_not_first hnf
    -- 投影等式
    have e_cu : (alcStep s i).cu = s.cu := by
      show alcCuNext s i = s.cu; exact hcu
    have e_wg : (alcStep s i).wg = s.wg := by
      show (if alcWgNewFire s i then i.wgNew else s.wg) = s.wg
      simp [hwg]
    have e_1H : (alcStep s i).wgslot1H = alcPEOH8 (~~~(s.wgslot (alcCuFin s.cu))) := by
      show (if s.fsm = .resCheck then alcPEOH8 (~~~(s.wgslot (alcCuFin (alcCuNext s i)))) else s.wgslot1H) = _
      rw [if_pos hrc, hcu]
    have e_id : (alcStep s i).wgslotId = alcPE8 (~~~(s.wgslot (alcCuFin s.cu))) := by
      show (if s.fsm = .resCheck then alcPE8 (~~~(s.wgslot (alcCuFin (alcCuNext s i)))) else s.wgslotId) = _
      rw [if_pos hrc, hcu]
    have e_sell : (alcStep s i).ldsSel = alcSelLds s := by
      show (if s.fsm = .resCheck then alcSelLds s else s.ldsSel) = _; rw [if_pos hrc]
    have e_sels : (alcStep s i).sgprSel = alcSelSgpr s := by
      show (if s.fsm = .resCheck then alcSelSgpr s else s.sgprSel) = _; rw [if_pos hrc]
    have e_selv : (alcStep s i).vgprSel = alcSelVgpr s := by
      show (if s.fsm = .resCheck then alcSelVgpr s else s.vgprSel) = _; rw [if_pos hrc]
    have e_cl : (alcStep s i).cacheLds = s.cacheLds := by
      show alcCacheNext s.cacheLds s (alcResFireLds s i) _ _ _ _ _ = s.cacheLds
      unfold alcCacheNext; rw [hwr, hfl]; simp
    have e_cs : (alcStep s i).cacheSgpr = s.cacheSgpr := by
      show alcCacheNext s.cacheSgpr s (alcResFireSgpr s i) _ _ _ _ _ = s.cacheSgpr
      unfold alcCacheNext; rw [hwr, hfs]; simp
    have e_cv : (alcStep s i).cacheVgpr = s.cacheVgpr := by
      show alcCacheNext s.cacheVgpr s (alcResFireVgpr s i) _ _ _ _ _ = s.cacheVgpr
      unfold alcCacheNext; rw [hwr, hfv]; simp
    -- 检查结果展开
    have hres5 := hres
    unfold alcResult at hres5
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hres5
    have hL : alcOrLds s = true := hres5.1.1.1.1
    have hS : alcOrSgpr s = true := hres5.1.1.1.2
    have hV : alcOrVgpr s = true := hres5.1.1.2
    have hslot : s.wgslot (alcCuFin s.cu) ≠ BitVec.allOnes 8 := hres5.1.2
    have hwf8 : (8#4 - s.wfslot (alcCuFin s.cu)) ≥ s.wg.numWf := hres5.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- wgslot1H ≠ 0
      rw [e_1H]
      exact alcPEOH8_ne_zero (alc_compl_ne_zero hslot)
    · -- wgslot' &&& 1H' = 0
      rw [e_cu, e_1H]
      have h0 := alcPEOH8_compl (s.wgslot (alcCuFin s.cu))
      show (alcWgslotNext s i) (alcCuFin s.cu) &&& alcPEOH8 (~~~(s.wgslot (alcCuFin s.cu))) = 0#8
      unfold alcWgslotNext alcUpd
      by_cases hc : alcCuFin s.cu = alcCuTmp s i
      · rw [if_pos hc, hmask, alc_or_zero]
        have : s.wgslot (alcCuTmp s i) = s.wgslot (alcCuFin s.cu) := by rw [← hc]
        rw [this]
        exact alc_and_and_compl h0
      · rw [if_neg hc]
        exact h0
    · -- 1H = 1 <<< id（:270-271 同源于 ~wgslot）
      rw [e_1H, e_id]
      exact alcPEOH8_eq_shift (alc_compl_ne_zero hslot)
    · -- lds fit
      rw [e_cu, e_cl, e_sell, e_wg]
      exact alc_sel_lds_ok s hL
    · -- sgpr fit
      rw [e_cu, e_cs, e_sels, e_wg]
      exact alc_sel_sgpr_ok s hS
    · -- vgpr fit
      rw [e_cu, e_cv, e_selv, e_wg]
      exact alc_sel_vgpr_ok s hV
    · -- wf fit
      rw [e_cu, e_wg]
      show (8#4 - alcWfslotNext s i (alcCuFin s.cu)) ≥ s.wg.numWf
      unfold alcWfslotNext alcUpd
      by_cases hc : alcCuFin s.cu = alcCuTmp s i
      · rw [if_pos hc]
        have hfa : ¬ (alcAllocFirstB s = true) := by
          unfold alcAllocFirstB; simp [hnf]
        rw [if_neg hfa]
        rw [alc_add_zero4]
        have hb : s.wfslot (alcCuTmp s i) ≤ 8#4 := hbound _
        have hce : s.wfslot (alcCuTmp s i) = s.wfslot (alcCuFin s.cu) := by rw [← hc]
        rw [hce] at hdle hb ⊢
        exact alc_wf_fit_dealloc hwf8 hb hdle
      · rw [if_neg hc]
        exact hwf8

/-- 任意守约输入序列下不变式保持 -/
theorem alcInv_run (ins : List AlcInputs)
    (henv : ∀ (pre : List AlcInputs) (i : AlcInputs), AlcEnvOk (alcRun alcInit pre) i) :
    AlcInv (alcRun alcInit ins) := by
  have key : ∀ l : List AlcInputs, AlcInv (alcRun alcInit l.reverse) := by
    intro l
    induction l with
    | nil => exact alcInv_init
    | cons x xs ih =>
      have e2 : alcRun alcInit ((x :: xs).reverse) = alcStep (alcRun alcInit xs.reverse) x := by
        simp [alcRun, List.reverse_cons, List.foldl_append]
      rw [e2]
      exact alcInv_step _ _ ih (henv _ _)
  have h := key ins.reverse
  rwa [List.reverse_reverse] at h

/- ========================================================================= -/
/- 8. 契约核销定理                                                             -/
/- ========================================================================= -/

/-- **H-ALLOC-SLOT 核销**：任何满足不变式的状态，ALLOC 首拍（:295 置位拍）
    选中的槽位 one-hot 非零、与已占用位图不交（只分配空闲槽位），且下发给
    rt 的 wg_slot_id（:319）正指向该空闲位。可达性由 alcInv_run 提供。 -/
theorem alc_h_alloc_slot (s : AlcState) (h : AlcInv s)
    (h1 : s.fsm = .alloc) (h2 : s.fsmR1 ≠ .alloc) :
    s.wgslot1H ≠ 0#8 ∧ (s.wgslot (alcCuFin s.cu)) &&& s.wgslot1H = 0#8 ∧
    (~~~(s.wgslot (alcCuFin s.cu)) >>> s.wgslotId.zeroExtend 8) &&& 1#8 = 1#8 := by
  obtain ⟨hnz, hdisj, hid, _⟩ := h.2.2 h1 h2
  refine ⟨hnz, hdisj, ?_⟩
  -- id 位 = 1H 的移位形式；与 wgslot 不交 ⟹ 补字的该位为 1
  have : ∀ (w : BitVec 8) (id : BitVec 3),
      (1#8 <<< id.zeroExtend 8) ≠ 0#8 → w &&& (1#8 <<< id.zeroExtend 8) = 0#8 →
      (~~~w >>> id.zeroExtend 8) &&& 1#8 = 1#8 := by
    intro w id a b; bv_decide
  rw [hid] at hnz hdisj
  exact this _ _ hnz hdisj

/-- **H-ALLOC-FIT 核销**：ALLOC 首拍三类资源的需求 ≤ rtcache 所选行剩余，
    且 WF 槽剩余 ≥ num_wf（:261-263 的检查在分配生效拍仍成立）。 -/
theorem alc_h_alloc_fit (s : AlcState) (h : AlcInv s)
    (h1 : s.fsm = .alloc) (h2 : s.fsmR1 ≠ .alloc) :
    s.cacheLds (alcCuFin s.cu) (alcSelFin s.ldsSel) ≥ s.wg.numLds ∧
    s.cacheSgpr (alcCuFin s.cu) (alcSelFin s.sgprSel) ≥ s.wg.numSgpr ∧
    s.cacheVgpr (alcCuFin s.cu) (alcSelFin s.vgprSel) ≥ s.wg.numVgpr ∧
    (8#4 - s.wfslot (alcCuFin s.cu)) ≥ s.wg.numWf := by
  obtain ⟨_, _, _, hfl, hfs, hfv, hwf⟩ := h.2.2 h1 h2
  exact ⟨hfl, hfs, hfv, hwf⟩

/-- **:91 断言核销（Q-ALC4）**：rtcache_writer 的 alloc 扣减断言语句
    `alloc_rawdata.size(sel) ≥ alloc_size` 在任何可达状态恒真（不会触发）；
    即三类资源的扣减都不回绕。 -/
theorem alc_assert91 (s : AlcState) (h : AlcInv s) (hw : alcAllocWr s = true) :
    s.cacheLds (alcCuFin s.cu) (alcSelFin s.ldsSel) ≥ s.wg.numLds ∧
    s.cacheSgpr (alcCuFin s.cu) (alcSelFin s.sgprSel) ≥ s.wg.numSgpr ∧
    s.cacheVgpr (alcCuFin s.cu) (alcSelFin s.vgprSel) ≥ s.wg.numVgpr := by
  unfold alcAllocWr alcAllocEn at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hf, hr1⟩ := hw
  have h2 : s.fsmR1 ≠ .alloc := by
    have e := h.1
    intro hcon
    rw [hcon] at e
    simp at e
    rw [e] at hr1
    simp at hr1
  have hfit := alc_h_alloc_fit s h hf h2
  exact ⟨hfit.1, hfit.2.1, hfit.2.2.1⟩

/-- ALLOC 期间分配决策寄存器保持（下发给 rt/cu_interface 的值 = 决策拍定案） -/
theorem alc_hold_alloc (s : AlcState) (i : AlcInputs) (hf : s.fsm = .alloc) :
    (alcStep s i).wgslotId = s.wgslotId ∧ (alcStep s i).wgslot1H = s.wgslot1H ∧
    (alcStep s i).cu = s.cu ∧ (alcStep s i).wg = s.wg ∧
    (alcStep s i).ldsSel = s.ldsSel ∧ (alcStep s i).sgprSel = s.sgprSel ∧
    (alcStep s i).vgprSel = s.vgprSel := by
  have hne : ¬ (s.fsm = .resCheck) := by simp [hf]
  have hcu : alcCuNext s i = s.cu := by simp [alcCuNext, hf]
  have hnf : s.fsm ≠ .idle := by simp [hf]
  have hwg : alcWgNewFire s i = false := alcWgNewFire_ne_idle hnf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (if s.fsm = .resCheck then _ else s.wgslotId) = _; rw [if_neg hne]
  · show (if s.fsm = .resCheck then _ else s.wgslot1H) = _; rw [if_neg hne]
  · exact hcu
  · show (if alcWgNewFire s i then i.wgNew else s.wg) = s.wg
    simp [hwg]
  · show (if s.fsm = .resCheck then _ else s.ldsSel) = _; rw [if_neg hne]
  · show (if s.fsm = .resCheck then _ else s.sgprSel) = _; rw [if_neg hne]
  · show (if s.fsm = .resCheck then _ else s.vgprSel) = _; rw [if_neg hne]

/- ========================================================================= -/
/- 9. 数值回归测试                                                             -/
/- ========================================================================= -/

section AlcRegressionTests

/-- WG A：2 WF、sgpr 100、vgpr 64、lds 256 -/
def alcWgA : AlcWgReq := ⟨2#4, 100#12, 64#11, 256#18⟩
/-- WG B：1 WF、sgpr 200 -/
def alcWgB : AlcWgReq := ⟨1#4, 200#12, 32#11, 0#18⟩
/-- WG C：sgpr 3000 > 任何 cache 行（2048），必然 REJECT -/
def alcWgC : AlcWgReq := ⟨1#4, 3000#12, 0#11, 0#18⟩

/-- 静默拍（全 ready、无 valid） -/
def alcNop : AlcInputs := {}

-- T1：A 完整分配（cu0 slot0；init cu=1 → CU_PREFER 后 cu=0）
def alcTrace1 : List AlcInputs := [
  { wgNewValid := true, wgNew := alcWgA },   -- idle → cuPrefer（捕获 wg）
  alcNop,                                    -- cuPrefer → resCheck，cu:=0
  alcNop,                                    -- resCheck cu0：通过 → alloc（捕获 id/sel）
  alcNop                                     -- alloc：三任务同拍 fire → idle
]
def alcS1 (k : Nat) : AlcState := alcRun alcInit (alcTrace1.take k)

-- 逐拍状态正确
example : (alcS1 1).fsm = .cuPrefer := by native_decide
example : (alcS1 2).fsm = .resCheck ∧ (alcS1 2).cu = 0#1 ∧ (alcS1 2).wg = alcWgA := by
  native_decide
example : (alcS1 3).fsm = .alloc ∧ (alcS1 3).fsmR1 = .resCheck ∧
    (alcS1 3).wgslotId = 0#3 ∧ (alcS1 3).wgslot1H = 0x01#8 := by native_decide
-- 分配生效：slot0 置位、wfslot=2、cache 精确扣减
example : (alcS1 4).fsm = .idle := by native_decide
example : (alcS1 4).wgslot ⟨0, by decide⟩ = 0x01#8 := by native_decide
example : (alcS1 4).wfslot ⟨0, by decide⟩ = 2#4 := by native_decide
example : (alcS1 4).cacheLds ⟨0, by decide⟩ ⟨0, by decide⟩ = 130816#18 := by
  native_decide
example : (alcS1 4).cacheSgpr ⟨0, by decide⟩ ⟨0, by decide⟩ = 1948#12 := by
  native_decide
example : (alcS1 4).cacheVgpr ⟨0, by decide⟩ ⟨0, by decide⟩ = 960#11 := by
  native_decide
-- ALLOC 首拍不变式的各合取项具体成立（H-ALLOC-SLOT/FIT 的数值见证）
example : (alcS1 3).wgslot ⟨0, by decide⟩ &&& (alcS1 3).wgslot1H = 0#8 ∧
    (alcS1 3).wgslot1H ≠ 0#8 := by native_decide
example : (alcS1 3).cacheSgpr ⟨0, by decide⟩ (alcSelFin (alcS1 3).sgprSel) ≥
    (alcS1 3).wg.numSgpr := by native_decide

-- T2：继续分配 B（应取 slot1）；再 dealloc A（slot0，2 WF）；再分配 B 复用 slot0
def alcTrace2 : List AlcInputs := alcTrace1 ++ [
  { wgNewValid := true, wgNew := alcWgB },   -- idle → cuPrefer
  alcNop,                                    -- cuPrefer → resCheck，cu:=1
  alcNop,                                    -- resCheck cu1：通过 → alloc（轮转）
  alcNop                                     -- alloc → idle
]
def alcS2 (k : Nat) : AlcState := alcRun alcInit (alcTrace2.take k)

example : (alcS2 7).fsm = .alloc ∧ (alcS2 7).cu = 1#1 ∧
    (alcS2 7).wgslotId = 0#3 ∧ (alcS2 7).wgslot1H = 0x01#8 := by native_decide
example : (alcS2 8).fsm = .idle ∧ (alcS2 8).wgslot ⟨1, by decide⟩ = 0x01#8 ∧
    (alcS2 8).wgslot ⟨0, by decide⟩ = 0x01#8 := by native_decide

-- dealloc A：cu0 slot0、2 WF（在 idle 拍）
def alcTrace3 : List AlcInputs := alcTrace2 ++ [
  { deallocV := true, deallocCu := 0#1, deallocSlot := 0#3, deallocNumWf := 2#4 }
]
example : (alcRun alcInit alcTrace3).wgslot ⟨0, by decide⟩ = 0#8 ∧
    (alcRun alcInit alcTrace3).wfslot ⟨0, by decide⟩ = 0#4 := by native_decide

-- T3：C 需求超界 → REJECT → wgbuffer_result(accept=0) → idle
def alcTrace4 : List AlcInputs := [
  { wgNewValid := true, wgNew := alcWgC },   -- idle → cuPrefer
  alcNop,                                    -- cuPrefer → resCheck，cu:=0
  alcNop,                                    -- resCheck cu0 失败，cuCnt 0→1，cu:=1
  alcNop,                                    -- resCheck cu1 失败，cuCnt+1≥2 → reject
  alcNop                                     -- reject：wgbuffer_result fire → idle
]
def alcS4 (k : Nat) : AlcState := alcRun alcInit (alcTrace4.take k)

example : (alcS4 3).fsm = .resCheck ∧ (alcS4 3).cu = 1#1 ∧ (alcS4 3).cuCnt = 1#2 := by
  native_decide
example : (alcS4 4).fsm = .reject := by native_decide
example : (alcS4 5).fsm = .idle := by native_decide
-- REJECT 不置位任何槽
example : (alcS4 5).wgslot ⟨0, by decide⟩ = 0#8 ∧ (alcS4 5).wgslot ⟨1, by decide⟩ = 0#8 := by
  native_decide

-- T4：RESOURCE_CHECK 期间 rt_result fire ⇒ 重查（repeat，Q-ALC3）
def alcTrace5 : List AlcInputs := [
  { wgNewValid := true, wgNew := alcWgA },
  alcNop,
  { resSgprV := true, resSgprCu := 0#1, resSgpr0 := 2048#12, resSgpr1 := 0#12 },
  alcNop,
  alcNop
]
example : (alcRun alcInit (alcTrace5.take 3)).fsm = .resCheck ∧
    (alcRun alcInit (alcTrace5.take 3)).cu = 0#1 := by native_decide
example : (alcRun alcInit alcTrace5).fsm = .idle := by native_decide

end AlcRegressionTests

/- 公理审计：bv_decide 定理带 LRAT trust 公理（Lean.ofReduceBool? 否——
   bv_decide 用 Lean.ofReduceBool 之外的 LRAT 证书公理；native_decide 测试
   会多 Lean.ofReduceBool，仅出现在 example 测试，不进定理）。 -/
#print axioms alc_h_alloc_slot
#print axioms alc_h_alloc_fit
#print axioms alc_assert91
#print axioms alcInv_step
#print axioms alcInv_run
#print axioms alc_hold_alloc

end Ventus.CTA
