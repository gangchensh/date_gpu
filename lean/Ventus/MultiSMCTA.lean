/- ========================================================================= -/
/-                        MultiSMCTA.lean                                     -/
/-  CTA 调度全模型接入整机组合（MSM-O2 消解）：                                -/
/-    host → wg_buffer → allocator → resource_table → cu_interface            -/
/-      → CTA2warp → SM（MultiSML2 的 2×SM + 真实 L2）→ warpRsp 回流           -/
/-      → CTA2warp CTArsp → cu_interface wf_gather → rt dealloc + host_wg_done  -/
/-  打通"host 下发 WG → SM 执行 → endprg → 完成回收上报 host"的整机闭环。      -/
/-                                                                           -/
/-  Chisel 源码对照（cta_scheduler.scala:106-145 顶层连线 + GPGPU_top.scala    -/
/-    :54-115 CTAinterface 字段映射 + :351-364 SM_wrapper 内 CTA2warp 对接）： -/
/-    host_wg_new ─▶ wg_buffer ─alloc_wg_new─▶ allocator ─rt_alloc─▶           -/
/-      resource_table_top ─cuinterface_wg_new(baseaddr)─┐                     -/
/-    wg_buffer ─cuinterface_wg_new(wgram2)──────────────┤                     -/
/-    allocator ─cuinterface_wg_new(cuinterface_buf)─────┴─▶ cu_interface      -/
/-      ─cu_wf_new(i)─▶ CTA2warp(i) ─warpReq─▶ SM(i)                         -/
/-    SM(i) ─warpRsp(warp_end 单拍脉冲)─▶ CTA2warp(i) ─CTArsp─▶               -/
/-      cu_interface.cu_wf_done(i) ─gather─▶ rt_dealloc ─▶ resource_table     -/
/-      ─slot_dealloc─▶ allocator（槽位簿记）；cu_interface ─host_wg_done─▶host -/
/-                                                                           -/
/- ======================== 建模决策（MCT-D 区） ============================= -/
/-  MCT-D0. SM+L2 底座整体复用 MultiSML2 的 mslStepAux（2×smdStepH + 真实      -/
/-      L2）；本文件只替换 SmIn 的来源（CTA 调度链驱动，替代 SmIn 事件注入）。 -/
/-  MCT-D1. CTA 链各模块全部例化真实逐拍模型：WgBuffer（wgbStep）、Allocator   -/
/-      （alcStep，含 rtcache_writer）、CuInterface（cuifStep）、CTA2warp×2     -/
/-      （c2wStep）。ResourceTable 为例外，见 MCT-D2。                          -/
/-  MCT-D2.【rt 抽象】resource_table_top 的三 handler（lds/sgpr/vgpr × CU）     -/
/-      逐拍 FSM（FIND 流水线/DEALLOC/SCAN/OUTPUT）不展开；以其事件语义         -/
/-      （ResourceTable.lean 的 rtStep/rtAllocBase/rtScan，已被 rt_alloc_       -/
/-      disjoint/rt_scan_ge_iff 等定理钉死）+ **固定延迟在飞队列** 建模：        -/
/-      alloc 接受后 mctLatAlloc 拍应用（best-fit 插入 + baseaddr 装配 +        -/
/-      SCAN 结果 mctLatScan 拍后推 rtcache）；dealloc 接受后 mctLatDealloc     -/
/-      拍应用。事件**按接受顺序在飞、头部依次应用**——保持 HW 每 handler 的     -/
/-      顺序处理语义；同 (CU,资源) 的 alloc/dealloc 先后序因此保持。三资源       -/
/-      handler 的并行性被合并为单事件流（时序抽象，场景内无跨资源乱序依赖）。   -/
/-  MCT-D3. wgbuffer 的 wgram1/wgram2 内容在 WgBuffer.lean 只建模 wg_id（其     -/
/-      D3）；本组合补幽灵表 wgbDesc（host 写入拍按 wgbWrAddr 记录完整 WG       -/
/-      描述符，与 WgBuffer.lean 的 ghost 不变量同构造），供 allocator 的        -/
/-      资源字段与 cu_interface 的 host_to_cu 字段取用。allocator 的             -/
/-      wgram_addr 透传字段（AlcWgReq D5 略去）补幽灵寄存器 alcAddr。           -/
/-      cuinterface_buf（Queue(1,pipe)）内容建模为 alcBuf : Option（无同拍       -/
/-      直通，比 HW 慢一拍——时序抽象）。cuif 的 io_buffer2cuinterface 输出       -/
/-      伴随描述符 = cuifDesc（accept 拍从 wgbDesc 捕获，与 cuifDataR 同步）。   -/
/-  MCT-D4. cu_interface 的 start_pc（纯透传字段，CuInterface.lean 未建模）      -/
/-      补幽灵表 pcGhost（cuif 入队拍按 (cu,slot) 记录，cu_wf_new fire 拍供       -/
/-      SM 的 reqPC）。                                                          -/
/-  MCT-D5. SM 侧 warp_end 观测：warpRspValid/outXWid 与 SmIn 无关（只依赖      -/
/-      状态+程序：其求值链 warpRspValid=fireWs∧simtStackOp ← outXV/route ←     -/
/-      CU/记分板/ibuf 状态，不经任何 inp 字段），故用 smdComb 对 smInNop 预演    -/
/-      取得本拍 warp_end 脉冲与 wid，再装配含真实 wgIdTag（CTA2warp data        -/
/-      迟读，:77）的 SmIn 喂 mslStepAux（若该独立性不成立，场景 A/B 的端到端    -/
/-      计数/基址断言即失败——轨迹通过即行为级佐证）。代价：每 SM 每拍两次       -/
/-      smdComb 求值。                                                            -/
/-  MCT-D6. cu_wf_done 的 RRArbiter 沿用 CuInterface.lean D3 的固定 CU0 优先    -/
/-      抽象；ctaRspReady(k) = (gfsm==getWf) && chosen==k。                      -/
/-  MCT-D7. host 侧：WG 注入为每拍 Option MctWgDesc（testbench 事件）；          -/
/-      host_wg_done.ready 恒 true（host 无限接收）。cuif init_ok 的 16 拍       -/
/-      清零窗口抽象为已完成（CuInterface.lean D2）。Top.lean W1/W2 字段映射     -/
/-      由本文件的描述符装配代码内联实现（同名同宽），W3（warp2CTA tag 直通）     -/
/-      由 c2w 输出直连 cuif done 输入体现。pc_reset 恒 false（同 MultiSM/Multi -/
/-      SML2 既有场景；W9 的前提由 SM 初态构造满足）。                            -/
/-  MCT-D8. slot_dealloc（rt→allocator 槽位回收）建模为 List 队列（容量 2，      -/
/-      同拍先弹后推）；cuif 的 rtRdy = slotQ 非满（HW 还有 handler ready 门控， -/
/-      抽象掉——场景内 dealloc 稀疏）。                                          -/
/-                                                                           -/
/- ======================== 边界与已知坑（MCT-B 区） ========================= -/
/-  MCT-B1【边界】rtcache 时序窗口（CtaScheduler.lean Q4）：allocator 用缓存      -/
/-      估计，rt 用真表 best-fit；本组合两者都真实例化，窗口的时序差由 MCT-D2    -/
/-      的固定延迟近似。场景设计使缓存始终精确（alloc 扣减同源于 best-fit 单段   -/
/-      情形），reject 监控器守"无伪拒绝"。                                     -/
/-  MCT-B2【忠实建模的已知 bug 现场】I-25（CTA2warp tag 迟读污染，T7）：本组      -/
/-      合中 c2w 的 data 迟读与 cuif gather 反压都是真实模型，污染窗口真实       -/
/-      存在；场景 B 的监控器记录回流 tag 供检查。I-46/I-47（endprg 不等在飞、   -/
/-      上报不等 flush）：warpRsp = warp_end 单拍脉冲（WS 模型固有），场景用     -/
/-      寄存器程序（无 dirty 行）使其不触发。I-5/I-6/I-7 同属忠实建模。          -/
/-  MCT-B3【边界】MMU/GVM 不例化（Top.lean D4）；asid 字段无去向。              -/
/- ========================================================================= -/

import Ventus.MultiSML2
import Ventus.CTA.WgBuffer
import Ventus.CTA.Allocator
import Ventus.CTA.ResourceTable
import Ventus.CTA.CuInterface
import Ventus.CTA.CTA2warp

namespace Ventus

open Ventus.CTA
open Ventus.Schedule Ventus.SIMT Ventus.Arith
open Ventus.L2 Ventus.L2.L2MSHR Ventus.L2.L2Scheduler

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常量、host 描述符与幽灵数据                                               -/
/- ========================================================================= -/

/-- rt alloc 事件的应用延迟（拍，MCT-D2；HW：CONNECT+FIND(cnt+3)+WRITE_OUTPUT(2)
    +baseaddr 队列 ≈ 6-12，取定值 8） -/
def mctLatAlloc : Nat := 8
/-- rt dealloc 事件的应用延迟（HW：CONNECT+DEALLOC(2) ≈ 3） -/
def mctLatDealloc : Nat := 3
/-- rt 应用后 SCAN→OUTPUT（rtcache 推送）的延迟（HW：SCAN(cnt+2)+OUTPUT(1)） -/
def mctLatScan : Nat := 4

/-- host 下发的 WG 描述符（io_host2cta 的模型侧子集；W1 的 16 字段中本组合
    消费的全体：资源量给 allocator、per-wf 量给 cuif、start_pc 给 SM） -/
structure MctWgDesc where
  wgId : BitVec 32          -- wg_id
  numWf : BitVec 4          -- num_wf
  numSgpr : BitVec 12       -- num_sgpr（WG 总量）
  numVgpr : BitVec 11       -- num_vgpr（WG 总量）
  numLds : BitVec 18        -- num_lds
  numSgprPerWf : BitVec 12  -- num_sgpr_per_wf
  numVgprPerWf : BitVec 11  -- num_vgpr_per_wf
  numPdsPerWf : BitVec 18   -- num_pds_per_wf
  startPc : BitVec 32       -- start_pc
  pdsBase : BitVec 32       -- pds_base
deriving DecidableEq, Repr

/-- 全零描述符（缺省填充用） -/
def mctDesc0 : MctWgDesc := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- 描述符 → allocator 的资源请求（ctainfo_host_to_alloc，D5 四字段） -/
def mctDesc2Alc (d : MctWgDesc) : AlcWgReq :=
  ⟨d.numWf, d.numSgpr, d.numVgpr, d.numLds⟩

/-- allocator → cu_interface 的任务内容（io_alloc2cuinterface，经
    cuinterface_buf Queue(1)；allocator.scala:331-336） -/
structure MctAlc2Cuif where
  cu : BitVec 1
  slot : BitVec 3
  numWf : BitVec 4
  enLds : Bool              -- lds_dealloc_en = (num_lds ≠ 0)
  enSgpr : Bool
  enVgpr : Bool
deriving DecidableEq, Repr

/-- rt → cu_interface 的基址输出（io_rt2cuinterface：三 handler baseaddr 汇聚，
    resource_table.scala:856-859） -/
structure MctBases where
  lds : BitVec 17
  sgpr : BitVec 11
  vgpr : BitVec 10
deriving DecidableEq, Repr

/- ========================================================================= -/
/- 2. resource_table_top 的组合模型（MCT-D2）                                   -/
/- ========================================================================= -/

/-- rt 在飞事件（alloc：三资源 best-fit 插入；dealloc：按 dealloc_en 摘除） -/
structure MctRtOp where
  isAlloc : Bool
  cu : BitVec 1
  slot : BitVec 3
  numLds : BitVec 18
  numSgpr : BitVec 12
  numVgpr : BitVec 11
  enLds : Bool              -- 仅 dealloc 用（alloc 时 rtStep 的 size=0 门控等效）
  enSgpr : Bool
  enVgpr : Bool
  cnt : Nat                 -- 应用倒计时
deriving DecidableEq, Repr

/-- 待推送 allocator 的 rtcache 更新（io_rt2cache：cu + 两段尺寸；值在应用拍
    从应用后链表捕获，MCT-D2） -/
structure MctScan where
  cu : BitVec 1
  s0 : Nat                  -- size(0) = 最大空段
  s1 : Nat                  -- size(1) = 次大空段
  cnt : Nat                 -- 推送倒计时
deriving DecidableEq, Repr

/-- resource_table_top 组合状态：6 张真实 RtRam（2 CU × 3 资源，事件语义
    由 ResourceTable.lean 定理钉死）+ 在飞事件队列 + 基址输出寄存器 +
    三路 SCAN 推送队列 + slot_dealloc Queue(2) -/
structure MctRt where
  lds : Fin 2 → RtRam
  sgpr : Fin 2 → RtRam
  vgpr : Fin 2 → RtRam
  ops : List MctRtOp        -- 在飞事件（按接受序；头部先应用）
  bases : Option MctBases   -- cuinterface_wg_new 输出寄存器（至多 1 笔在飞，
                            -- HW alloc_record 语义）
  scanLds : List MctScan
  scanSgpr : List MctScan
  scanVgpr : List MctScan
  slotQ : List (BitVec 1 × BitVec 3 × BitVec 4)  -- slot_dealloc Queue(2)：
                            -- (cu, wg_slot_id, num_wf)

def mctRtInit : MctRt :=
  { lds := fun _ => rtEmpty, sgpr := fun _ => rtEmpty, vgpr := fun _ => rtEmpty
  , ops := [], bases := none
  , scanLds := [], scanSgpr := [], scanVgpr := [], slotQ := [] }

/-- Fin 2 函数写更新（本文件局部） -/
def mctUpd2 (f : Fin 2 → α) (c : Fin 2) (v : α) : Fin 2 → α :=
  fun x => if x = c then v else f x

/-- Fin 16 函数写更新（pcGhost 用） -/
def mctUpd16 (f : Fin 16 → α) (g : Fin 16) (v : α) : Fin 16 → α :=
  fun x => if x = g then v else f x

/-- rt alloc 应用：best-fit 基址（读应用前链表）→ 三表插入 → bases 装配 →
    三资源各排一路 SCAN（值为应用后链表的最大两段） -/
def mctRtApplyAlloc (rt : MctRt) (op : MctRtOp) : MctRt × MctBases :=
  let cu := alcCuFin op.cu
  let slotF := wgbFin op.slot
  let sL := op.numLds.toNat
  let sS := op.numSgpr.toNat
  let sV := op.numVgpr.toNat
  let bL := rtAllocBase (rt.lds cu) rtNUM_LDS slotF sL
  let bS := rtAllocBase (rt.sgpr cu) rtNUM_SGPR slotF sS
  let bV := rtAllocBase (rt.vgpr cu) rtNUM_VGPR slotF sV
  let lds' := mctUpd2 rt.lds cu (rtStep (rt.lds cu) rtNUM_LDS (.alloc slotF sL))
  let sgpr' := mctUpd2 rt.sgpr cu (rtStep (rt.sgpr cu) rtNUM_SGPR (.alloc slotF sS))
  let vgpr' := mctUpd2 rt.vgpr cu (rtStep (rt.vgpr cu) rtNUM_VGPR (.alloc slotF sV))
  let scL := rtScan (lds' cu) rtNUM_LDS
  let scS := rtScan (sgpr' cu) rtNUM_SGPR
  let scV := rtScan (vgpr' cu) rtNUM_VGPR
  ( { rt with
      lds := lds', sgpr := sgpr', vgpr := vgpr'
    , bases := some ⟨BitVec.ofNat 17 bL, BitVec.ofNat 11 bS, BitVec.ofNat 10 bV⟩
    , scanLds := rt.scanLds ++ [⟨op.cu, scL.1, scL.2, mctLatScan⟩]
    , scanSgpr := rt.scanSgpr ++ [⟨op.cu, scS.1, scS.2, mctLatScan⟩]
    , scanVgpr := rt.scanVgpr ++ [⟨op.cu, scV.1, scV.2, mctLatScan⟩] }
  , ⟨BitVec.ofNat 17 bL, BitVec.ofNat 11 bS, BitVec.ofNat 10 bV⟩ )

/-- rt dealloc 应用：按 dealloc_en 摘除（rtStep .dealloc；未启用资源不动也
    不排 SCAN，对应 HW 的 IGNORE 支路 resource_table.scala:785-795） -/
def mctRtApplyDealloc (rt : MctRt) (op : MctRtOp) : MctRt :=
  let cu := alcCuFin op.cu
  let slotF := wgbFin op.slot
  let lds' := if op.enLds then
      let r' := rtStep (rt.lds cu) rtNUM_LDS (.dealloc slotF)
      (mctUpd2 rt.lds cu r', rt.scanLds ++
        [⟨op.cu, (rtScan r' rtNUM_LDS).1, (rtScan r' rtNUM_LDS).2, mctLatScan⟩])
    else (rt.lds, rt.scanLds)
  let sgpr' := if op.enSgpr then
      let r' := rtStep (rt.sgpr cu) rtNUM_SGPR (.dealloc slotF)
      (mctUpd2 rt.sgpr cu r', rt.scanSgpr ++
        [⟨op.cu, (rtScan r' rtNUM_SGPR).1, (rtScan r' rtNUM_SGPR).2, mctLatScan⟩])
    else (rt.sgpr, rt.scanSgpr)
  let vgpr' := if op.enVgpr then
      let r' := rtStep (rt.vgpr cu) rtNUM_VGPR (.dealloc slotF)
      (mctUpd2 rt.vgpr cu r', rt.scanVgpr ++
        [⟨op.cu, (rtScan r' rtNUM_VGPR).1, (rtScan r' rtNUM_VGPR).2, mctLatScan⟩])
    else (rt.vgpr, rt.scanVgpr)
  { rt with
    lds := lds'.1, scanLds := lds'.2
  , sgpr := sgpr'.1, scanSgpr := sgpr'.2
  , vgpr := vgpr'.1, scanVgpr := vgpr'.2 }

/-- 本拍 rt 应用事件（监控用）：应用的 alloc 基址（至多 1 笔）与 dealloc 数 -/
structure MctRtEv where
  apAlloc : Option MctBases
  apAllocN : Nat
  apDeallocN : Nat
deriving DecidableEq, Repr

/-- 头部结算：ops 已全部倒计时后，头部 cnt=0 者依次应用（在飞事件按接受序，
    后到的等头部；fuel = 队列长度上界） -/
def mctRtSettleGo : Nat → MctRt → MctRtEv → MctRt × MctRtEv
  | 0, rt, ev => (rt, ev)
  | fuel + 1, rt, ev =>
    match rt.ops with
    | [] => (rt, ev)
    | o :: _ =>
      if o.cnt == 0 then
        if o.isAlloc then
          let (rt1, bs) := mctRtApplyAlloc { rt with ops := rt.ops.tail } o
          mctRtSettleGo fuel rt1
            { ev with apAlloc := some bs, apAllocN := ev.apAllocN + 1 }
        else
          mctRtSettleGo fuel (mctRtApplyDealloc { rt with ops := rt.ops.tail } o)
            { ev with apDeallocN := ev.apDeallocN + 1 }
      else (rt, ev)

def mctRtSettle (rt : MctRt) : MctRt × MctRtEv :=
  mctRtSettleGo rt.ops.length rt ⟨none, 0, 0⟩

/-- rt 对 allocator 的 alloc 接受条件（MCT-D2：HW 的 alloc_record"至多 1 笔
    在飞"+ baseaddr 已消费 + handler IDLE 的合并近似） -/
def mctRtAllocRdy (rt : MctRt) : Bool :=
  rt.bases.isNone && !(rt.ops.any (fun o => o.isAlloc))

/-- rt 对 cuif 的 dealloc 接受条件（MCT-D8：slot_dealloc Queue(2) 非满） -/
def mctRtDeallocRdy (rt : MctRt) : Bool := decide (rt.slotQ.length < 2)

/- ========================================================================= -/
/- 3. 组合状态 / 连线求值 / mctStep                                            -/
/- ========================================================================= -/

/-- 整机组合状态：MultiSML2（2×SM+真实 L2）+ CTA 调度链 + 幽灵簿记（MCT-D3/D4） -/
structure MctState where
  msl : MslState                 -- 2×SM + 真实 L2（mslStepAux 步进）
  wgb : WgbState                 -- wg_buffer
  alc : AlcState                 -- allocator（含 rtcache）
  cuif : CuifState               -- cu_interface
  c2w0 : C2wState                -- CTA2warp(0)（SM0/CU0 侧）
  c2w1 : C2wState                -- CTA2warp(1)（SM1/CU1 侧）
  rt : MctRt                     -- resource_table_top（MCT-D2）
  wgbDesc : Fin 8 → MctWgDesc    -- 幽灵：wgram 完整描述符（MCT-D3）
  cuifDesc : MctWgDesc           -- 幽灵：wgb→cuif 在途描述符（随 cuifDataR）
  alcBuf : Option MctAlc2Cuif    -- cuinterface_buf（Queue(1)，MCT-D3）
  alcAddr : BitVec 3             -- 幽灵：allocator 当前 WG 的 wgram_addr
  pcGhost : Fin 16 → BitVec 32   -- 幽灵：(cu,slot) → start_pc（MCT-D4）

/-- 初始组合状态（SM 侧由调用方给；CTA 链全复位；rt 六表全空） -/
def mctInit (sm0 sm1 : SmdState) : MctState where
  msl := mslInit sm0 sm1
  wgb := wgbInit
  alc := alcInit
  cuif := cuifInit
  c2w0 := c2wInit
  c2w1 := c2wInit
  rt := mctRtInit
  wgbDesc := fun _ => mctDesc0
  cuifDesc := mctDesc0
  alcBuf := none
  alcAddr := 0#3
  pcGhost := fun _ => 0#32

/-- scan 队列的拍内更新：先倒计时，按 fire 弹头部 -/
def mctScanStep (q : List MctScan) (fire : Bool) : List MctScan :=
  let q1 := q.map (fun sc => { sc with cnt := sc.cnt - 1 })
  if fire then q1.tail else q1

/-- scan 队列头的有效位（倒计时归 0 即对 allocator valid；HW 的 OUTPUT 态） -/
def mctScanHeadV (q : List MctScan) : Bool :=
  match q with | [] => false | sc :: _ => decide (sc.cnt = 0)

/-- 组合单拍事件（监控用；全部在拍前状态 + 本拍组合上求值） -/
structure MctEv where
  hostF : Bool              -- host WG 被 wgb 接受
  hostWg : BitVec 32
  allocF : Bool             -- allocator → rt 的 rt_alloc fire
  allocCu : BitVec 1
  allocSlot : BitVec 3
  apAlloc : Option MctBases -- 本拍 rt 应用的 alloc 基址（最多一笔）
  apAllocN : Nat
  apDeallocN : Nat
  enqF : Bool               -- cuif 三源会合入队
  wfF0 : Bool               -- SM0 收到 warp 派发（c2w0 warpReq fire）
  wfF1 : Bool
  end0 : Bool               -- SM0 warp_end 脉冲
  end1 : Bool
  deq0 : Bool               -- c2w0 的 CTArsp 出队（= cuif done 消费）
  deq1 : Bool
  deqTag0 : BitVec 6        -- 出队携带的 tag（I-25 观测点）
  deqTag1 : BitVec 6
  arbF : Bool               -- cuif gather 接受一笔 done
  arbCu : BitVec 1
  rtDeF : Bool              -- cuif → rt 的 dealloc fire
  hdF : Bool                -- host_wg_done fire
  hdWg : BitVec 32
  rejF : Bool               -- allocator REJECT 结果回 wgb
deriving DecidableEq, Repr

/-- 组合单拍：返回 (次态, 事件)。求值序：SM warp_end 观测（MCT-D5）→
    CTA2warp 组合 → cuif/wgb/allocator 输入装配 → fires → 各模块同步步进。
    全链无跨模块组合环（c2w 的 ctaRspReady 只依赖 cuif 的 gfsm 寄存器与各
    fifo 状态；SM 输入只依赖 c2w/cuif 的拍前状态）。 -/
def mctStepAux (p0 p1 : SmProg) (s : MctState) (hin : Option MctWgDesc) :
    MctState × MctEv :=
  -- 0. SM warp_end 观测（warpRspValid/outXWid 与 SmIn 无关，MCT-D5）
  let obs0 := smdComb p0 s.msl.sm0 smInNop true
  let obs1 := smdComb p1 s.msl.sm1 smInNop true
  let endV0 : Bool := obs0.wsO.warpRspValid
  let endW0 : BitVec 3 := obs0.outXWid
  let endV1 : Bool := obs1.wsO.warpRspValid
  let endW1 : BitVec 3 := obs1.outXWid
  -- 1. cuif gather 对 CTA2warp CTArsp 的消费选择（MCT-D6 固定 CU0 优先）
  let getWf : Bool := decide (s.cuif.gfsm = CuifG.getWf)
  let doneV0 : Bool := decide (0 < s.c2w0.fifo.length)
  let doneV1 : Bool := decide (0 < s.c2w1.fifo.length)
  let rspRdy0 : Bool := getWf && doneV0
  let rspRdy1 : Bool := getWf && !doneV0 && doneV1
  -- 2. CTA2warp 输入/输出（CTAreq ← cuif cu_wf_new；warpRsp ← SM warp_end；
  --    wg_id_lookup = warp_end_id，Top.lean W3 + CTA2warp.scala:51）
  let c2wIn0 : C2wInputs :=
    { ctaReqValid := cuifWfNewValid s.cuif 0#1, ctaReqTag := cuifWfNewTag s.cuif
    , warpRspValid := endV0, warpRspWid := endW0, wgIdLookup := endW0
    , ctaRspReady := rspRdy0 }
  let c2wIn1 : C2wInputs :=
    { ctaReqValid := cuifWfNewValid s.cuif 1#1, ctaReqTag := cuifWfNewTag s.cuif
    , warpRspValid := endV1, warpRspWid := endW1, wgIdLookup := endW1
    , ctaRspReady := rspRdy1 }
  let c2wO0 := c2wOut s.c2w0 c2wIn0
  let c2wO1 := c2wOut s.c2w1 c2wIn1
  -- 3. cuif 入队三源会合（cu_interface.scala:55-58）与 fifo 容量
  let hd : CuifWg := cuifHead s.cuif
  let fifoRdy : Bool := decide (s.cuif.fifo.length < 2)
  let othersV : Bool := s.alcBuf.isSome && s.rt.bases.isSome
  let enqV : Bool := wgbCuifOutValid s.wgb && othersV
  let enqF : Bool := enqV && fifoRdy
  let buf := s.alcBuf.getD ⟨0, 0, 0, false, false, false⟩
  let bas := s.rt.bases.getD ⟨0, 0, 0⟩
  let enqWg : CuifWg :=
    { cuId := buf.cu, wgSlotId := buf.slot, numWf := buf.numWf
    , wgId := s.cuifDesc.wgId
    , numSgprPerWf := s.cuifDesc.numSgprPerWf
    , numVgprPerWf := s.cuifDesc.numVgprPerWf
    , numPdsPerWf := s.cuifDesc.numPdsPerWf
    , sgprBase := bas.sgpr, vgprBase := bas.vgpr, ldsBase := bas.lds
    , pdsBase := s.cuifDesc.pdsBase
    , ldsDeallocEn := buf.enLds, sgprDeallocEn := buf.enSgpr
    , vgprDeallocEn := buf.enVgpr }
  -- 4. wgb 输入（host 注入 + allocator 提供/回收 + cuif 通路 ready）
  let alcResValid : Bool :=
    (decide (s.alc.fsm = AlcFsm.alloc) || decide (s.alc.fsm = AlcFsm.reject)) &&
    !s.alc.wgram2Reg
  let wgbIn : WgbInputs :=
    { hostValid := hin.isSome
    , hostTag := (hin.getD mctDesc0).wgId
    , allocReady := decide (s.alc.fsm = AlcFsm.idle)    -- allocator.scala:188
    , resValid := alcResValid
    , resAccept := decide (s.alc.fsm = AlcFsm.alloc)
    , resAddr := s.alcAddr
    , cuifReady := othersV && fifoRdy }
  -- 5. allocator 输入（wg 提供 ← wgb；rtcache ← rt scan 队列；dealloc ← slotQ）
  let wgOffer : MctWgDesc := s.wgbDesc (wgbFin (wgbAllocOutAddr s.wgb))
  let scanL := s.rt.scanLds.head?.getD ⟨0, 0, 0, 0⟩
  let scanS := s.rt.scanSgpr.head?.getD ⟨0, 0, 0, 0⟩
  let scanV := s.rt.scanVgpr.head?.getD ⟨0, 0, 0, 0⟩
  let slotH := s.rt.slotQ.head?.getD (0, 0, 0)
  let alcIn : AlcInputs :=
    { wgNewValid := wgbAllocOutValid s.wgb
    , wgNew := mctDesc2Alc wgOffer
    , resLdsV := mctScanHeadV s.rt.scanLds
    , resLdsCu := scanL.cu
    , resLds0 := BitVec.ofNat 18 scanL.s0
    , resLds1 := BitVec.ofNat 18 scanL.s1
    , resSgprV := mctScanHeadV s.rt.scanSgpr
    , resSgprCu := scanS.cu
    , resSgpr0 := BitVec.ofNat 12 scanS.s0
    , resSgpr1 := BitVec.ofNat 12 scanS.s1
    , resVgprV := mctScanHeadV s.rt.scanVgpr
    , resVgprCu := scanV.cu
    , resVgpr0 := BitVec.ofNat 11 scanV.s0
    , resVgpr1 := BitVec.ofNat 11 scanV.s1
    , deallocV := decide (0 < s.rt.slotQ.length)
    , deallocCu := slotH.1
    , deallocSlot := slotH.2.1
    , deallocNumWf := slotH.2.2
    , rtAllocRdy := mctRtAllocRdy s.rt
    , cuifRdy := s.alcBuf.isNone
    , wgbufRdy := wgbResReady s.wgb wgbIn }
  -- 6. cuif 输入（三源会合 + 双 CU 的 done + rt/host 反压）
  let cuifIn : CuifInputs :=
    { enqValid := enqV, enqWg := enqWg
    , cuRdy0 := c2wReqReady s.c2w0
    , cuRdy1 := c2wReqReady s.c2w1
    , doneV0 := doneV0, doneV1 := doneV1
    , doneTag0 := c2wRspTagOf s.c2w0.data s.c2w0.fifo
    , doneTag1 := c2wRspTagOf s.c2w1.data s.c2w1.fifo
    , rtRdy := mctRtDeallocRdy s.rt
    , hostRdy := true }
  -- 7. fires（各模块共享同一拍组合视图）
  let hostF := wgbHostFire s.wgb wgbIn
  let alcNewF := alcWgNewFire s.alc alcIn
  let rtAllocF := alcRtAllocFire s.alc alcIn
  let alcCuifF := alcCuifFire s.alc alcIn
  let slotDeF := alcDeallocFire s.alc alcIn
  let resFL := alcResFireLds s.alc alcIn
  let resFS := alcResFireSgpr s.alc alcIn
  let resFV := alcResFireVgpr s.alc alcIn
  let rtDeF := cuifRtFire s.cuif cuifIn
  let hdF := cuifHostFire s.cuif cuifIn
  let arbF := cuifArbFire s.cuif cuifIn
  let deq0 := c2wDeqFire s.c2w0 c2wIn0
  let deq1 := c2wDeqFire s.c2w1 c2wIn1
  -- 8. SM 输入（dispatch 经 CTA2warp 直通；wgIdTag = data(endWid) 迟读，
  --    CTA2warp.scala:58；reqWg/reqCnt/reqPC/reqSgpr/reqVgpr 在 reqFire 拍
  --    必对应 cuif fifo 头——cu_wf_new.fire ⟹ 头存在且 cuId 匹配）
  let smIn0 : SmIn :=
    { smInNop with
      reqFire := c2wO0.warpReqValid
    , reqWid := c2wO0.warpReqWid
    , reqWg := hd.wgSlotId
    , reqCnt := hd.numWf
    , reqPC := s.pcGhost (cuifGaddr hd.cuId hd.wgSlotId)
    , reqSgpr := s.cuif.splitSgpr.zeroExtend 12
    , reqVgpr := s.cuif.splitVgpr.zeroExtend 11
    , wgIdTag := c2wO0.wgIdTag
    , warpRspReady := c2wO0.warpRspReady }
  let smIn1 : SmIn :=
    { smInNop with
      reqFire := c2wO1.warpReqValid
    , reqWid := c2wO1.warpReqWid
    , reqWg := hd.wgSlotId
    , reqCnt := hd.numWf
    , reqPC := s.pcGhost (cuifGaddr hd.cuId hd.wgSlotId)
    , reqSgpr := s.cuif.splitSgpr.zeroExtend 12
    , reqVgpr := s.cuif.splitVgpr.zeroExtend 11
    , wgIdTag := c2wO1.wgIdTag
    , warpRspReady := c2wO1.warpRspReady }
  -- 9. 各模块同步步进
  let mslEv := mslStepAux p0 p1 s.msl smIn0 smIn1
  let wgb' := wgbStep s.wgb wgbIn
  let alc' := alcStep s.alc alcIn
  let cuif' := cuifStep s.cuif cuifIn
  let c2w0' := c2wStep s.c2w0 c2wIn0
  let c2w1' := c2wStep s.c2w1 c2wIn1
  -- rt：倒计时（ops+scans）→ 头部结算（应用 alloc/dealloc，装配 bases、
  -- 排新 scan）→ 接受新事件入尾 → slotQ 同拍先弹后推（Queue 语义）
  let opsDec := s.rt.ops.map (fun o => { o with cnt := o.cnt - 1 })
  let rtPre : MctRt :=
    { s.rt with
      ops := opsDec
    , scanLds := mctScanStep s.rt.scanLds resFL
    , scanSgpr := mctScanStep s.rt.scanSgpr resFS
    , scanVgpr := mctScanStep s.rt.scanVgpr resFV }
  let (rtS, rtEv) := mctRtSettle rtPre
  let rtA := if rtAllocF then
      { rtS with ops := rtS.ops ++
          [⟨true, s.alc.cu, s.alc.wgslotId,
            s.alc.wg.numLds, s.alc.wg.numSgpr, s.alc.wg.numVgpr,
            true, true, true, mctLatAlloc⟩] }
    else rtS
  let db := cuifDeallocBits s.cuif
  let rtD := if rtDeF then
      { rtA with ops := rtA.ops ++
          [⟨false, db.1, db.2.1, 0, 0, 0,
            db.2.2.ldsDeallocEn, db.2.2.sgprDeallocEn, db.2.2.vgprDeallocEn,
            mctLatDealloc⟩] }
    else rtA
  let slotQ' := (if slotDeF then s.rt.slotQ.tail else s.rt.slotQ) ++
    (if rtDeF then [(db.1, db.2.1, db.2.2.numWf)] else [])
  let rt' : MctRt :=
    { rtD with
      slotQ := slotQ'
    , bases := if enqF then none else rtS.bases }
  -- 10. 幽灵簿记（MCT-D3/D4）
  let wgbDesc' := match hin with
    | some d =>
      if hostF then wgbUpd s.wgbDesc (wgbFin (wgbWrAddr s.wgb)) d else s.wgbDesc
    | none => s.wgbDesc
  let cuifDesc' := if wgbClearAct s.wgb wgbIn then
      s.wgbDesc (wgbFin wgbIn.resAddr) else s.cuifDesc
  let alcAddr' := if alcNewF then wgbAllocOutAddr s.wgb else s.alcAddr
  let alcBuf' := if alcCuifF then
      some ⟨s.alc.cu, s.alc.wgslotId, s.alc.wg.numWf,
        decide (s.alc.wg.numLds ≠ 0#18), decide (s.alc.wg.numSgpr ≠ 0#12),
        decide (s.alc.wg.numVgpr ≠ 0#11)⟩
    else (if enqF then none else s.alcBuf)
  let pcGhost' := if enqF then
      mctUpd16 s.pcGhost (cuifGaddr buf.cu buf.slot) s.cuifDesc.startPc
    else s.pcGhost
  let s' : MctState :=
    { msl := mslEv.1, wgb := wgb', alc := alc', cuif := cuif'
    , c2w0 := c2w0', c2w1 := c2w1', rt := rt'
    , wgbDesc := wgbDesc', cuifDesc := cuifDesc'
    , alcBuf := alcBuf', alcAddr := alcAddr', pcGhost := pcGhost' }
  let ev : MctEv :=
    { hostF := hostF, hostWg := (hin.getD mctDesc0).wgId
    , allocF := rtAllocF, allocCu := s.alc.cu, allocSlot := s.alc.wgslotId
    , apAlloc := rtEv.apAlloc, apAllocN := rtEv.apAllocN
    , apDeallocN := rtEv.apDeallocN
    , enqF := enqF
    , wfF0 := c2wO0.warpReqValid, wfF1 := c2wO1.warpReqValid
    , end0 := endV0, end1 := endV1
    , deq0 := deq0, deq1 := deq1
    , deqTag0 := c2wRspTagOf s.c2w0.data s.c2w0.fifo
    , deqTag1 := c2wRspTagOf s.c2w1.data s.c2w1.fifo
    , arbF := arbF, arbCu := cuifChosenCu cuifIn
    , rtDeF := rtDeF
    , hdF := hdF, hdWg := (cuifDeallocBits s.cuif).2.2.wgId
    , rejF := alcWgbufFire s.alc alcIn && decide (s.alc.fsm = AlcFsm.reject) }
  (s', ev)

/-- 组合单拍（无事件版） -/
def mctStep (p0 p1 : SmProg) (s : MctState) (hin : Option MctWgDesc) : MctState :=
  (mctStepAux p0 p1 s hin).1

/-- 多拍运行 -/
def mctRun (p0 p1 : SmProg) (s : MctState) (hosts : List (Option MctWgDesc)) :
    MctState :=
  hosts.foldl (mctStep p0 p1) s

/- ========================================================================= -/
/- 4. 监控器                                                                   -/
/- ========================================================================= -/

/-- 监控累积器（首事件记拍号+1，0=未发生；计数/记录字段见各注释） -/
structure MctChk where
  tick : Nat
  hostN : Nat                 -- host WG 接受计数
  allocN : Nat                -- rt_alloc fire 计数
  allocT : Nat                -- 首次 rt_alloc 拍+1
  allocCu : BitVec 1          -- 首次 alloc 的 CU（sm_id 分配观测）
  allocSlot : BitVec 3        -- 首次 alloc 的 wg 槽
  apN : Nat                   -- rt alloc 应用计数
  apT : Nat                   -- 首次应用拍+1
  apSgpr : Nat                -- 首次应用的 sgpr 基址
  apVgpr : Nat
  apLds : Nat
  apSgpr2 : Nat               -- 第二次应用（多 WG 场景）
  apVgpr2 : Nat
  apSgpr3 : Nat               -- 第三次应用
  apVgpr3 : Nat
  deapN : Nat                 -- rt dealloc 应用计数
  enqN : Nat                  -- cuif 入队计数
  enqT : Nat
  wf0 : Nat                   -- SM0 warp 派发计数
  wf1 : Nat
  end0 : Nat                  -- SM0 warp_end 计数
  end1 : Nat
  deq0 : Nat                  -- CU0 CTArsp 出队计数
  deq1 : Nat
  deq0tag1 : BitVec 6         -- CU0 第 1/2 笔出队的 tag（I-25 观测）
  deq0tag2 : BitVec 6
  arb0 : Nat                  -- cuif gather 按 CU 计数
  arb1 : Nat
  rtDeN : Nat                 -- cuif→rt dealloc 计数
  hdN : Nat                   -- host_wg_done 计数
  hdT : Nat                   -- 首次上报拍+1
  hdWg1 : BitVec 32           -- 第 1/2/3 笔上报的 wgId
  hdWg2 : BitVec 32
  hdWg3 : BitVec 32
  rejN : Nat                  -- allocator REJECT 计数（MCT-B1：场景内应为 0）
deriving DecidableEq, Repr

def mctChk0 : MctChk :=
  { tick := 0, hostN := 0
  , allocN := 0, allocT := 0, allocCu := 0, allocSlot := 0
  , apN := 0, apT := 0, apSgpr := 0, apVgpr := 0, apLds := 0
  , apSgpr2 := 0, apVgpr2 := 0, apSgpr3 := 0, apVgpr3 := 0
  , deapN := 0, enqN := 0, enqT := 0
  , wf0 := 0, wf1 := 0, end0 := 0, end1 := 0
  , deq0 := 0, deq1 := 0, deq0tag1 := 0, deq0tag2 := 0
  , arb0 := 0, arb1 := 0, rtDeN := 0
  , hdN := 0, hdT := 0, hdWg1 := 0, hdWg2 := 0, hdWg3 := 0, rejN := 0 }

def mctMonStep (p0 p1 : SmProg) (acc : MctChk × MctState) (hin : Option MctWgDesc) :
    MctChk × MctState :=
  let (m, s) := acc
  let (s', ev) := mctStepAux p0 p1 s hin
  let t := m.tick + 1
  let fst (old : Nat) (b : Bool) : Nat := if b && (old == 0) then t else old
  ( { tick := t
    , hostN := m.hostN + (if ev.hostF then 1 else 0)
    , allocN := m.allocN + (if ev.allocF then 1 else 0)
    , allocT := fst m.allocT ev.allocF
    , allocCu := if ev.allocF && (m.allocN == 0) then ev.allocCu else m.allocCu
    , allocSlot := if ev.allocF && (m.allocN == 0) then ev.allocSlot else m.allocSlot
    , apN := m.apN + ev.apAllocN
    , apT := fst m.apT ev.apAlloc.isSome
    , apSgpr := if m.apN == 0 then
        (ev.apAlloc.map (fun b => b.sgpr.toNat)).getD m.apSgpr else m.apSgpr
    , apVgpr := if m.apN == 0 then
        (ev.apAlloc.map (fun b => b.vgpr.toNat)).getD m.apVgpr else m.apVgpr
    , apLds := if m.apN == 0 then
        (ev.apAlloc.map (fun b => b.lds.toNat)).getD m.apLds else m.apLds
    , apSgpr2 := if m.apN == 1 then
        (ev.apAlloc.map (fun b => b.sgpr.toNat)).getD m.apSgpr2 else m.apSgpr2
    , apVgpr2 := if m.apN == 1 then
        (ev.apAlloc.map (fun b => b.vgpr.toNat)).getD m.apVgpr2 else m.apVgpr2
    , apSgpr3 := if m.apN == 2 then
        (ev.apAlloc.map (fun b => b.sgpr.toNat)).getD m.apSgpr3 else m.apSgpr3
    , apVgpr3 := if m.apN == 2 then
        (ev.apAlloc.map (fun b => b.vgpr.toNat)).getD m.apVgpr3 else m.apVgpr3
    , deapN := m.deapN + ev.apDeallocN
    , enqN := m.enqN + (if ev.enqF then 1 else 0)
    , enqT := fst m.enqT ev.enqF
    , wf0 := m.wf0 + (if ev.wfF0 then 1 else 0)
    , wf1 := m.wf1 + (if ev.wfF1 then 1 else 0)
    , end0 := m.end0 + (if ev.end0 then 1 else 0)
    , end1 := m.end1 + (if ev.end1 then 1 else 0)
    , deq0 := m.deq0 + (if ev.deq0 then 1 else 0)
    , deq1 := m.deq1 + (if ev.deq1 then 1 else 0)
    , deq0tag1 := if ev.deq0 && (m.deq0 == 0) then ev.deqTag0 else m.deq0tag1
    , deq0tag2 := if ev.deq0 && (m.deq0 == 1) then ev.deqTag0 else m.deq0tag2
    , arb0 := m.arb0 + (if ev.arbF && (ev.arbCu == 0#1) then 1 else 0)
    , arb1 := m.arb1 + (if ev.arbF && (ev.arbCu == 1#1) then 1 else 0)
    , rtDeN := m.rtDeN + (if ev.rtDeF then 1 else 0)
    , hdN := m.hdN + (if ev.hdF then 1 else 0)
    , hdT := fst m.hdT ev.hdF
    , hdWg1 := if ev.hdF && (m.hdN == 0) then ev.hdWg else m.hdWg1
    , hdWg2 := if ev.hdF && (m.hdN == 1) then ev.hdWg else m.hdWg2
    , hdWg3 := if ev.hdF && (m.hdN == 2) then ev.hdWg else m.hdWg3
    , rejN := m.rejN + (if ev.rejF then 1 else 0) }
  , s' )

/- ========================================================================= -/
/- 5. 小件数值回归（III 类自检）                                                -/
/- ========================================================================= -/

-- 描述符 → allocator 请求转换
example : mctDesc2Alc ⟨7#32, 2#4, 100#12, 64#11, 256#18, 32#12, 32#11, 0#18, 0#32, 0#32⟩
    = ⟨2#4, 100#12, 64#11, 256#18⟩ := rfl

-- rt 空表初始：alloc 接受条件成立；scan 与空表一致（rtScan 空表 = (N, 0)，
-- 与 alcInit 的 cache 初值一致——组合起点一致性）
example : mctRtAllocRdy mctRtInit = true := by native_decide
example : rtScan rtEmpty rtNUM_SGPR = (2048, 0) := by native_decide

-- rt alloc 应用：空 CU0 sgpr 表申请 100 → base 0、插入后 cnt=1、scan 排队
example :
    let op : MctRtOp := ⟨true, 0#1, 3#3, 0#18, 100#12, 0#11, true, true, true, 0⟩
    let (rt', bs) := mctRtApplyAlloc mctRtInit op
    (bs.sgpr == 0#11) && ((rt'.sgpr ⟨0, by decide⟩).cnt == 1) &&
    (rt'.scanSgpr.length == 1) &&
    ((rt'.scanSgpr.head?.getD ⟨0,0,0,0⟩).s0 == 1948) := by native_decide

-- rt dealloc 应用：摘除后 cnt=0、scan 队尾（dealloc 排的）值回到 (2048, 0)
-- （队首仍是 alloc 时排的 (1948, 0)，两条按序推送 allocator）
example :
    let opA : MctRtOp := ⟨true, 0#1, 3#3, 0#18, 100#12, 0#11, true, true, true, 0⟩
    let rt1 := (mctRtApplyAlloc mctRtInit opA).1
    let opD : MctRtOp := ⟨false, 0#1, 3#3, 0, 0, 0, false, true, false, 0⟩
    let rt2 := mctRtApplyDealloc rt1 opD
    ((rt2.sgpr ⟨0, by decide⟩).cnt == 0) && (rt2.scanSgpr.length == 2) &&
    ((rt2.scanSgpr.getLast?.getD ⟨0,0,0,0⟩).s0 == 2048) &&
    ((rt2.lds ⟨0, by decide⟩).cnt == 0) := by native_decide

-- settle：cnt=0 的头部被应用；cnt>0 不应用
example :
    let op : MctRtOp := ⟨true, 0#1, 0#3, 0#18, 100#12, 0#11, true, true, true, 0⟩
    let rt := { mctRtInit with ops := [op] }
    ((mctRtSettle rt).1.sgpr ⟨0, by decide⟩).cnt == 1 := by native_decide
example :
    let op : MctRtOp := ⟨true, 0#1, 0#3, 0#18, 100#12, 0#11, true, true, true, 2⟩
    let rt := { mctRtInit with ops := [op] }
    ((mctRtSettle rt).1.sgpr ⟨0, by decide⟩).cnt == 0 := by native_decide

/- ========================================================================= -/
/- 6. 场景 A：单 WG 全生命周期闭环                                              -/
/-    host 下发 WG（2 warp，sgpr/vgpr 各 64、lds 1024）→ wgb → allocator       -/
/-    （CU_PREFER 选 CU0，slot0）→ rt best-fit（基址全 0）→ cuif 二拆           -/
/-    （wf0: sgpr 0、wf1: sgpr 32）→ CTA2warp(0)（wid0/wid1）→ SM0 执行         -/
/-    lui x1 + endprg → warpRsp ×2 → gather 精确计 2 → rt_dealloc +            -/
/-    host_wg_done(wgId) → rt 摘除 + slotQ 回收 + scan 复原 cache               -/
/- ========================================================================= -/

/-- 场景程序（两 SM 共用；纯寄存器：lui x1,0x10000 ; endprg——I-46/47 的
    flush 窗口在无 dirty 行下不触发，MCT-B2） -/
def mctProgA : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x100000B7#32        -- lui  x1, 0x10000（x1 ← 0x10000000）
    else if pc = 0x04#32 then 0x0000400B#32   -- endprg
    else 0#32

/-- 场景 A 的 WG：wgId=0xA5、2 warp、sgpr/vgpr 各 64（per-wf 32）、lds 1024 -/
def mctWgA : MctWgDesc :=
  ⟨0xA5#32, 2#4, 64#12, 64#11, 1024#18, 32#12, 32#11, 0#18, 0#32, 0#32⟩

def mctNA : Nat := 200

/-- 输入：t=0 host 下发 WG A，其后空转 -/
def mctInsA : List (Option MctWgDesc) :=
  (List.range mctNA).map fun t => if t = 0 then some mctWgA else none

def mctS0A : MctState := mctInit msmSmLd0 msmSmLd0

def mctRunChkA : MctChk × MctState :=
  mctInsA.foldl (mctMonStep mctProgA mctProgA) (mctChk0, mctS0A)

/-- 场景 A 事件链判收（监控器层：链路连通 + 计数精确） -/
def mctEvtOkA (m : MctChk) : Bool :=
  -- 全生命周期事件计数：host1、alloc1、rt 应用 alloc1/dealloc1、enq1、
  -- SM0 派发 2 warp、SM0 两个 warp_end、CU0 两笔 CTArsp 出队、gather 两笔、
  -- rt dealloc 1、host 上报 1、无 REJECT（MCT-B1：场景内缓存精确）
  (m.hostN == 1) && (m.allocN == 1) && (m.apN == 1) && (m.deapN == 1) &&
  (m.enqN == 1) && (m.wf0 == 2) && (m.wf1 == 0) &&
  (m.end0 == 2) && (m.end1 == 0) &&
  (m.deq0 == 2) && (m.deq1 == 0) && (m.arb0 == 2) && (m.arb1 == 0) &&
  (m.rtDeN == 1) && (m.hdN == 1) && (m.rejN == 0) &&
  -- sm_id 分配与资源分配：CU0、slot0、基址全 0（空表 best-fit）
  (m.allocCu == 0#1) && (m.allocSlot == 0#3) &&
  (m.apSgpr == 0) && (m.apVgpr == 0) && (m.apLds == 0) &&
  -- 闭环：上报的 wgId 就是 host 下发的 wgId
  (m.hdWg1 == 0xA5#32) &&
  -- wf_gather 计数精确：两笔 done 回流 tag = slot0 的 wf0/wf1（0b000000/
  -- 0b000001，顺序不限），无一错计（I-25 未触发的直接证据）
  ((m.deq0tag1 == 0#6) && (m.deq0tag2 == 1#6) ||
   (m.deq0tag1 == 1#6) && (m.deq0tag2 == 0#6)) &&
  -- 因果序：host 派发 ≺ alloc ≺ rt 应用 ≺ cuif 入队 ≺ host 上报
  (m.allocT > 0) && (m.apT > m.allocT) && (m.enqT > m.apT) && (m.hdT > m.enqT)

/-- **场景 A 事件链定理（闭环连通性）**。（单遍 native_decide；公理审计多
    Lean.ofReduceBool，归档注明。） -/
theorem mctTraceA_evt : mctEvtOkA mctRunChkA.1 = true := by
  native_decide

/-- 场景 A 终态判收（资源分配到达 SM + 执行证据 + 全链回收无泄漏） -/
def mctFinOkA (m : MctChk) (sf : MctState) : Bool :=
  mctEvtOkA m &&
  -- **资源分配正确到达 SM**：wf0 → wid0（sgpr/vgpr 基址 0）、
  -- wf1 → wid1（sgpr/vgpr 基址 32 = rt 基址 0 + 1 × numPerWf）
  (sf.msl.sm0.base.base.csr.sgprBase ⟨0, by decide⟩ == 0#12) &&
  (sf.msl.sm0.base.base.csr.sgprBase ⟨1, by decide⟩ == 32#12) &&
  (sf.msl.sm0.base.base.csr.vgprBase ⟨0, by decide⟩ == 0#11) &&
  (sf.msl.sm0.base.base.csr.vgprBase ⟨1, by decide⟩ == 32#11) &&
  -- **warp 在 SM 上执行完毕**：两 warp 的 lui x1 写回各自落在自己的 sgpr
  -- 段（wid0 → bank1 addr0；wid1 → bank2 addr8，ocWbScaBankId/ocWbScaAddr）
  ((smSrfAt sf.msl.sm0.base.base ⟨1, by decide⟩).mem ⟨0, by decide⟩ == 0x10000000#32) &&
  ((smSrfAt sf.msl.sm0.base.base ⟨2, by decide⟩).mem ⟨8, by decide⟩ == 0x10000000#32) &&
  -- **资源回收无泄漏**：rt 六表全空（CU0×3 经历了 alloc→dealloc 全程）
  ((sf.rt.lds ⟨0, by decide⟩).cnt == 0) && ((sf.rt.lds ⟨1, by decide⟩).cnt == 0) &&
  ((sf.rt.sgpr ⟨0, by decide⟩).cnt == 0) && ((sf.rt.sgpr ⟨1, by decide⟩).cnt == 0) &&
  ((sf.rt.vgpr ⟨0, by decide⟩).cnt == 0) && ((sf.rt.vgpr ⟨1, by decide⟩).cnt == 0) &&
  -- allocator 槽位簿记归零 + rtcache 复原（dealloc 后的 SCAN 推送已生效：
  -- CU0 三资源回到 (MAX, 0)，CU1 从未被动过）
  (sf.alc.wgslot ⟨0, by decide⟩ == 0#8) && (sf.alc.wgslot ⟨1, by decide⟩ == 0#8) &&
  (sf.alc.wfslot ⟨0, by decide⟩ == 0#4) && (sf.alc.wfslot ⟨1, by decide⟩ == 0#4) &&
  (sf.alc.cacheLds ⟨0, by decide⟩ ⟨0, by decide⟩ == 131072#18) &&
  (sf.alc.cacheSgpr ⟨0, by decide⟩ ⟨0, by decide⟩ == 2048#12) &&
  (sf.alc.cacheVgpr ⟨0, by decide⟩ ⟨0, by decide⟩ == 1024#11) &&
  (sf.alc.cacheSgpr ⟨0, by decide⟩ ⟨1, by decide⟩ == 0#12) &&
  (sf.alc.cacheSgpr ⟨1, by decide⟩ ⟨0, by decide⟩ == 2048#12) &&
  -- CTA 链归位：c2w 槽位/响应 FIFO、cuif fifo/gather 簿记、wgb、rt 队列
  (sf.c2w0.idxUsing == 0#8) && (sf.c2w0.fifo.length == 0) &&
  (sf.c2w1.idxUsing == 0#8) && (sf.c2w1.fifo.length == 0) &&
  (sf.cuif.fifo.length == 0) &&
  (List.finRange 16).all (fun g => sf.cuif.liveMem g == false) &&
  (List.finRange 16).all (fun g => sf.cuif.cntMem g == 0#4) &&
  (sf.wgb.valid == 0#8) &&   -- wgb.alloc 位在 accept 后不主动清除（WgBuffer.lean
                             -- Q-WGB3 的忠实建模：被 valid=0 掩蔽、复用时经
                             -- rstmask1 清除），故不归零断言
  (sf.rt.slotQ.length == 0) && sf.rt.ops.isEmpty && sf.rt.bases.isNone &&
  sf.rt.scanLds.isEmpty && sf.rt.scanSgpr.isEmpty && sf.rt.scanVgpr.isEmpty &&
  sf.alcBuf.isNone &&
  -- SM/L2 归位
  (sf.msl.sm0.base.base.ws.warpActive == 0#8) &&
  (sf.msl.sm1.base.base.ws.warpActive == 0#8) &&
  (sf.msl.sm0.lsu.state == Mem.lsuSIdle) && (sf.msl.sm1.lsu.state == Mem.lsuSIdle) &&
  (sf.msl.sm0.dc.miss.isNone) && (sf.msl.sm1.dc.miss.isNone) &&
  (sf.msl.sm0.dc.wbQ.isEmpty) && (sf.msl.sm1.dc.wbQ.isEmpty) &&
  (sf.msl.sc.valids == 0#32) && !sf.msl.sc.drbValid && sf.msl.memQ.isEmpty &&
  (sf.msl.sinkA.lists == 0#32)

/-- **场景 A 主定理（CTA 全模型整机闭环）**：一个 2-warp WG 从 host 下发，
    经 wgb → allocator（CU0/slot0）→ rt best-fit（基址 0）→ cuif 二拆 →
    CTA2warp → SM0 执行（lui 写回落点验证 sgpr 基址）→ endprg ×2 → warpRsp
    回流 → wf_gather 精确计 2 → rt dealloc + host_wg_done(wgId) → 资源全
    回收（六表空、簿记零、cache 复原、全链归位）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem mctTraceA_ok : mctFinOkA mctRunChkA.1 mctRunChkA.2 = true := by
  native_decide

/- ========================================================================= -/
/- 7. 场景 B：多 WG 并发/相继（资源分配不交）                                   -/
/-    t=0/1/2 host 连续下发 WG-A（2wf，sgpr/vgpr 各 256）、WG-B（1wf，各        -/
/-    128）、WG-C（2wf，各 256）。allocator 轮转（cu 初值 1）：A→CU0、B→CU1、   -/
/-    C→CU0（与 A 同 CU 相继共存）。A/C 在 CU0 的资源段必须不交（机制 =        -/
/-    ResourceTable.lean 的 rt_alloc_disjoint：best-fit 分配与全部在驻区间      -/
/-    不交；本场景为其组合层数值见证）。三 WG 各自经全链执行并回收。           -/
/- ========================================================================= -/

/-- WG-A：wgId=0xA0，2 warp，sgpr/vgpr 各 256（per-wf 128）、无 lds -/
def mctWgB1 : MctWgDesc :=
  ⟨0xA0#32, 2#4, 256#12, 256#11, 0#18, 128#12, 128#11, 0#18, 0#32, 0#32⟩
/-- WG-B：wgId=0xB0，1 warp，sgpr/vgpr 各 128 -/
def mctWgB2 : MctWgDesc :=
  ⟨0xB0#32, 1#4, 128#12, 128#11, 0#18, 128#12, 128#11, 0#18, 0#32, 0#32⟩
/-- WG-C：wgId=0xC0，2 warp，sgpr/vgpr 各 256（per-wf 128） -/
def mctWgB3 : MctWgDesc :=
  ⟨0xC0#32, 2#4, 256#12, 256#11, 0#18, 128#12, 128#11, 0#18, 0#32, 0#32⟩

def mctNB : Nat := 200

/-- 输入：t=0/1/2 连续下发 A/B/C，其后空转 -/
def mctInsB : List (Option MctWgDesc) :=
  (List.range mctNB).map fun t =>
    if t = 0 then some mctWgB1
    else if t = 1 then some mctWgB2
    else if t = 2 then some mctWgB3
    else none

def mctRunChkB : MctChk × MctState :=
  mctInsB.foldl (mctMonStep mctProgA mctProgA) (mctChk0, mctInit msmSmLd0 msmSmLd0)

/-- 场景 B 事件链判收 -/
def mctEvtOkB (m : MctChk) : Bool :=
  -- 计数：3 WG 全链各走一遍；SM0 执行 A(2wf)+C(2wf)，SM1 执行 B(1wf)
  (m.hostN == 3) && (m.allocN == 3) && (m.apN == 3) && (m.deapN == 3) &&
  (m.enqN == 3) && (m.wf0 == 4) && (m.wf1 == 1) &&
  (m.end0 == 4) && (m.end1 == 1) &&
  (m.deq0 == 4) && (m.deq1 == 1) && (m.arb0 == 4) && (m.arb1 == 1) &&
  (m.rtDeN == 3) && (m.hdN == 3) && (m.rejN == 0) &&
  -- **资源分配不交（CU0 上 A 与 C）**：A 的 sgpr/vgpr 段 [0,256) 与
  -- C 的 [256,512) 端点相接而不交（rt_alloc_disjoint 的组合层数值见证；
  -- B 在 CU1 的独立表上分配基址 0）
  (m.apSgpr == 0) && (m.apVgpr == 0) &&
  (m.apSgpr2 == 0) && (m.apVgpr2 == 0) &&
  (m.apSgpr3 == 256) && (m.apVgpr3 == 256) &&
  (m.apSgpr + 256 ≤ m.apSgpr3) && (m.apVgpr + 256 ≤ m.apVgpr3) &&
  -- 三笔上报的 wgId 恰为 {A, B, C}（次序任意：gather 固定 CU0 优先 +
  -- 各 SM 执行进度共同决定）
  ((m.hdWg1 == 0xA0#32) || (m.hdWg1 == 0xB0#32) || (m.hdWg1 == 0xC0#32)) &&
  ((m.hdWg2 == 0xA0#32) || (m.hdWg2 == 0xB0#32) || (m.hdWg2 == 0xC0#32)) &&
  ((m.hdWg3 == 0xA0#32) || (m.hdWg3 == 0xB0#32) || (m.hdWg3 == 0xC0#32)) &&
  (m.hdWg1 != m.hdWg2) && (m.hdWg1 != m.hdWg3) && (m.hdWg2 != m.hdWg3) &&
  -- I-25 观测：CU0 的前两笔回流 tag = A 的 wf0/wf1（A 的 warp 先行结束，
  -- 其响应在 wid 被 C 复用前已被消费——无污染）
  ((m.deq0tag1 == 0#6) && (m.deq0tag2 == 1#6) ||
   (m.deq0tag1 == 1#6) && (m.deq0tag2 == 0#6))

/-- 场景 B 终态判收（SM 侧基址断言说明：A 的两个 warp 执行快（endprg 约
    派发后 9 拍），C 的 warp 派发到 SM0 时 A 的 warp 已结束、wid0/wid1
    已被释放（c2w 最低空闲位复用）——故 csr 终态保留的是 C 的基址
    （wid0=256、wid1=384），而 A 的写回证据留在 srf 的原落点；I-25 的
    污染窗口（响应滞留 ≥2 拍 + 同 wid 复用）在本场景不触发：响应均被
    cuif 即时消费（deq0tag1/2 = 0/1 见证）。 -/
def mctFinOkB (m : MctChk) (sf : MctState) : Bool :=
  mctEvtOkB m &&
  -- csr 终态 = C 的基址（wid 复用，见上注）；wid2/3 从未被派发（wf0=4 佐证）
  (sf.msl.sm0.base.base.csr.sgprBase ⟨0, by decide⟩ == 256#12) &&
  (sf.msl.sm0.base.base.csr.sgprBase ⟨1, by decide⟩ == 384#12) &&
  (sf.msl.sm0.base.base.csr.sgprBase ⟨2, by decide⟩ == 0#12) &&
  (sf.msl.sm0.base.base.csr.sgprBase ⟨3, by decide⟩ == 0#12) &&
  (sf.msl.sm0.base.base.csr.vgprBase ⟨0, by decide⟩ == 256#11) &&
  (sf.msl.sm1.base.base.csr.sgprBase ⟨0, by decide⟩ == 0#12) &&
  -- 执行证据：四 warp 的 lui 写回落点 = A wf0(b1,a0) / A wf1(b2,a32) /
  -- C wf0(b1,a64) / C wf1(b2,a96)——同一 wid 不同 sgpr 段，落点不交
  ((smSrfAt sf.msl.sm0.base.base ⟨1, by decide⟩).mem ⟨0, by decide⟩ == 0x10000000#32) &&
  ((smSrfAt sf.msl.sm0.base.base ⟨2, by decide⟩).mem ⟨32, by decide⟩ == 0x10000000#32) &&
  ((smSrfAt sf.msl.sm0.base.base ⟨1, by decide⟩).mem ⟨64, by decide⟩ == 0x10000000#32) &&
  ((smSrfAt sf.msl.sm0.base.base ⟨2, by decide⟩).mem ⟨96, by decide⟩ == 0x10000000#32) &&
  ((smSrfAt sf.msl.sm1.base.base ⟨1, by decide⟩).mem ⟨0, by decide⟩ == 0x10000000#32) &&
  -- 资源回收无泄漏（同场景 A 的归位断言）
  ((sf.rt.lds ⟨0, by decide⟩).cnt == 0) && ((sf.rt.lds ⟨1, by decide⟩).cnt == 0) &&
  ((sf.rt.sgpr ⟨0, by decide⟩).cnt == 0) && ((sf.rt.sgpr ⟨1, by decide⟩).cnt == 0) &&
  ((sf.rt.vgpr ⟨0, by decide⟩).cnt == 0) && ((sf.rt.vgpr ⟨1, by decide⟩).cnt == 0) &&
  (sf.alc.wgslot ⟨0, by decide⟩ == 0#8) && (sf.alc.wgslot ⟨1, by decide⟩ == 0#8) &&
  (sf.alc.wfslot ⟨0, by decide⟩ == 0#4) && (sf.alc.wfslot ⟨1, by decide⟩ == 0#4) &&
  (sf.alc.cacheSgpr ⟨0, by decide⟩ ⟨0, by decide⟩ == 2048#12) &&
  (sf.alc.cacheSgpr ⟨1, by decide⟩ ⟨0, by decide⟩ == 2048#12) &&
  (sf.alc.cacheVgpr ⟨0, by decide⟩ ⟨0, by decide⟩ == 1024#11) &&
  (sf.c2w0.idxUsing == 0#8) && (sf.c2w0.fifo.length == 0) &&
  (sf.c2w1.idxUsing == 0#8) && (sf.c2w1.fifo.length == 0) &&
  (sf.cuif.fifo.length == 0) &&
  (List.finRange 16).all (fun g => sf.cuif.liveMem g == false) &&
  (List.finRange 16).all (fun g => sf.cuif.cntMem g == 0#4) &&
  (sf.wgb.valid == 0#8) &&
  (sf.rt.slotQ.length == 0) && sf.rt.ops.isEmpty && sf.rt.bases.isNone &&
  sf.rt.scanLds.isEmpty && sf.rt.scanSgpr.isEmpty && sf.rt.scanVgpr.isEmpty &&
  sf.alcBuf.isNone &&
  (sf.msl.sm0.base.base.ws.warpActive == 0#8) &&
  (sf.msl.sm1.base.base.ws.warpActive == 0#8) &&
  (sf.msl.sm0.lsu.state == Mem.lsuSIdle) && (sf.msl.sm1.lsu.state == Mem.lsuSIdle) &&
  (sf.msl.sm0.dc.miss.isNone) && (sf.msl.sm1.dc.miss.isNone) &&
  (sf.msl.sc.valids == 0#32) && !sf.msl.sc.drbValid && sf.msl.memQ.isEmpty

/-- **场景 B 主定理（多 WG 并发/相继）**：三 WG 相继下发，A→CU0、B→CU1、
    C→CU0 与 A 相继共存；A/C 在 CU0 的 sgpr/vgpr 段 [0,256)/[256,512) 不交
    （rt_alloc_disjoint 机制的组合层见证）；三 WG 全部执行完毕并正确回收
    上报（wgId 集合精确、无 REJECT、无泄漏）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem mctTraceB_ok : mctFinOkB mctRunChkB.1 mctRunChkB.2 = true := by
  native_decide

/- ========================================================================= -/
/- 7.5 资源不交性的定理级引用（rt_alloc_disjoint 在场景 B 具体状态上的实例化） -/
/- ========================================================================= -/

/-- 场景 B 的 CU0 sgpr 链表在 WG-A（slot0，256 项）应用后的具体状态
    （与组合轨迹中 apT 拍的 sf.rt.sgpr 0 同构造） -/
def mctRamBCu0A : RtRam := rtStep rtEmpty rtNUM_SGPR (.alloc ⟨0, by decide⟩ 256)

/-- 空表良构（cnt=0 时全部量化条件 vacuous） -/
theorem mctRtWfEmpty : RtWf rtEmpty rtNUM_SGPR where
  npos := by native_decide
  cntLe := by native_decide
  bounds := by intro i h; have h0 : i < 0 := h; omega
  sorted := by intro i h; have h0 : i + 1 < 0 := h; omega
  prevOk := by intro i h; have h0 : i + 1 < 0 := h; omega
  tailOk := by intro h; have h0 : 0 < 0 := h; omega

/-- A 的 alloc 在空表上守约 -/
theorem mctRtOkA : rtEventOk rtEmpty rtNUM_SGPR (.alloc ⟨0, by decide⟩ 256) := by
  refine ⟨by native_decide, ?_, ?_⟩
  · intro i h; have h0 : i < 0 := h; omega
  · exact Or.inr ⟨0, by native_decide, by native_decide⟩

/-- A 应用后链表良构（rt_step_wf 实例） -/
theorem mctRtWfA : RtWf mctRamBCu0A rtNUM_SGPR :=
  rt_step_wf rtEmpty rtNUM_SGPR mctRtWfEmpty _ mctRtOkA

/-- C（slot1，256 项）的 alloc 在 A 在驻的链表上守约 -/
theorem mctRtOkC : rtEventOk mctRamBCu0A rtNUM_SGPR (.alloc ⟨1, by decide⟩ 256) := by
  refine ⟨by native_decide, ?_, ?_⟩
  · intro i hi
    have hc : mctRamBCu0A.cnt = 1 := by native_decide
    rw [hc] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [show mctRamBCu0A.walk 0 = ⟨0, by decide⟩ from by native_decide]
    decide
  · exact Or.inr ⟨1, by native_decide, by native_decide⟩

/-- **场景 B 资源不交性（rt_alloc_disjoint 的组合级实例化）**：CU0 sgpr 表
    在 A（slot0，区间 [0,256)）在驻时，C（slot1，size 256）的契约内分配
    基址 = 256，与 A 的区间端点相接而不交（addr2(A) = 255 < 256）。
    组合轨迹的数值见证（mctTraceB_ok 的 apSgpr=0/apSgpr3=256）与此同源。 -/
theorem mctRtB_disjoint :
    rtAllocBase mctRamBCu0A rtNUM_SGPR ⟨1, by decide⟩ 256 = 256 ∧
    mctRamBCu0A.addr2 (mctRamBCu0A.walk 0) <
      rtAllocBase mctRamBCu0A rtNUM_SGPR ⟨1, by decide⟩ 256 := by
  have h := rt_alloc_disjoint mctRamBCu0A rtNUM_SGPR mctRtWfA ⟨1, by decide⟩ 256
    mctRtOkC (by decide) 0 (by native_decide)
  have hbase : rtAllocBase mctRamBCu0A rtNUM_SGPR ⟨1, by decide⟩ 256 = 256 := by
    native_decide
  have ha1 : mctRamBCu0A.addr1 (mctRamBCu0A.walk 0) = 0 := by native_decide
  rw [hbase, ha1] at h
  refine ⟨hbase, ?_⟩
  rcases h with hl | hr
  · omega
  · rw [hbase]; exact hr

/- ========================================================================= -/
/- 8. 发现与公理审计                                                           -/
/-                                                                            -/
/-  I 类（对原版 Chisel 的审查）：本文件组合轨迹未触发新 I 类 bug；既有已知     -/
/-    现场的组合行为核查结果：                                                -/
/-    - I-25（CTA2warp tag 迟读污染）：组合中污染窗口真实存在（c2w 迟读 +       -/
/-      gather 反压均忠实建模），场景 A/B 的时序下响应均被即时消费、wid 复用    -/
/-      晚于响应消费（场景 B 的 deq0tag1/2 = 0/1 为证）——窗口未命中，与         -/
/-      CTA2warp.lean T7 的触发条件分析一致（需响应滞留 ≥2 拍且同 wid 复用）。  -/
/-    - I-46/I-47（endprg 不等在飞、上报不等 flush）：场景用纯寄存器程序，       -/
/-      无在飞访存/dirty 行，warpRsp 单拍脉冲语义照常建模但不产生可观测后果。   -/
/-    - WgBuffer.lean Q-WGB3（accept 不清 wgram_alloc 位）在组合终态可观测：     -/
/-      场景 A 终态 wgb.alloc = 0b1 残留——被 valid=0 掩蔽、复用时经 rstmask1    -/
/-      清除，确认非 bug（本文件 mctFinOkA 相应断言已按此语义书写）。           -/
/-    - Top.lean Q3（cta2host 的 cu_id 在顶层丢弃）：本组合的 host 上报只取      -/
/-      wgId，与该连线事实一致。                                              -/
/-  II 类（翻译/组合层）：本文件新逻辑 = rt 组合模型（MCT-D2）、幽灵簿记         -/
/-    （MCT-D3/D4）、三源会合与双 CTA2warp 接线——全部为组合层纯函数，配 §5      -/
/-    数值回归（desc 转换、rt alloc/dealloc/settle、空表 scan 与 alcInit 的      -/
/-    一致性）。已知偏差面（降级，MCT-B1/D2）：rt 三 handler 合并为单事件流、    -/
/-    alloc/dealloc/scan 取固定延迟、cuinterface_buf 无 pipe 直通（慢一拍）、    -/
/-    cu_wf_done 仲裁固定 CU0 优先（沿用 CuInterface.lean D3）、cuif init 窗     -/
/-    抽象（MCT-D7）。这些只影响时序不影响事件语义；场景 A/B 的断言不含任何     -/
/-    写死的中间拍号（只断言计数、因果序、终态）。                              -/
/-  III 类：调试中发现本文件初版 dealloc 回归例期望值写错（scan 队首/队尾取错， -/
/-    已修正）；mctEvtOkA 初版未发现规格错误（一次通过）。                       -/
/- ========================================================================= -/

#print axioms mctTraceA_evt
#print axioms mctTraceA_ok
#print axioms mctTraceB_ok
#print axioms mctRtB_disjoint

end Ventus
