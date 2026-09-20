/- ========================================================================= -/
/-                         MultiSML2.lean                                    -/
/-  多 SM 整机组合第二块（MSM-O1 障碍消解）：2×SM（SMMemDc.lean §3H 的          -/
/-  smdStepH 握手变体，SMD-D7）+ **真实 L2 模型组合**（L2/L2Channels 的         -/
/-  SinkA/SinkD + L2/L2MSHR 的 32 项 MSHR + L2/Directory 的 Directory_test    -/
/-  + L2/Scheduler 的 Scheduler，均逐拍例化真实 step 函数）。                  -/
/-                                                                           -/
/-  真实链路（对 Chisel 顶层 L2Cache.scala 的接线，逐信号对应）：               -/
/-    SM.dc ──A(Get/Put)──▶ [仲裁 MSL-D1] ─▶ SinkA ──req──▶ Scheduler          -/
/-      Scheduler.request ─▶ Directory.read（io.read，:238-239）               -/
/-      Directory.result ─▶ Scheduler（allocate/secondary push/drb enq）       -/
/-      MSHR schedule.a ─▶ SourceA ─▶ 外层内存（memCycles=32，MSL-D4）         -/
/-      外层内存 D ─▶ SinkD ─▶ Scheduler.sinkd ─▶ MSHR.dataReg                 -/
/-      MSHR schedule.dir ─▶ Directory.write（:227，valid 直连）               -/
/-      schedule.d pop / drb deq ─▶ D 通道响应 ─▶ SM.dc（grant，SMD-D7）       -/
/-      Put 数据：SinkA putbuffer ─(pb_pop @ resultFire, MSL-D7)─▶ dataMem     -/
/-                                                                           -/
/- ======================== 建模决策（MSL-D 区） ============================= -/
/-  MSL-D0. SM 侧复用 smdStepH（SMMemDc.lean §3H，SMD-D7）：miss=Get acquire    -/
/-      重举至接受、refill 等 grant、dirty 驱逐/flush 写回经 wbQ 出 Put、       -/
/-      hintAck 需 wbQ 排空。source 编码：SM0=0、SM1=1（16 位）。               -/
/-  MSL-D1. A 通道仲裁 = 固定优先级 SM0>SM1（同 MSM-D1；单 outstanding ⇒        -/
/-      每 SM 至多 1 Get 在飞， starvation 不可持续）。                         -/
/-  MSL-D2. Scheduler 的 requests ListBuffer 在其模型中只有 valid 影子          -/
/-      （Scheduler.lean D2：队深≥2 时 HW pop 保持 valid 而影子清 0）。本组合    -/
/-      用 reqQ（每 entry 的 source FIFO）恢复 HW 语义：push（alloc 入          -/
/-      insertOH 位 / secondary 入 tagMatches 位）与 pop（schedule.d pop 于     -/
/-      select 位）逐拍跟踪，l2scStep 之后用 reqQ 非空重算 valids。队内容量     -/
/-      pushReady = 总深度 < 32（entry 池）。                                   -/
/-  MSL-D3. 数据面功能式：dataMem : BitVec 32 → BitVec 1024（块基址 → 行），     -/
/-      兼作 L2 BankedStore 与外层内存（二者在本场景无分歧：L2 命中数据即         -/
/-      上次 Put 落数，miss 数据即初值）。BankedStore 本体/SourceD 流水线不      -/
/-      例化（MSL-B1）。                                                      -/
/-  MSL-D4. 外层内存 = memCycles=32（l2MemCycles，top/parameters.scala:107）    -/
/-      倒计 FIFO + 真实 SinkD 寄存器链（sinkDStep/sinkDResp）。SourceA 侧      -/
/-      a.ready 恒 true（sourceAReqReady=true）。                               -/
/-  MSL-D5. sourceDReqReady 两遍消解：SourceD 不例化，其 d 通道反压 = 目标      -/
/-      SM 的 refill 门控（smdRefillRdyH，与壳内 smdRefillGoH 同源）。先按      -/
/-      sdRdy=true 求组合（wA），若 schedDValid 则目标 = reqQ 队头、否则 drb    -/
/-      头（非 Get 的 drb 项—Put 的 AccessAck—SM 侧无消费者，直接放行丢弃）；   -/
/-      目标不就绪则 sdRdy=false 重求（d 请求退出选择，drb 同拍被堵=队头阻      -/
/-      塞，与 SourceD 单口一致）。grant 与 pop/deq 严格同拍 ⇒ 无丢失。         -/
/-  MSL-D6. headOpcode 恒 Get：requests 队列在本组合场景只装 Get miss           -/
/-      （Put 均 hit、不进队列；putMiss 监控器守该前提）。                      -/
/-  MSL-D7. Put 数据落盘在 directory resultFire 拍（pb_pop 同拍弹出），比真     -/
/-      实 SourceD 早数拍；场景内无同块并发读写，无时序分歧。                   -/
/-  MSL-D8. Directory read.valid = request 可接受（reqAcc = reqValid ∧          -/
/-      mshrFree ∧ pushReady ∧ dir.ready ∧ !issueFlushInv），使 read.fire ≡      -/
/-      request.fire（消双重读）；与 HW 的差集（mshr 满/池满）在本场景外。      -/
/-  MSL-D9. Directory tag_match 由 tagMatches.orR 驱动（Scheduler.scala:231     -/
/-      的自然接线； Directory:172 notReplace 的唯一外部来源）。                -/
/-  MSL-D10. 每拍求值序：SM 请求（拍前状态）→ SinkA req 组合 → Directory 两     -/
/-      趟（resultReady 依赖 resultHit，后者不依赖 resultReady，无环）→         -/
/-      Scheduler 组合 → sdRdy 两遍消解 → SM/L2 各模块同步步进。全组合无        -/
/-      跨模块组合环（目录 result 由寄存器输出驱动）。                          -/
/-  MSL-D11【新踩坑，实测】L2scState.mshrs 是 `Nat → L2mState` 函数字段：       -/
/-      l2scStep 每拍裹一层闭包且访问无记忆化 ⇒ 第 t 拍单次访问 O(t) 展开、     -/
/-      全程 O(T²)（220 拍实测 >50min 不可行）。组合层每拍把 32 个 entry        -/
/-      物化进 Array（reqQ 同），链长恒 1（物化后全模块构建 ~11s/场景）。       -/
/-      同族先例：SRAMTemplate.lean D10。另：Directory/cc_dir 的 wipe/复位      -/
/-      扫描（~66 拍）走真实路径（预暖捷径曾暴露 SRAM resetBusy 吞写教训——     -/
/-      reset 期间用户写被复位写覆盖，SRAMTemplate:108-114/:275-284）。        -/
/-                                                                           -/
/- ======================== 边界与障碍（MSL-B/O 区） ========================= -/
/-  MSL-B1【降级】SourceD FSM（SourceD.lean，含其 Q5 stage_8 响应篡改 bug）     -/
/-      与 BankedStore（L2MSHR §4）不在组合内：响应生成/读数据到达时序由        -/
/-      MSL-D3/D5/D7 的功能式数据面替代。I-40（BankedStore 读写同行冲突）       -/
/-      因此不在组合可观测面内。                                                -/
/-  MSL-B2【边界】probe 不存在：Ventus L2 的 Directory_test 无 client 表、无    -/
/-      对 L1 的 probe 通道（模型 L2dIn/L2dOut 无相应字段，复审确认）；跨 L1     -/
/-      staleness 不检测（同 MSM-D3，真实硬件 L1 间不互一致）。"acquire/         -/
/-      release 全链路"在本设计 = Get acquire + AccessAckData grant + Put       -/
/-      write-back + flush HintAck（wbQ 排空驱动）。                            -/
/-  MSL-B3【边界】I-44（ListBuffer 池耗尽重复 refill）在本组合下**不可达**：    -/
/-      两 SM 各单 outstanding（SMD-D2）⇒ L2 并发请求 ≤2 ≪ entry 池 32；       -/
/-      pushReady 恒 true，E3 不破。I-44 的机证证据保持 Discharge.lean 手构     -/
/-      状态轨迹（本文件不重证）。                                              -/
/-  MSL-B4【边界】L2 flush（Hint→Directory 1024 拍扫描，含 I-35                -/
/-      flushCount 卡死）不触发：SM 侧 flush 的 L2 Hint 请求不                  -/
/-      发（沿用 SMD-D6 收窄，arb2Fire=false），HintAck 由 wbQ 排空驱动         -/
/-      （SMD-D7）。跨 SM 可见性只需 L1→L2 的 Put，不需要 L2→外层内存 flush。   -/
/-  MSL-O1【残余】SinkC/SinkE、TL-C/E 通道无（Ventus L1 无主动 release          -/
/-      probe 应答语义）；MSM-O2（CTA 全模型）依旧，派发 = SmIn 事件注入。      -/
/- ========================================================================= -/

import Ventus.MultiSM
import Ventus.L2.Scheduler
import Ventus.L2.Directory

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith
open Ventus.L2 Ventus.L2.L2MSHR Ventus.L2.L2Scheduler

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 数据打包与请求转换小件                                                     -/
/- ========================================================================= -/

/-- 32 字行 → 1024 位 TL 数据（字 k 占 bit [32k+31:32k]，LSB-first，
    与 BankedStore.scala:108/asUInt 一致，对照 L2MSHR D8 字节序） -/
def mslPackRow (f : Fin 32 → BitVec 32) : BitVec 1024 :=
  (List.finRange 32).foldl (fun acc i =>
    acc ||| ((f i).zeroExtend 1024 <<< (32 * i.val))) 0#1024

/-- 1024 位 TL 数据 → 32 字行（mslPackRow 的逆） -/
def mslUnpackRow (d : BitVec 1024) : Fin 32 → BitVec 32 :=
  fun i => d.extractLsb' (32 * i.val) 32

/-- L2 数据阵列/外层内存初值：与 smdL2Init 同模式（块基址 [31:7] = blockAddr） -/
def mslDataInit (addr : BitVec 32) : BitVec 1024 :=
  mslPackRow (smdL2Init (addr.extractLsb' 7 25))

/-- 字节掩码合并（Put 落数；mask 位 k 管字节 k，BankedStore waymask 语义） -/
def mslMergeMask (old new : BitVec 1024) (mask : BitVec 128) : BitVec 1024 :=
  (List.finRange 128).foldl (fun acc i =>
    if mask.getLsbD i.val then
      (acc &&& ~~~((0xFF#8).zeroExtend 1024 <<< (8 * i.val))) |||
        ((new.extractLsb' (8 * i.val) 8).zeroExtend 1024 <<< (8 * i.val))
    else acc) old

/-- SM 请求 → TLBundleA（SinkA 输入）。地址 = blockAddr 补 7 位 0（块基址）；
    size=7（128B）；Put 全掩码；Get 不带数据（dat 字段无语义，MSHR Q7 同类） -/
def mslBundleA (src : BitVec 16) (r : SmdAReq) : TLBundleA where
  opcode := r.op
  size := 7#7
  source := src
  address := r.ba.zeroExtend 32 <<< 7
  mask := BitVec.allOnes 128
  data := mslPackRow r.dat
  param := 0#3

/-- L2Channels.FullRequest → Directory.L2FullRequest（字段恒等；l2cidx 0 宽 →
    BitVec 1 恒 0，Directory.lean D3） -/
def mslToFullReq (r : FullRequest) : L2FullRequest where
  opcode := r.opcode
  size := r.size
  source := r.source
  tag := r.tag
  offset := r.offset
  put := r.put
  data := r.data
  mask := r.mask
  param := r.param
  set := r.set
  l2cidx := 0#1

/-- Directory result → Scheduler 的 L2mStatus（allocate.bits 恒等直传，
    Scheduler.lean D8；offset/param/data 在 DirectoryResult_lite 中不存在，
    置 0——消费侧（MSHR aBits/merge）对本场景不读它们） -/
def mslDirRes (o : L2dOut) : L2mStatus where
  opcode := o.resultOpcode
  size := o.resultSize
  source := o.resultSource
  tag := o.resultTag
  offset := 0#7
  put := o.resultPut
  data := 0#1024
  mask := o.resultMask
  param := 0#3
  set := o.resultSet
  l2cidx := BitVec.ofNat 0 0
  hit := o.resultHit
  way := o.resultWay
  dirty := o.resultDirty
  flush := o.resultFlush
  lastFlush := o.resultLastFlush

/- ========================================================================= -/
/- 2. 组合状态 / 组合求值 / mslStep                                            -/
/- ========================================================================= -/

/-- 外层内存（MSL-D4）在飞响应：目标 MSHR entry + 剩余拍数 -/
structure MslMemRsp where
  entry : Nat
  cnt : Nat
deriving DecidableEq, Repr

/-- 多 SM + 真实 L2 组合状态 -/
structure MslState where
  sm0 : SmdState
  sm1 : SmdState
  sinkA : SinkAState
  sc : L2scState
  dir : L2dState
  sinkD : SinkDState
  memQ : List MslMemRsp              -- 外层内存倒计 FIFO（MSL-D4）
  reqQ : Nat → List (BitVec 16)      -- 每 MSHR entry 的请求 source FIFO（MSL-D2）
  dataMem : BitVec 32 → BitVec 1024  -- 数据面（MSL-D3）

/-- 初始组合状态（SM 侧由调用方给；L2 侧全复位——Directory wipe + cc_dir
    SRAM 复位扫描约 66 拍（期间 request.ready=false，SM 的 acquire 由
    acqDone 重举机制等待）；物化优化（MSL-D11）后这段成本可忽略，故不取
    预暖捷径，保持真实复位路径） -/
def mslInit (sm0 sm1 : SmdState) : MslState where
  sm0 := sm0
  sm1 := sm1
  sinkA := sinkAInit
  sc := l2scInit
  dir := l2dInit
  sinkD := sinkDInit
  memQ := []
  reqQ := fun _ => []
  dataMem := mslDataInit

/-- requests 池 pushReady（MSL-D2：entry 总数 < 32） -/
def mslPushReady (s : MslState) : Bool :=
  decide ((List.range 32).foldl (fun acc i => acc + (s.reqQ i).length) 0 < 32)

/-- 目标 SM 的 refill 门控（MSL-D5 反压源；与壳内 smdRefillGoH 同源） -/
def mslGrantRdy (s : MslState) (src : BitVec 16) : Bool :=
  if src == 0#16 then smdRefillRdyH s.sm0.dc (Mem.mshrDcRdy s.sm0.mshr)
  else smdRefillRdyH s.sm1.dc (Mem.mshrDcRdy s.sm1.mshr)

/-- 一拍组合求值的全部中间量（MSL-D10；sdRdy 为两遍消解的参数） -/
structure MslW where
  dirOut : L2dOut
  dirIn : L2dIn
  scIn : L2scIn
  saIn : SinkAIn
  aFire : Bool
  schedDValid : Bool
  sel : Nat
  putResultFire : Bool

/-- 组合求值（给定 sdRdy）。求值序见 MSL-D10；Directory 两趟（resultReady
    依赖 resultHit，反向无依赖）。 -/
def mslWires (s : MslState) (aV : Bool) (aBits : TLBundleA) (sdRdy : Bool) : MslW :=
  -- SinkA req 组合（reqValid/reqBits 与 reqReady 无关，SinkA.scala:74,:78-92）
  let saIn0 : SinkAIn :=
    { aValid := aV, a := aBits, reqReady := true
    , pbPopValid := false, pbPopIndex := 0 }
  let reqV := sinkAReqValid s.sinkA saIn0
  let reqBits := sinkAReqBits s.sinkA saIn0
  -- Directory 探测（ready/writeReady 只依赖状态，Directory:271-272）
  let dirOut0 := l2dOut s.dir l2dInIdle
  let pushRdy := mslPushReady s
  -- request 可接受（MSL-D8；read.fire ≡ request.fire）
  let reqAcc := reqV && l2scMshrFree s.sc && pushRdy && dirOut0.ready &&
    !s.sc.issueFlushInv
  -- Directory write 口（Scheduler.scala:227：write.valid 直连 schedule.dir.valid）
  let scIn0 : L2scIn :=
    { l2scInIdle with
        sourceDReqReady := sdRdy
      , dirWriteReady := dirOut0.writeReady }
  let schedDirV := l2scSchedDirValid s.sc scIn0
  let selE := (s.sc.mshrs (l2scSelect s.sc scIn0)).request
  let dirInR : L2dIn := { l2dInIdle with
      writeValid := schedDirV
    , writeWay := selE.way
    , writeSet := selE.set
    , writeTag := selE.tag
    , readValid := reqAcc
    , readBits := mslToFullReq reqBits
    , resultReady := true }
  let dirOut1 := l2dOut s.dir dirInR
  -- result.ready（Scheduler.scala:246-252：hit→drb.enq.ready，miss→push.ready）
  let resultRdy := if dirOut1.resultHit then !s.sc.drbValid else pushRdy
  -- tag_match（MSL-D9）
  let scInPre : L2scIn :=
    { scIn0 with
        dirResValid := dirOut1.resultValid
      , dirRes := mslDirRes dirOut1 }
  let dirIn : L2dIn :=
    { dirInR with
        resultReady := resultRdy
      , tagMatchIn := (l2scTagMatches s.sc scInPre != 0#32) }
  let dirOut := l2dOut s.dir dirIn
  let requestRdy := reqAcc && dirOut.readReady
  -- SinkA 最终输入（Put 的 pb_pop 由 resultFire 驱动，MSL-D7）
  let putResFire := dirOut.resultValid && resultRdy &&
    ((dirOut.resultOpcode == l2opPutFull) || (dirOut.resultOpcode == l2opPutPartial))
  let saIn : SinkAIn :=
    { aValid := aV, a := aBits, reqReady := requestRdy
    , pbPopValid := putResFire, pbPopIndex := dirOut.resultPut }
  let aFire := aV && sinkAARdy s.sinkA saIn
  -- sinkd（真实 SinkD 的寄存输出，拍前状态）
  let sdResp := sinkDResp s.sinkD
  let scIn : L2scIn :=
    { l2scInIdle with
      dirResValid := dirOut.resultValid
    , dirRes := mslDirRes dirOut
    , dirWriteReady := dirOut.writeReady
    , dirReady := dirOut.ready
    , dirReadReady := dirOut.readReady
    , sourceAReqReady := true
    , sourceDReqReady := sdRdy
    , sinkdValid := sdResp.1
    , sinkdSource := sdResp.2.source
    , sinkdOpcode := sdResp.2.opcode
    , sinkdData := sdResp.2.data
    , reqValid := reqV
    , reqOpcode := reqBits.opcode
    , reqParam := reqBits.param
    , reqSource := reqBits.source
    , putbufEmpty := sinkAEmpty s.sinkA saIn
    , pushReady := pushRdy
    , headOpcode := l2mOpGet }
  { dirOut := dirOut, dirIn := dirIn, scIn := scIn, saIn := saIn
  , aFire := aFire
  , schedDValid := l2scSchedDValid s.sc scIn
  , sel := l2scSelect s.sc scIn
  , putResultFire := putResFire }

/-- 单拍事件（监控用；全部在拍前状态 + 本拍组合上求值） -/
structure MslEv where
  getFired0 : Bool
  getFired1 : Bool
  putFired0 : Bool
  putFired1 : Bool
  grant0 : Bool
  grant1 : Bool
  secPush : Bool      -- 本拍发生 MSHR secondary 合并（push 且非 alloc）
  popCnt : Nat        -- 拍后 MSHR 占用数（valids popcount，HW 语义恢复后）
  putMiss : Bool      -- Put 在 L2 miss（MSL-D6 前提守卫；本组合场景应恒 false）
  bad : Bool          -- 协议违例：pop 空队列 / grant 打到无 miss 的 SM
deriving DecidableEq, Repr

/-- BitVec 32 popcount（观测用） -/
def mslPopcount (x : BitVec 32) : Nat :=
  (List.range 32).foldl (fun acc i => acc + (if x.getLsbD i then 1 else 0)) 0

/-- 组合单拍：返回 (次态, 事件)。求值序见 MSL-D10；sdRdy 两遍消解见 MSL-D5。 -/
def mslStepAux (p0 p1 : SmProg) (s : MslState) (i0 i1 : SmIn) : MslState × MslEv :=
  -- 1. SM→L2 请求与仲裁（MSL-D0/D1）
  let areq0 := smdDcAReq s.sm0.dc
  let areq1 := smdDcAReq s.sm1.dc
  let aV := areq0.isSome || areq1.isSome
  let aSrc : BitVec 16 := if areq0.isSome then 0#16 else 1#16
  let aBits : TLBundleA := match areq0 with
    | some r => mslBundleA 0#16 r
    | none => match areq1 with
      | some r => mslBundleA 1#16 r
      | none => mslBundleA 0#16 { op := 0#3, ba := 0#25, dat := fun _ => 0#32 }
  -- 2. sdRdy 两遍消解（MSL-D5）
  let wA := mslWires s aV aBits true
  let sdRdy := if wA.schedDValid then
      mslGrantRdy s ((s.reqQ wA.sel).head?.getD 0#16)
    else if s.sc.drbValid then
      (if s.sc.drbBits.opcode == l2opGet then mslGrantRdy s s.sc.drbBits.source
       else true)
    else true
  let w := if sdRdy then wA else mslWires s aV aBits false
  -- 3. D 通道授权（pop=MSHR refill 弹队 / drbDeq=命中缓冲出队；二者互斥）
  let popFire := l2scPopValid s.sc w.scIn
  let popSrc := (s.reqQ w.sel).head?.getD 0#16
  let popData := (s.sc.mshrs w.sel).dataReg
  let drbDeq := s.sc.drbValid && !w.schedDValid && sdRdy
  let drbIsGet := s.sc.drbBits.opcode == l2opGet
  let drbAddr : BitVec 32 := expandAddress s.sc.drbBits.tag s.sc.drbBits.set 0#7
  let gV : BitVec 16 → Bool := fun k =>
    (popFire && (popSrc == k)) || (drbDeq && drbIsGet && (s.sc.drbBits.source == k))
  let gD : BitVec 16 → (Fin 32 → BitVec 32) := fun k =>
    if popFire && (popSrc == k) then mslUnpackRow popData
    else mslUnpackRow (s.dataMem drbAddr)
  let getF : BitVec 16 → Bool := fun k =>
    w.aFire && (aSrc == k) && (aBits.opcode == l2opGet)
  let putF : BitVec 16 → Bool := fun k =>
    w.aFire && (aSrc == k) && (aBits.opcode == l2opPutFull)
  let l2if0 : SmdL2If :=
    { grantV := gV 0#16, grantDat := gD 0#16
    , getFired := getF 0#16, putFired := putF 0#16 }
  let l2if1 : SmdL2If :=
    { grantV := gV 1#16, grantDat := gD 1#16
    , getFired := getF 1#16, putFired := putF 1#16 }
  -- 4. SM 步进（SMD-D7 握手变体）
  let sm0' := smdStepH p0 s.sm0 i0 l2if0
  let sm1' := smdStepH p1 s.sm1 i1 l2if1
  -- 5. 外层内存（MSL-D4）：倒计 FIFO + 真实 SinkD
  let headFire := match s.memQ with | r :: _ => r.cnt == 0 | [] => false
  let headEntry := match s.memQ with | r :: _ => r.entry | [] => 0
  let headR := (s.sc.mshrs headEntry).request
  let aFireMem := l2scAFire s.sc w.scIn w.sel
  let memQ1 := (if headFire then s.memQ.drop 1 else s.memQ).map
    (fun r => { r with cnt := r.cnt - 1 })
  let memQ' := if aFireMem then memQ1 ++ [{ entry := w.sel, cnt := l2MemCycles }]
    else memQ1
  let sinkD' := sinkDStep s.sinkD headFire l2opAccessAckData
    (BitVec.ofNat 16 headEntry)
    (s.dataMem (expandAddress headR.tag headR.set 0#7))
  -- 6. requests 队列（MSL-D2：HW 语义恢复）
  let pushFire := l2scPushValid s.sc w.scIn && mslPushReady s
  let pushIdx := if l2scAlloc s.sc w.scIn then lbCtz (l2scInsertOH s.sc)
    else lbCtz (l2scTagMatches s.sc w.scIn)
  let reqQ' : Nat → List (BitVec 16) := fun i =>
    let q1 := if popFire && (i == w.sel) then (s.reqQ i).drop 1 else s.reqQ i
    if pushFire && (i == pushIdx) then q1.concat w.scIn.dirRes.source else q1
  -- 7. L2 各模块同步步进
  let sinkA' := sinkAStep s.sinkA w.saIn
  let sc0 := l2scStep s.sc w.scIn
  -- mshrs/reqQ 每拍具体化（MSL-D11：闭包链逐拍 +1 层且访问无记忆 ⇒ O(T²)，
  -- 实测 220 拍 >50min 不可行；物化后链长恒 1）
  let mshrArr : Array L2mState := (List.finRange 32).map (fun j => sc0.mshrs j.val)
    |>.toArray
  let reqQA : Array (List (BitVec 16)) := (List.range 32).map reqQ' |>.toArray
  let sc' : L2scState :=
    { sc0 with
        mshrs := fun i => mshrArr.getD i l2mInit
      , valids := l2scOfPred (fun i => (reqQ' i).isEmpty == false) }
  let dir' := l2dStep s.dir w.dirIn
  -- 8. 数据阵列：Put 落数（MSL-D7）
  let pb := sinkAPbBeat s.sinkA w.saIn
  let putAddr : BitVec 32 := expandAddress w.dirOut.resultTag w.dirOut.resultSet 0#7
  let dataMem' := if w.putResultFire then
    fun ba => if ba == putAddr
      then mslMergeMask (s.dataMem putAddr) pb.data pb.mask else s.dataMem ba
    else s.dataMem
  let s' : MslState :=
    { sm0 := sm0', sm1 := sm1', sinkA := sinkA', sc := sc'
    , dir := dir', sinkD := sinkD', memQ := memQ'
    , reqQ := fun i => reqQA.getD i [], dataMem := dataMem' }
  let ev : MslEv :=
    { getFired0 := getF 0#16, getFired1 := getF 1#16
    , putFired0 := putF 0#16, putFired1 := putF 1#16
    , grant0 := gV 0#16, grant1 := gV 1#16
    , secPush := pushFire && !l2scAlloc s.sc w.scIn
    , popCnt := mslPopcount sc'.valids
    , putMiss := w.putResultFire && !w.dirOut.resultHit
    , bad := (popFire && (s.reqQ w.sel).isEmpty)
      || (gV 0#16 && s.sm0.dc.miss.isNone) || (gV 1#16 && s.sm1.dc.miss.isNone) }
  (s', ev)

/-- 组合单拍（无事件版） -/
def mslStep (p0 p1 : SmProg) (s : MslState) (i0 i1 : SmIn) : MslState :=
  (mslStepAux p0 p1 s i0 i1).1

/-- 多拍运行 -/
def mslRun (p0 p1 : SmProg) (s : MslState) (ins : List (SmIn × SmIn)) : MslState :=
  ins.foldl (fun acc inp => mslStep p0 p1 acc inp.1 inp.2) s

/- ========================================================================= -/
/- 3. 小件数值回归（III 类自检）                                                -/
/- ========================================================================= -/

-- pack/unpack 回环（具体行）
example : (List.finRange 32).all (fun i =>
    mslUnpackRow (mslPackRow smdRowA) i == smdRowA i) = true := by native_decide

-- merge 全掩码 = 新值
example : mslMergeMask (mslPackRow (fun _ => 0x11#32)) (mslPackRow smdRowA)
    (BitVec.allOnes 128) = mslPackRow smdRowA := by native_decide

-- 地址连线：L1 blockAddr（addr[31:7]）<<< 7 = L2 块基址；parse 回环（场景 A/B
-- 两地址各自钉死 tag/set）
example :
    ((0x200000#25).zeroExtend 32 <<< 7) = 0x10000000#32 ∧
    parseTag (0x10000000#32) = 0x8000#19 ∧ parseSet (0x10000000#32) = 0#6 ∧
    ((0x400000#25).zeroExtend 32 <<< 7) = 0x20000000#32 ∧
    parseTag (0x20000000#32) = 0x10000#19 ∧ parseSet (0x20000000#32) = 0#6 := by
  native_decide

-- 请求打包：Get 的地址/opcode/source 正确
example :
    let r : SmdAReq := { op := 4#3, ba := 0x200000#25, dat := fun _ => 0#32 }
    let b := mslBundleA 1#16 r
    b.address = 0x10000000#32 ∧ b.opcode = 4#3 ∧ b.source = 1#16 ∧
    b.size = 7#7 := by native_decide

/- ========================================================================= -/
/- 4. 监控器                                                                   -/
/- ========================================================================= -/

/-- 监控累积器（首拍事件记拍号+1，0=未发生；secPush/maxPop 为计数/峰值） -/
structure MslChk where
  tick : Nat
  getFire0 : Nat
  getFire1 : Nat
  putFire0 : Nat
  putFire1 : Nat
  grant0 : Nat
  grant1 : Nat
  secPush : Nat
  maxPop : Nat
  putMiss : Bool
  bad : Bool
deriving DecidableEq, Repr

def mslChk0 : MslChk :=
  { tick := 0, getFire0 := 0, getFire1 := 0, putFire0 := 0, putFire1 := 0
  , grant0 := 0, grant1 := 0, secPush := 0, maxPop := 0
  , putMiss := false, bad := false }

def mslMonStep (p0 p1 : SmProg) (acc : MslChk × MslState) (inp : SmIn × SmIn) :
    MslChk × MslState :=
  let (m, s) := acc
  let (s', ev) := mslStepAux p0 p1 s inp.1 inp.2
  let fst (old : Nat) (b : Bool) : Nat := if b && (old == 0) then m.tick + 1 else old
  ({ tick := m.tick + 1
   , getFire0 := fst m.getFire0 ev.getFired0
   , getFire1 := fst m.getFire1 ev.getFired1
   , putFire0 := fst m.putFire0 ev.putFired0
   , putFire1 := fst m.putFire1 ev.putFired1
   , grant0 := fst m.grant0 ev.grant0
   , grant1 := fst m.grant1 ev.grant1
   , secPush := m.secPush + (if ev.secPush then 1 else 0)
   , maxPop := max m.maxPop ev.popCnt
   , putMiss := m.putMiss || ev.putMiss
   , bad := m.bad || ev.bad }, s')

/- ========================================================================= -/
/- 5. 场景 A：跨 SM 同地址写读经真实 L2                                         -/
/-    （SM0 store rowA→A：Get acquire miss → L2 MSHR → 外层内存 32 拍 →         -/
/-     AccessAckData refill → 写分配 dirty；endprg flush → wbQ → Put 写回       -/
/-     真实 SinkA/putbuffer + Directory（hit，b3 dirty 置位）→ dataMem；        -/
/-    SM1 load A：Get acquire → L2 Directory hit → drb → grant → v2=rowA）      -/
/- ========================================================================= -/

def mslNA : Nat := 220
/-- SM1 派发延迟：L2 wipe（~66 拍）+ SM0 miss 全链路（~40 拍）+ flush 余量 -/
def mslDelayA : Nat := 130

def mslS0A : MslState := mslInit msmSmSt0 msmSmLd0

/-- 输入：t=0 派 SM0（store 程序），t=130 派 SM1（load 程序），其余空转 -/
def mslInsA : List (SmIn × SmIn) :=
  (List.range mslNA).map fun t =>
    (if t = 0 then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop,
     if t = mslDelayA then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop)

def mslRunChkA : MslChk × MslState :=
  mslInsA.foldl (mslMonStep msmProgSt msmProgLd) (mslChk0, mslS0A)

/-- 场景 A 终态判收 -/
def mslFinOkA (m : MslChk) (sf : MslState) : Bool :=
  -- **跨 SM 写读一致**：SM1 v2（bank2 addr4）全 32 lane = SM0 写入的 rowA
  (List.finRange 32).all (fun t =>
    (smVrfAt sf.sm1.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == smdRowA t) &&
  -- SM0 的 flush Put 落入真实 L2 数据阵列（经 SinkA putbuffer + Directory hit）
  (sf.dataMem 0x10000000#32 == mslPackRow smdRowA) &&
  -- 反证对照：L2 初值 ≠ rowA（SM1 读到的确实来自 SM0 写回而非初值）
  (mslDataInit 0x10000000#32 != mslPackRow smdRowA) &&
  -- 真实 Directory 的 dirty 状态位（b3 支路，Directory:187-188）被 Put hit 置位
  (List.finRange 16).any (fun w => l2StatusGet sf.dir.statusD 0 w.val) &&
  -- **acquire/release 事件序**（因果序，非写死拍号）：
  -- SM0 acquire 接受 → grant（refill）→ flush 写回 Put 被 L2 接受；
  -- SM1 acquire 接受 → grant（hit 响应）
  (m.getFire0 > 0) && (m.grant0 > m.getFire0) && (m.putFire0 > m.grant0) &&
  (m.getFire1 > 0) && (m.grant1 > m.getFire1) &&
  -- 协议守卫：无 pop 空队、无打空 grant、Put 全部 L2 hit（MSL-D6 前提）
  !m.bad && !m.putMiss &&
  -- L2 侧归位：MSHR 全释放、drb 空、外层内存无在飞、putbuffer 全收
  (sf.sc.valids == 0#32) && !sf.sc.drbValid && sf.memQ.isEmpty &&
  (sf.sinkA.lists == 0#32) &&
  -- 双 SM 归位
  (sf.sm0.base.base.ws.warpActive == 0#8) &&
  (sf.sm1.base.base.ws.warpActive == 0#8) &&
  (sf.sm0.lsu.state == Mem.lsuSIdle) && (sf.sm1.lsu.state == Mem.lsuSIdle) &&
  (sf.sm0.dc.miss.isNone) && (sf.sm1.dc.miss.isNone) &&
  (sf.sm0.dc.wbQ.isEmpty) && (sf.sm1.dc.wbQ.isEmpty) &&
  (sf.sm0.dc.rspQ.isNone) && (sf.sm1.dc.rspQ.isNone)

/-- **场景 A 主定理（跨 SM 同地址写读经真实 L2）**。
    证据链：事件序（SM0 acquire ≺ grant ≺ Put 写回；SM1 acquire ≺ grant）+
    终态值（SM1.v2 = rowA、L2 数据阵列[A] = rowA、Directory dirty 位置位、
    L2 初值 ≠ rowA 的反证对照）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem mslTraceA_ok : mslFinOkA mslRunChkA.1 mslRunChkA.2 = true := by
  native_decide

/- ========================================================================= -/
/- 6. 场景 B：同块并发 miss 的 MSHR 合并（双 SM 同拍派 load 同块 B，            -/
/-    B = 0x20000000；SM0 acquire 先被仲裁接受（MSL-D1）→ alloc entry0；        -/
/-    SM1 acquire 晚 1 拍 → Directory result 时 tagMatches 命中 entry0 →        -/
/-    secondary push（不新增 MSHR）；refill 后队首/次队先后 grant 两 SM）       -/
/- ========================================================================= -/

/-- 双 SM 共用的 load 程序：lui x1,0x20000 ; vle32.v v2,(x1) ; endprg -/
def mslProgLdB : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x200000B7#32        -- lui  x1, 0x20000（B=0x20000000）
    else if pc = 0x04#32 then 0x0200E107#32   -- vle32.v v2, (x1)
    else if pc = 0x08#32 then 0x0000400B#32   -- endprg
    else 0#32

/-- 块 B 的 L2 初值行（期望读回值；blockAddr = 0x20000000[31:7]） -/
def mslRowB : Fin 32 → BitVec 32 := smdL2Init 0x400000#25

def mslS0B : MslState := mslInit msmSmLd0 msmSmLd0

def mslNB : Nat := 160

/-- 输入：t=0 同拍派两 SM 各自的 warp0（同程序、同地址 B） -/
def mslInsB : List (SmIn × SmIn) :=
  (List.range mslNB).map fun t =>
    (if t = 0 then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop,
     if t = 0 then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop)

def mslRunChkB : MslChk × MslState :=
  mslInsB.foldl (mslMonStep mslProgLdB mslProgLdB) (mslChk0, mslS0B)

/-- 场景 B 终态判收 -/
def mslFinOkB (m : MslChk) (sf : MslState) : Bool :=
  -- 两 SM 各自 v2 全 32 lane = 块 B 初值（数据经外层内存 → 真实 SinkD →
  -- MSHR.dataReg → schedule.d 弹队 → grant 到达）
  (List.finRange 32).all (fun t =>
    (smVrfAt sf.sm0.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == mslRowB t) &&
  (List.finRange 32).all (fun t =>
    (smVrfAt sf.sm1.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == mslRowB t) &&
  -- **MSHR 合并观测**：发生 secondary push，且全程 MSHR 占用峰值 = 1
  -- （两 SM 的同块并发 miss 共用一个 entry；若各自 alloc 则 maxPop = 2）
  (m.secPush > 0) && (m.maxPop == 1) &&
  -- 事件序：SM0 acquire 先于 SM1（仲裁 MSL-D1）；SM0 grant 先于 SM1
  -- （队首先弹）；两 SM 的 grant 均在各自 acquire 之后
  (m.getFire0 > 0) && (m.getFire1 > m.getFire0) &&
  (m.grant0 > m.getFire0) && (m.grant1 > m.grant0) &&
  !m.bad && !m.putMiss &&
  -- 归位
  (sf.sc.valids == 0#32) && !sf.sc.drbValid && sf.memQ.isEmpty &&
  (sf.sinkA.lists == 0#32) &&
  (sf.sm0.base.base.ws.warpActive == 0#8) &&
  (sf.sm1.base.base.ws.warpActive == 0#8) &&
  (sf.sm0.dc.miss.isNone) && (sf.sm1.dc.miss.isNone) &&
  (sf.sm0.dc.rspQ.isNone) && (sf.sm1.dc.rspQ.isNone)

/-- **场景 B 主定理（同块并发 miss 的真实 L2 MSHR 合并）**：两 SM 同拍并发
    load 同一块 B；L2 侧只分配一个 MSHR entry（maxPop=1）、第二请求经
    tagMatches 走 secondary 合并（secPush>0）；两 SM 先后收到同一份
    AccessAckData 并各自回填 v2 = B 初值。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem mslTraceB_ok : mslFinOkB mslRunChkB.1 mslRunChkB.2 = true := by
  native_decide

/- ========================================================================= -/
/- 7. 发现与公理审计                                                           -/
/-                                                                            -/
/-  发现（I/II/III 类审查）：本文件新逻辑 = MSL-D1 仲裁、MSL-D2 reqQ 影子       -/
/-    恢复、MSL-D5 两遍反压消解、数据面功能式打包——全部为组合层纯函数，配       -/
/-    §3 数值回归；SM 侧改造（SMD-D7）为新增变体，stub 既有定理/轨迹回归绿      -/
/-    （smdT_* / smdTraceC_ok / smdTraceD_ok / msmTraceA_ok 构建通过）。        -/
/-  I 类：组合轨迹中未触发既有 I 类 bug 的新表现（场景内 Put 全 hit、           -/
/-    无 flush、无 secondary-Put 合并，I-42/I-43/I-44 的触发条件均不满足；      -/
/-    putMiss/bad 监控器恒 false 作证）。I-44 组合下不可达的论证见 MSL-B3。     -/
/-  II 类风险点（记录备查）：(a) read.valid 门控（MSL-D8）与 HW 的差集未覆      -/
/-    盖；(b) reqQ 恢复逻辑与 l2scStep 影子的一致性靠 pop/push 事件同源         -/
/-    （同拍同 entry push+pop 序：先弹后推，与 ListBuffer:106 的 Mux 支一致）； -/
/-    (c) Put 落数提前到 resultFire 拍（MSL-D7）。                              -/
/-  III 类：§3 小件回归（pack/unpack 回环、merge 全掩码、地址连线、请求打包）。 -/
/- ========================================================================= -/

#print axioms mslTraceA_ok
#print axioms mslTraceB_ok

end Ventus
