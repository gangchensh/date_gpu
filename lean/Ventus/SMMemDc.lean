/- ========================================================================= -/
/-                          SMMemDc.lean                                     -/
/-  SM 组合模型访存通路再升级：global（非 LDS）地址走 **DCache 功能壳 + L2      -/
/-  stub**，消除 SMMem.lean 的 M-O1/M-O2 边界（global 地址请求被 dcache stub    -/
/-  吞掉、MSHR 条目悬挂）。底座 = SMMem.lean 的 smmComb/smmStep（LDS 已通），   -/
/-  复制-增量纪律同 M-D0（SMMem.lean 只读）。                                   -/
/-                                                                           -/
/-  真实链路（在 SMMem.lean 链路基础上的增量，逐行对照）：                      -/
/-    pipe.scala:416        lsu.io.dcache_req <> io.dcache_req（→ L1 DCache）； -/
/-    LSU.scala:282         to_dcache.valid = s_dcache|s_dcache_1|s_dcache_2；  -/
/-    LSU.scala:227-282     to_dcache.bits（tag=addr(31,15)、setIdx=addr(14,7)、-/
/-      blkOff=addr(6,2)、word1H、active、data、opcode/param）；                -/
/-    DCache.scala:218      coreReq.ready 九项合取（收窄，SMD-D2）；            -/
/-    DCache.scala:442-478   st1 ready when/elsewhen 链（命中/读 miss/写 miss/  -/
/-      invalidate/flush/waitMSHR/AMO 吞掉）＝ DCache.lean dcSt1Ready；         -/
/-    DCache.scala:685-757   coreRsp_st2/rspVld/hintAck 响应管线＝ dcRspSt2Enq/ -/
/-      dcCoreRspEnq；                                                         -/
/-    DCache.scala:818,:912  写 miss 响应走 fromMemReq 旁路（不等回填）；        -/
/-    LSU.scala:560-563     rspArbiter = Arbiter(DCacheCoreRsp_np,2)：          -/
/-      in(0)=dcache_rsp（**本文件接通**）、in(1)=shared_rsp，in(0) 优先；      -/
/-    MSHR.scala:45         from_dcache.ready = state.isIdle（arbiter out.ready） -/
/-                                                                           -/
/- ======================== 建模决策（SMD-D 区） ============================= -/
/-  SMD-D0. smdComb 是 SMMem.lean smmComb 的全量复制 + 三处增量：               -/
/-      (a) lsuIn.dcacheReady 从 `true` stub 升级为壳就绪（st1 可出 && 无在飞   -/
/-          miss && WSHR 未满，:218 收窄）；                                  -/
/-      (b) shIn.rspReady 升级为 rspArbiter in(1).ready = out.ready &&          -/
/-          !in(0).valid（dcache_rsp 优先）；                                 -/
/-      (c) mshrIn.dcValid/rspId/rspData/rspMask 升级为 arbiter 输出选择        -/
/-          （in(0)=壳响应优先，否则 shared_rsp）。                            -/
/-  SMD-D1. 复用 DCache.lean 的**时序控制核**：SmdDc.core = DcState，每拍由      -/
/-      dcStep 驱动；其收窄环境输入（DcIn 各项）全部由本壳功能状态确定性计算    -/
/-      （smdDcIn0），不引入自由环境。st1 驻留请求的数据通路部分（tag/blkOff/   -/
/-      word1H/active/data）被 DcSt1 收窄掉，由影寄存器 sh1 平行携带（同拍      -/
/-      入/出，对齐性同 DCache.lean D3 注）。hit 判定、写分配、dirty 写回由     -/
/-      功能壳按 :237/:267/:408-410/:562-617 的语义实现。                       -/
/-  SMD-D2. L1MSHR 收窄为**单 outstanding** miss 槽（SmdMiss）：coreReq.ready   -/
/-      在 miss 在飞期间恒 false（不建 secondary 合并、不许新请求命中在飞       -/
/-      miss）。合并/多 outstanding 的模块级证据在 L1MSHR.lean                  -/
/-      （l1m_primary_alloc/l1m_secondary_merge 等），本壳不重复建模。          -/
/-      missReqRdy=miss 空、memArb0/1Rdy=true、probeStat02=true、               -/
/-      inflightRWw=false 在单 outstanding 下均为安全值。                       -/
/-  SMD-D3. L2 stub：函数式内存 `l2 : BitVec 25 → Fin 32 → BitVec 32`           -/
/-      （blockAddr → 32 字）+ **固定延迟** smdL2Lat=4 拍（SmdMiss.cnt 倒计）。 -/
/-      flush/invalidate 的 L2 hintAck（d_opcode=2）在 flushCnt 倒计后回一拍，  -/
/-      驱动 dcStep 的 waitforL2flush/ghost 响应链（:423-427/:695-699/:754）。 -/
/-  SMD-D4. coreRsp_Q（:191，32 深）收窄为 1 项 rspQ + 反压：coreRspQEnqRdy =   -/
/-      !rspQ.isSome || 本拍出队。响应数据通路（DcRspSt2 收窄掉的 data/mask）    -/
/-      由 pendRsp 影管线平行携带（hit 拍/读 miss 回填拍捕获），入队事件严格    -/
/-      对齐 dcCoreRspEnq && coreRspQEnqRdy（对齐不变量见 smdDcStep 注释）。    -/
/-  SMD-D5. 替换策略：2 路组相联 + 伪 LRU（每 set 一个 mru 位，驱逐 !mru）。     -/
/-      I-27（真机 MRU 表更新 bug）在 TagAccess 内部，处于 DCache.lean 收窄     -/
/-      抽象之外，本壳采用**正确** LRU，不声称复现 I-27；I-28（dirtyMask 丢     -/
/-      字节）的字节级 dirtyMask 不在本壳粒度内（dirty 为整行位），证据引用     -/
/-      DCache.lean dcT_i28_asymmetry；I-29（LFSR 写回污染）需 allocateWrite    -/
/-      与滞留写同拍同 (set,way)，本壳时序不构造该组合（证据 dcT_w1_*）；I-30   -/
/-      （flush 响应元数据错乱）的脆点在 dcStep 内忠实存在，但本壳的 hintAck   -/
/-      驱动（flushCnt 倒计 + pendRsp/rspQ 空闲才发）刻意避开触发条件——        -/
/-      挂账问题留 dcT_w2* 系列，不在本文件复现。                               -/
/-  SMD-D6. flush/invalidate（LSU flush_dcache 发 opcode=3，本实例 param=0      -/
/-      =invalidate）：st1 接受后由 dcStep 的 waitforL2flush 自然阻塞 st1；壳   -/
/-      在 hintAck 拍**一次性**把全部 dirty 行写回 L2 并清 dirty（invalidate    -/
/-      另清 valid）——真实硬件是 TagAccess 逐 set 走查 + WSHR 排水的多拍过程，  -/
/-      本壳只保留可观测效果（dirty 数据先于 flush 响应到达 L2、wshrEmpty 后    -/
/-      才放行 st1）。hasDirtySt1 恒 false（走查被瞬时化）。AMO/LR/SC 落 :477    -/
/-      默认分支被吞掉（I-16 忠实保留；本文件场景不产生）。                     -/
/- ========================================================================= -/

import Ventus.SMMem
import Ventus.Mem.DCache

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. DCache 功能壳：类型与参数                                                 -/
/- ========================================================================= -/

/-- L2 固定延迟（拍，SMD-D3） -/
def smdL2Lat : BitVec 8 := 4

/-- Tag/Data 阵列一行（一路；数据 = 32 字 = 128B 块） -/
structure SmdLine where
  valid : Bool
  dirty : Bool
  tag   : BitVec 17
  dat   : Fin 32 → BitVec 32

def smdLine0 : SmdLine := ⟨false, false, 0#17, fun _ => 0#32⟩

/-- 影 st1：DcSt1 收窄掉的数据通路部分（SMD-D1），与 core.st1 同拍入/出 -/
structure SmdSh1 where
  tag     : BitVec 17
  setIdx  : BitVec 8
  blkOff  : Fin 32 → BitVec 5
  word1H  : Fin 32 → BitVec 4
  active  : Fin 32 → Bool
  dat     : Fin 32 → BitVec 32
  isWrite : Bool
  instrId : BitVec 3

/-- 单 outstanding miss 槽（SMD-D2） -/
structure SmdMiss where
  ba      : BitVec 25          -- blockAddr = Cat(tag, setIdx)（:276）
  instrId : BitVec 3
  isWrite : Bool
  blkOff  : Fin 32 → BitVec 5
  word1H  : Fin 32 → BitVec 4
  mask    : BitVec 32          -- active lanes 打包
  dat     : Fin 32 → BitVec 32 -- 写 miss 的写数据（write-allocate 合并用）
  cnt     : BitVec 8           -- L2 延迟倒计

/-- LSU 侧响应（coreRsp_Q 表项：DCacheCoreRsp_np 的 instrId/isWrite/data/
    activeMask；activeMask 预打包为 BitVec 32，对齐 MSHR rspMask） -/
structure SmdRsp where
  instrId : BitVec 3
  isWrite : Bool
  dat     : Fin 32 → BitVec 32
  mask    : BitVec 32

/-- 待写回块（SMD-D7 握手模式的 Put 请求负载；stub 模式不使用） -/
structure SmdWb where
  ba  : BitVec 25
  dat : Fin 32 → BitVec 32

/-- DCache 功能壳状态 -/
structure SmdDc where
  core     : Mem.DcState       -- DCache.lean 时序控制核（dcStep 驱动，SMD-D1）
  sh1      : Option SmdSh1     -- 影 st1
  pendRsp  : Option SmdRsp     -- 影响应管线（hit/读miss 捕获 → coreRsp 入队对齐）
  rspQ     : Option SmdRsp     -- coreRsp_Q 收窄 1 项（SMD-D4）
  line     : BitVec 8 → BitVec 2 → SmdLine
  mru      : BitVec 8 → BitVec 2
  miss     : Option SmdMiss
  wshr     : Mem.DcwState      -- DCache.lean §4 复用（写回登记，观测用）
  l2       : BitVec 25 → Fin 32 → BitVec 32   -- L2 函数式内存（SMD-D3）
  flushCnt : BitVec 2          -- flush 接受后 hintAck 倒计（SMD-D3）
  wbLog    : List (BitVec 25)  -- dirty 写回事件日志（驱逐 + flush，观测用）
  acqDone  : Bool              -- SMD-D7 握手变体：本 miss 的 Get 已被 L2 接受（stub 恒 false）
  wbQ      : List SmdWb        -- SMD-D7 握手变体：待写回 Put 队列（stub 恒 []）

/-- L2 初始内容：确定性的可识别模式（blockAddr、字号注入） -/
def smdL2Init (ba : BitVec 25) (w : Fin 32) : BitVec 32 :=
  0x5A000000#32 + (ba.zeroExtend 32 <<< 5) + BitVec.ofNat 32 w.val

def smdDcInit : SmdDc :=
  { core := Mem.dcInit, sh1 := none, pendRsp := none, rspQ := none
  , line := fun _ _ => smdLine0, mru := fun _ => 0#2, miss := none
  , wshr := Mem.dcwInit, l2 := smdL2Init, flushCnt := 0#2, wbLog := []
  , acqDone := false, wbQ := [] }

/- ---- 小工具 ---- -/

/-- BitVec 5 → Fin 32（blockOffset 索引） -/
def smdFin5 (b : BitVec 5) : Fin 32 := ⟨b.toNat, b.isLt⟩

/-- 字节使能展开为 32 位掩码（genDataMapPerByte 的逐字节语义） -/
def smdBe32 (be : BitVec 4) : BitVec 32 :=
  (if be &&& 1#4 ≠ 0#4 then 0x000000FF#32 else 0#32) |||
  (if be &&& 2#4 ≠ 0#4 then 0x0000FF00#32 else 0#32) |||
  (if be &&& 4#4 ≠ 0#4 then 0x00FF0000#32 else 0#32) |||
  (if be &&& 8#4 ≠ 0#4 then 0xFF000000#32 else 0#32)

/-- 字节使能合并：be 置位字节取 newW，其余保留 oldW -/
def smdMergeWord (oldW newW : BitVec 32) (be : BitVec 4) : BitVec 32 :=
  (oldW &&& ~~~smdBe32 be) ||| (newW &&& smdBe32 be)

/-- 活跃 lane 按 blkOff 落字、按 word1H 合并字节（写命中 / write-allocate 共用） -/
def smdWrLanes (base : Fin 32 → BitVec 32) (blkOff : Fin 32 → BitVec 5)
    (word1H : Fin 32 → BitVec 4) (mask : BitVec 32) (dat : Fin 32 → BitVec 32) :
    Fin 32 → BitVec 32 :=
  (List.finRange 32).foldl (fun acc l =>
    if (mask >>> l.val) &&& 1#32 = 1#32 then
      fun w => if w = smdFin5 (blkOff l)
        then smdMergeWord (acc (smdFin5 (blkOff l))) (dat l) (word1H l) else acc w
    else acc) base

/-- 读行捕获：活跃 lane 取 blkOff 字，其余 0 -/
def smdRdRow (ln : SmdLine) (blkOff : Fin 32 → BitVec 5) (act : Fin 32 → Bool) :
    Fin 32 → BitVec 32 :=
  fun l => if act l then ln.dat (smdFin5 (blkOff l)) else 0#32

/-- 阵列更新 -/
def smdUpdLine (f : BitVec 8 → BitVec 2 → SmdLine) (set : BitVec 8) (way : BitVec 2)
    (l : SmdLine) : BitVec 8 → BitVec 2 → SmdLine :=
  fun s w => if s == set && w == way then l else f s w

/-- L2 写一块 -/
def smdUpdL2 (l2 : BitVec 25 → Fin 32 → BitVec 32) (ba : BitVec 25)
    (row : Fin 32 → BitVec 32) : BitVec 25 → Fin 32 → BitVec 32 :=
  fun b w => if b == ba then row w else l2 b w

/-- hit 判定与命中 way（:237 hit_st1；两路 priority 取低） -/
def smdHitWay (dc : SmdDc) (set : BitVec 8) (tag : BitVec 17) : Option (BitVec 2) :=
  if (dc.line set 0#2).valid && (dc.line set 0#2).tag == tag then some 0#2
  else if (dc.line set 1#2).valid && (dc.line set 1#2).tag == tag then some 1#2
  else none

/-- 当前 st1 请求的 hit 判定（数据来自影 st1） -/
def smdSt1Hit (dc : SmdDc) : Option (BitVec 2) :=
  match dc.sh1 with
  | some h => smdHitWay dc h.setIdx h.tag
  | none => none

/-- 替换受害者（SMD-D5 伪 LRU：先填空 way，否则驱逐 !mru）；snd = needReplace -/
def smdVictim (dc : SmdDc) (set : BitVec 8) : BitVec 2 × Bool :=
  if !(dc.line set 0#2).valid then (0#2, false)
  else if !(dc.line set 1#2).valid then (1#2, false)
  else (if dc.mru set == 0#2 then 1#2 else 0#2, true)

/- ========================================================================= -/
/- 2. 壳组合求值：dcStep 环境输入与对外接口                                     -/
/-                                                                           -/
/-  求值分两级破文本环：                                                       -/
/-  * inA（missRspOutV=false、fromMemReqV=false）：refillGo 的门控              -/
/-    dcRspSt2EnqRdy/dcRspVldEnqRdy 只依赖 inA。自洽性论证：                    -/
/-    (i) miss.isSome ⇒ st1 必空（miss 捕获与 st1 出队同拍，且 coreReq.ready    -/
/-        含 miss.isNone）⇒ 写 miss fire 恒假 ⇒ in0 的 fromMemReqV 亦为假；     -/
/-    (ii) miss.isNone ⇒ refillGo=false ⇒ missRspOutV 两级一致（皆假）。        -/
/-  * in0 = inA + missRspOutV/allocWriteV/needReplace/fromMemReqV 等真值。      -/
/- ========================================================================= -/

/-- flush/invalidate 的 L2 hintAck（SMD-D3/D6）：flushCnt 倒计到 1 且响应
    管线空闲（pendRsp 空、rspQ 可入、ghost 已预置进 rspSt2）才发——避开
    Q2(a)(b)（I-30）的触发条件（SMD-D5） -/
def smdHintAck (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  dc.flushCnt == 1#2 && dc.pendRsp.isNone && (!dc.rspQ.isSome || mshrRdy) &&
    dc.core.rspSt2.isSome

/-- 一级环境输入（missRspOutV=false、fromMemReqV=false；其余为壳真值） -/
def smdDcInA (dc : SmdDc) (mshrRdy : Bool) : Mem.DcIn :=
  { fire := none
  , missRspOutV := false
  , missRspInstrId := match dc.miss with | some m => m.instrId | none => 0#3
  , probeStatus4 := false                 -- 无 probe 滞留（SMD-D2）
  , allocWriteV := false
  , needReplace := false
  , memArb0Rdy := true                    -- L2 stub 恒收（SMD-D3）
  , arb2Rdy := true
  , arb2Fire := false                     -- flushL2 的 L2 请求收窄不发（SMD-D6）
  , cacheHit := (smdSt1Hit dc).isSome
  , injectTagProbe := false
  , coreRspQEnqRdy := !dc.rspQ.isSome || mshrRdy
  , missReqRdy := dc.miss.isNone          -- 单 outstanding（SMD-D2）
  , memArb1Rdy := true
  , probeStat02 := true
  , inflightRWw := false
  , hasDirtySt1 := false                  -- SMD-D6（走查瞬时化）
  , mshrEmpty := dc.miss.isNone
  , wshrEmpty := Mem.dcwEmpty dc.wshr
  , memRspHeadV := smdHintAck dc mshrRdy
  , memRspHeadOp := if smdHintAck dc mshrRdy then 2#3 else 1#3  -- Q4 规避：非 ack 拍 ≠2
  , missRspSet := match dc.miss with | some m => Mem.dcGetSetIdx m.ba | none => 0#8
  , waymaskHit := match smdSt1Hit dc with | some w => 1#2 <<< w | none => 0#2
  , waymaskRepl := match dc.miss with
      | some m => 1#2 <<< (smdVictim dc (Mem.dcGetSetIdx m.ba)).1
      | none => 0#2
  , fromMemReqV := false
  , fromMemReqInstrId := match dc.sh1 with | some h => h.instrId | none => 0#3 }

/-- miss 完成（refill）拍：倒计到 1 且 coreRsp_st2/rspVld 管线可接收。
    门控保证 pendRsp 影管线不回填覆盖（SMD-D4 对齐不变量的关键） -/
def smdRefillGo (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  match dc.miss with
  | some m => m.cnt == 1#8 &&
      Mem.dcRspSt2EnqRdy dc.core (smdDcInA dc mshrRdy) &&
      Mem.dcRspVldEnqRdy dc.core (smdDcInA dc mshrRdy)
  | none => false

/-- 写 miss 在 st1 完成（fire）：响应走 fromMemReq 旁路（:818/:912） -/
def smdWrMissFire (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  Mem.dcCtrlFire dc.core (smdDcInA dc mshrRdy) &&
    (match dc.core.st1 with
     | some r => r.ctrl.isWrite && !(smdSt1Hit dc).isSome
     | none => false)

/-- 二级环境输入（dcStep 本拍实际输入；fire 字段由 smdDcStep 另填） -/
def smdDcIn0 (dc : SmdDc) (mshrRdy : Bool) : Mem.DcIn :=
  let inA := smdDcInA dc mshrRdy
  let go := smdRefillGo dc mshrRdy
  { inA with
    missRspOutV := go && (match dc.miss with | some m => !m.isWrite | none => false)
      -- SMD-D2 收窄：写 miss 不产生 missRspOut（其响应已走 fromMemReq），
      -- 避免 dcRspSt2Enq :690-694 分支对写 miss 重复入队
  , allocWriteV := go                     -- :620 TagAccess.allocateWrite
  , needReplace := go &&
      (match dc.miss with
       | some m => (dc.line (Mem.dcGetSetIdx m.ba) 0#2).valid &&
                   (dc.line (Mem.dcGetSetIdx m.ba) 1#2).valid
       | none => false)
  , fromMemReqV := smdWrMissFire dc mshrRdy }

/-- to_dcache.ready（:218 收窄，SMD-D0a）：st1 可出 && 无在飞 miss && WSHR 未满。
    flush 在 st1 等待期间 st1 不可出，天然阻塞新请求（无 op3 泄漏窗口） -/
def smdDcReqRdy (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  (dc.core.st1.isNone || Mem.dcCtrlFire dc.core (smdDcIn0 dc mshrRdy)) &&
    dc.miss.isNone && !(Mem.dcwFull dc.wshr)

/-- 壳对 LSU 侧的组合输出 -/
structure SmdDcComb where
  reqRdy  : Bool                 -- to_dcache.ready
  rspV    : Bool                 -- dcache_rsp.valid（rspQ 队头）
  rspId   : BitVec 3
  rspData : Fin 32 → BitVec 32
  rspMask : BitVec 32

def smdDcCombOf (dc : SmdDc) (mshrRdy : Bool) : SmdDcComb :=
  { reqRdy := smdDcReqRdy dc mshrRdy
  , rspV := dc.rspQ.isSome
  , rspId := match dc.rspQ with | some r => r.instrId | none => 0#3
  , rspData := match dc.rspQ with | some r => r.dat | none => fun _ => 0#32
  , rspMask := match dc.rspQ with | some r => r.mask | none => 0#32 }

/- ========================================================================= -/
/- 3. 壳单拍转移（smdDcStep）                                                   -/
/-                                                                           -/
/-  pendRsp/rspSt2/rspVld 对齐不变量（SMD-D4）：                                -/
/-   * pendRsp 在 hit fire 拍（dcReadHit/dcWriteHit，:241-243）或读 miss 回填   -/
/-     拍（missRspOutV，:690-694）置位；                                       -/
/-   * 弹出条件 = coreRsp_Q 入队 fire = dcCoreRspEnq.isSome && coreRspQEnqRdy    -/
/-     （hit 路径经 dcFromCoreReq=rspVld deq fire，fromMemRsp 路径经             -/
/-     fromMemRsp && enqRdy），与 dcStep 内部 rspSt2/rspVld 出队同拍；          -/
/-   * 置位与弹出同拍时先弹后置（hit ready 已含 rspVldEnqRdy，refillGo 已含      -/
/-     dcRspVldEnqRdy/dcRspSt2EnqRdy 门控 ⇒ 不覆盖未弹项）；                    -/
/-   * 写 miss 响应走 fromMemReq 旁路（:818/:912），不经 pendRsp；              -/
/-   * flush 响应走 hintAck（:754），smdHintAck 要求 pendRsp/rspQ 空闲 ⇒ 无     -/
/-     三路竞争（Q2b 的 OR 合并丢失场景被刻意避开，SMD-D5）。                   -/
/- ========================================================================= -/

/-- 影 st1 装配：coreReq fire 拍捕获（与 dcStep 的 st1 := i.fire 同拍） -/
def smdSh1Of (req : Mem.LsuDcacheReq) : SmdSh1 :=
  { tag := req.tag, setIdx := req.setIdx, blkOff := req.blkOff, word1H := req.word1H
  , active := req.active, dat := req.data
  , isWrite := (Mem.dcGenControl req.opcode req.param).isWrite
  , instrId := req.instrId }

/-- flush/invalidate 的瞬时全 dirty 写回（SMD-D6；真实为 TagAccess 逐 set 走查
    + WSHR 排水的多拍过程）。返回 (l2', line', wbLog')。 -/
def smdFlushWb (l2 : BitVec 25 → Fin 32 → BitVec 32)
    (line : BitVec 8 → BitVec 2 → SmdLine) (log : List (BitVec 25)) (inv : Bool) :
    (BitVec 25 → Fin 32 → BitVec 32) × (BitVec 8 → BitVec 2 → SmdLine) ×
      List (BitVec 25) :=
  (List.finRange 256).foldl (fun acc si =>
    (List.finRange 2).foldl (fun acc2 wi =>
      let (l2a, lna, loga) := acc2
      let set : BitVec 8 := BitVec.ofNat 8 si.val
      let way : BitVec 2 := BitVec.ofNat 2 wi.val
      let ln := lna set way
      if ln.valid && ln.dirty then
        let ba := Mem.dcBlockAddr ln.tag set
        (smdUpdL2 l2a ba ln.dat, smdUpdLine lna set way ⟨!inv, false, ln.tag, ln.dat⟩,
         loga ++ [ba])
      else if inv && ln.valid then
        (l2a, smdUpdLine lna set way ⟨false, false, ln.tag, ln.dat⟩, loga)
      else acc2) acc) (l2, line, log)

/-- 壳单拍转移。reqV/req = LSU to_dcache.valid/bits（LSU.scala:282,:227-282）；
    mshrRdy = MSHR from_dcache.ready（MSHR.scala:45，arbiter out.ready）。 -/
def smdDcStep (dc : SmdDc) (reqV : Bool) (req : Mem.LsuDcacheReq) (mshrRdy : Bool) :
    SmdDc :=
  let in0 := smdDcIn0 dc mshrRdy
  let rdy := smdDcReqRdy dc mshrRdy
  let fire := reqV && rdy                                             -- :212-219
  let nctrl := Mem.dcGenControl req.opcode req.param
  let isFluInv : Bool := nctrl.isFlush || nctrl.isInvalidate
  let dcIn : Mem.DcIn :=
    { in0 with fire := if fire
        then some ⟨nctrl, req.opcode == 3#3, req.setIdx, req.instrId⟩ else none }
  -- ---- 事件（均与 fire 字段无关，用 in0 求值） ----
  let hitW := smdSt1Hit dc
  let rdHit : Bool := Mem.dcReadHit dc.core in0                       -- :241
  let wrHit : Bool := Mem.dcWriteHit dc.core in0                      -- :243
  let wrMissF : Bool := smdWrMissFire dc mshrRdy
  let rdMissF : Bool := Mem.dcCtrlFire dc.core in0 &&
    (match dc.core.st1 with
     | some r => r.ctrl.isRead && !hitW.isSome
     | none => false)
  let go : Bool := smdRefillGo dc mshrRdy
  let ack : Bool := smdHintAck dc mshrRdy
  let enqRdy : Bool := !dc.rspQ.isSome || mshrRdy                     -- coreRspQEnqRdy
  let enqEv := Mem.dcCoreRspEnq dc.core dcIn                          -- :753-757
  let enqFire : Bool := enqEv.isSome && enqRdy
  -- ---- 命中写（:408-410 remap 后数据/掩码写 SRAM；dirty 置位 :267 语义） ----
  let line1 :=
    match dc.sh1, hitW with
    | some h, some w =>
      if wrHit then
        let ln := dc.line h.setIdx w
        let ln' : SmdLine := ⟨ln.valid, true, ln.tag,
          smdWrLanes ln.dat h.blkOff h.word1H (smmPackMask h.active) h.dat⟩
        smdUpdLine dc.line h.setIdx w ln'
      else dc.line
    | _, _ => dc.line
  let mru1 :=
    match dc.sh1, hitW with
    | some h, some w => if rdHit || wrHit
        then fun s => if s == h.setIdx then w else dc.mru s else dc.mru
    | _, _ => dc.mru
  -- ---- 回填（missRspOut 拍，:578-581/:616-621；含 dirty 驱逐写回） ----
  let missBa : BitVec 25 := match dc.miss with | some m => m.ba | none => 0#25
  let rSet := Mem.dcGetSetIdx missBa
  let victim := smdVictim dc rSet
  let vln := dc.line rSet victim.1
  let wbThis : Bool := go && victim.2 && vln.dirty         -- dirty 驱逐写回
  let wbBA : BitVec 25 := Mem.dcBlockAddr vln.tag rSet
  let merged : Fin 32 → BitVec 32 := match dc.miss with
    | some m => if m.isWrite then smdWrLanes (dc.l2 m.ba) m.blkOff m.word1H m.mask m.dat
                else dc.l2 m.ba
    | none => fun _ => 0#32
  let line2 := if go then
      match dc.miss with
      | some m => smdUpdLine line1 rSet victim.1 ⟨true, m.isWrite, Mem.dcGetTag m.ba, merged⟩
      | none => line1
    else line1
  let mru2 := if go then (fun s => if s == rSet then victim.1 else mru1 s) else mru1
  let l2a := if wbThis then smdUpdL2 dc.l2 wbBA vln.dat else dc.l2
  let loga := if wbThis then dc.wbLog ++ [wbBA] else dc.wbLog
  -- ---- flush/invalidate 的瞬时写回（SMD-D6，ack 拍） ----
  let isInv : Bool := match dc.core.st1 with | some r => r.ctrl.isInvalidate | none => false
  let (l2b, line3, logb) :=
    if ack then smdFlushWb l2a line2 loga isInv else (l2a, line2, loga)
  -- ---- WSHR（复用 DCache.lean §4；L2 stub 次拍即收 ⇒ 有项即 pop） ----
  let wshrPopV : Bool := !Mem.dcwEmpty dc.wshr
  let wshrPopIdx : Fin 4 :=
    ((List.finRange 4).find? (fun i => dc.wshr.valid i)).getD ⟨0, by decide⟩
  let wshr' := Mem.dcwStep dc.wshr wbThis wbBA wshrPopV wshrPopIdx
  -- ---- 影响应管线（pop 后置新，对齐不变量见节头注释） ----
  let pend1 := if enqFire && !wrMissF && !ack then none else dc.pendRsp
  let pend2 := match dc.sh1, hitW with
    | some h, some w =>
      if rdHit || wrHit then
        some ⟨h.instrId, wrHit,
              (if rdHit then smdRdRow (dc.line h.setIdx w) h.blkOff h.active
               else fun _ => 0#32),
              smmPackMask h.active⟩
      else pend1
    | _, _ => pend1
  let pend3 := if go then
      match dc.miss with
      | some m => if !m.isWrite then
          some ⟨m.instrId, false,
                (fun l => if (m.mask >>> l.val) &&& 1#32 = 1#32
                  then merged (smdFin5 (m.blkOff l)) else 0#32),
                m.mask⟩
        else pend2
      | none => pend2
    else pend2
  -- ---- coreRsp_Q（1 项收窄）：入队三选一（写 miss 旁路 / flush hintAck /
  --      pendRsp 弹出），出队 = MSHR 侧消费 ----
  let pushV : Option SmdRsp :=
    if !enqFire then none
    else match enqEv with
      | none => none
      | some eid =>
        if wrMissF then
          match dc.sh1 with
          | some h => some ⟨eid, true, (fun _ => 0#32), smmPackMask h.active⟩
          | none => none
        else if ack then some ⟨eid, false, (fun _ => 0#32), 0#32⟩
        else dc.pendRsp
  let rspQ' := if enqFire then pushV
    else if dc.rspQ.isSome && mshrRdy then none else dc.rspQ
  -- ---- miss 槽（捕获 / 倒计 / 完成） ----
  let missCap : Option SmdMiss :=
    if wrMissF || rdMissF then
      match dc.core.st1, dc.sh1 with
      | some r, some h =>
        some ⟨Mem.dcBlockAddr h.tag h.setIdx, h.instrId, r.ctrl.isWrite,
              h.blkOff, h.word1H, smmPackMask h.active, h.dat, smdL2Lat⟩
      | _, _ => none
    else none
  let miss' := if go then none
    else match dc.miss with
      | some m => some { m with cnt := if m.cnt == 1#8 then 1#8 else m.cnt - 1#8 }
      | none => missCap
  -- ---- flush 倒计 ----
  let flushCnt' := if fire && isFluInv then 2#2
    else if dc.flushCnt == 2#2 then 1#2
    else if ack then 0#2 else dc.flushCnt
  { core := Mem.dcStep dc.core dcIn
  , sh1 := if fire then some (smdSh1Of req)
      else if Mem.dcCoreQFire dc.core in0 then none else dc.sh1
  , pendRsp := pend3
  , rspQ := rspQ'
  , line := line3
  , mru := mru2
  , miss := miss'
  , wshr := wshr'
  , l2 := l2b
  , flushCnt := flushCnt'
  , wbLog := logb
  , acqDone := false          -- stub 模式不使用握手字段（SMD-D7）
  , wbQ := [] }

/- ========================================================================= -/
/- 3H. MSM-O1 握手化变体：miss 的 acquire/grant 与写回的 Put 通道化             -/
/-     （MultiSML2.lean 的真实 L2 组合用；stub 路径一字未动）                   -/
/-                                                                           -/
/-  SMD-D7. 与 stub（§1-3）的差异：                                            -/
/-   * miss 槽不倒计（cnt 冻结在捕获值），refill 由环境 grant（l2if.grantV）    -/
/-     驱动；回填数据来自 l2if.grantDat 而非 dc.l2。管线门控 smdRefillRdyH      -/
/-     与 stub 完全相同（dcRspSt2EnqRdy/dcRspVldEnqRdy 两级）；环境须保持       -/
/-     grant 直至门控放行（MultiSML2 由 sourceDReqReady 反压保证）。            -/
/-   * acquire：miss 捕获后按拍对外举 Get（smdDcAReq），环境接受拍              -/
/-     （l2if.getFired）置 acqDone 停止重举；写 miss 同样只发 Get               -/
/-     （write-allocate，回填拍合并写数据，同 stub）。                          -/
/-   * dirty 驱逐/flush 写回不直写 dc.l2：驱逐在 refill 拍入 wbQ；flush 在      -/
/-     **接受拍**一次性收集全部 dirty 行入 wbQ（smdFlushCollect，行侧 dirty/    -/
/-     valid 清除语义同 smdFlushWb）；wbQ 队首按拍举 Put，l2if.putFired 拍      -/
/-     出队。hintAck（smdHintAckH）= stub 条件 ∧ wbQ 排空 ⇒ flush 响应必在      -/
/-     全部写回被 L2 接受之后（跨 SM 写读序的关键）。                           -/
/-   * memArb0/1Rdy 仍恒 true：core 看到的 L2 接受理想化，反压由壳的            -/
/-     acqDone/wbQ 重举吸收（SMD-D2 单 outstanding ⇒ 至多一个 Get 在飞，        -/
/-     wbQ 每拍至多出一项与 SinkA 单口一致）。                                  -/
/-   * dc.l2 字段在本变体中不读写（保留仅为结构兼容）；wbLog 仍记驱逐事件       -/
/-     （观测用；flush 收集不再记 wbLog——MultiSML2 不走 wbLog 合并契约）。      -/
/-   * smdComb 增加 hs 默认参数（false = stub，既有调用点/定理语句不变）；      -/
/-     hs=true 时 dcacheReady 换用 smdDcReqRdyH（wbQ 感知的 hintAck 门控，      -/
/-     防止 flush st1 在写回排空前被提前放行）。                                -/
/- ========================================================================= -/

/-- SM→L2 请求（acquire Get=4 / write-back PutFullData=0；数据随请求携带，
    1024 位打包在组合侧完成） -/
structure SmdAReq where
  op  : BitVec 3
  ba  : BitVec 25
  dat : Fin 32 → BitVec 32

/-- L2→SM 环境输入（grant = D 通道 AccessAckData；getFired/putFired = A 通道
    本拍接受回执） -/
structure SmdL2If where
  grantV   : Bool
  grantDat : Fin 32 → BitVec 32
  getFired : Bool
  putFired : Bool

def smdL2IfIdle : SmdL2If :=
  { grantV := false, grantDat := fun _ => 0#32, getFired := false, putFired := false }

/-- 壳的 A 通道请求输出（拍前状态组合；Put 优先于 Get——flush 期间无 miss 在飞，
    驱逐 Put 与下一笔 miss 的 Get 可同挂，写回先行保证 L2 可见性序） -/
def smdDcAReq (dc : SmdDc) : Option SmdAReq :=
  match dc.wbQ with
  | w :: _ => some { op := 0#3, ba := w.ba, dat := w.dat }
  | [] => match dc.miss with
    | some m => if dc.acqDone then none
      else some { op := 4#3, ba := m.ba, dat := fun _ => 0#32 }
    | none => none

/-- hintAck 的握手版（SMD-D7）：stub 条件 ∧ 写回队列排空 -/
def smdHintAckH (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  smdHintAck dc mshrRdy && dc.wbQ.isEmpty

/-- 一级环境输入的握手版（仅 memRspHeadV/Op 换 ackH；其余同 smdDcInA） -/
def smdDcInAH (dc : SmdDc) (mshrRdy : Bool) : Mem.DcIn :=
  let inA := smdDcInA dc mshrRdy
  { inA with
    memRspHeadV := smdHintAckH dc mshrRdy
  , memRspHeadOp := if smdHintAckH dc mshrRdy then 2#3 else 1#3 }

/-- refill 管线门控（= stub smdRefillGo 去掉倒计触发；壳与环境共用本函数对齐，
    MultiSML2 的 sourceDReqReady 反压即由它驱动） -/
def smdRefillRdyH (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  match dc.miss with
  | some _ => Mem.dcRspSt2EnqRdy dc.core (smdDcInAH dc mshrRdy) &&
      Mem.dcRspVldEnqRdy dc.core (smdDcInAH dc mshrRdy)
  | none => false

/-- miss 完成（refill）拍的握手版：grant 到达且管线可接收 -/
def smdRefillGoH (dc : SmdDc) (mshrRdy : Bool) (l2if : SmdL2If) : Bool :=
  l2if.grantV && smdRefillRdyH dc mshrRdy

/-- 写 miss 在 st1 完成（fire）的握手版（仅 inA 换 smdDcInAH） -/
def smdWrMissFireH (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  Mem.dcCtrlFire dc.core (smdDcInAH dc mshrRdy) &&
    (match dc.core.st1 with
     | some r => r.ctrl.isWrite && !(smdSt1Hit dc).isSome
     | none => false)

/-- 二级环境输入的握手版（go 换 grant 驱动） -/
def smdDcIn0H (dc : SmdDc) (mshrRdy : Bool) (l2if : SmdL2If) : Mem.DcIn :=
  let inA := smdDcInAH dc mshrRdy
  let go := smdRefillGoH dc mshrRdy l2if
  { inA with
    missRspOutV := go && (match dc.miss with | some m => !m.isWrite | none => false)
  , allocWriteV := go
  , needReplace := go &&
      (match dc.miss with
       | some m => (dc.line (Mem.dcGetSetIdx m.ba) 0#2).valid &&
                   (dc.line (Mem.dcGetSetIdx m.ba) 1#2).valid
       | none => false)
  , fromMemReqV := smdWrMissFireH dc mshrRdy }

/-- to_dcache.ready 的握手版（SMD-D7）。注：dcCtrlFire 此处用 smdDcInAH 而非
    in0H——go 相关字段在本谓词取值上无影响（miss.isSome ⇒ 整体 false；
    miss.isNone ⇒ go=false ⇒ in0H ≡ smdDcInAH），故无需 l2if 参数。 -/
def smdDcReqRdyH (dc : SmdDc) (mshrRdy : Bool) : Bool :=
  (dc.core.st1.isNone || Mem.dcCtrlFire dc.core (smdDcInAH dc mshrRdy)) &&
    dc.miss.isNone && !(Mem.dcwFull dc.wshr)

/-- flush/invalidate 接受拍的 dirty 行收集（SMD-D7；smdFlushWb 的队列版：
    不写 L2，改写回请求入 wbQ；行侧 dirty/valid 清除语义相同）。
    返回 (line', wbQ')。 -/
def smdFlushCollect (line : BitVec 8 → BitVec 2 → SmdLine) (q : List SmdWb)
    (inv : Bool) : (BitVec 8 → BitVec 2 → SmdLine) × List SmdWb :=
  (List.finRange 256).foldl (fun acc si =>
    (List.finRange 2).foldl (fun acc2 wi =>
      let (lna, qa) := acc2
      let set : BitVec 8 := BitVec.ofNat 8 si.val
      let way : BitVec 2 := BitVec.ofNat 2 wi.val
      let ln := lna set way
      if ln.valid && ln.dirty then
        (smdUpdLine lna set way ⟨!inv, false, ln.tag, ln.dat⟩,
         qa ++ [{ ba := Mem.dcBlockAddr ln.tag set, dat := ln.dat }])
      else if inv && ln.valid then
        (smdUpdLine lna set way ⟨false, false, ln.tag, ln.dat⟩, qa)
      else acc2) acc) (line, q)

/-- 壳单拍转移的握手变体（SMD-D7）。逐段对应 smdDcStep，差异：go/ack 换握手
    语义、merged 用 grantDat、驱逐写回入 wbQ、flush 在接受拍收集、miss 槽
    不倒计、acqDone/wbQ 维护、dc.l2 不写。 -/
def smdDcStepH (dc : SmdDc) (reqV : Bool) (req : Mem.LsuDcacheReq) (mshrRdy : Bool)
    (l2if : SmdL2If) : SmdDc :=
  let in0 := smdDcIn0H dc mshrRdy l2if
  let rdy := smdDcReqRdyH dc mshrRdy
  let fire := reqV && rdy                                             -- :212-219
  let nctrl := Mem.dcGenControl req.opcode req.param
  let isFluInv : Bool := nctrl.isFlush || nctrl.isInvalidate
  let dcIn : Mem.DcIn :=
    { in0 with fire := if fire
        then some ⟨nctrl, req.opcode == 3#3, req.setIdx, req.instrId⟩ else none }
  -- ---- 事件（均与 fire 字段无关，用 in0 求值） ----
  let hitW := smdSt1Hit dc
  let rdHit : Bool := Mem.dcReadHit dc.core in0                       -- :241
  let wrHit : Bool := Mem.dcWriteHit dc.core in0                      -- :243
  let wrMissF : Bool := smdWrMissFireH dc mshrRdy
  let rdMissF : Bool := Mem.dcCtrlFire dc.core in0 &&
    (match dc.core.st1 with
     | some r => r.ctrl.isRead && !hitW.isSome
     | none => false)
  let go : Bool := smdRefillGoH dc mshrRdy l2if
  let ack : Bool := smdHintAckH dc mshrRdy
  let enqRdy : Bool := !dc.rspQ.isSome || mshrRdy                     -- coreRspQEnqRdy
  let enqEv := Mem.dcCoreRspEnq dc.core dcIn                          -- :753-757
  let enqFire : Bool := enqEv.isSome && enqRdy
  -- ---- 命中写（同 stub） ----
  let line1 :=
    match dc.sh1, hitW with
    | some h, some w =>
      if wrHit then
        let ln := dc.line h.setIdx w
        let ln' : SmdLine := ⟨ln.valid, true, ln.tag,
          smdWrLanes ln.dat h.blkOff h.word1H (smmPackMask h.active) h.dat⟩
        smdUpdLine dc.line h.setIdx w ln'
      else dc.line
    | _, _ => dc.line
  let mru1 :=
    match dc.sh1, hitW with
    | some h, some w => if rdHit || wrHit
        then fun s => if s == h.setIdx then w else dc.mru s else dc.mru
    | _, _ => dc.mru
  -- ---- 回填（grant 拍；数据来自 l2if.grantDat；dirty 驱逐入 wbQ 而非写 l2） ----
  let missBa : BitVec 25 := match dc.miss with | some m => m.ba | none => 0#25
  let rSet := Mem.dcGetSetIdx missBa
  let victim := smdVictim dc rSet
  let vln := dc.line rSet victim.1
  let wbThis : Bool := go && victim.2 && vln.dirty
  let wbBA : BitVec 25 := Mem.dcBlockAddr vln.tag rSet
  let merged : Fin 32 → BitVec 32 := match dc.miss with
    | some m => if m.isWrite then smdWrLanes l2if.grantDat m.blkOff m.word1H m.mask m.dat
                else l2if.grantDat
    | none => fun _ => 0#32
  let line2 := if go then
      match dc.miss with
      | some m => smdUpdLine line1 rSet victim.1 ⟨true, m.isWrite, Mem.dcGetTag m.ba, merged⟩
      | none => line1
    else line1
  let mru2 := if go then (fun s => if s == rSet then victim.1 else mru1 s) else mru1
  let wbQ1 := if wbThis then dc.wbQ ++ [{ ba := wbBA, dat := vln.dat }] else dc.wbQ
  let loga := if wbThis then dc.wbLog ++ [wbBA] else dc.wbLog
  -- ---- flush/invalidate 的接受拍收集（SMD-D7；ack 拍不再写回——wbQ 已排空） ----
  let (line3, wbQ2) := if fire && isFluInv
    then smdFlushCollect line2 wbQ1 nctrl.isInvalidate else (line2, wbQ1)
  let wbQ3 := if l2if.putFired then wbQ2.drop 1 else wbQ2
  -- ---- WSHR（观测用；pop = Put 被 L2 接受拍） ----
  let wshrPopV : Bool := l2if.putFired && !Mem.dcwEmpty dc.wshr
  let wshrPopIdx : Fin 4 :=
    ((List.finRange 4).find? (fun i => dc.wshr.valid i)).getD ⟨0, by decide⟩
  let wshr' := Mem.dcwStep dc.wshr wbThis wbBA wshrPopV wshrPopIdx
  -- ---- 影响应管线（同 stub；go/ack 已换握手语义） ----
  let pend1 := if enqFire && !wrMissF && !ack then none else dc.pendRsp
  let pend2 := match dc.sh1, hitW with
    | some h, some w =>
      if rdHit || wrHit then
        some ⟨h.instrId, wrHit,
              (if rdHit then smdRdRow (dc.line h.setIdx w) h.blkOff h.active
               else fun _ => 0#32),
              smmPackMask h.active⟩
      else pend1
    | _, _ => pend1
  let pend3 := if go then
      match dc.miss with
      | some m => if !m.isWrite then
          some ⟨m.instrId, false,
                (fun l => if (m.mask >>> l.val) &&& 1#32 = 1#32
                  then merged (smdFin5 (m.blkOff l)) else 0#32),
                m.mask⟩
        else pend2
      | none => pend2
    else pend2
  -- ---- coreRsp_Q（同 stub） ----
  let pushV : Option SmdRsp :=
    if !enqFire then none
    else match enqEv with
      | none => none
      | some eid =>
        if wrMissF then
          match dc.sh1 with
          | some h => some ⟨eid, true, (fun _ => 0#32), smmPackMask h.active⟩
          | none => none
        else if ack then some ⟨eid, false, (fun _ => 0#32), 0#32⟩
        else dc.pendRsp
  let rspQ' := if enqFire then pushV
    else if dc.rspQ.isSome && mshrRdy then none else dc.rspQ
  -- ---- miss 槽（捕获 / 等 grant / 完成；不倒计） ----
  let missCap : Option SmdMiss :=
    if wrMissF || rdMissF then
      match dc.core.st1, dc.sh1 with
      | some r, some h =>
        some ⟨Mem.dcBlockAddr h.tag h.setIdx, h.instrId, r.ctrl.isWrite,
              h.blkOff, h.word1H, smmPackMask h.active, h.dat, smdL2Lat⟩
      | _, _ => none
    else none
  let miss' := if go then none
    else match dc.miss with
      | some m => some m                        -- 冻结，等 grant
      | none => missCap
  let acqDone' := if wrMissF || rdMissF || go then false
    else if l2if.getFired then true else dc.acqDone
  -- ---- flush 倒计（同 stub；ack 需 wbQ 排空，见 smdHintAckH） ----
  let flushCnt' := if fire && isFluInv then 2#2
    else if dc.flushCnt == 2#2 then 1#2
    else if ack then 0#2 else dc.flushCnt
  { core := Mem.dcStep dc.core dcIn
  , sh1 := if fire then some (smdSh1Of req)
      else if Mem.dcCoreQFire dc.core in0 then none else dc.sh1
  , pendRsp := pend3
  , rspQ := rspQ'
  , line := line3
  , mru := mru2
  , miss := miss'
  , wshr := wshr'
  , l2 := dc.l2            -- SMD-D7：本变体不直写 L2 stub
  , flushCnt := flushCnt'
  , wbLog := loga          -- flush 收集不记 wbLog（SMD-D7）
  , acqDone := acqDone'
  , wbQ := wbQ3 }

/- ========================================================================= -/
/- 4. SM 集成：SmdState / smdComb / smdStep                                     -/
/-    （smmComb/smmStep 的全量复制 + SMD-D0 三处增量；SMMem.lean 只读）          -/
/- ========================================================================= -/

/-- SM global 访存变体状态：SmmState 同名字段 + DCache 壳 -/
structure SmdState where
  base     : SmvState                 -- smwComb 底座（SM+SIMT+wb_v 全通）
  fifoFull : Bool                     -- InputFIFO maybe_full（LSU.scala:551）
  fifoBits : Mem.LsuVExe              -- InputFIFO ram
  boards   : BitVec 3 → BitVec 4      -- ShiftBoard×8 taps（LSU.scala:572-576）
  lsu      : Mem.LsuState             -- AddrCalculate（:113-489）
  shm      : Mem.SmState              -- SharedMemory（ShareMem.scala:55-195）
  mshr     : Mem.MshrState            -- MSHRv2（MSHR.scala:31-108）
  dc       : SmdDc                    -- DCache 功能壳 + L2 stub（本文件 §1-3）

/-- 初始状态：底座全初值 + 访存子系统全初值 + DCache 壳初值 -/
def smdInitOf (v : SmvState) : SmdState :=
  { base := v, fifoFull := false, fifoBits := Mem.lsuVExe0
  , boards := fun _ => 0#4, lsu := Mem.lsuInit, shm := Mem.smInit, mshr := Mem.mshrInit
  , dc := smdDcInit }

/-- 组合求值（逐段对应 SMMem.lean smmComb，差异处标 SMD-D0）。返回类型复用
    SmmComb（三处增量全部落在既有字段的取值内：lsuIn.dcacheReady、
    shIn.rspReady、mshrIn.dcValid/rspId/rspData/rspMask）。 -/
def smdComb (prog : SmProg) (s : SmdState) (inp : SmIn) (hs : Bool := false) : SmmComb :=
  let sb0 := s.base.base
  -- ---- ibuffer 头控制字重建与记分板阻塞向量（同 smmComb） ----
  let headCtrl : Fin 8 → SmCtrl := fun w =>
    smCtrlOfTag prog (sb0.ib.outBits w).tag (sb0.ib.outBits w).wid
  let sbBusy : BitVec 8 :=
    pipeScoreboardBusy (fun w => sbDelay (sb0.sb w) (smToSbCtrl (headCtrl w)))
  let ibufRdy : BitVec 8 := smPack8 (fun w => sb0.ib.ibufRdy w)
  -- ---- DualIssue：CU 发射侧（同 smmComb） ----
  let cuIssCtrl : Fin 8 → SmCtrl := fun j =>
    smCtrlOfTag prog (cuIssueBits (smCuAt sb0 j)).control.tag (cuIssueBits (smCuAt sb0 j)).control.wid
  let reqX : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && !smInstIsVec (cuIssCtrl j))
  let reqV : BitVec 8 := smPack8 (fun j => cuIssueValid (smCuAt sb0 j) && smInstIsVec (cuIssCtrl j))
  let outXV : Bool := rraOutValid (by decide) reqX sb0.lgXss
  let outXJ : Fin 8 := rraChoice (by decide) reqX sb0.lgXss
  let outXBits : CuIssueBits := cuIssueBits (smCuAt sb0 outXJ)
  let outXC : SmCtrl := cuIssCtrl outXJ
  let issC : IssCtrl := smToIssCtrl outXC
  let outVV : Bool := rraOutValid (by decide) reqV sb0.lgVss
  let outVJ : Fin 8 := rraChoice (by decide) reqV sb0.lgVss
  let outVBits : CuIssueBits := cuIssueBits (smCuAt sb0 outVJ)
  let outVC : SmCtrl := cuIssCtrl outVJ
  let issV : IssCtrl := smToIssCtrl outVC
  -- ---- sALU（同 smmComb） ----
  let fireSAlu : Bool := outXV && (issRoute issC == [.sALU])
  let aluRes : BitVec 32 × Bool :=
    saAlu (outXC.row.aluFn.extractLsb' 0 5)
      (outXBits.alu_src1 ⟨0, by decide⟩) (outXBits.alu_src2 ⟨0, by decide⟩)
      (outXBits.alu_src3 ⟨0, by decide⟩)
  let brFire : Bool := fireSAlu && (outXC.row.branch != 0#2)
  let brJump : Bool :=
    if outXC.row.branch == 1#2 then aluRes.2
    else (outXC.row.branch == 2#2 || outXC.row.branch == 3#2)
  let brWid : BitVec 3 := outXBits.control.wid
  let brTarget : BitVec 32 := outXBits.alu_src3 ⟨0, by decide⟩
  -- ---- vALU 等宽 + branch_join 事件 + fetch_ctl_buf（同 smmComb） ----
  let cmpV : BitVec 32 :=
    smvCmpVec outVC.row.aluFn outVC.row.reverse
      outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let bi : BjBranchIn 32 :=
    { valuMask := exvIfMask cmpV
    , maskInit := smvMaskInit outVBits.vmask sb0.bj.tmask
    , PCbranch := outVBits.alu_src3 ⟨0, by decide⟩
    , PCexecute := outVC.pc
    , PCreconv := sb0.csr.simtRpc }
  let fcEnqRdy : Bool := !s.base.fcV || !brFire
  let wsFlushDV : Bool := wsMask0 sb0.ws.endprgCnt sb0.ws.wgValid != 0#8
  -- ---- M-D0a/M-D0b：LSU 顶层装配（LSU.scala:551-579，同 smmComb） ----
  let exeMaskV : BitVec 32 := smvMaskInit outVBits.vmask sb0.bj.tmask
  let lsuReqBits : Mem.LsuVExe := smmLsuReqBits outVC outVBits exeMaskV
  let lsuReqWid : BitVec 3 := outVBits.control.wid
  let lsuReqV : Bool := outVV && (issRoute issV == [.LSU])
  let fifoDeqRdy : Bool := (s.lsu.state == Mem.lsuSIdle) && !wsFlushDV
  let fifoEnqRdy : Bool := !s.fifoFull || fifoDeqRdy
  let lsuReqRdyT : Bool := Mem.lsuReqReady s.boards lsuReqWid fifoEnqRdy
  let portRdyV : IssPort → Bool := fun p => match p with
    | .vALU => if outVC.row.simtStack then fcEnqRdy else true
    | .SIMT => fcEnqRdy
    | .LSU => lsuReqRdyT
    | _ => false
  let issueVInRdy : Bool := issInReady issV portRdyV
  let ocOutVFire : Bool := outVV && issueVInRdy
  let isVBr : Bool := issRoute issV == [.vALU, .SIMT]
  let isJoin : Bool := issRoute issV == [.SIMT]
  let fireVAlu : Bool := ocOutVFire && ((issRoute issV).any (fun t => decide (t = .vALU)))
  let fireSimt : Bool := ocOutVFire && (isVBr || isJoin)
  let fireLsu : Bool := ocOutVFire && (issRoute issV == [.LSU])
  let fifoEnqValid : Bool := Mem.lsuReqValidGated s.boards lsuReqWid lsuReqV
  let fifoEnqFire : Bool := fifoEnqValid && fifoEnqRdy
  let fifoDeqValid : Bool := s.fifoFull || fifoEnqValid
  let fifoDeqBits : Mem.LsuVExe := if s.fifoFull then s.fifoBits else lsuReqBits
  let fifoDeqFire : Bool := fifoDeqValid && fifoDeqRdy
  -- ---- SMD-D0a：DCache 壳组合输出（mshrRdyDc 只依赖 mshr 状态，无组合环） ----
  let mshrRdyDc : Bool := Mem.mshrDcRdy s.mshr                        -- MSHR.scala:45
  let dcc : SmdDcComb := if hs                       -- SMD-D7：握手变体的 reqRdy
    then { smdDcCombOf s.dc mshrRdyDc with reqRdy := smdDcReqRdyH s.dc mshrRdyDc }
    else smdDcCombOf s.dc mshrRdyDc
  -- AddrCalculate 输入（LSU.scala:554-578）
  let lsuMshrV : Bool := Mem.lsuMshrValid s.lsu
  let lsuIn : Mem.LsuIn :=
    { fifoValid   := fifoDeqValid
    , fifoBits    := fifoDeqBits
    , flushValid  := wsFlushDV
    , mshrReady   := Mem.mshrAddrRdy s.mshr
    , idxEntry    := if lsuMshrV && Mem.mshrAddrRdy s.mshr
                     then Mem.mshrValidEntry s.mshr else 0#3
    , dcacheReady := dcc.reqRdy          -- SMD-D0a（原：true stub，M-D4）
    , sharedReady := Mem.smReqReady s.shm
    , csrTid := 0#32, csrPds := 0#32, csrNumw := 0#32 }
  let lsuOut : Mem.LsuOut := Mem.lsuOutputs s.lsu lsuIn
  let lsuShFire : Bool := lsuOut.sharedValid && lsuIn.sharedReady
  -- ShareMem 输入（SMD-D0b：rspReady = arbiter in(1).ready = out.ready &&
  --   !in(0).valid，LSU.scala:560-563；原：mshrDcRdy 直连，M-D4）
  let shIn : Mem.SmIn :=
    { reqValid := lsuOut.sharedValid
    , req := smmShReqOf lsuOut.sharedBits
    , rspReady := mshrRdyDc && !dcc.rspV }
  let shRspV : Bool := Mem.smRspValid s.shm
  let shRsp : Mem.SmCoreRsp := Mem.smRspBits s.shm
  -- MSHR 输出（to_pipe，MSHR.scala:97-106）→ LSU2WB（LSU.scala:490-529）
  let rspValid : Bool := Mem.mshrOutValid s.mshr
  let rspTagM : Mem.MshrTag := Mem.mshrOutTag s.mshr
  let rspTag : Mem.LsuMshrTag := smmWbTagOf rspTagM
  let rspData : Mem.LsuRow := Mem.mshrOutData s.mshr
  let rspWid : BitVec 3 := rspTag.warp_id
  let lsuWbXV : Bool := rspValid && rspTag.wxd
  let lsuWbVV : Bool := rspValid && !rspTag.wxd && rspTag.wfd
  let bjEv : BjEvent 32 :=
    if !fireSimt then .nop
    else if isVBr then .branch bi
    else .join outVC.pc
  let bjOut : BjOut 32 := (bjSysStep sb0.bj bjEv).2
  let fcEnqValid : Bool := bjOut.fetchValid
  let fcDeqValid : Bool := s.base.fcV || fcEnqValid
  let fcDeqFire : Bool := fcDeqValid && !brFire
  let fcDeqJump : Bool := if s.base.fcV then s.base.fcJ else bjOut.fetchJump
  let fcDeqPC : BitVec 32 := if s.base.fcV then s.base.fcPC else bjOut.fetchPC
  let fcDeqWid : BitVec 3 := if s.base.fcV then s.base.fcWid else outVBits.control.wid
  let brMFire : Bool := brFire || fcDeqFire
  let brMJump : Bool := if brFire then brJump else fcDeqJump
  let brMWid : BitVec 3 := if brFire then brWid else fcDeqWid
  let brMTarget : BitVec 32 := if brFire then brTarget else fcDeqPC
  let portRdyX : IssPort → Bool := fun p => match p with
    | .sALU => true | .CSR => true | .ws => !brMFire | _ => false
  let fireCsr : Bool := outXV && (issRoute issC == [.CSR])
  let fireWs : Bool := outXV && (issRoute issC == [.ws]) && !brMFire
  -- ---- warp_sche 输入（同 smmComb） ----
  let wsIn : WsInputs :=
    { warpReqFire := inp.reqFire, reqWid := inp.reqWid, newWgId := inp.reqWg
    , newWfCount := inp.reqCnt
    , warpControlFire := fireWs, simtStackOp := outXC.row.simtStackOp
    , wcWid := outXBits.control.wid, wgIdTag := inp.wgIdTag
    , warpRspReady := inp.warpRspReady
    , scoreboardBusy := sbBusy
    , exeBusy := 0#8
    , pcIbufRdy := ibufRdy
    , flushDCacheReady := Mem.lsuFlushRdy s.lsu
    , branchFire := brMFire, branchJump := brMJump, branchWid := brMWid
    , pcRspValid := false, pcRspMiss := false, pcRspWid := 0#3
    , pcReset := inp.pcReset }
  let wsO : WsOutputs := wsOut sb0.ws wsIn
  -- ---- 完美取指（同 smmComb） ----
  let fetchV : Bool := wsO.pcReqValid
  let fetchWid : BitVec 3 := wsO.pcReqWid
  let fetchPC : BitVec 32 := (sb0.pcc (wsFin fetchWid)).pout
  let fetchGrp : IbGrp IbInsn :=
    ⟨smToIbInsn (smFetchInsn prog fetchWid fetchPC),
     smToIbInsn (smFetchInsn prog fetchWid (fetchPC + 4#32)),
     (sb0.pcc (wsFin fetchWid)).mask⟩
  let ibEnqFire : Bool :=
    pipeIbEnqFire fetchV 0#2 (sb0.ib.inRdy ⟨fetchV, fetchGrp, wsO.flushValid, wsO.flushWid, 0#8⟩)
  -- ---- ibuffer2issue + instDemux（同 smmComb） ----
  let warpRdyW : Fin 8 → Bool := fun w =>
    ((wsO.warpReady >>> BitVec.ofNat 8 w.val) &&& 1#8) == 1#8
  let headIsVecW : Fin 8 → Bool := fun w => ibInstIsVec (sb0.ib.outBits w)
  let xReq : BitVec 8 := smPack8 (fun w => sb0.ib.outV w && warpRdyW w && !headIsVecW w)
  let vReq : BitVec 8 := smPack8 (fun w => sb0.ib.outV w && warpRdyW w && headIsVecW w)
  let cuRdy : Fin 8 → Bool := fun j => cuControlRdy (smCuAt sb0 j)
  let i2iXV : Bool := rraOutValid (by decide) xReq sb0.lgXi2i
  let i2iXW : Fin 8 := rraChoice (by decide) xReq sb0.lgXi2i
  let i2iXC : SmCtrl := headCtrl i2iXW
  let i2iVV : Bool := rraOutValid (by decide) vReq sb0.lgVi2i
  let i2iVW : Fin 8 := rraChoice (by decide) vReq sb0.lgVi2i
  let i2iVC : SmCtrl := headCtrl i2iVW
  let dem : OcDemuxRes 8 := ocDemux cuRdy i2iVV i2iXV (smToCuCtrl i2iVC) (smToCuCtrl i2iXC)
  let i2iXFire : Bool := i2iXV && dem.in1Rdy
  let i2iVFire : Bool := i2iVV && dem.in0Rdy
  let i2iXWid : BitVec 3 := BitVec.ofNat 3 i2iXW.val
  let i2iVWid : BitVec 3 := BitVec.ofNat 3 i2iVW.val
  let i2iInRdyW : Fin 8 → Bool := fun w =>
    if headIsVecW w then rraInReady (by decide) vReq sb0.lgVi2i dem.in0Rdy w
    else rraInReady (by decide) xReq sb0.lgXi2i dem.in1Rdy w
  let ibIn : IbTopIn :=
    { inV := pipeIbInValid fetchV 0#2, grp := fetchGrp
    , flushV := wsO.flushValid, flushW := wsO.flushWid
    , outRdy := smPack8 (fun w => pipeIbOutReady (i2iInRdyW w) (warpRdyW w)) }
  let issueXInRdy : Bool := issInReady issC portRdyX
  let ocOutXFire : Bool := outXV && issueXInRdy
  let dualInRdyJ : Fin 8 → Bool := fun j =>
    if smInstIsVec (cuIssCtrl j) then rraInReady (by decide) reqV sb0.lgVss issueVInRdy j
    else rraInReady (by decide) reqX sb0.lgXss issueXInRdy j
  -- ---- 标量写回仲裁（M-D0c 继承：in_x(2) 接 lsu2wb.out_x） ----
  let aluWbValid : Bool := fireSAlu && outXC.row.wxd && (outXC.row.branch != 1#2)
  let csrWbValid : Bool := fireCsr && outXC.row.wxd
  let wbXValids : BitVec 6 :=
    (BitVec.ofBool aluWbValid).zeroExtend 6 |||
    ((BitVec.ofBool lsuWbXV).zeroExtend 6 <<< 2) |||
    ((BitVec.ofBool csrWbValid).zeroExtend 6 <<< 3)
  let wbXChoice : Fin 6 := wbArbChoice (by decide) wbXValids
  let wbXFire : Bool := wbArbOutValid wbXValids
  let wbXWid : BitVec 3 := if wbXChoice.val = 2 then rspTag.warp_id else outXBits.control.wid
  let wbXIdxw : BitVec 8 := if wbXChoice.val = 2 then rspTag.reg_idxw else outXC.regIdxw
  let wbXWxd : Bool := if wbXChoice.val = 2 then rspTag.wxd else outXC.row.wxd
  let wbXData : BitVec 32 :=
    if wbXChoice.val = 0 then aluRes.1
    else if wbXChoice.val = 2 then rspData ⟨0, by decide⟩
    else 0#32
  let wbBank : BitVec 2 := ocWbScaBankId wbXIdxw wbXWid
  let wbAddr : BitVec 8 := ocWbScaAddr (sb0.csr.sgprBase (wsFin wbXWid)) wbXIdxw
  let wbWrEn : Bool := wbXFire && wbXWxd && (wbXIdxw != 0#8)
  -- ---- W-D0b 继承的 wb_v 写回链（M-D0c：in_v(2) 接 lsu2wb.out_v） ----
  let wbVValid : Bool :=
    outVV && ((issRoute issV).any (fun t => decide (t = .vALU)))
      && outVC.row.wvd && !outVC.row.simtStack
  let wbVValids : BitVec 6 :=
    (BitVec.ofBool wbVValid).zeroExtend 6 |||
    ((BitVec.ofBool lsuWbVV).zeroExtend 6 <<< 2)
  let wbVChoice : Fin 6 := wbArbChoice (by decide) wbVValids
  let wbVFire : Bool := wbArbOutValid wbVValids
  let wbVWid : BitVec 3 := if wbVChoice.val = 2 then rspTag.warp_id else outVBits.control.wid
  let wbVIdxw : BitVec 8 := if wbVChoice.val = 2 then rspTag.reg_idxw else outVC.regIdxw
  let wbVWvd : Bool := if wbVChoice.val = 2 then rspTag.wfd else outVC.row.wvd
  let wbVData : RfVRow := smwWbData outVC.row.aluFn outVC.row.reverse exeMaskV
    outVBits.alu_src1 outVBits.alu_src2 outVBits.alu_src3
  let wbVOutData : RfVRow :=
    if wbVChoice.val = 0 then wbVData
    else if wbVChoice.val = 2 then rspData
    else cuRow0
  let wbVMaskFn : RfVMask :=
    if wbVChoice.val = 2 then (fun t => rspTagM.mask.getLsbD t.val)
    else smwWbMaskFn exeMaskV
  let wbVBank : BitVec 2 := ocWbVecBankId wbVIdxw wbVWid
  let wbVAddr : BitVec 8 := ocWbVecAddr (sb0.csr.vgprBase (wsFin wbVWid)) wbVIdxw
  let wbVWen : Bool := wbVFire && wbVWvd
  -- ---- LSU2WB lsu_rsp.ready（LSU.scala:516-520，同 smmComb） ----
  let lsuRspRdy : Bool :=
    Mem.lsu2wbRspReady ⟨rspValid, ⟨rspTag, rspData⟩,
      wbArbInReady wbXValids true ⟨2, by decide⟩,
      wbArbInReady wbVValids true ⟨2, by decide⟩⟩
  let lsuRspFire : Bool := rspValid && lsuRspRdy
  -- ---- SMD-D0c：rspArbiter 真值（LSU.scala:560-563：in(0)=dcache_rsp 优先，
  --      in(1)=shared_rsp；原：dcValid = shRspV 直连，M-D4） ----
  let mshrIn : Mem.MshrIn :=
    { addrValid := lsuMshrV
    , addrTag := smmMshrTagOf lsuOut.mshrTag
    , dcValid := dcc.rspV || shRspV
    , rspId := if dcc.rspV then dcc.rspId else shRsp.instrId
    , rspData := if dcc.rspV then dcc.rspData else shRsp.data
    , rspMask := if dcc.rspV then dcc.rspMask else smmPackMask shRsp.activeMask
    , outReady := lsuRspRdy }
  let mshrDcF : Bool := Mem.mshrDcFire s.mshr mshrIn
  -- ---- crossbar 输入（同 smmComb） ----
  let xin : OcXbarIn :=
    { chosenS := smChSAt sb0, chosenV := smChVAt sb0
    , validS := smChSvAt sb0, validV := smChVvAt sb0
    , dataS := fun i => rfSOut (smSrfAt sb0 i), dataV := fun i => rfVOut (smVrfAt sb0 i)
    , dataV0 := fun _ => rfVV0 }
  let cuIn : Fin 8 → CuInputs := fun j =>
    { controlValid := dem.valid j, ctrl := dem.bits j
    , bv0 := (ocXbar xin j.val 0).valid, bv1 := (ocXbar xin j.val 1).valid
    , bv2 := (ocXbar xin j.val 2).valid, bv3 := (ocXbar xin j.val 3).valid
    , bb0 := ⟨(ocXbar xin j.val 0).regOrder, (ocXbar xin j.val 0).data, (ocXbar xin j.val 0).v0⟩
    , bb1 := ⟨(ocXbar xin j.val 1).regOrder, (ocXbar xin j.val 1).data, (ocXbar xin j.val 1).v0⟩
    , bb2 := ⟨(ocXbar xin j.val 2).regOrder, (ocXbar xin j.val 2).data, (ocXbar xin j.val 2).v0⟩
    , bb3 := ⟨(ocXbar xin j.val 3).regOrder, (ocXbar xin j.val 3).data, (ocXbar xin j.val 3).v0⟩
    , issueReady := dualInRdyJ j
    , sgprBase := sb0.csr.sgprBase, vgprBase := sb0.csr.vgprBase }
  let reqs : Fin 32 → CuArbReq := fun p =>
    cuOutArbBits (smCuAt sb0 ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let rv : Fin 32 → Bool := fun p =>
    cuOutArbValidK (smCuAt sb0 ⟨p.val / 4, by have h := p.isLt; omega⟩)
      (cuIn ⟨p.val / 4, by have h := p.isLt; omega⟩) (p.val % 4)
  let bankAddrS : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocScaChoice reqs rv i (smLgSAt sb0 i))).rsAddr
  let bankAddrV : Fin 4 → BitVec 8 := fun i =>
    (reqs (ocVecChoice reqs rv i (smLgVAt sb0 i))).rsAddr
  -- ---- 记分板输入（M-D0d 继承：fence_end 接 lsu.io.fence_end(i)） ----
  let sbIn : Fin 8 → SbInputs := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    { if_fire := (i2iXFire && (i2iXWid == w3)) || (i2iVFire && (i2iVWid == w3))
    , if_ctrl := if (i2iXFire && (i2iXWid == w3)) then smToSbCtrl i2iXC else smToSbCtrl i2iVC
    , wb_v_fire := wbVFire && (wbVWid == w3)
    , wb_v_wvd := wbVWvd
    , wb_v_idxw := wbVIdxw
    , wb_x_fire := wbXFire && (wbXWid == w3), wb_x_wxd := wbXWxd, wb_x_idxw := wbXIdxw
    , br_ctrl := (brMFire && (brMWid == w3)) || (fireWs && (outXBits.control.wid == w3))
        || (bjOut.complete && (outVBits.control.wid == w3))
    , fence_end := Mem.lsuSbEmpty (s.boards w3)
        (Mem.lsuSbLeftOf fireLsu lsuReqWid w3)
        (Mem.lsuSbRightOf lsuRspFire rspWid w3)
    , opColV_in := i2iVFire && (i2iVWid == w3)
    , opColV_out := ocOutVFire && (outVBits.control.wid == w3)
    , opColX_in := i2iXFire && (i2iXWid == w3)
    , opColX_out := ocOutXFire && (outXBits.control.wid == w3) }
  -- ---- PCcontrol 驱动（同 smmComb） ----
  let pccIn : Fin 8 → PccIn := fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    if inp.pcReset then ⟨0#32, false, 1#2, 0#2⟩
    else if inp.reqFire && (inp.reqWid == w3) then ⟨inp.reqPC, false, 1#2, 0#2⟩
    else if brMFire && brMJump && (brMWid == w3) then ⟨brMTarget, false, 1#2, 0#2⟩
    else if fetchV && (fetchWid == w3) then ⟨0#32, false, 2#2, 0#2⟩
    else ⟨0#32, false, 0#2, 0#2⟩
  -- ---- 寄存器堆 bank 输入（同 smmComb，W-D0d） ----
  let rfInS : Fin 4 → RfSInputs := fun i =>
    ⟨bankAddrS i, wbAddr, wbXData, wbWrEn && (wbBank == BitVec.ofNat 2 i.val)⟩
  let rfInV : Fin 4 → RfVInputs := fun i =>
    ⟨bankAddrV i, wbVAddr, wbVOutData, wbVWen && (wbVBank == BitVec.ofNat 2 i.val), wbVMaskFn⟩
  let bankLgS' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocScaPack reqs rv i) true (smLgSAt sb0 i)
  let bankLgV' : Fin 4 → Fin 32 := fun i =>
    rraStep (by decide) (ocVecPack reqs rv i) true (smLgVAt sb0 i)
  { wsIn := wsIn, wsO := wsO
  , fetchV := fetchV, fetchWid := fetchWid, ibEnqFire := ibEnqFire
  , ibIn := ibIn
  , i2iXFire := i2iXFire, i2iVFire := i2iVFire, i2iXWid := i2iXWid, i2iVWid := i2iVWid
  , outXV := outXV, outXWid := outXBits.control.wid, ocOutXFire := ocOutXFire
  , fireSAlu := fireSAlu, fireCsr := fireCsr, fireWs := fireWs
  , aluOut := aluRes.1
  , brFire := brFire, brJump := brJump, brWid := brWid, brTarget := brTarget
  , wbXFire := wbXFire, wbXWid := wbXWid, wbXIdxw := wbXIdxw, wbXWxd := wbXWxd
  , wbXData := wbXData
  , pccIn := pccIn, sbIn := sbIn, cuIn := cuIn, rfInS := rfInS, rfInV := rfInV
  , lgXi2i := rraStep (by decide) xReq dem.in1Rdy sb0.lgXi2i
  , lgVi2i := rraStep (by decide) vReq dem.in0Rdy sb0.lgVi2i
  , lgXss := rraStep (by decide) reqX issueXInRdy sb0.lgXss
  , lgVss := rraStep (by decide) reqV issueVInRdy sb0.lgVss
  , bankLgS := bankLgS', bankLgV := bankLgV'
  , chosenS := fun i => BitVec.ofNat 5 (ocScaChoice reqs rv i (smLgSAt sb0 i)).val
  , chosenV := fun i => BitVec.ofNat 5 (ocVecChoice reqs rv i (smLgVAt sb0 i)).val
  , chosenSv := fun i => ocScaOutValid reqs rv i (smLgSAt sb0 i)
  , chosenVv := fun i => ocVecOutValid reqs rv i (smLgVAt sb0 i)
  , outVV := outVV, outVWid := outVBits.control.wid
  , issueVInRdy := issueVInRdy, ocOutVFire := ocOutVFire
  , fireVAlu := fireVAlu, fireSimt := fireSimt
  , fireVBr := fireSimt && isVBr, fireJoin := fireSimt && isJoin
  , bjEv := bjEv, bjOut := bjOut, bi := bi
  , ifMask := bjIfMask bi, elseMask := bjElseMask bi
  , fcEnqRdy := fcEnqRdy, fcEnqValid := fcEnqValid
  , fcDeqValid := fcDeqValid, fcDeqFire := fcDeqFire
  , fcDeqJump := fcDeqJump, fcDeqPC := fcDeqPC, fcDeqWid := fcDeqWid
  , brMFire := brMFire, brMJump := brMJump, brMWid := brMWid, brMTarget := brMTarget
  , exeMaskV := exeMaskV, wbVValid := wbVValid, wbVChoice := wbVChoice
  , wbVFire := wbVFire, wbVWid := wbVWid, wbVIdxw := wbVIdxw, wbVWvd := wbVWvd
  , wbVData := wbVData, wbVOutData := wbVOutData, wbVMaskFn := wbVMaskFn
  , wbVBank := wbVBank, wbVAddr := wbVAddr, wbVWen := wbVWen
  , wbXValids := wbXValids, wbVValids := wbVValids, wbXChoice := wbXChoice
  -- M-D0 增量字段（取值同 smmComb）
  , wsFlushDV := wsFlushDV
  , lsuReqV := lsuReqV, lsuReqWid := lsuReqWid, lsuReqBits := lsuReqBits
  , lsuReqRdyT := lsuReqRdyT, fireLsu := fireLsu
  , fifoEnqValid := fifoEnqValid, fifoEnqRdy := fifoEnqRdy, fifoEnqFire := fifoEnqFire
  , fifoDeqValid := fifoDeqValid, fifoDeqBits := fifoDeqBits, fifoDeqFire := fifoDeqFire
  , lsuIn := lsuIn, lsuOut := lsuOut, lsuShFire := lsuShFire
  , shIn := shIn, shRspV := shRspV
  , mshrIn := mshrIn, mshrDcF := mshrDcF
  , rspValid := rspValid, rspTag := rspTag, rspData := rspData, rspWid := rspWid
  , lsuWbXV := lsuWbXV, lsuWbVV := lsuWbVV
  , lsuRspRdy := lsuRspRdy, lsuRspFire := lsuRspFire }

/-- SM global 访存变体单拍：smmStep 同形 + DCache 壳转移（SMD-D0）。 -/
def smdStep (prog : SmProg) (s : SmdState) (inp : SmIn) : SmdState :=
  let c := smdComb prog s inp
  let b0 := s.base.base
  { base :=
    { base :=
      { ws := wsStep b0.ws c.wsIn
      , pcc := fun w => pccStep (b0.pcc w) (c.pccIn w)
      , ib := ibTopStep b0.ib c.ibIn
      , sb := fun w => sbStep (b0.sb w) (c.sbIn w)
      , cu := ((List.finRange 8).map fun j => cuStep (smCuAt b0 j) (c.cuIn j)).toArray
      , lgXi2i := c.lgXi2i, lgVi2i := c.lgVi2i, lgXss := c.lgXss, lgVss := c.lgVss
      , bankLgS := ((List.finRange 4).map c.bankLgS).toArray
      , bankLgV := ((List.finRange 4).map c.bankLgV).toArray
      , chosenS := ((List.finRange 4).map c.chosenS).toArray
      , chosenV := ((List.finRange 4).map c.chosenV).toArray
      , chosenSv := ((List.finRange 4).map c.chosenSv).toArray
      , chosenVv := ((List.finRange 4).map c.chosenVv).toArray
      , srf := ((List.finRange 4).map fun i => rfSStep (smSrfAt b0 i) (c.rfInS i)).toArray
      , vrf := ((List.finRange 4).map fun i => rfVStep (smVrfAt b0 i) (c.rfInV i)).toArray
      , csr := if inp.reqFire then
          { b0.csr with
            sgprBase := fun w => if w == wsFin inp.reqWid then inp.reqSgpr else b0.csr.sgprBase w
          , vgprBase := fun w => if w == wsFin inp.reqWid then inp.reqVgpr else b0.csr.vgprBase w }
        else b0.csr
      , bj := (bjSysStep b0.bj c.bjEv).1 }
    , fcV := (s.base.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.base.fcV))
    , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchJump else s.base.fcJ
    , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchPC else s.base.fcPC
    , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.outVWid else s.base.fcWid }
  , fifoFull := if c.fifoEnqFire != c.fifoDeqFire then c.fifoEnqFire else s.fifoFull
  , fifoBits := if c.fifoEnqFire then c.lsuReqBits else s.fifoBits
  , boards := Mem.lsuSbStepAll s.boards c.fireLsu c.lsuReqWid c.lsuRspFire c.rspWid
  , lsu := Mem.lsuStep Mem.lsuSmaxDefault s.lsu c.lsuIn
  , shm := Mem.smStep s.shm c.shIn
  , mshr := Mem.mshrStep s.mshr c.mshrIn
  -- ---- SMD-D0：DCache 壳（reqV/req 来自本拍 lsuOut；mshrRdy 只依赖旧态） ----
  , dc := smdDcStep s.dc c.lsuOut.dcacheValid c.lsuOut.dcacheBits
      (Mem.mshrDcRdy s.mshr) }

/-- 多拍运行 -/
def smdRun (prog : SmProg) (s : SmdState) (ins : List SmIn) : SmdState :=
  ins.foldl (smdStep prog) s

/-- SM 单拍的握手变体（SMD-D7）：comb 用 hs=true（dcacheReady 换 ReqRdyH），
    dc 用 smdDcStepH；l2if 由组合侧（MultiSML2）按拍供给。 -/
def smdStepH (prog : SmProg) (s : SmdState) (inp : SmIn) (l2if : SmdL2If) : SmdState :=
  let c := smdComb prog s inp true
  let b0 := s.base.base
  { base :=
    { base :=
      { ws := wsStep b0.ws c.wsIn
      , pcc := fun w => pccStep (b0.pcc w) (c.pccIn w)
      , ib := ibTopStep b0.ib c.ibIn
      , sb := fun w => sbStep (b0.sb w) (c.sbIn w)
      , cu := ((List.finRange 8).map fun j => cuStep (smCuAt b0 j) (c.cuIn j)).toArray
      , lgXi2i := c.lgXi2i, lgVi2i := c.lgVi2i, lgXss := c.lgXss, lgVss := c.lgVss
      , bankLgS := ((List.finRange 4).map c.bankLgS).toArray
      , bankLgV := ((List.finRange 4).map c.bankLgV).toArray
      , chosenS := ((List.finRange 4).map c.chosenS).toArray
      , chosenV := ((List.finRange 4).map c.chosenV).toArray
      , chosenSv := ((List.finRange 4).map c.chosenSv).toArray
      , chosenVv := ((List.finRange 4).map c.chosenVv).toArray
      , srf := ((List.finRange 4).map fun i => rfSStep (smSrfAt b0 i) (c.rfInS i)).toArray
      , vrf := ((List.finRange 4).map fun i => rfVStep (smVrfAt b0 i) (c.rfInV i)).toArray
      , csr := if inp.reqFire then
          { b0.csr with
            sgprBase := fun w => if w == wsFin inp.reqWid then inp.reqSgpr else b0.csr.sgprBase w
          , vgprBase := fun w => if w == wsFin inp.reqWid then inp.reqVgpr else b0.csr.vgprBase w }
        else b0.csr
      , bj := (bjSysStep b0.bj c.bjEv).1 }
    , fcV := (s.base.fcV && !c.fcDeqFire) || (c.fcEnqValid && !(c.fcDeqFire && !s.base.fcV))
    , fcJ := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchJump else s.base.fcJ
    , fcPC := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.bjOut.fetchPC else s.base.fcPC
    , fcWid := if c.fcEnqValid && (c.fcDeqFire || !s.base.fcV) then c.outVWid else s.base.fcWid }
  , fifoFull := if c.fifoEnqFire != c.fifoDeqFire then c.fifoEnqFire else s.fifoFull
  , fifoBits := if c.fifoEnqFire then c.lsuReqBits else s.fifoBits
  , boards := Mem.lsuSbStepAll s.boards c.fireLsu c.lsuReqWid c.lsuRspFire c.rspWid
  , lsu := Mem.lsuStep Mem.lsuSmaxDefault s.lsu c.lsuIn
  , shm := Mem.smStep s.shm c.shIn
  , mshr := Mem.mshrStep s.mshr c.mshrIn
  -- ---- SMD-D7：DCache 壳握手变体 ----
  , dc := smdDcStepH s.dc c.lsuOut.dcacheValid c.lsuOut.dcacheBits
      (Mem.mshrDcRdy s.mshr) l2if }

/- ========================================================================= -/
/- 5. 连线语义定理与壳级单元测试                                               -/
/- ========================================================================= -/

/-- 连线：lsuIn.dcacheReady = 壳就绪（SMD-D0a；原 M-D4 的 true stub 被替换） -/
theorem smdT_dcacheReady_wire (prog : SmProg) (s : SmdState) (inp : SmIn) :
    (smdComb prog s inp).lsuIn.dcacheReady =
      (smdDcCombOf s.dc (Mem.mshrDcRdy s.mshr)).reqRdy := rfl

/-- 连线：shared_rsp.ready = arbiter in(1).ready = out.ready && !in(0).valid
    （SMD-D0b，LSU.scala:560-563；原 M-D4 直连 mshrDcRdy） -/
theorem smdT_shRspRdy_wire (prog : SmProg) (s : SmdState) (inp : SmIn) :
    (smdComb prog s inp).shIn.rspReady =
      (Mem.mshrDcRdy s.mshr &&
        !(smdDcCombOf s.dc (Mem.mshrDcRdy s.mshr)).rspV) := rfl

/-- 连线：MSHR from_dcache = arbiter 输出（SMD-D0c：in(0)=dcache_rsp 优先） -/
theorem smdT_arb_mux_wire (prog : SmProg) (s : SmdState) (inp : SmIn) :
    let dcc := smdDcCombOf s.dc (Mem.mshrDcRdy s.mshr)
    let shRsp := Mem.smRspBits s.shm
    (smdComb prog s inp).mshrIn.dcValid = (dcc.rspV || Mem.smRspValid s.shm) ∧
    (smdComb prog s inp).mshrIn.rspId = (if dcc.rspV then dcc.rspId else shRsp.instrId) ∧
    (smdComb prog s inp).mshrIn.rspMask =
      (if dcc.rspV then dcc.rspMask else smmPackMask shRsp.activeMask) := ⟨rfl, rfl, rfl⟩

/-- 连线：DCache 壳步进的请求来自本拍 lsuOut（pipe.scala:416） -/
theorem smdT_dcstep_wire (prog : SmProg) (s : SmdState) (inp : SmIn) :
    (smdStep prog s inp).dc =
      smdDcStep s.dc (smdComb prog s inp).lsuOut.dcacheValid
        (smdComb prog s inp).lsuOut.dcacheBits (Mem.mshrDcRdy s.mshr) := rfl

/-- 字节使能合并规格：全使能取新、零使能取旧、半字低取新 -/
theorem smdT_mergeWord (o n : BitVec 32) :
    smdMergeWord o n 0xF#4 = n ∧
    smdMergeWord o n 0x0#4 = o ∧
    smdMergeWord o n 0x3#4 = (o &&& 0xFFFF0000#32) ||| (n &&& 0x0000FFFF#32) := by
  simp only [smdMergeWord, smdBe32] <;> bv_decide

/- ---- 壳级微轨迹（不走 SM 整机）：写 miss → L2 回填（write-allocate）→
    读命中 → 读响应。12 拍。 ---- -/

/-- 微轨迹请求：tag=0x2000/setIdx=0（blockAddr=0x200000）、全 lane、全字使能 -/
def smdDcMicroReq (op : BitVec 3) (prm : BitVec 4) (iid : BitVec 3)
    (dat : Fin 32 → BitVec 32) : Mem.LsuDcacheReq :=
  { instrId := iid, tag := 0x2000#17, setIdx := 0#8
  , blkOff := fun l => BitVec.ofNat 5 l.val
  , word1H := fun _ => 0xF#4, active := fun _ => true, data := dat
  , opcode := op, param := prm }

/-- 微轨迹数据行：lane t = 0xAB00 + t -/
def smdRowMicro : Fin 32 → BitVec 32 := fun t => 0xAB00#32 + BitVec.ofNat 32 t.val

/-- 微轨迹状态序列（含初态，共 13 项）：t0 写请求（opcode=1），t6 读请求
    （opcode=0），其余空转；mshrRdy 恒 true（即时消费） -/
def smdDcMicroTrace : List SmdDc :=
  let wr := smdDcMicroReq 1#3 0#4 3#3 smdRowMicro
  let rd := smdDcMicroReq 0#3 0#4 4#3 (fun _ => 0#32)
  let nop := smdDcMicroReq 0#3 0#4 0#3 (fun _ => 0#32)
  let seq : List (Bool × Mem.LsuDcacheReq) :=
    (true, wr) :: List.replicate 5 (false, nop) ++ [(true, rd)] ++
      List.replicate 6 (false, nop)
  (seq.foldl (fun p rq =>
    let dc' := smdDcStep p.1 rq.1 rq.2 true
    (dc', p.2 ++ [dc'])) (smdDcInit, [smdDcInit])).2

/-- **壳级单元定理（命中/miss/refill 主路径）**：写 miss（iid=3）→ 写响应
    次拍即出（fromMemReq 旁路）→ L2 固定延迟回填（write-allocate 合并）→
    读命中（iid=4）→ 读响应数据 = 写入行。L2 初始数据未被误写。 -/
theorem smdT_micro :
    -- 写 miss 响应（t1 拍后状态）：iid=3、isWrite、全掩码
    (((smdDcMicroTrace.drop 2).head?.bind (fun d => d.rspQ)).map (·.instrId) == some 3#3) &&
    (((smdDcMicroTrace.drop 2).head?.bind (fun d => d.rspQ)).map (·.isWrite) == some true) &&
    (((smdDcMicroTrace.drop 2).head?.bind (fun d => d.rspQ)).map (·.mask) == some 0xFFFFFFFF#32) &&
    -- 读命中响应（某拍）：iid=4、数据 lane0/31 = 写入值
    (smdDcMicroTrace.any (fun dc =>
      dc.rspQ.map (fun r => r.instrId == 4#3 && !r.isWrite &&
        r.dat ⟨0, by decide⟩ == 0xAB00#32 &&
        r.dat ⟨31, by decide⟩ == 0xAB1F#32) == some true)) &&
    -- 终态：行 valid+dirty、tag、数据 = 写入行；miss 槽空；L2 未被写
    (match smdDcMicroTrace.getLast? with
     | some fin =>
       (fin.line 0#8 0#2).valid && (fin.line 0#8 0#2).dirty &&
       ((fin.line 0#8 0#2).tag == 0x2000#17) &&
       ((fin.line 0#8 0#2).dat ⟨5, by decide⟩ == 0xAB05#32) &&
       fin.miss.isNone && (fin.l2 0x200000#25 ⟨5, by decide⟩ ==
         smdL2Init 0x200000#25 ⟨5, by decide⟩)
     | none => false) = true := by
  native_decide

/- ========================================================================= -/
/- 6. 场景 C：global store→load 写读一致（首笔 store 走 miss→L2→refill，        -/
/-    第二笔 store 与 load 走命中路径）                                         -/
/-                                                                           -/
/-  程序（warp0，真实机器码；译码回归见 6.1）：                                 -/
/-    0x00 lui  x1, 0x10000   ; 0x100000B7  x1 := 0x10000000（global 基址 A）   -/
/-    0x04 vse32.v v1, (x1)   ; 0x0200E0A7  写 rowA → **miss→refill→写分配**    -/
/-    0x08 vse32.v v5, (x1)   ; 0x0200E2A7  写 rowC → **写命中**                -/
/-    0x0C vle32.v v2, (x1)   ; 0x0200E107  读回 → v2（**读命中**）             -/
/-    0x10 endprg             ; 0x0000400B                                    -/
/-  数据（vgpr_base=16 ⇒ bank 内基址 4）：v1=rowA（bank1 addr4）、              -/
/-    v5=rowC（bank1 addr5）。全掩码、128B 对齐 ⇒ 每指令单 (tag,setIdx) 组、     -/
/-    单 dcache 请求。期望：v2 全 lane = rowC；flush 把 dirty 行 A 写回 L2       -/
/-    （L2[baA] = rowC）；事件链含 miss 捕获、写响应旁路、回填、命中。           -/
/- ========================================================================= -/

/-- 数据行：lane t = 0xAB00 + t（v1） -/
def smdRowA : RfVRow := fun t => 0xAB00#32 + BitVec.ofNat 32 t.val
/-- 数据行：lane t = 0x5C00 + t（v5，覆盖写） -/
def smdRowC : RfVRow := fun t => 0x5C00#32 + BitVec.ofNat 32 t.val
/-- 数据行：lane t = 0xCD00 + t（v3，场景 D 的 B 块） -/
def smdRowB : RfVRow := fun t => 0xCD00#32 + BitVec.ofNat 32 t.val

def smdProgC : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x100000B7#32
    else if pc = 0x04#32 then 0x0200E0A7#32
    else if pc = 0x08#32 then 0x0200E2A7#32
    else if pc = 0x0C#32 then 0x0200E107#32
    else if pc = 0x10#32 then 0x0000400B#32
    else 0#32

/-- 场景 C 初始状态：v1（bank1 addr4）与 v5（bank1 addr5）预置 + tmask 全 1 -/
def smdS0C : SmdState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a =>
        if a.val = 4 then smdRowA
        else if a.val = 5 then smdRowC else rfVInit.mem a }
    else rfVInit).toArray
  smdInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景 C 拍数 -/
def smdNC : Nat := 80

/-- 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr base=0、vgpr base=16） -/
def smdInsC : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smdNC - 1) smInNop

/- ---- 6.1 机器码译码回归（III 类自检） ---- -/

-- lui x1, 0x10000：LUI 行、rd=1
example :
    let c := smDecode 0x100000B7#32 0#3 0x00#32
    (c.row == (decRowOf decAllTables "LUI")) && (c.regIdxw == 1#8) &&
    (issRoute (smToIssCtrl c) == [.sALU]) = true := by native_decide

-- vse32.v v5, (x1)：VSE32_V 行、vs3=5、rs1=1、mem_cmd=M_XWR、路由 LSU
example :
    let c := smDecode 0x0200E2A7#32 0#3 0x08#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 5#8) &&
    (c.regIdx1 == 1#8) && (c.row.memCmd == 2#2) &&
    (issRoute (smToIssCtrl c) == [.LSU]) = true := by native_decide

-- 地址链数值：0x10000000 非 LDS（走 dcache）、tag/setIdx/blkOff 分解
example :
    (Mem.lsuAllShared Mem.lsuSmaxDefault
      ⟨fun _ => 0x10000000#32, fun _ => 0, fun _ => 0, fun _ => true,
       smmLsuCtrlOf (smDecode 0x0200E0A7#32 0#3 0x04#32)⟩ 0 0 0 == false) &&
    (Mem.lsuTagOf 0x10000000#32 == 0x2000#17) &&
    (Mem.lsuSetOf 0x10000000#32 == 0#8) &&
    (Mem.lsuBlkOf 0x1000007C#32 == 31#5) &&
    (Mem.dcBlockAddr (Mem.lsuTagOf 0x10000000#32) (Mem.lsuSetOf 0x10000000#32) ==
      0x200000#25) = true := by native_decide

/- ---- 6.2 监控器 ---- -/

/-- 监控累积器：DCache 链事件时间线 + 终态判收 -/
structure SmdChk where
  tick      : Nat
  luiWbT    : Nat          -- 首个 LUI 标量写回拍+1
  stT       : Nat          -- store lsu_req.fire（第 1/2/3 笔）拍+1
  st2T      : Nat
  st3T      : Nat
  dcReqT    : Nat          -- 首个 to_dcache fire 拍+1
  missCapT  : Nat          -- 首个 miss 捕获拍+1
  wrRspT    : Nat          -- 首个 dcache 写响应进 MSHR 拍+1
  refillT   : Nat          -- 首个回填拍+1
  wbEvT     : Nat          -- 首个 dirty 驱逐写回拍+1
  wbEvBA    : BitVec 25
  rdMissT   : Nat          -- 首个读 miss 捕获拍+1
  ldT       : Nat          -- load lsu_req.fire 拍+1
  ldWbT     : Nat          -- load wb_v fire（in_v(2) 源）拍+1
  ldWbD0    : BitVec 32
  ldWbD31   : BitVec 32
  busyAtWb  : Bool
  busyAftWb : Bool
  flushRspT : Nat          -- flush 响应（mask=0）进 MSHR 拍+1
  nDcReq    : Nat          -- to_dcache fire 总数
  nDcRsp    : Nat          -- dcache_rsp 进 MSHR 总数
  mismFire  : Nat          -- fireLsu ≠ fifoEnqFire（M-D2 沿用，应 0）
  endT      : Nat
  finOk     : Bool
  deriving DecidableEq, Repr

def smdChk0 : SmdChk :=
  { tick := 0, luiWbT := 0, stT := 0, st2T := 0, st3T := 0
  , dcReqT := 0, missCapT := 0, wrRspT := 0, refillT := 0, wbEvT := 0, wbEvBA := 0#25
  , rdMissT := 0, ldT := 0, ldWbT := 0, ldWbD0 := 0#32, ldWbD31 := 0#32
  , busyAtWb := false, busyAftWb := false, flushRspT := 0
  , nDcReq := 0, nDcRsp := 0, mismFire := 0, endT := 0, finOk := false }

/-- 监控单拍（ldIdxw = load 目的寄存器号） -/
def smdMonStep (ldIdxw : BitVec 8) (prog : SmProg) (acc : SmdChk × SmdState)
    (inp : SmIn) : SmdChk × SmdState :=
  let (m, s) := acc
  let c := smdComb prog s inp
  let s' := smdStep prog s inp
  let t := m.tick
  let dcc := smdDcCombOf s.dc (Mem.mshrDcRdy s.mshr)
  let dcReqF : Bool := c.lsuOut.dcacheValid && dcc.reqRdy
  let dcRspF : Bool := c.mshrDcF && dcc.rspV
  let isWrReq : Bool := Mem.lsuMemCmdWr c.lsuReqBits.ctrl.mem_cmd
  let missCap : Bool := s.dc.miss.isNone && s'.dc.miss.isSome
  let missCapWr : Bool := (s'.dc.miss.map (·.isWrite) == some true)
  let refill : Bool := s.dc.miss.isSome && s'.dc.miss.isNone
  let wbEv : Bool := refill && s'.dc.wbLog.length > s.dc.wbLog.length
  let isWrRsp : Bool := dcRspF && (s.dc.rspQ.map (·.isWrite) == some true)
  let flushRsp : Bool := dcRspF && (s.dc.rspQ.map (·.mask) == some 0#32)
  let m1 := { m with
      tick := t + 1
    , mismFire := m.mismFire + (if c.fireLsu != c.fifoEnqFire then 1 else 0)
    , nDcReq := m.nDcReq + (if dcReqF then 1 else 0)
    , nDcRsp := m.nDcRsp + (if dcRspF then 1 else 0)
    , dcReqT := if dcReqF && m.dcReqT == 0 then t + 1 else m.dcReqT
    , missCapT := if missCap && m.missCapT == 0 then t + 1 else m.missCapT
    , rdMissT := if missCap && !missCapWr && m.rdMissT == 0 then t + 1 else m.rdMissT
    , wrRspT := if isWrRsp && m.wrRspT == 0 then t + 1 else m.wrRspT
    , refillT := if refill && m.refillT == 0 then t + 1 else m.refillT
    , wbEvT := if wbEv && m.wbEvT == 0 then t + 1 else m.wbEvT
    , wbEvBA := if wbEv && m.wbEvT == 0
        then (s'.dc.wbLog.reverse.head?).getD 0#25 else m.wbEvBA
    , flushRspT := if flushRsp && m.flushRspT == 0 then t + 1 else m.flushRspT
    , endT := if c.fireWs && c.outXWid == 0#3 && m.endT == 0 then t + 1 else m.endT }
  let m2 := if c.wbXFire && c.wbXIdxw == 1#8 && m1.luiWbT == 0
      then { m1 with luiWbT := t + 1 } else m1
  let m3 := if c.fireLsu && isWrReq then
      if m2.stT == 0 then { m2 with stT := t + 1 }
      else if m2.st2T == 0 then { m2 with st2T := t + 1 }
      else if m2.st3T == 0 then { m2 with st3T := t + 1 } else m2
    else m2
  let m4 := if c.fireLsu && !isWrReq && m3.ldT == 0 then { m3 with ldT := t + 1 } else m3
  let m5 := if c.wbVFire && c.wbVChoice.val == 2 && m4.ldWbT == 0 then
      { m4 with
          ldWbT := t + 1
        , ldWbD0 := c.wbVOutData ⟨0, by decide⟩, ldWbD31 := c.wbVOutData ⟨31, by decide⟩
        , busyAtWb := sbRead false (s.base.base.sb ⟨0, by decide⟩).vectorReg ldIdxw
        , busyAftWb := sbRead false (s'.base.base.sb ⟨0, by decide⟩).vectorReg ldIdxw }
    else m4
  (m5, s')

/-- 场景 C 单遍运行 + 终态判收 -/
def smdRunChkC (prog : SmProg) (ins : List SmIn) : SmdChk :=
  let (m, sf) := ins.foldl (smdMonStep 2#8 prog) (smdChk0, smdS0C)
  { m with finOk :=
      -- v2（bank2 addr4）全 32 lane == rowC（写命中覆盖后读命中，整机级写读一致）
      (List.finRange 32).all (fun t =>
        (smVrfAt sf.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == smdRowC t) &&
      -- flush 把 dirty 行 A 写回 L2（SMD-D6；采样 lane0/31）
      (sf.dc.l2 0x200000#25 ⟨0, by decide⟩ == 0x5C00#32) &&
      (sf.dc.l2 0x200000#25 ⟨31, by decide⟩ == 0x5C1F#32) &&
      -- 无驱逐（两 way 足够）：wbLog 仅含 flush 写回的 baA
      (sf.dc.wbLog == [0x200000#25]) &&
      -- warp 收尾与子系统归位
      (sf.base.base.ws.warpActive == 0#8) &&
      (wsMask0 sf.base.base.ws.endprgCnt sf.base.base.ws.wgValid == 0#8) &&
      (sf.lsu.state == Mem.lsuSIdle) && (sf.fifoFull == false) &&
      (sf.mshr.used == 0#8) && (sf.boards 0#3 == 0#4) &&
      -- DCache 壳归位
      (sf.dc.miss.isNone) && (sf.dc.rspQ.isNone) && (sf.dc.core.st1.isNone) &&
      (sf.dc.flushCnt == 0#2) &&
      (m.mismFire == 0) }

/- ========================================================================= -/
/- 7. 场景 D：同 set 三块轮换——dirty 驱逐写回 L2 的整机观测                     -/
/-                                                                           -/
/-  程序（warp0）：                                                            -/
/-    0x00 lui  x1, 0x10000   ; 0x100000B7  A = 0x10000000（set0, tag 0x2000）  -/
/-    0x04 lui  x2, 0x10008   ; 0x10008137  B = 0x10008000（set0, tag 0x2001）  -/
/-    0x08 lui  x3, 0x10010   ; 0x100101B7  C = 0x10010000（set0, tag 0x2002）  -/
/-    0x0C vse32.v v1, (x1)   ; 0x0200E0A7  A := rowA（miss，填 way0，dirty）   -/
/-    0x10 vse32.v v3, (x2)   ; 0x020161A7  B := rowB（miss，填 way1，dirty）   -/
/-    0x14 vse32.v v5, (x3)   ; 0x0201E2A7  C := rowC（miss，**驱逐 A（LRU），    -/
/-                                           A dirty ⇒ 写回 L2**，填 way0）     -/
/-    0x18 vle32.v v2, (x1)   ; 0x0200E107  读 A（miss，**驱逐 B 写回**，       -/
/-                                           从 L2 回填 ⇒ v2 = rowA ⟺ 写回      -/
/-                                           真的发生过）                        -/
/-    0x1C endprg             ; 0x0000400B（flush 写回 dirty 的 C）             -/
/- ========================================================================= -/

def smdProgD : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x100000B7#32
    else if pc = 0x04#32 then 0x10008137#32
    else if pc = 0x08#32 then 0x100101B7#32
    else if pc = 0x0C#32 then 0x0200E0A7#32
    else if pc = 0x10#32 then 0x020161A7#32
    else if pc = 0x14#32 then 0x0201E2A7#32
    else if pc = 0x18#32 then 0x0200E107#32
    else if pc = 0x1C#32 then 0x0000400B#32
    else 0#32

/-- 场景 D 初始状态：v1（bank1 addr4）= rowA、v3（bank3 addr4）= rowB、
    v5（bank1 addr5）= rowC -/
def smdS0D : SmdState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a =>
        if a.val = 4 then smdRowA
        else if a.val = 5 then smdRowC else rfVInit.mem a }
    else if i.val = 3 then { rfVInit with mem := fun a =>
        if a.val = 4 then smdRowB else rfVInit.mem a }
    else rfVInit).toArray
  smdInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- 场景 D 拍数 -/
def smdND : Nat := 128

/-- 输入：拍 0 派发 warp0，其后空转 -/
def smdInsD : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 :: List.replicate (smdND - 1) smInNop

/- ---- 7.1 机器码译码回归（III 类自检） ---- -/

-- lui x2, 0x10008 / lui x3, 0x10010
example :
    (smDecode 0x10008137#32 0#3 0x04#32).regIdxw == 2#8 &&
    ((smDecode 0x100101B7#32 0#3 0x08#32).row == (decRowOf decAllTables "LUI")) &&
    (smDecode 0x100101B7#32 0#3 0x08#32).regIdxw == 3#8 := by native_decide

-- vse32.v v3, (x2)（复用 SMMem 场景 B 已验证编码）与 vse32.v v5, (x3)
example :
    let c := smDecode 0x0201E2A7#32 0#3 0x14#32
    (c.row == (decRowOf decAllTables "VSE32_V")) && (c.regIdx3 == 5#8) &&
    (c.regIdx1 == 3#8) && (c.row.memCmd == 2#2) = true := by native_decide

-- 三块同 set 不同 tag（驱逐链的地址前提）
example :
    (Mem.lsuSetOf 0x10000000#32 == 0#8) && (Mem.lsuSetOf 0x10008000#32 == 0#8) &&
    (Mem.lsuSetOf 0x10010000#32 == 0#8) &&
    (Mem.lsuTagOf 0x10000000#32 == 0x2000#17) &&
    (Mem.lsuTagOf 0x10008000#32 == 0x2001#17) &&
    (Mem.lsuTagOf 0x10010000#32 == 0x2002#17) &&
    (Mem.dcBlockAddr 0x2000#17 0#8 == 0x200000#25) &&
    (Mem.dcBlockAddr 0x2001#17 0#8 == 0x200100#25) &&
    (Mem.dcBlockAddr 0x2002#17 0#8 == 0x200200#25) = true := by native_decide

/- ---- 7.2 轨迹判收 ---- -/

/-- 场景 D 单遍运行 + 终态判收 -/
def smdRunChkD (prog : SmProg) (ins : List SmIn) : SmdChk :=
  let (m, sf) := ins.foldl (smdMonStep 2#8 prog) (smdChk0, smdS0D)
  { m with finOk :=
      -- **dirty 驱逐写回的直接观测**：A 被驱逐后再读回（从 L2 回填）仍 = rowA；
      -- 若写回丢失，L2 残留的是 smdL2Init 模式（0x5A00...），v2 ≠ rowA
      (List.finRange 32).all (fun t =>
        (smVrfAt sf.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == smdRowA t) &&
      -- 反证对照：L2 原始模式 ≠ rowA（lane0：0x5A040000 ≠ 0xAB00）
      (smdL2Init 0x200000#25 ⟨0, by decide⟩ != smdRowA ⟨0, by decide⟩) &&
      -- L2 三块内容：A 来自驱逐写回（wbEv），C/B 来自 flush 写回（endprg 在
      -- load 完成前发射——flush 先行把 dirty 的 C/B 一并写回，与 SMMem 场景 A
      -- 中 endT < ldWbT 同现象：endprg 不等待在飞访存）（采样 lane0/31）
      (sf.dc.l2 0x200000#25 ⟨0, by decide⟩ == 0xAB00#32) &&
      (sf.dc.l2 0x200000#25 ⟨31, by decide⟩ == 0xAB1F#32) &&
      (sf.dc.l2 0x200100#25 ⟨0, by decide⟩ == 0xCD00#32) &&
      (sf.dc.l2 0x200100#25 ⟨31, by decide⟩ == 0xCD1F#32) &&
      (sf.dc.l2 0x200200#25 ⟨0, by decide⟩ == 0x5C00#32) &&
      (sf.dc.l2 0x200200#25 ⟨31, by decide⟩ == 0x5C1F#32) &&
      -- 写回事件序：驱逐 A（t32）→ flush 写回 C、B（t35，set/way 序）
      (sf.dc.wbLog == [0x200000#25, 0x200200#25, 0x200100#25]) &&
      -- warp 收尾与子系统归位
      (sf.base.base.ws.warpActive == 0#8) &&
      (wsMask0 sf.base.base.ws.endprgCnt sf.base.base.ws.wgValid == 0#8) &&
      (sf.lsu.state == Mem.lsuSIdle) && (sf.fifoFull == false) &&
      (sf.mshr.used == 0#8) && (sf.boards 0#3 == 0#4) &&
      (sf.dc.miss.isNone) && (sf.dc.rspQ.isNone) && (sf.dc.core.st1.isNone) &&
      (sf.dc.flushCnt == 0#2) &&
      (m.mismFire == 0) }

/- ---- 6.3/7.3 期望时间线与主定理（时间线经 /tmp 原生探针核实；拍号 = 探针拍+1） ---- -/

/-- 场景 C 期望：store1 miss（to_dcache fire 11 → miss 捕获 12 → 写响应走
    fromMemReq 旁路 13 → 回填 16）；store2（13 fire）与 load（17 fire）均命中；
    load wb_v 24（in_v(2) 源，lane0/31 = 0x5C00/0x5C1F = rowC，busy(v2) 写回拍
    清除）；flush 响应 26；endprg 19；4 笔 dcache 请求（2 store + 1 load +
    1 flush）与 4 笔响应。 -/
def smdExpC : SmdChk :=
  { tick := smdNC, luiWbT := 5
  , stT := 9, st2T := 13, st3T := 0
  , dcReqT := 11, missCapT := 12, wrRspT := 13, refillT := 16
  , wbEvT := 0, wbEvBA := 0#25, rdMissT := 0
  , ldT := 17, ldWbT := 24, ldWbD0 := 0x00005C00#32, ldWbD31 := 0x00005C1F#32
  , busyAtWb := true, busyAftWb := false, flushRspT := 26
  , nDcReq := 4, nDcRsp := 4, mismFire := 0, endT := 19, finOk := true }

/-- **场景 C 主定理（global 写读一致，端到端）**：lui → vse32（miss→L2→refill→
    写分配）→ vse32（写命中覆盖）→ vle32（读命中）→ v2 全 lane = rowC；
    flush（invalidate）把 dirty 行 A 写回 L2（L2[baA] = rowC）并清 valid；
    MSHR 条目全程正常分配/完成/释放（M-O1 的悬挂消除）。对接引用：DCache.lean
    的 st1 ready 链（dcSt1Ready，:442-478）、coreRsp 事件（dcCoreRspEnq，
    :753-757）、WSHR（dcw_*）；L1MSHR.lean 的合并/分配定理（l1m_primary_alloc
    等，SMD-D2 收窄后未例化，仅作模块级佐证）；MSHR.lean
    `mshr_entryComplete_of_rsp`、LSU.lean `lsu2wb_rspFire_iff`（响应下游）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem smdTraceC_ok : smdRunChkC smdProgC smdInsC = smdExpC := by
  native_decide

/-- 场景 D 期望：三笔 store 全 miss（fire 13/17/21；首个 miss 捕获 16、
    回填 20）；store C 回填（32）驱逐 dirty 的 A ⇒ **写回 L2**（wbEvT=32,
    ba=0x200000）；endprg（27）先行，flush 把 dirty 的 C、B 写回（响应 36）；
    load（fire 25）在 flush 清线后 miss（rdMissT=37）→ 从 L2 回填 A ⇒
    v2 = rowA（写回的直接观测，wb 44）。 -/
def smdExpD : SmdChk :=
  { tick := smdND, luiWbT := 5
  , stT := 13, st2T := 17, st3T := 21
  , dcReqT := 15, missCapT := 16, wrRspT := 17, refillT := 20
  , wbEvT := 32, wbEvBA := 0x200000#25, rdMissT := 37
  , ldT := 25, ldWbT := 44, ldWbD0 := 0x0000AB00#32, ldWbD31 := 0x0000AB1F#32
  , busyAtWb := true, busyAftWb := false, flushRspT := 36
  , nDcReq := 5, nDcRsp := 5, mismFire := 0, endT := 27, finOk := true }

/-- **场景 D 主定理（dirty 驱逐写回 L2 的整机观测）**：A/B/C 同 set 三块轮换；
    store C 触发 dirty 行 A 的驱逐写回（wbLog[0]=baA）；load A 在 A 被驱逐后
    从 L2 读回 rowA——若写回缺失，读到的将是 L2 初始模式（0x5A04...），
    v2 ≠ rowA。同时验证了 miss→L2→refill→（内部重放）主路径与 flush 全 dirty
    写回（SMD-D6）。（单遍 native_decide；公理审计多 Lean.ofReduceBool。） -/
theorem smdTraceD_ok : smdRunChkD smdProgD smdInsD = smdExpD := by
  native_decide

/- ========================================================================= -/
/- 8. 障碍清单与发现（上报主会话）                                             -/
/- ========================================================================= -/
/-
  M-O1【障碍，已在本文件解除】global（非 LDS）地址的访存通路接通：
    LSU to_dcache → DCache 功能壳（dcStep 控制核 + 功能 tag/data/miss/WSHR/L2）
    → rspArbiter in(0) → MSHRv2 → LSU2WB → wb。两条整机轨迹判收：smdTraceC_ok
    （命中路径 + 首笔 miss→refill，80 拍）与 smdTraceD_ok（miss/refill/dirty
    驱逐写回/flush，128 拍）。M-O1(ii) 的 flush 伪响应（activeMask=0 的
    coreRsp）已建模（smdHintAck 路径，flushRspT 观测），MSHR 侧无扰动
    （mask=0 ⇒ data/cm 不变，两场景 mismFire=0 且归位判收通过）。
    SMMem.lean 未改动；若主会话决定回合，增量点即 SMD-D0 的 (a)(b)(c) 三处。

  SMD-B1【模型边界】L1MSHR 收窄为单 outstanding（SMD-D2）：secondary 合并、
    miss 下命中（hit-under-miss）不建模（coreReq.ready 在 miss 在飞期间恒
    false）。后果：性能时序偏保守，功能正确性不受影响；多 outstanding 场景
    （同 warp 连续两条 global load 的深度重叠）留后续波次，模块级证据在
    L1MSHR.lean。

  SMD-B2【模型边界】coreRsp_Q 收窄为 1 项 + 反压（SMD-D4）；响应数据通路由
    pendRsp 影管线携带，入队事件与 dcCoreRspEnq 严格对齐（不变量见 §3 节头）。
    I-30（flush 响应元数据错乱）的触发条件（Q2(a): memRsp 队头滞留
    d_opcode=2 期间再来 flush；Q2(b): hintAck 与其他响应同拍合并）被本壳的
    hintAck 驱动刻意避开——本文件不复现 I-30，机制证据留 DCache.lean
    dcT_w2* 系列。

  SMD-B3【模型边界】dirty 粒度为整行（SMD-D5）：I-28 的字节级 dirtyMask 丢失
    不在本壳粒度内；替换为正确伪 LRU，I-27 的 MRU 表机制在收窄抽象外。

  SMD-B4【行为观察，非新 bug】场景 D 中 endprg（fireWs 拍 27）先于在飞 load
    的写回（44），flush/invalidate 在 load 完成前把全部 dirty 行写回并清线；
    load 随后 miss 并从 L2 读回正确数据。与 SMMem 场景 A 的 endT=15 < ldWbT=20
    同族（endprg 不等待访存完成）——记为既有观察的 global 路复核，未见异常。

  I 类审查（本范围逐行对照 LSU.scala:227-282/:560-563、DCache.scala:212-219/
  :237-243/:408-410/:442-478/:562-621/:685-757/:769-776/:818/:912、
  MSHR.scala:45-47 的对接）：未见新疑点；写 miss 响应的 fromMemReq 旁路
  （:818/:912）与读 miss 的 missRspOut 路径（:690-694）在本壳均按既有收窄
  语义驱动。II 类：无（壳为新增模型，不与既有翻译冲突）；SMD-D1 的影寄存器
  对齐由两场景全掩码轨迹覆盖。III 类：6.1/7.1 译码回归（机器码 → 译码行/
  寄存器号/路由/地址分解）全部 native_decide 通过。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（预期，AGENTS.md 已备案） -/
#print axioms smdT_dcacheReady_wire
#print axioms smdT_shRspRdy_wire
#print axioms smdT_arb_mux_wire
#print axioms smdT_dcstep_wire
#print axioms smdT_mergeWord
#print axioms smdT_micro
#print axioms smdTraceC_ok
#print axioms smdTraceD_ok

end Ventus
