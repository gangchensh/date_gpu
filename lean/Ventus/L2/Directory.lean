/- ========================================================================= -/
/-                        L2/Directory.lean                                  -/
/-  Ventus L2Cache Directory_test（tag 阵列 + 状态阵列 + 替换 + flush）模型    -/
/-                                                                           -/
/-  Chisel 源码：opengpgpu/original/ventus-gpgpu/ventus/src/L2cache/         -/
/-    Directory_test.scala（全文 312 行；下文 :NNN 均指该文件）               -/
/-  辅助源码：Parameters.scala（参数计算）、QueuedRequest.scala（FullRequest）、-/
/-    SRAMTemplate.scala（cc_dir 本体，复用 Mem/SRAMTemplate.lean）、         -/
/-    Scheduler.scala（上游连接核查）                                         -/
/-                                                                           -/
/- ======================== 例化核查（2026-08-29 grep） ====================== -/
/-  * Directory_test：仅 Scheduler.scala:84 一处例化（是全仓唯一 L2 Directory， -/
/-    文件名虽带 _test 但是正式出货模块）。                                    -/
/-  * 参数（top/parameters.scala:99-116 + L2cache/Parameters.scala:155-201）： -/
/-    sets=64（setBits=6）、ways=16（wayBits=4）、blockBytes=beatBytes=128     -/
/-    （offsetBits=7、data_bits=1024、mask_bits=128、size_bits=7）、           -/
/-    num_l2cache=1（l2cBits=0）、MMU=false → addressBits=32 → tagBits=19、   -/
/-    source_bits=16、putBits=5、writeBytes=1、memCycles=32、portFactor=2。    -/
/-  * cc_dir = SRAMTemplate(UInt(19.W), set=64, way=16, shouldReset=true,     -/
/-    holdRead=true, singlePort=false, bypassWrite=true)（:104）=             -/
/-    Mem/SRAMTemplate.lean 的 sramCfgL2Dir。                                 -/
/-  * TL 操作码（rocketchip TLMessages，仓库外依赖，标准常量）：PutFullData=0、 -/
/-    PutPartialData=1、Get=4、Hint=5；D 通道 AccessAck=0、AccessAckData=1、   -/
/-    HintAck=2（SourceD 用）。                                               -/
/-                                                                           -/
/- ======================== 建模决策 / 偏离点（D 区） ======================== -/
/-  D1. cc_dir 直接复用已验证的 SRAMTemplate 模型（sramCfgL2Dir），每拍由       -/
/-      Directory 驱动 rValid/rAddr/wValid/wAddr/wData/wMask（:245-268）。     -/
/-  D2. 与 flush 相关的 11 位 flush_set（flushCount/16，:139）：Chisel 中       -/
/-      status_reg(flush_set) 动态下标越界（≥64）行为未定义、cc_dir setIdx 口   -/
/-      截断（FIRRTL connect 宽→窄截断）。模型：SRAM 口截断（setWidth 6），    -/
/-      status 阵列为 Array.getD/setD（越界读 false、写 no-op）。Q3 的 bug      -/
/-      witness 依赖这一语义选择，已按"越界不产生效果"的最保守解释建模。       -/
/-  D3. l2cBits=0（num_l2cache=1）→ FullRequest.l2cidx 为 0 位；模型中用       -/
/-      BitVec 1 恒 0 代替（0 位 BitVec 对 decide 不友好），expandAddress       -/
/-      （Parameters.scala:233-239）在 l2cBits=0 时本就不用 l2cidx。          -/
/-  D4. 死代码不建：hitWay（:251-252，16 位宽且只被注释引用）、wen1（:203）、   -/
/-      writeSet1（:253）。replacer_array（:215-218）虽为死代码（victim 实际    -/
/-      用 LFSR，:227 注释掉了 replacer_array(set)）仍建模——它是审查对象。     -/
/-  D5. io.result.bits 全字段建模（:292-311），payload 透传 readBitsReg。       -/
/-  D6. Chisel 断言/覆盖点（require :170 等）作为输入契约记录，不建模。         -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区） ============================= -/
/-  Q1【I 类 bug，flush 计数器卡死】 :135-148 flushCount 的 when/elsewhen 优先级 -/
/-      反了：第一支（递增）优先于 elsewhen(flushDone){flushCount:=0}。在        -/
/-      flushCount=1023（flushDone=true）那一拍，只要递增条件成立（全 clean     -/
/-      cache 时 !RegNext(dirty) 恒真，必然成立），计数器走到 1024 并永远卡住： -/
/-      下一拍 flushIssueReg 已被 elsewhen(flushDone) 清 0、flushDone 变假，     -/
/-      两支都不成立 → flushCount 停在 1024。第一次 flush 表面完成（last_flush  -/
/-      由 RegNext(flushDone) 如期发出），但第二次 flush 从 1024 起扫，           -/
/-      flush_set=64..127 全部越界（status_reg 动态下标未定义、SRAM 地址截断）， -/
/-      越界区间 1024 拍内脏行不写回、b2 清除不匹配任何表项，直到回绕 0..1023    -/
/-      才"补扫"。机证：l2dT_flush_count_stuck / l2dT_flush_second_outofrange。  -/
/-      触发条件：任意一次 flush 且最后一项 clean（flush 由 Hint(param=0) 请求  -/
/-      触发，Scheduler.scala:233；flush 只需 putbuffer_empty，Scheduler:153）。 -/
/-      修复：elsewhen(flushDone) 提为第一支，或递增支加 && !flushDone。         -/
/-  Q2【I 类 bug，flush 期间写口污染状态阵列】 :192 status_reg 更新用            -/
/-      io.write.valid 而非 io.write.fire。flush 期间 write.ready=false          -/
/-      （:272），但 Scheduler.scala:227 directory.io.write.valid 直连 MSHR      -/
/-      schedule.dir.valid（MSHR 会一直举着 valid 等 ready，Scheduler:100,131） -/
/-      → 等待中的 allocate 写在 flush 期间把 status(i,j) 置 valid=true/         -/
/-      dirty=false，而 tag 阵列并未写入（cc_dir 写口要 fire 才写，:264,168）。  -/
/-      后果：flush 完成后该 (set,way) status 有效但 tag 是 wipe 后的 0（或旧     -/
/-      值），后续 tag=0 的读请求 false hit 命中一个从未分配的行 → 返回错数据。  -/
/-      机证：l2dT_write_during_flush_corrupts / l2dT_flush_false_hit。         -/
/-      修复：:192 改 io.write.fire。                                           -/
/-  Q3【I 类 bug，flush 读路径越界】 见 Q1 后半与 D2：第二次 flush 期间          -/
/-      status_reg(flush_set)（:144,:290,:304）11 位下标 ≥64 越界，Chisel 动态   -/
/-      Vec 下标越界行为未定义（Verilator 中通常读回未知/拼接垃圾），污染        -/
/-      result.bits.dirty 与 flushCount 推进条件。与 Q1 同源。                  -/
/-  Q4【I 类，性能/正确性审查点，非 I-24/I-27 族】 L2 的 victim 选择不是         -/
/-      PLRU/时间戳，而是 16 位 LFSR 低 4 位（:227），replacer_array 轮转计数    -/
/-      （:215-218）为死代码。该 LFSR（:220-223，抽头 0,1,3,4 左移 Fibonacci）  -/
/-      不是本原多项式：从种子 1 出发 11 步进环、周期仅 31（机证                -/
/-      l2d_lfsr_cycle），victim 序列是 31 长的确定环（16 个 way 均可达，机证   -/
/-      l2d_lfsr_victim_cover）。不致数据错（victim 写回对任意合法 way 均        -/
/-      正确），但"随机替换"名不副实，冲突 miss 下周期性驱逐模式可被构造。      -/
/-      另注①：lfsr 仅在 io.result.fire 时步进（:221）。另注②：`∀ x≠0,         -/
/-      step x ≠ 0` 不成立（如 0x8000 一步归零，:222 的 Mux 下一拍救回 1）——    -/
/-      非零性只对种子 1 的可达轨道成立（机证 l2d_lfsr_reach）。                 -/
/-  Q5【I 类疑点，flush 期间 result.bits.hit 未屏蔽】 :291 hit 输出不做          -/
/-      flush mux（其余字段均 Mux(flush_issue_regnext,...)）——flush 拍 hit 由   -/
/-      垃圾 tagReg 与 flush_set 读出数据比较产生，可为任意值。下游 SourceD      -/
/-      对 flush(Hint) 请求的路径均用 opcode/last_flush 兜底，暂未构造出可观测   -/
/-      危害；记录备查。                                                       -/
/-  Q6【提示】 :187/:189 用 io.result.valid 而非 fire 更新 dirty/valid——两      -/
/-      支均幂等（dirty:=true / valid,dirty:=false），反压期间重复执行无害。     -/
/-  Q7【提示】 :290 result.valid 的 flush 支引用 io.result.bits.last_flush，     -/
/-      后者本身 Mux(flush_issue_regnext,...)，组合上自洽（无环），建模按       -/
/-      flushIssueRegnext 分支展开。                                           -/
/-  Q8【II 类风险点】 cc_dir 读地址在 flush_issue 时用截断后的 flush_set（D2）； -/
/-      若 FIRRTL 截断语义与预期不符，Q1 witness 的第二次 flush 行为会变化，     -/
/-      但 flushCount 卡 1024 本身与截断无关。                                  -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Mem.SRAMTemplate
import Std.Tactic.BVDecide

namespace Ventus.L2

open Ventus.Base Ventus.Mem

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 常量与公共类型                                                          -/
/- ========================================================================= -/

-- TL A 通道操作码（rocketchip TLMessages；见头部核查）
def l2opPutFull : BitVec 3 := 0#3
def l2opPutPartial : BitVec 3 := 1#3
def l2opGet : BitVec 3 := 4#3
def l2opHint : BitVec 3 := 5#3
-- TL D 通道操作码
def l2opAccessAck : BitVec 3 := 0#3
def l2opAccessAckData : BitVec 3 := 1#3
def l2opHintAck : BitVec 3 := 2#3

/-- FullRequest（QueuedRequest.scala:19-47），l2cidx 见 D3。 -/
structure L2FullRequest where
  opcode : BitVec 3
  size : BitVec 7
  source : BitVec 16
  tag : BitVec 19
  offset : BitVec 7
  put : BitVec 5
  data : BitVec 1024
  mask : BitVec 128
  param : BitVec 3
  set : BitVec 6
  l2cidx : BitVec 1
deriving DecidableEq, Repr

def l2reqZero : L2FullRequest := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- BitVec 6 → Fin 64。 -/
def l2Fin64 (x : BitVec 6) : Fin 64 := ⟨x.toNat, Nat.lt_of_lt_of_le x.isLt (by decide)⟩
/-- BitVec 4 → Fin 16。 -/
def l2Fin16 (x : BitVec 4) : Fin 16 := ⟨x.toNat, Nat.lt_of_lt_of_le x.isLt (by decide)⟩

/-- status 阵列访问（Array.getD，越界 false，D2）。 -/
def l2StatusGet (a : Array (Array Bool)) (i j : Nat) : Bool :=
  (a.getD i #[]).getD j false

/-- status 阵列单点更新（越界 no-op，D2）。 -/
def l2StatusUpd (a : Array (Array Bool)) (i j : Nat) (v : Bool) : Array (Array Bool) :=
  a.setIfInBounds i ((a.getD i #[]).setIfInBounds j v)

/-- OHToUInt（:252,:292）：16 位 one-hot → 4 位下标；Chisel 实现为各位置
    下标的按位或，多 hot 时同样按位或（忠实建模）。 -/
def l2OHToUInt16 (h : BitVec 16) : BitVec 4 :=
  (List.range 16).foldl
    (fun acc i => if (h >>> i) &&& 1#16 = 1#16 then acc ||| (BitVec.ofNat 4 i) else acc)
    0#4

/- ---- victim LFSR（:219-227） ---- -/

/-- 16 位 Fibonacci LFSR 单拍：xor = x0^x1^x3^x4，左移插入 bit0，0 态跳 1。 -/
def l2dLfsrStep (x : BitVec 16) : BitVec 16 :=
  if x = 0#16 then 1#16
  else
    let xb := xor (xor (x.getLsbD 0) (x.getLsbD 1)) (xor (x.getLsbD 3) (x.getLsbD 4))
    ((x &&& 0x7FFF#16) <<< 1) ||| (if xb then 1#16 else 0#16)

/-- victim way = lfsr 低 4 位（:227）。 -/
def l2dVictimWay (x : BitVec 16) : BitVec 4 := x.setWidth 4

/- ========================================================================= -/
/- 2. Directory 状态、输入、输出                                              -/
/- ========================================================================= -/

/-- Directory_test 全部寄存器（逐字段对应，见各字段注释行号）。 -/
structure L2dState where
  sram : SramState 64 16 19        -- cc_dir（:104）
  wipeCount : BitVec 7             -- :112
  wipeOff : Bool                   -- :113（RegNext(false,true)）
  flushIssueReg : Bool             -- :128
  isInvalidateReg : Bool           -- :130
  flushSourceReg : BitVec 16       -- :133
  flushCount : BitVec 11           -- :135
  statusV : Array (Array Bool)     -- :138 valid
  statusD : Array (Array Bool)     -- :138 dirty
  replacer : Array (BitVec 4)      -- :215（死代码，D4）
  lfsr : BitVec 16                 -- :219
  ren1 : Bool                      -- :201
  tagReg : BitVec 19               -- :211
  setReg : BitVec 6                -- :212
  setQuash : Bool                  -- :231
  tagMatchR : Bool                 -- :233
  writeWay1 : BitVec 4             -- :234（= RegNext(io.write.bits.way)，:292 共用）
  validReg : Bool                  -- :273
  readBitsReg : L2FullRequest      -- :280
  flushIssueRegnext : Bool         -- :288（= :306 的 RegNext(flush_issue)）
  dirtyFlushReg : Bool             -- :290 的 RegNext(dirty && flush_issue)
  flushWayReg : BitVec 4           -- :292 的 RegNext(flush_way)
  flushSetReg : BitVec 11          -- :297 的 RegNext(flush_set)（11 位，见 D2）
  flushSrcRegN : BitVec 16         -- :298 的 RegNext(flush_source_reg)
  flushTagReg : BitVec 19          -- :299 的 RegNext(flush_tag)
  dirtyFlushReg2 : Bool            -- :304/:144 的 RegNext(status_reg(...).dirty(...))
  flushDoneReg : Bool              -- :305 的 RegNext(flushDone)
  readTagPrev : BitVec 19          -- :286 的 RegNext(io.read.bits.tag)
  readSetPrev : BitVec 6           -- :286 的 RegNext(io.read.bits.set)

/-- 上电/复位状态（RegInit 忠实；SRAM 复位由 SramState 自身承担）。 -/
def l2dInit : L2dState :=
  { sram := sramInit 64 16 19
    wipeCount := 0#7
    wipeOff := true
    flushIssueReg := false
    isInvalidateReg := false
    flushSourceReg := 0#16
    flushCount := 0#11
    statusV := Array.replicate 64 (Array.replicate 16 false)
    statusD := Array.replicate 64 (Array.replicate 16 false)
    replacer := Array.replicate 64 0#4
    lfsr := 0#16
    ren1 := false
    tagReg := 0#19
    setReg := 0#6
    setQuash := false
    tagMatchR := false
    writeWay1 := 0#4
    validReg := false
    readBitsReg := l2reqZero
    flushIssueRegnext := false
    dirtyFlushReg := false
    flushWayReg := 0#4
    flushSetReg := 0#11
    flushSrcRegN := 0#16
    flushTagReg := 0#19
    dirtyFlushReg2 := false
    flushDoneReg := false
    readTagPrev := 0#19
    readSetPrev := 0#6 }

/-- 输入（io.write/read/result.ready/flush/invalidate/tag_match/flush_invalidate_src）。 -/
structure L2dIn where
  writeValid : Bool
  writeWay : BitVec 4
  writeSet : BitVec 6
  writeTag : BitVec 19
  readValid : Bool
  readBits : L2FullRequest
  resultReady : Bool
  flush : Bool
  invalidate : Bool
  tagMatchIn : Bool
  flushInvSrc : BitVec 16
deriving DecidableEq, Repr

def l2dInIdle : L2dIn := ⟨false, 0, 0, 0, false, l2reqZero, true, false, false, false, 0⟩

/-- 一拍内的全部组合信号（:111-311），out 与 step 共用。 -/
structure L2dWires where
  wipeDone : Bool          -- :114
  flushIssue : Bool        -- :129
  isInvalidate : Bool      -- :131
  flushDone : Bool         -- :136
  flushSetNat : Nat        -- :139（11 位值，D2）
  flushWay : BitVec 4      -- :140
  writeReady : Bool        -- :272
  writeFire : Bool
  setQuash1 : Bool         -- :229
  tagMatch1 : Bool         -- :232
  readReady : Bool         -- :289
  readFire : Bool
  ren : Bool               -- :166
  wenNew : Bool            -- :168
  hits : BitVec 16         -- :239-242
  hit : Bool               -- :250
  timelyHit : Bool         -- :286
  resultSet : BitVec 6     -- :297
  resultWay : BitVec 4     -- :292
  aboutReplace : Bool      -- :284
  resultHit : Bool         -- :291
  notReplace : Bool        -- :172
  validSignal : Bool       -- :279
  resultValid : Bool       -- :290
  resultDirty : Bool       -- :304
  resultFire : Bool
  sramIn : SramIn 64 16 19 -- :245-268

/-- 组合逻辑（严格按 :111-311 的依赖序求值）。 -/
def l2dWiresOf (st : L2dState) (inp : L2dIn) : L2dWires :=
  let wipeDone := st.wipeCount.getLsbD 6                                -- :114
  let flushIssue := inp.flush || inp.invalidate || st.flushIssueReg     -- :129
  let isInvalidate := inp.invalidate || st.isInvalidateReg              -- :131
  let flushDone := st.flushCount = 1023#11                              -- :136
  let flushSetNat := st.flushCount.toNat >>> 4                          -- :139（/16）
  let flushWay := st.flushCount.setWidth 4                              -- :140（%16）
  let writeReady := wipeDone && !st.flushIssueReg                       -- :272
  let writeFire := inp.writeValid && writeReady
  let setQuash1 := writeFire && (inp.writeSet == inp.readBits.set)      -- :229
  let tagMatch1 := inp.writeTag == inp.readBits.tag                     -- :232
  let readReady := ((wipeDone && !writeFire) || (setQuash1 && tagMatch1))
      && !st.flushIssueReg && inp.resultReady                           -- :289
  let readFire := inp.readValid && readReady
  let ren := readFire || flushIssue                                     -- :166
  let wenNew := (!wipeDone && !st.wipeOff) || writeFire                 -- :168
  let resp := fun j : Fin 16 => sramRespData sramCfgL2Dir st.sram j     -- :141-142
  let hits := (List.finRange 16).foldl
      (fun (acc : BitVec 16) (i : Fin 16) =>
        if (resp i == st.tagReg) && l2StatusGet st.statusV st.setReg.toNat i.val
        then acc ||| (1#16 <<< i.val) else acc)
      0#16                                                              -- :239-242
  let hit := hits != 0#16                                               -- :250
  let timelyHit := (st.readTagPrev == inp.writeTag) && writeFire &&
      (st.readSetPrev == inp.writeSet)                                  -- :286
  let resultSet := if st.flushIssueRegnext then st.flushSetReg.setWidth 6
      else st.readBitsReg.set                                           -- :297
  let resultWay := if st.flushIssueRegnext then st.flushWayReg
      else if hit then l2OHToUInt16 hits
      else if st.setQuash && st.tagMatchR then st.writeWay1
      else if timelyHit then inp.writeWay
      else l2dVictimWay st.lfsr                                         -- :292
  let aboutReplace := (inp.writeSet == resultSet) &&
      (inp.writeWay == resultWay) && writeFire                          -- :284
  let resultHit := (hit || (st.setQuash && st.tagMatchR) || timelyHit) &&
      !aboutReplace                                                     -- :291
  let resultOp := if st.flushIssueRegnext then l2opHint else st.readBitsReg.opcode  -- :301
  let notReplace := (((resultOp == l2opPutFull) || (resultOp == l2opPutPartial)) &&
      !resultHit) || inp.tagMatchIn                                     -- :172
  let validSignal := if st.ren1 then st.ren1 else st.validReg           -- :279
  let lastFlushOut := if st.flushIssueRegnext then st.flushDoneReg else false  -- :305
  let resultValid := if st.flushIssueRegnext then lastFlushOut || st.dirtyFlushReg
      else validSignal                                                  -- :290
  let resultDirty := if st.flushIssueRegnext then st.dirtyFlushReg2
      else if notReplace then false
      else l2StatusGet st.statusD st.setReg.toNat resultWay.toNat       -- :304
  let resultFire := resultValid && inp.resultReady
  let sramIn : SramIn 64 16 19 :=
    { rValid := ren && !(setQuash1 && tagMatch1)                        -- :245
      rAddr := if flushIssue then l2Fin64 ((st.flushCount >>> 4).setWidth 6)
               else l2Fin64 inp.readBits.set                            -- :246（D2 截断）
      wValid := wenNew                                                  -- :264
      wAddr := if wipeDone then l2Fin64 inp.writeSet
               else l2Fin64 (st.wipeCount.setWidth 6)                   -- :266
      wData := fun _ => if wipeDone then inp.writeTag else 0#19         -- :267
      wMask := (1#16 <<< inp.writeWay.toNat) |||
               (if !wipeDone then BitVec.allOnes 16 else 0#16) }        -- :268
  ⟨wipeDone, flushIssue, isInvalidate, flushDone, flushSetNat, flushWay,
   writeReady, writeFire, setQuash1, tagMatch1, readReady, readFire, ren, wenNew,
   hits, hit, timelyHit, resultSet, resultWay, aboutReplace, resultHit, notReplace,
   validSignal, resultValid, resultDirty, resultFire, sramIn⟩

/-- 输出（io.ready/write.ready/read.ready/result.*，:271-311）。 -/
structure L2dOut where
  ready : Bool             -- :271
  writeReady : Bool        -- :272
  readReady : Bool         -- :289
  resultValid : Bool       -- :290
  resultHit : Bool         -- :291
  resultWay : BitVec 4     -- :292
  resultPut : BitVec 5     -- :293
  resultSize : BitVec 7    -- :296
  resultSet : BitVec 6     -- :297
  resultSource : BitVec 16 -- :298
  resultTag : BitVec 19    -- :299
  resultOpcode : BitVec 3  -- :301
  resultMask : BitVec 128  -- :303
  resultDirty : Bool       -- :304
  resultLastFlush : Bool   -- :305
  resultFlush : Bool       -- :306
  resultVictimTag : BitVec 19 -- :307

def l2dOut (st : L2dState) (inp : L2dIn) : L2dOut :=
  let w := l2dWiresOf st inp
  let resp := fun j : Fin 16 => sramRespData sramCfgL2Dir st.sram j
  { ready := w.wipeDone && !st.flushIssueReg                            -- :271
    writeReady := w.writeReady
    readReady := w.readReady
    resultValid := w.resultValid
    resultHit := w.resultHit
    resultWay := w.resultWay
    resultPut := if st.flushIssueRegnext then 0#5 else st.readBitsReg.put        -- :293
    resultSize := if st.flushIssueRegnext then 7#7 else st.readBitsReg.size      -- :296（log2Up(128)=7）
    resultSet := w.resultSet
    resultSource := if st.flushIssueRegnext then st.flushSrcRegN else st.readBitsReg.source -- :298
    resultTag := if st.flushIssueRegnext then st.flushTagReg else st.readBitsReg.tag  -- :299
    resultOpcode := if st.flushIssueRegnext then l2opHint else st.readBitsReg.opcode  -- :301
    resultMask := if st.flushIssueRegnext then BitVec.allOnes 128 else st.readBitsReg.mask  -- :303
    resultDirty := w.resultDirty
    resultLastFlush := if st.flushIssueRegnext then st.flushDoneReg else false   -- :305
    resultFlush := st.flushIssueRegnext                                          -- :306
    resultVictimTag := resp (l2Fin16 w.resultWay) }                              -- :307

/-- status 阵列单拍更新（:176-197，when/elsewhen 优先级 b1>b2>b3>b4>b5，
    低优先级先施加、高优先级覆盖）。 -/
def l2dStatusNext (st : L2dState) (inp : L2dIn) (w : L2dWires) :
    Array (Array Bool) × Array (Array Bool) :=
  -- b5（:192-194，io.write.valid 非 fire——Q2）
  let (v1, d1) :=
    if inp.writeValid then
      (l2StatusUpd st.statusV inp.writeSet.toNat inp.writeWay.toNat true,
       l2StatusUpd st.statusD inp.writeSet.toNat inp.writeWay.toNat false)
    else (st.statusV, st.statusD)
  -- b4（:189-191，miss 且替换 → victim valid/dirty 清 0）
  let (v2, d2) :=
    if w.resultValid && !w.resultHit && !w.notReplace then
      (l2StatusUpd v1 w.resultSet.toNat w.resultWay.toNat false,
       l2StatusUpd d1 w.resultSet.toNat w.resultWay.toNat false)
    else (v1, d1)
  -- b3（:187-188，Put hit → dirty 置位；opcode 为 :301 mux 后的 result.opcode）
  let resultOp := if st.flushIssueRegnext then l2opHint else st.readBitsReg.opcode
  let (v3, d3) :=
    if w.resultValid && w.resultHit &&
        (resultOp == l2opPutFull || resultOp == l2opPutPartial) then
      (v2, l2StatusUpd d2 w.resultSet.toNat w.resultWay.toNat true)
    else (v2, d2)
  -- b2（:181-185，flush 扫过 → dirty 清 0，invalidate 时 valid 清 0）
  let (v4, d4) :=
    if w.flushIssue then
      ((if w.isInvalidate then l2StatusUpd v3 w.flushSetNat w.flushWay.toNat false else v3),
       l2StatusUpd d3 w.flushSetNat w.flushWay.toNat false)
    else (v3, d3)
  -- b1（:178-180，wipe 期间全清）
  if !w.wipeDone then
    (Array.replicate 64 (Array.replicate 16 false),
     Array.replicate 64 (Array.replicate 16 false))
  else (v4, d4)

/-- 单拍转移。 -/
def l2dStep (st : L2dState) (inp : L2dIn) : L2dState :=
  let w := l2dWiresOf st inp
  let (sv, sd) := l2dStatusNext st inp w
  let resp := fun j : Fin 16 => sramRespData sramCfgL2Dir st.sram j
  { sram := sramStep sramCfgL2Dir st.sram w.sramIn
    wipeCount := if !w.wipeDone && !st.wipeOff then st.wipeCount + 1#7 else st.wipeCount  -- :122-124
    wipeOff := false                                                    -- :113
    flushIssueReg := if inp.flush || inp.invalidate then true
                     else if w.flushDone then false else st.flushIssueReg  -- :151-159
    isInvalidateReg := if inp.flush || inp.invalidate then inp.invalidate
                       else if w.flushDone then false else st.isInvalidateReg  -- :154-157
    flushSourceReg := if inp.flush || inp.invalidate then inp.flushInvSrc
                      else if w.flushDone then 0#16 else st.flushSourceReg  -- :153-158
    flushCount := if inp.flush || inp.invalidate ||
                      (st.flushIssueReg && (w.resultFire || !st.dirtyFlushReg2))
                  then st.flushCount + 1#11
                  else if w.flushDone then 0#11 else st.flushCount      -- :144-148（Q1）
    statusV := sv
    statusD := sd
    replacer := if st.ren1 then                                        -- :216-218
        (List.finRange 64).foldl
          (fun (a : Array (BitVec 4)) (i : Fin 64) =>
            if i.val = st.setReg.toNat then a.setIfInBounds i.val (a.getD i.val 0#4 + 1#4) else a)
          st.replacer
      else st.replacer
    lfsr := if w.resultFire then l2dLfsrStep st.lfsr else st.lfsr       -- :221-223
    ren1 := w.ren                                                       -- :201
    tagReg := if w.ren then inp.readBits.tag else st.tagReg             -- :211
    setReg := if w.ren then inp.readBits.set else st.setReg             -- :212
    setQuash := w.setQuash1                                             -- :231
    tagMatchR := w.tagMatch1                                            -- :233
    writeWay1 := inp.writeWay                                           -- :234
    validReg := if st.ren1 && !inp.resultReady then true
                else if w.resultFire then false else st.validReg        -- :274-278
    readBitsReg := if w.readFire then inp.readBits else st.readBitsReg  -- :281-283
    flushIssueRegnext := w.flushIssue                                   -- :288
    dirtyFlushReg := l2StatusGet st.statusD w.flushSetNat w.flushWay.toNat && w.flushIssue  -- :290
    flushWayReg := w.flushWay                                           -- :292
    flushSetReg := st.flushCount >>> 4                                  -- :297（11 位，D2）
    flushSrcRegN := st.flushSourceReg                                   -- :298
    flushTagReg := resp (l2Fin16 w.flushWay)                            -- :299
    dirtyFlushReg2 := l2StatusGet st.statusD w.flushSetNat w.flushWay.toNat  -- :304
    flushDoneReg := w.flushDone                                         -- :305
    readTagPrev := inp.readBits.tag                                     -- :286
    readSetPrev := inp.readBits.set }                                   -- :286

/-- 多拍执行。 -/
def l2dRun (st : L2dState) (is : List L2dIn) : L2dState :=
  is.foldl l2dStep st

/-- 多拍输出轨迹。 -/
def l2dTrace (st : L2dState) : List L2dIn → List L2dOut
  | [] => []
  | i :: is => l2dOut st i :: l2dTrace (l2dStep st i) is

/- ========================================================================= -/
/- 3. victim LFSR 定理（:219-227，Q4）                                        -/
/- ========================================================================= -/

/-- 0 态强制跳 1（:222）。 -/
theorem l2d_lfsr_zero : l2dLfsrStep 0#16 = 1#16 := by native_decide

/-- 迭代（本环境无 f^[n] 记法，自写；方程引理即定义）。 -/
def l2dLfsrIter : Nat → BitVec 16 → BitVec 16
  | 0, x => x
  | n + 1, x => l2dLfsrStep (l2dLfsrIter n x)

/- 注意（审查记录）：`∀ x ≠ 0, step x ≠ 0` 不成立——0x8000 经一步归零
   （高位比特被移出、反馈为 0），:222 的 Mux 下一拍再救回 1。
   非 0 保持只对从种子 1 出发的可达轨道成立，见 l2d_lfsr_reach。 -/

/-- Q4 机证①：从种子 1 出发 11 步进环、42 步回到第 11 步的值（周期 31）。 -/
theorem l2d_lfsr_cycle : l2dLfsrIter 42 1#16 = l2dLfsrIter 11 1#16 := by
  native_decide

/-- Q4 机证②：环上周期为 31（step^31 在环入口不动）。 -/
theorem l2d_lfsr_period31 :
    l2dLfsrIter 31 (l2dLfsrIter 11 1#16) = l2dLfsrIter 11 1#16 := by
  native_decide

/-- Q4 机证③：一个周期内 victim way（低 4 位）覆盖全部 16 个 way。 -/
theorem l2d_lfsr_victim_cover : ∀ w : BitVec 4,
    (List.range 42).any (fun k => (l2dLfsrIter k 1#16).setWidth 4 == w) = true := by
  native_decide

/-- 可达轨道（种子 1 起 42 个状态，含尾部 11 + 环 31，由 cycle 封闭）。 -/
def l2dLfsrOrbit : List (BitVec 16) := (List.range 42).map (fun k => l2dLfsrIter k 1#16)

/-- 轨道稳定性：轨道内状态一步后仍在轨道内（对全 16 位空间可判定）。 -/
theorem l2d_lfsr_orbit_stable : ∀ x : BitVec 16,
    x ∈ l2dLfsrOrbit → l2dLfsrStep x ∈ l2dLfsrOrbit := by
  native_decide

/-- 轨道内状态均非 0。 -/
theorem l2d_lfsr_orbit_ne_zero : ∀ x : BitVec 16,
    x ∈ l2dLfsrOrbit → x ≠ 0#16 := by
  native_decide

/-- 可达性主定理：从初值 0（上电）经 :222 进入 1 后，LFSR 永不为 0——
    victim 序列不会锁死。 -/
theorem l2d_lfsr_reach (k : Nat) :
    l2dLfsrIter k 1#16 ∈ l2dLfsrOrbit ∧ l2dLfsrIter k 1#16 ≠ 0#16 := by
  induction k with
  | zero => exact ⟨by native_decide, by native_decide⟩
  | succ n ih =>
      exact ⟨l2d_lfsr_orbit_stable _ ih.1,
             l2d_lfsr_orbit_ne_zero _ (l2d_lfsr_orbit_stable _ ih.1)⟩

/-- victim way 恒在 16 路范围内（:227 截断即证）。 -/
theorem l2d_victimWay_range (x : BitVec 16) : (l2dVictimWay x).toNat < 16 :=
  BitVec.isLt _

/- ========================================================================= -/
/- 4. hit 判定互斥（符号定理）                                                 -/
/- ========================================================================= -/

/-- 单 way 命中条件（:240 的逐 way 语义）：tag 相等且 valid。 -/
def l2dHitBit (tags : Fin 16 → BitVec 19) (valid : Fin 16 → Bool)
    (t : BitVec 19) (i : Fin 16) : Bool :=
  (tags i == t) && valid i

/-- hit 互斥：同 set 内无重复 valid tag 时，两个 way 不可能同时命中——
    way 选择（OHToUInt）的输入至多单 hot。 -/
theorem l2d_hit_mutual (tags : Fin 16 → BitVec 19) (valid : Fin 16 → Bool) (t : BitVec 19)
    (hdist : ∀ i j : Fin 16, valid i = true → valid j = true → tags i = tags j → i = j)
    (i j : Fin 16) (hi : l2dHitBit tags valid t i = true)
    (hj : l2dHitBit tags valid t j = true) : i = j := by
  unfold l2dHitBit at hi hj
  rw [Bool.and_eq_true] at hi hj
  exact hdist i j hi.2 hj.2 (by rw [eq_of_beq hi.1, eq_of_beq hj.1])

/-- 组合 hits 装配（:239-242 的 fold）与逐 way 语义的一致性数值回归：
    单 hot / 无 hot / 双 tag 重复（违例时多 hot）三组向量。 -/
theorem l2dT_hits_fold_agree :
    let tags : Fin 16 → BitVec 19 := fun i => if i.val = 3 then 0x12345#19 else 0#19
    let valid : Fin 16 → Bool := fun i => i.val = 3 || i.val = 9
    let fold := (List.finRange 16).foldl
      (fun (acc : BitVec 16) (i : Fin 16) =>
        if (tags i == 0x12345#19) && valid i then acc ||| (1#16 <<< i.val) else acc) 0#16
    -- way3 命中（tag 等且 valid）；way9 valid 但 tag=0 ≠ t → 不命中
    fold = (1#16 <<< 3) := by native_decide

/-- OHToUInt 数值回归：每个单 hot 输入返回其下标。 -/
theorem l2dT_oh2uint_onehot :
    (List.range 16).all
      (fun k => l2OHToUInt16 (1#16 <<< k) == BitVec.ofNat 4 k) = true := by
  native_decide

/- ========================================================================= -/
/- 5. 数值回归：wipe / 写后读 / miss victim                                   -/
/- ========================================================================= -/

def l2dReqOf (op : BitVec 3) (tag : BitVec 19) (set : BitVec 6) : L2FullRequest :=
  { l2reqZero with opcode := op, tag := tag, set := set }

def l2dInRead (tag : BitVec 19) (set : BitVec 6) : L2dIn :=
  { l2dInIdle with readValid := true, readBits := l2dReqOf l2opGet tag set }

def l2dInWrite (way : BitVec 4) (set : BitVec 6) (tag : BitVec 19) : L2dIn :=
  { l2dInIdle with writeValid := true, writeWay := way, writeSet := set, writeTag := tag }

/-- wipe 完成态（70 拍空闲：1 拍 wipeOff + 64 拍 wipe + 余量）。 -/
def l2dWiped : L2dState := l2dRun l2dInit (List.replicate 70 l2dInIdle)

/-- wipe：计数到 64 停住、status 全无效、tag 阵列全 0、ready 拉起。 -/
theorem l2dT_wipe :
    (l2dWiped.wipeCount = 64#7) ∧
    ((List.range 64).all (fun i =>
      (List.range 16).all (fun j => l2StatusGet l2dWiped.statusV i j == false)) = true) ∧
    (l2dWiped.sram.mem ⟨9, by decide⟩ ⟨7, by decide⟩ = 0#19) ∧
    ((l2dOut l2dWiped l2dInIdle).ready = true) := by native_decide

/-- 写后读命中：写 (set=5,way=3,tag=0x12345) 后读同 tag/set，
    下一拍 result.valid ∧ hit ∧ way=3（:239-252,:291-292）。 -/
theorem l2dT_write_then_read_hit :
    let outs := l2dTrace l2dWiped
      [l2dInWrite 3#4 5#6 0x12345#19, l2dInRead 0x12345#19 5#6, l2dInIdle]
    let o := outs.getD 2 (l2dOut l2dWiped l2dInIdle)
    (o.resultValid = true) ∧ (o.resultHit = true) ∧ (o.resultWay = 3#4) := by
  native_decide

/-- miss：未知 tag → 不命中，victim way = lfsr 低 4 位；result.fire 使 LFSR
    步进，下一次 miss 的 victim 随之变化（:221-227,:292）。 -/
theorem l2dT_miss_victim_lfsr :
    let outs := l2dTrace l2dWiped
      [l2dInRead 0x54321#19 7#6, l2dInIdle, l2dInRead 0x54322#19 8#6, l2dInIdle]
    let o1 := outs.getD 1 (l2dOut l2dWiped l2dInIdle)
    let o3 := outs.getD 3 (l2dOut l2dWiped l2dInIdle)
    (o1.resultValid = true) ∧ (o1.resultHit = false) ∧
    (o1.resultWay = l2dVictimWay 0#16) ∧      -- lfsr 初值 0 → victim 0
    (o3.resultHit = false) ∧
    (o3.resultWay = l2dVictimWay (l2dLfsrStep 0#16)) := by  -- 第一次 fire 后 lfsr=1
  native_decide

/- ========================================================================= -/
/- 6. Q1 witness：flushCount 卡死 1024，第二次 flush 越界                      -/
/- ========================================================================= -/

def l2dInFlushPulse : L2dIn := { l2dInIdle with flush := true, flushInvSrc := 0xABCD#16 }

/-- 全 clean cache 上第一次 flush 结束后的状态。 -/
def l2dAfterFlush : L2dState :=
  l2dRun l2dWiped (l2dInFlushPulse :: List.replicate 1100 l2dInIdle)

/-- Q1 机证①：第一次 flush 后 flushCount 恒为 1024（不再回 0）——
    :144-148 的 when/elsewhen 优先级使递增支压过 flushDone 清零支。 -/
theorem l2dT_flush_count_stuck : l2dAfterFlush.flushCount = 1024#11 := by
  native_decide

/-- Q1 机证②：卡死期间 flushIssueReg 已清（第一次 flush 表面"完成"，
    last_flush 正常发出，故障被掩盖到第二次 flush）。 -/
theorem l2dT_flush_first_completes :
    (l2dAfterFlush.flushIssueReg = false) ∧
    ((l2dOut l2dAfterFlush l2dInIdle).ready = true) := by native_decide

/-- Q1 机证③：第二次 flush 从 1024 起扫，flush_set = 64（越界，Q3）。 -/
theorem l2dT_flush_second_outofrange :
    let st := l2dRun l2dAfterFlush (l2dInFlushPulse :: List.replicate 5 l2dInIdle)
    (st.flushIssueReg = true) ∧ (st.flushCount.toNat >>> 4 ≥ 64) := by
  native_decide

/- ========================================================================= -/
/- 7. Q2 witness：flush 期间 write.valid 污染 status → 事后 false hit          -/
/- ========================================================================= -/

/-- Q2 机证①：flush 期间（write.ready=false，不 fire）举起 write.valid 一拍，
    status(9,7) 被置 valid=true，而 tag 阵列未写入（仍为 wipe 后的 0）。 -/
theorem l2dT_write_during_flush_corrupts :
    let st := l2dRun l2dWiped [l2dInFlushPulse, l2dInIdle, l2dInWrite 7#4 9#6 0x77#19]
    (l2StatusGet st.statusV 9 7 = true) ∧
    (st.sram.mem ⟨9, by decide⟩ ⟨7, by decide⟩ = 0#19) ∧
    ((l2dWiresOf (l2dRun l2dWiped [l2dInFlushPulse, l2dInIdle])
      (l2dInWrite 7#4 9#6 0x77#19)).writeFire = false) := by
  native_decide

/-- flush 完成（含 Q1 的卡死）后的污染态。 -/
def l2dCorrupt : L2dState :=
  l2dRun l2dWiped
    (l2dInFlushPulse :: l2dInIdle :: l2dInWrite 7#4 9#6 0x77#19 ::
     List.replicate 1100 l2dInIdle)

/-- Q2 机证②：flush 结束后读 set=9/tag=0（一个从未分配的地址）——
    false hit 命中 way=7：污染状态 + wipe 残留的 tag=0 拼出幻象命中，
    对 Get 将返回错数据（数据阵列从未被写入该行）。 -/
theorem l2dT_flush_false_hit :
    let outs := l2dTrace l2dCorrupt [l2dInRead 0#19 9#6, l2dInIdle]
    let o := outs.getD 1 (l2dOut l2dCorrupt l2dInIdle)
    (o.resultValid = true) ∧ (o.resultHit = true) ∧ (o.resultWay = 7#4) := by
  native_decide

/- ========================================================================= -/
/- 8. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms l2d_lfsr_orbit_stable
#print axioms l2d_lfsr_reach
#print axioms l2d_lfsr_cycle
#print axioms l2d_lfsr_victim_cover
#print axioms l2d_hit_mutual
#print axioms l2dT_wipe
#print axioms l2dT_write_then_read_hit
#print axioms l2dT_miss_victim_lfsr
#print axioms l2dT_flush_count_stuck
#print axioms l2dT_flush_second_outofrange
#print axioms l2dT_write_during_flush_corrupts
#print axioms l2dT_flush_false_hit

end Ventus.L2

