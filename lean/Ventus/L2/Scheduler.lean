/- ========================================================================= -/
/-                         L2/Scheduler.lean                                 -/
/-  L2Cache 的 Scheduler 的 Lean 4 模型、bug 可达性核销与证明                 -/
/-  Chisel 源码：opengpgpu/original/ventus-gpgpu/ventus/src/L2cache/         -/
/-    Scheduler.scala(290 行)；配合 MSHR/SinkD/Directory_test/BankedStore    -/
/-    （均已各自建模，MSHR/BankedStore 复用 L2MSHR.lean 的 l2m*）。           -/
/-  例化参数（top/parameters.scala，同 L2MSHR.lean 头部）：NSets=64、         -/
/-    NWays=16、blockBytes=beatBytes=128 ⇒ blockBeats=1、memCycles=32、       -/
/-    dirReg=false ⇒ mshrs = all_mshrs = max(2,⌈32/1⌉) = 32                  -/
/-    （Parameters.scala:424-431,:293）；ListBuffer queues=32、secondary=32   -/
/-    （:165,:89）。                                                          -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 32 个 MSHR 组建模为 `Nat → L2mState`（仅 i<32 有意义），复用已验证   -/
/-      的 l2mStep/l2mOut；函数表示便于证明 ⇒ L2scState 无 DecidableEq         -/
/-      （测试只比输出比特，不比状态）。                                     -/
/-  D2. requests ListBuffer（:89）只建模 valid 位影子（BitVec 32）：队深≥2   -/
/-      时 pop 后 HW 保持 valid=1 而影子清 0——对本批定理是安全方向（影子     -/
/-      valid=0 ⇒ scheAValid=0，见 I-39 不变量）；requests.io.data 队首内容   -/
/-      不建模，headOpcode 作输入。                                          -/
/-  D3. 优先级选择用 L2Channels 闭形式 lbLowestOne（= ~(leftOR(x)<<1)&&&x     -/
/-      的无截断等值，同 L2Channels D4/Q1 先例）；64 位 selectOH 性质由       -/
/-      l2sc_selectOH_bv（bv_decide）一次给出。                               -/
/-  D4. mshr_select===i.asUInt（:129-131,:134）改写为 selectOH 第 i 位：     -/
/-      one-hot（l2scSelectOH_spec）时等值；selectOH=0 时 HW 的 mshr_select=0 -/
/-      使 entry 0 的 *Ready 为真，但 entry 0 若有 Valid 则 mshr_request≠0，  -/
/-      矛盾——fire 级语义一致。                                              -/
/-  D5. OHToUInt（:107,:182,:214,:223）仅在 payload/输出路径用 lbCtz，定理   -/
/-      不依赖其值；:214 mixed 按 HW 语义建模 OHToUInt(0)=0（Q3 依赖此）。    -/
/-      tagMatches 多热为 don't-care（两 entry 不同 (tag,set)，本文件不证）。 -/
/-  D6. write_buffer（:125，容量 8）以 4 位计数精确建模。                     -/
/-  D7. dir_result_buffer（:244，1 项 Queue，pipe/flow=false）：enq.ready=    -/
/-      !drbValid，同拍 enq+deq 不可能。                                      -/
/-  D8. spike_info（:209,:275）省略（同 L2MSHR D2）；allocate.bits 全字段     -/
/-      直传 directory.io.result.bits（:192-209），建模为恒等。               -/
/-  D9. sinkD.io.d（:55-57）out_d 直通、:45-47/:69-78 通道接线不涉及本批     -/
/-      定理，注释级覆盖。                                                    -/
/-                                                                           -/
/- ===================== Q 区（疑点 / 障碍 / 新踩坑，随时记录） ============= -/
/-  Q1. (:181) is_pending = tagMatches.orR && alloc ≡ false，pending_index    -/
/-      恒 0 且无读取点——死代码（III 类代码质量，非功能 bug）。               -/
/-  Q2. (:190) allocate.valid 不吃 requests.io.push.ready（allocate 电平敏   -/
/-      感、不看 ready）：若 push.ready 可为 0 而 result 保持，allocate 空转   -/
/-      重复触发且 push 不落 ⇒ valids 与 scheAValid 失步（I-39 潜在触发路     -/
/-      径）。可达性依赖"directory 单 result 在飞"（读发起时已 gate           -/
/-      mshr_free && push.ready，:225；此后 pool 只减不增）——列为环境假设   -/
/-      E3，待 Directory 级确认。                                            -/
/-  Q3. (:214) mixed 广播缺 tagMatches.orR 守卫：OHToUInt(0)=0 ⇒ 任何         -/
/-      directory result（hit 或无匹配 miss）只要 opcode 与 entry 0 不同，    -/
/-      就把 entry 0 打上 mixed ⇒ sche_dir_valid 永不可置位（MSHR.scala:123） -/
/-      ⇒ 该 entry 的 refill 不写 directory、不写 bankedStore（:276）。疑似   -/
/-      I 类 bug（候选 I-42），详见返回报告。                                 -/
/-  Q4. (:246-252) miss-dirty 的 result.ready=push.ready 不含                 -/
/-      dir_result_buffer.enq.ready：drb 满时 miss-dirty result 被消费但      -/
/-      enq 被丢弃 ⇒ 脏 victim 写回丢失。疑似 I 类（候选 I-43），可达性待     -/
/-      Directory/SourceD 时序确认。                                          -/
/-  Q5. bv_decide 不支持变量下标 getLsbD/变量移位（已知踩坑）；one-hot 位      -/
/-      唯一性走 Nat testBit + div/mod 代数（l2sc_onehot_unique）。           -/
/- ========================================================================= -/

import Ventus.L2.L2Channels
import Ventus.L2.L2MSHR
import Std.Tactic.BVDecide

namespace Ventus.L2.L2Scheduler

open Ventus.L2 Ventus.L2.L2MSHR

/- 1. 参数与基础常量 -/
/-- MSHR 个数（Parameters.scala:427,429-431：max(2,(32+1-1)/1)=32） -/
def l2scMshrs : Nat := 32

/-- TL-D opcode AccessAckData=1（TLMessages；Scheduler.scala:127 的 sinkd 过滤） -/
def l2scOpAccessAckData : BitVec 3 := 1
/-- TL-A opcode Hint=5（TLMessages；:62,:232-233） -/
def l2scOpHint : BitVec 3 := 5
/-- 由逐位谓词装配 BitVec 32（Cat(...).reverse 的逐位形式，:97-101,:174-175）。
    Nat 递归形式，便于归纳证明 getLsbD 规格。 -/
def l2scOfPredGo (f : Nat → Bool) : Nat → BitVec 32
  | 0 => 0#32
  | (k+1) => l2scOfPredGo f k ||| (if f k then 1#32 <<< k else 0#32)

def l2scOfPred (f : Nat → Bool) : BitVec 32 := l2scOfPredGo f 32
/-- rightOR（chisel3 util：第 i 位 = 第 i..31 位的或），:121 用 -/
def l2scRightOR (x : BitVec 32) : BitVec 32 :=
  (List.range 32).foldl (fun acc k => acc ||| (x >>> k)) 0#32
/-- OHToUInt 的 HW 语义（含 OHToUInt(0)=0），:107,:182,:214,:223（D5） -/
def l2scOtu (x : BitVec 32) : Nat := if x = 0#32 then 0 else lbCtz x

/- 2. 状态与输入 -/
/-- Scheduler 时序状态 -/
structure L2scState where
  mshrs : Nat → L2mState   -- :91（D1；仅 i<32 有意义）
  valids : BitVec 32       -- requests.io.valid 影子（:89,:148；D2）
  robinFilter : BitVec 32  -- :103
  issueFlushInv : Bool     -- :61
  wbCount : BitVec 4       -- write_buffer 深度（:125，容量 8；D6）
  drbValid : Bool          -- dir_result_buffer 占用位（:244；D7）
  drbBits : L2mStatus      -- :247

/-- 复位态（各 RegInit：:61,:103；MSHR/ListBuffer/Queue 上电 0） -/
def l2scInit : L2scState where
  mshrs := fun _ => l2mInit
  valids := 0#32
  robinFilter := 0#32
  issueFlushInv := false
  wbCount := 0#4
  drbValid := false
  drbBits := l2mStatusZero

/-- 每拍环境输入（子模块输出侧信号，按 L2 组合定理方法论作为输入） -/
structure L2scIn where
  dirResValid : Bool        -- directory.io.result.valid
  dirRes : L2mStatus        -- directory.io.result.bits（DirectoryResult 字段集）
  dirWriteReady : Bool      -- directory.io.write.ready（:100,:131）
  dirReady : Bool           -- directory.io.ready（:225,:239）
  dirReadReady : Bool       -- directory.io.read.ready（:239）
  sourceAReqReady : Bool    -- sourceA.io.req.ready（:98,:129,:142）
  sourceDReqReady : Bool    -- sourceD.io.req.ready（:99,:130,:235,:249）
  sourceDFinish : Bool      -- sourceD.io.finish_issue（:64）
  mshrWait : Bool           -- sourceD.io.mshr_wait（:133）
  sinkdValid : Bool         -- sinkD.io.resp.valid（:127）
  sinkdSource : BitVec 16   -- sinkD.io.resp.bits.source
  sinkdOpcode : BitVec 3    -- sinkD.io.resp.bits.opcode
  sinkdData : BitVec 1024   -- sinkD.io.resp.bits.data
  reqValid : Bool           -- sinkA.io.req.valid（:156）
  reqOpcode : BitVec 3      -- sinkA.io.req.bits.opcode（:62,:225,:232-233）
  reqParam : BitVec 3       -- :232-233
  reqSource : BitVec 16     -- :234
  putbufEmpty : Bool        -- sinkA.io.empty（:152）
  pushReady : Bool          -- requests.io.push.ready（:225,:239,:252）
  headOpcode : BitVec 3     -- requests.io.data.opcode（:134,:258,:265；D2）
  wbEnqValid : Bool         -- sourceD.io.a.valid（:140）
  radrValid : Bool          -- sourceD.io.bs_radr.valid（:282）
  radrSet : BitVec 6
  radrWay : BitVec 4
  wadrValid : Bool          -- sourceD.io.bs_wadr.valid（:283）
  wadrSet : BitVec 6
  wadrWay : BitVec 4
  deriving DecidableEq, Repr

/-- 全闲输入（测试基线） -/
def l2scInIdle : L2scIn where
  dirResValid := false
  dirRes := l2mStatusZero
  dirWriteReady := true
  dirReady := true
  dirReadReady := true
  sourceAReqReady := true
  sourceDReqReady := true
  sourceDFinish := false
  mshrWait := false
  sinkdValid := false
  sinkdSource := 0#16
  sinkdOpcode := 0#3
  sinkdData := 0#1024
  reqValid := false
  reqOpcode := 0#3
  reqParam := 0#3
  reqSource := 0#16
  putbufEmpty := true
  pushReady := true
  headOpcode := 0#3
  wbEnqValid := false
  radrValid := false
  radrSet := 0#6
  radrWay := 0#4
  wadrValid := false
  wadrSet := 0#6
  wadrWay := 0#4

/- 3. 组合逻辑（逐行对应 Scheduler.scala） -/
/-- entry i 的 schedule.a.valid（MSHR.scala:97 = sche_a_valid && !mshr_wait） -/
def l2scAV (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  (st.mshrs i).scheAValid && !inp.mshrWait

/-- entry i 的 schedule.d.valid（MSHR.scala:89，io.valid=requests.io.valid(i)，:132） -/
def l2scDV (st : L2scState) (_inp : L2scIn) (i : Nat) : Bool :=
  st.valids.getLsbD i && (st.mshrs i).sinkDReg && !(st.mshrs i).scheAValid

/-- entry i 的 schedule.dir.valid（MSHR.scala:134） -/
def l2scDirV (st : L2scState) (_inp : L2scIn) (i : Nat) : Bool :=
  (st.mshrs i).scheDirValid && ((st.mshrs i).request.opcode == l2mOpGet)

/-- mshr_request 第 i 位（:97-101） -/
def l2scReqBit (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  (inp.sourceAReqReady && l2scAV st inp i) ||
  (inp.sourceDReqReady && l2scDV st inp i) ||
  (l2scDirV st inp i && inp.dirWriteReady)

def l2scMshrRequest (st : L2scState) (inp : L2scIn) : BitVec 32 :=
  l2scOfPred (l2scReqBit st inp)
/-- robin_request = Cat(mshr_request, mshr_request & robin_filter)（:104） -/
def l2scRobinRequest (st : L2scState) (inp : L2scIn) : BitVec 64 :=
  l2scMshrRequest st inp ++ (l2scMshrRequest st inp &&& st.robinFilter)

/-- mshr_selectOH2（:105，D3 闭形式） -/
def l2scSelectOH2 (st : L2scState) (inp : L2scIn) : BitVec 64 :=
  lbLowestOne (l2scRobinRequest st inp)
/-- mshr_selectOH（:106） -/
def l2scSelectOH (st : L2scState) (inp : L2scIn) : BitVec 32 :=
  (l2scSelectOH2 st inp).extractLsb' 32 32 ||| (l2scSelectOH2 st inp).extractLsb' 0 32
/-- mshr_select（:107；仅 payload/输出用，D5） -/
def l2scSelect (st : L2scState) (inp : L2scIn) : Nat :=
  l2scOtu (l2scSelectOH st inp)

/-- mshr_validOH / mshr_free / mshr_empty（:148-151） -/
def l2scMshrFree (st : L2scState) : Bool := (~~~st.valids) ≠ 0#32
def l2scMshrEmpty (st : L2scState) : Bool := (~~~st.valids) = BitVec.allOnes 32
/-- mshr_insertOH（:185-186，最低空闲 entry，D3 闭形式） -/
def l2scInsertOH (st : L2scState) : BitVec 32 := lbLowestOne (~~~st.valids)

/-- tagMatches（:174-175） -/
def l2scTagBit (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  st.valids.getLsbD i && ((st.mshrs i).request.tag == inp.dirRes.tag) &&
  ((st.mshrs i).request.set == inp.dirRes.set) && !inp.dirRes.hit

def l2scTagMatches (st : L2scState) (inp : L2scIn) : BitVec 32 :=
  l2scOfPred (l2scTagBit st inp)
/-- alloc / is_pending（:180-181；is_pending 恒 false，Q1 死代码不建模） -/
def l2scAlloc (st : L2scState) (inp : L2scIn) : Bool :=
  l2scTagMatches st inp = 0#32
/-- entry i 的 allocate.valid（:187-191） -/
def l2scAllocValid (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.dirResValid && l2scAlloc st inp && (l2scInsertOH st).getLsbD i &&
  !inp.dirRes.hit && !inp.dirRes.flush

/-- write_buffer.io.deq.valid（:129,:143,:145；D6） -/
def l2scWbDeqValid (st : L2scState) : Bool := st.wbCount ≠ 0#4
/-- 各 entry 的 schedule.*.ready（:129-131，D4 的 one-hot 位形式） -/
def l2scAReady (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.sourceAReqReady && (l2scSelectOH st inp).getLsbD i && !l2scWbDeqValid st
def l2scDReady (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.sourceDReqReady && (l2scSelectOH st inp).getLsbD i && st.valids.getLsbD i
def l2scDirReady (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.dirWriteReady && (l2scSelectOH st inp).getLsbD i

/-- entry i 的 sinkd.valid（:127；i.asUInt 与 16 位 source 的零扩展比较） -/
def l2scSinkdV (_st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.sinkdValid && (inp.sinkdSource == BitVec.ofNat 16 i) &&
  (inp.sinkdOpcode == l2scOpAccessAckData)

/-- entry i 的 mixed（:214；OHToUInt(0)=0 的 HW 语义，D5/Q3） -/
def l2scMixedI (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  inp.dirResValid && (l2scOtu (l2scTagMatches st inp) = i) &&
  (inp.dirRes.opcode != (st.mshrs i).request.opcode)

/-- Mux1H 选择（:110）：oh 为 one-hot 时 = 被选中 entry 的谓词（布尔 OR 形式） -/
def l2scMux1H (oh : BitVec 32) (f : Nat → Bool) : Bool :=
  (oh &&& l2scOfPred f) ≠ 0#32
/-- schedule.d.valid（:110 的 Mux1H 输出） -/
def l2scSchedDValid (st : L2scState) (inp : L2scIn) : Bool :=
  l2scMux1H (l2scSelectOH st inp) (l2scDV st inp)
/-- schedule.dir.valid（:110,:227,:276） -/
def l2scSchedDirValid (st : L2scState) (inp : L2scIn) : Bool :=
  l2scMux1H (l2scSelectOH st inp) (l2scDirV st inp)
/-- schedule.a.valid（:110,:145 的 Mux 支路） -/
def l2scSchedAValid (st : L2scState) (inp : L2scIn) : Bool :=
  l2scMux1H (l2scSelectOH st inp) (l2scAV st inp)

/-- entry i 的 merge.valid（:134） -/
def l2scMergeValid (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  l2scSchedDValid st inp &&
  ((inp.headOpcode == l2mOpPutFullData) || (inp.headOpcode == l2mOpPutPartialData)) &&
  (l2scSelect st inp = i)

/-- requests.io.push（:217-223） -/
def l2scPushValid (_st : L2scState) (inp : L2scIn) : Bool :=
  inp.dirResValid && !inp.dirRes.hit && !inp.dirRes.flush

def l2scPushOH (st : L2scState) (inp : L2scIn) : BitVec 32 :=
  if l2scAlloc st inp then l2scInsertOH st else l2scTagMatches st inp
/-- requests.io.pop（:235-236；D4：valid(mshr_select) 以 selectOH&&&valids≠0 表示） -/
def l2scPopValid (st : L2scState) (inp : L2scIn) : Bool :=
  ((l2scSelectOH st inp) &&& st.valids ≠ 0#32) &&
  l2scSchedDValid st inp && inp.sourceDReqReady

/-- 各 entry 的 fire（MSHR 内部消费） -/
def l2scAFire (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  l2scAV st inp i && l2scAReady st inp i
def l2scDirFire (st : L2scState) (inp : L2scIn) (i : Nat) : Bool :=
  l2scDirV st inp i && l2scDirReady st inp i

/-- 装配 entry i 的 MSHR 输入（:124-136 的 Scheduler→MSHR 接线） -/
def l2scMshrIn (st : L2scState) (inp : L2scIn) (i : Nat) : L2mInput where
  allocValid := l2scAllocValid st inp i               -- :188-191
  allocBits := inp.dirRes                             -- :192-209（D8 恒等直传）
  valid := st.valids.getLsbD i                        -- :132
  mshrWait := inp.mshrWait                            -- :133
  mixed := l2scMixedI st inp i                        -- :214
  aReady := l2scAReady st inp i                       -- :129
  dReady := l2scDReady st inp i                       -- :130
  dirReady := l2scDirReady st inp i                   -- :131
  mergeValid := l2scMergeValid st inp i               -- :134
  mergeBits :=                                        -- :135（D2：内容不影响本批定理）
    { mask := 0, data := 0, opcode := inp.headOpcode, put := 0, source := 0 }
  sinkdValid := l2scSinkdV st inp i                   -- :127
  sinkdBits :=                                        -- :128
    { opcode := inp.sinkdOpcode, source := inp.sinkdSource, data := inp.sinkdData }

/-- request.ready（:239） -/
def l2scRequestReady (st : L2scState) (inp : L2scIn) : Bool :=
  l2scMshrFree st && inp.pushReady && inp.dirReadReady && inp.dirReady &&
  !st.issueFlushInv
/-- request.fire（:62,:232-233） -/
def l2scRequestFire (st : L2scState) (inp : L2scIn) : Bool :=
  inp.reqValid && l2scRequestReady st inp

/-- bankedStore.io.sinkD_adr（:276-279）：valid=schedule.dir.valid；
    set/way 取被选中 entry 的 dir.bits（one-hot 时等值 Mux1H，D5） -/
def l2scSinkDAdrValid (st : L2scState) (inp : L2scIn) : Bool :=
  l2scSchedDirValid st inp
def l2scSinkDAdrSet (st : L2scState) (inp : L2scIn) : BitVec 6 :=
  (st.mshrs (l2scSelect st inp)).request.set
def l2scSinkDAdrWay (st : L2scState) (inp : L2scIn) : BitVec 4 :=
  (st.mshrs (l2scSelect st inp)).request.way

/-- I-40 冲突检测（复用 L2MSHR 的 BankedStore 冲突定义，:276-285 接线） -/
def l2scBsCollision (st : L2scState) (inp : L2scIn) : Bool :=
  l2mBsCollision
    { radrValid := inp.radrValid, radrSet := inp.radrSet, radrWay := inp.radrWay
      wadrValid := inp.wadrValid, wadrSet := inp.wadrSet, wadrWay := inp.wadrWay
      wadrData := 0, wadrMask := 0
      sinkDValid := l2scSinkDAdrValid st inp
      sinkDSet := l2scSinkDAdrSet st inp
      sinkDWay := l2scSinkDAdrWay st inp
      sinkDData := 0, sinkDMask := 0 }

/- 4. 状态转移 -/
def l2scStep (st : L2scState) (inp : L2scIn) : L2scState where
  mshrs := fun i => l2mStep (st.mshrs i) (l2scMshrIn st inp i)
  -- valids 影子：pop 清位、push fire 置位，同位同拍 push 优先（D2）
  valids :=
    (st.valids &&& ~~~(if l2scPopValid st inp then l2scSelectOH st inp else 0#32)) |||
    (if l2scPushValid st inp && inp.pushReady then l2scPushOH st inp else 0#32)
  -- :121
  robinFilter :=
    if l2scMshrRequest st inp ≠ 0#32 then ~~~(l2scRightOR (l2scSelectOH st inp))
    else st.robinFilter
  -- :61-66
  issueFlushInv :=
    if l2scRequestFire st inp && (inp.reqOpcode == l2scOpHint) then true
    else if inp.sourceDFinish then false
    else st.issueFlushInv
  -- :140-146（D6：enq.ready = 未满，deq.fire = 非空 && sourceA.req.ready）
  wbCount :=
    let enq := inp.wbEnqValid && (st.wbCount ≠ 8#4)
    let deq := l2scWbDeqValid st && inp.sourceAReqReady
    if enq && !deq then st.wbCount + 1#4
    else if deq && !enq then st.wbCount - 1#4
    else st.wbCount
  -- :244-252（D7）
  drbValid :=
    let enqFire := inp.dirResValid &&
      (inp.dirRes.hit || inp.dirRes.dirty || inp.dirRes.lastFlush) && !st.drbValid
    let deqFire := st.drbValid && !l2scSchedDValid st inp && inp.sourceDReqReady
    if enqFire then true else if deqFire then false else st.drbValid
  drbBits :=
    let enqFire := inp.dirResValid &&
      (inp.dirRes.hit || inp.dirRes.dirty || inp.dirRes.lastFlush) && !st.drbValid
    if enqFire then inp.dirRes else st.drbBits

def l2scRun : L2scState → List L2scIn → L2scState
  | st, [] => st
  | st, i :: is => l2scRun (l2scStep st i) is

/- 5. l2scOfPred 规格 -/
/-- 装配的逐位刻画（归纳形式；k ≤ 32 保证移位不溢出） -/
theorem l2scOfPredGo_getLsbD (f : Nat → Bool) (k i : Nat) (hk : k ≤ 32) :
    (l2scOfPredGo f k).getLsbD i = (decide (i < k) && f i) := by
  induction k with
  | zero => simp [l2scOfPredGo, BitVec.getLsbD_zero]
  | succ k ih =>
    have hk' : k ≤ 32 := by omega
    have hk'' : k < 32 := by omega
    simp only [l2scOfPredGo]
    rw [BitVec.getLsbD_or, ih hk']
    have h1 : (1#32 <<< k).getLsbD i = decide (i = k) := by
      rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
      by_cases hik : i = k
      · simp [hik, hk'']
      · by_cases hi : i < k
        · simp [hi, hik]
        · simp [show i - k ≠ 0 by omega, hik]
    by_cases hf : f k = true
    · by_cases hik : i = k
      · subst hik; simp [hf, h1]
      · have hiff : (i < k + 1) ↔ i < k := by omega
        simp [hf, h1, hik, hiff]
    · have hf' : f k = false := by simpa using hf
      by_cases hik : i = k
      · subst hik; simp [hf', BitVec.getLsbD_zero]
      · have hiff : (i < k + 1) ↔ i < k := by omega
        simp [hf', BitVec.getLsbD_zero, hiff]

theorem l2scOfPred_getLsbD (f : Nat → Bool) (i : Nat) (hi : i < 32) :
    (l2scOfPred f).getLsbD i = f i := by
  show (l2scOfPredGo f 32).getLsbD i = f i
  rw [l2scOfPredGo_getLsbD f 32 i (by omega)]
  simp [hi]
/-- 全假装配为 0（逆否形式见 l2scOfPred_ne_zero 的使用端） -/
theorem l2scOfPred_eq_zero (f : Nat → Bool) (h : ∀ i, i < 32 → f i = false) :
    l2scOfPred f = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [l2scOfPred_getLsbD f i hi, BitVec.getLsbD_zero, h i hi]
/-- 非零装配必有一位 -/
theorem l2scOfPred_ne_zero (f : Nat → Bool) (h : l2scOfPred f ≠ 0#32) :
    ∃ i, i < 32 ∧ f i = true := by
  apply Classical.byContradiction
  intro hc
  apply h
  apply l2scOfPred_eq_zero
  intro i hi
  by_cases hf : f i = true
  · exact (hc ⟨i, hi, hf⟩).elim
  · simpa using hf

/- 6'. 冒烟测试（构建即跑，保证骨架可计算） -/
/-- 冒烟：复位态无请求/无选择/insertOH=bit0；全占用时 insertOH=0 -/
theorem l2sc_t_init_idle :
    (l2scMshrRequest l2scInit l2scInIdle = 0#32 ∧
     l2scSelectOH l2scInit l2scInIdle = 0#32 ∧ l2scInsertOH l2scInit = 1#32) ∧
    l2scInsertOH { l2scInit with valids := BitVec.allOnes 32 } = 0#32 := by
  native_decide

/- 7. selectOH 规格（:104-106 的位级性质，bv_decide 一次成形） -/
/-- round-robin 选择的位级规格：one-hot、非空当且仅当有请求、授予必是请求 -/
theorem l2sc_selectOH_bv (a filt : BitVec 32) :
    let rr : BitVec 64 := a ++ (a &&& filt)
    let oh2 : BitVec 64 := rr &&& (0#64 - rr)
    let sel : BitVec 32 := oh2.extractLsb' 32 32 ||| oh2.extractLsb' 0 32
    sel &&& (sel - 1#32) = 0#32 ∧ (sel = 0#32 ↔ a = 0#32) ∧ sel &&& a = sel := by
  bv_decide

/-- 模型端 selectOH 规格（:106） -/
theorem l2scSelectOH_spec (st : L2scState) (inp : L2scIn) :
    l2scSelectOH st inp &&& (l2scSelectOH st inp - 1#32) = 0#32 ∧
    (l2scSelectOH st inp = 0#32 ↔ l2scMshrRequest st inp = 0#32) ∧
    l2scSelectOH st inp &&& l2scMshrRequest st inp = l2scSelectOH st inp := by
  have h := l2sc_selectOH_bv (l2scMshrRequest st inp) st.robinFilter
  simp only [l2scSelectOH, l2scSelectOH2, l2scRobinRequest, lbLowestOne]
  exact h

/-- 授予位必为请求位（:97-101 的逐位形式） -/
theorem l2scSelectOH_getLsbD_req (st : L2scState) (inp : L2scIn) (i : Nat)
    (hi : i < 32) (h : (l2scSelectOH st inp).getLsbD i = true) :
    l2scReqBit st inp i = true := by
  have h2 : (l2scSelectOH st inp &&& l2scMshrRequest st inp).getLsbD i = true := by
    rw [(l2scSelectOH_spec st inp).2.2]; exact h
  rw [BitVec.getLsbD_and] at h2
  simp at h2
  have h4 : (l2scMshrRequest st inp).getLsbD i = true := h2.2
  rwa [l2scMshrRequest, l2scOfPred_getLsbD _ i hi] at h4

/- 8. one-hot 位唯一性（Nat testBit + div/mod 代数，Q5） -/
/-- testBit 的 div/mod 刻画 -/
theorem l2sc_testBit_div (n k : Nat) : n.testBit k = decide (n / 2^k % 2 = 1) := by
  induction k generalizing n with
  | zero => simp [Nat.testBit_zero]
  | succ k ih =>
    rw [Nat.testBit_succ, ih]
    have h2 : 2 * 2^k = 2^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.div_div_eq_div_mul, h2]

/-- n 的第 i、j 位均置位（i<j）⇒ n-1 的第 j 位仍置位（借位被第 i 位阻断） -/
theorem l2sc_testBit_pred_of_lt {n i j : Nat} (hi : n.testBit i = true)
    (hj : n.testBit j = true) (hij : i < j) : (n - 1).testBit j = true := by
  -- 余数第 i 位置位故 ≥ 1（借位不会越过第 j 位以下的置位位）
  have ht : (n % 2^j).testBit i = true := by
    rw [Nat.testBit_mod_two_pow]; simp [hij, hi]
  have hR1 : 1 ≤ n % 2^j := Nat.pos_of_ne_zero (fun hc => by
    rw [hc, Nat.zero_testBit] at ht; exact Bool.false_ne_true ht)
  rw [l2sc_testBit_div] at hi hj ⊢
  have hj' : n / 2^j % 2 = 1 := of_decide_eq_true hj
  have hPpos : 0 < 2^j := Nat.pow_pos (by omega)
  -- n = 2^j*(n/2^j) + n%2^j，且商为奇
  have hdecomp : 2^j * (n / 2^j) + n % 2^j = n := Nat.div_add_mod n (2^j)
  obtain ⟨Q, hQ⟩ : ∃ Q, n / 2^j = 2 * Q + 1 := by
    refine ⟨n / 2^j / 2, ?_⟩
    have h := Nat.div_add_mod (n / 2^j) 2
    rw [hj'] at h; omega
  -- (n-1)/2^j = 2Q+1（余数 ≥1 借 Nat.exists_eq_add_of_le 分解，避开截断减）
  have hdiv : (n - 1) / 2^j = 2 * Q + 1 := by
    have hn : n = 2^j * (2 * Q + 1) + n % 2^j := by rw [← hQ]; exact hdecomp.symm
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hR1
    have hRl : r < 2^j := by have hlt := Nat.mod_lt n hPpos; omega
    have hn1 : n - 1 = r + 2^j * (2 * Q + 1) := by omega
    rw [hn1, Nat.add_mul_div_left r (2 * Q + 1) hPpos,
        Nat.div_eq_of_lt hRl, Nat.zero_add]
  rw [hdiv]; simp [show (2 * Q + 1) % 2 = 1 by omega]

/-- one-hot（x &&& (x-1) = 0）的位唯一性 -/
theorem l2sc_onehot_unique (oh : BitVec 32) (i j : Nat)
    (h1 : oh &&& (oh - 1#32) = 0#32)
    (hi : oh.getLsbD i = true) (hj : oh.getLsbD j = true) : i = j := by
  have W : ∀ (x : BitVec 32) (a b : Nat), x &&& (x - 1#32) = 0#32 →
      x.getLsbD a = true → x.getLsbD b = true → a < b → False := by
    intro x a b hx1 ha hb hlt
    have hb' : (x - 1#32).getLsbD b = true := by
      have hn0 : x.toNat ≠ 0 := by
        intro hc
        have htd : x.getLsbD a = Nat.testBit x.toNat a := rfl
        rw [hc, Nat.zero_testBit] at htd
        rw [htd] at ha
        exact Bool.false_ne_true ha
      have hle : 1#32 ≤ x := by
        rw [BitVec.le_def, BitVec.toNat_one (by omega)]
        exact Nat.pos_of_ne_zero hn0
      have hsub : (x - 1#32).toNat = x.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_one (by omega)]
      show (x - 1#32).toNat.testBit b = true
      rw [hsub]
      exact l2sc_testBit_pred_of_lt ha hb hlt
    have hcontra : (x &&& (x - 1#32)).getLsbD b = true := by
      rw [BitVec.getLsbD_and, hb, hb']; rfl
    rw [hx1, BitVec.getLsbD_zero] at hcontra
    exact Bool.false_ne_true hcontra
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd h (fun _ => W oh i j h1 hi hj h)
  · exact h
  · exact absurd h (fun _ => W oh j i h1 hj hi h)

/-- 越界位为零（BitVec 32） -/
theorem l2sc_getLsbD_false_of_ge32 {x : BitVec 32} {i : Nat} (h : 32 ≤ i) :
    x.getLsbD i = false := by
  have hlt : x.toNat < 2^32 := x.isLt
  have hle : (2:Nat)^32 ≤ 2^i := Nat.pow_le_pow_right (by omega) h
  show (Nat.testBit x.toNat i) = false
  rw [l2sc_testBit_div]
  have hz : x.toNat / 2^i = 0 := Nat.div_eq_of_lt (by omega)
  simp [hz]

theorem l2sc_getLsbD_lt32 {x : BitVec 32} {i : Nat} (h : x.getLsbD i = true) :
    i < 32 := by
  apply Classical.byContradiction
  intro hc
  rw [l2sc_getLsbD_false_of_ge32 (by omega)] at h
  exact Bool.false_ne_true h

/-- 非零 BitVec 必有置位位 -/
theorem l2sc_getLsbD_exists {x : BitVec 32} (hx : x ≠ 0#32) :
    ∃ i, i < 32 ∧ x.getLsbD i = true := by
  apply Classical.byContradiction
  intro hc
  apply hx
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_zero]
  by_cases hb : x.getLsbD i = true
  · exact (hc ⟨i, hi, hb⟩).elim
  · simpa using hb

/- 9. lbCtz 命中（OHToUInt 桥，:107,:214） -/
/-- lbCtz 的折叠函数（与 L2Channels.lbCtz 定义内的匿名 lambda 定义等值） -/
def l2scCtzF (x : BitVec 32) (r i : Nat) : Nat := if r == 32 && x.getLsbD i then i else r

/-- 已命中（r<32）后折叠不再移动 -/
theorem l2scCtzF_lt32 (x : BitVec 32) (r i : Nat) (hr : r < 32) : l2scCtzF x r i = r := by
  cases h : (r == 32)
  · simp [l2scCtzF, h]
  · rw [beq_iff_eq] at h; omega

/-- 起点 32 的单步 -/
theorem l2scCtzF_32 (x : BitVec 32) (i : Nat) :
    l2scCtzF x 32 i = if x.getLsbD i then i else 32 := by
  simp [l2scCtzF]

/-- 已命中后整段折叠保持 -/
theorem l2scCtzF_fold_stay (x : BitVec 32) (r : Nat) (hr : r < 32) :
    ∀ (l : List Nat), (l.foldl (l2scCtzF x) r) = r := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, l2scCtzF_lt32 x r a hr]; exact ih

/-- 折叠不变式：表内有置位下标（均 <32）⇒ 结果命中最左者 -/
theorem l2sc_lbCtz_go {x : BitVec 32} :
    ∀ (l : List Nat), (∀ m, m ∈ l → m < 32) →
      (∃ m, m ∈ l ∧ m < 32 ∧ x.getLsbD m = true) →
      (l.foldl (l2scCtzF x) 32) < 32 ∧
      x.getLsbD (l.foldl (l2scCtzF x) 32) = true := by
  intro l
  induction l with
  | nil =>
    intro _ h
    obtain ⟨m, hm, -, -⟩ := h
    simp at hm
  | cons a l ih =>
    intro hbnd h
    rw [List.foldl_cons, l2scCtzF_32]
    by_cases ha : x.getLsbD a = true
    · rw [if_pos ha, l2scCtzF_fold_stay x a (hbnd a List.mem_cons_self) l]
      exact ⟨hbnd a List.mem_cons_self, ha⟩
    · rw [if_neg ha]
      apply ih (fun m hm => hbnd m (List.mem_cons_of_mem a hm))
      obtain ⟨m, hm, hm32, hmx⟩ := h
      rcases List.mem_cons.mp hm with rfl | hml
      · exact absurd hmx ha
      · exact ⟨m, hml, hm32, hmx⟩

/-- lbCtz 命中：x 非零 ⇒ x 在 lbCtz x 处置位且 lbCtz x < 32（:107 OHToUInt） -/
theorem l2sc_lbCtz_getLsbD {x : BitVec 32} (hx : x ≠ 0#32) :
    lbCtz x < 32 ∧ x.getLsbD (lbCtz x) = true := by
  obtain ⟨m, hm32, hmx⟩ := l2sc_getLsbD_exists hx
  show ((List.range 32).foldl (l2scCtzF x) 32) < 32 ∧
    x.getLsbD ((List.range 32).foldl (l2scCtzF x) 32) = true
  exact l2sc_lbCtz_go (List.range 32) (fun m' h => List.mem_range.mp h)
    ⟨m, List.mem_range.mpr hm32, hm32, hmx⟩

/- 10. Mux1H 转移（:110） -/
/-- Mux1H 转移：one-hot 选择下，被选位处的谓词成立 -/
theorem l2scMux1H_transfer {oh : BitVec 32} {f : Nat → Bool} {i : Nat}
    (h1 : oh &&& (oh - 1#32) = 0#32)
    (hm : l2scMux1H oh f = true)
    (hi : oh.getLsbD i = true) (h32 : i < 32) : f i = true := by
  have hne : (oh &&& l2scOfPred f) ≠ 0#32 := by
    simpa [l2scMux1H] using hm
  obtain ⟨k, hk32, hkf⟩ := l2sc_getLsbD_exists hne
  rw [BitVec.getLsbD_and] at hkf
  simp at hkf
  have hki := l2sc_onehot_unique oh k i h1 hkf.1 hi
  subst hki
  rw [l2scOfPred_getLsbD f k h32] at hkf
  exact hkf.2

/- 11. 环境假设与四条核销 -/
/-- 环境假设（子模块/协议侧规约；L2 组合定理方法论：只用子模块 spec） -/
def l2scEnv (st : L2scState) (inp : L2scIn) : Prop :=
  -- E1：sinkD 响应只打活跃 entry、且为该 entry 的首个响应（TileLink 每 A 恰好
  --     一个 D 响应；A 的 source = 分配时的 mshr_select（:124），故 < 32）
  (inp.sinkdValid = true → inp.sinkdOpcode = l2scOpAccessAckData →
    ∃ j, j < 32 ∧ inp.sinkdSource = BitVec.ofNat 16 j ∧
         st.valids.getLsbD j = true ∧ (st.mshrs j).sinkDReg = false) ∧
  -- E3：allocate 命中 ⇒ push 被接受（Q2 的依赖：directory 单 result 在飞，
  --     读发起时已 gate mshr_free && push.ready（:225），此后 pool 只减不增）
  (∀ i, l2scAllocValid st inp i = true → inp.pushReady = true)

theorem l2sc_ofNat16_inj {i j : Nat} (hi32 : i < 32) (hj32 : j < 32)
    (heq : BitVec.ofNat 16 i = BitVec.ofNat 16 j) : i = j := by
  have ht := congrArg BitVec.toNat heq
  simp [BitVec.toNat_ofNat] at ht
  omega

/-- pop.valid 的分量（:235） -/
theorem l2scPopValid_parts {st : L2scState} {inp : L2scIn}
    (h : l2scPopValid st inp = true) :
    ((l2scSelectOH st inp &&& st.valids) ≠ 0#32) ∧
    l2scSchedDValid st inp = true ∧ inp.sourceDReqReady = true := by
  unfold l2scPopValid at h
  have h' := Bool.and_eq_true_iff.mp h
  have h'' := Bool.and_eq_true_iff.mp h'.1
  exact ⟨of_decide_eq_true h''.1, h''.2, h'.2⟩
/-- schedule.d.valid 的分量（MSHR.scala:89） -/
theorem l2scDV_parts {st : L2scState} {inp : L2scIn} {i : Nat}
    (h : l2scDV st inp i = true) :
    st.valids.getLsbD i = true ∧ (st.mshrs i).sinkDReg = true ∧
    (st.mshrs i).scheAValid = false := by
  unfold l2scDV at h
  have h' := Bool.and_eq_true_iff.mp h
  have h'' := Bool.and_eq_true_iff.mp h'.1
  refine ⟨h''.1, h''.2, ?_⟩
  cases hc : (st.mshrs i).scheAValid
  · rfl
  · rw [hc] at h'
    exact absurd h'.2 (by simp)
/-- sinkd.valid 的分量（:127） -/
theorem l2scSinkdV_parts {st : L2scState} {inp : L2scIn} {i : Nat}
    (h : l2scSinkdV st inp i = true) :
    inp.sinkdValid = true ∧ inp.sinkdSource = BitVec.ofNat 16 i ∧
    inp.sinkdOpcode = l2scOpAccessAckData := by
  unfold l2scSinkdV at h
  have h' := Bool.and_eq_true_iff.mp h
  have h'' := Bool.and_eq_true_iff.mp h'.1
  exact ⟨h''.1, beq_iff_eq.mp h''.2, beq_iff_eq.mp h'.2⟩
/-- merge.valid 的分量（:134） -/
theorem l2scMergeValid_parts {st : L2scState} {inp : L2scIn} {i : Nat}
    (h : l2scMergeValid st inp i = true) :
    l2scSchedDValid st inp = true ∧ l2scSelect st inp = i := by
  unfold l2scMergeValid at h
  have h' := Bool.and_eq_true_iff.mp h
  have h'' := Bool.and_eq_true_iff.mp h'.1
  exact ⟨h''.1, of_decide_eq_true h'.2⟩
/-- allocate.valid 的分量 -/
theorem l2scAllocValid_parts {st : L2scState} {inp : L2scIn} {i : Nat}
    (h : l2scAllocValid st inp i = true) :
    inp.dirResValid = true ∧ l2scAlloc st inp = true ∧
    (l2scInsertOH st).getLsbD i = true ∧
    inp.dirRes.hit = false ∧ inp.dirRes.flush = false := by
  simp [l2scAllocValid] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
/-- insertOH 选中的必是空闲位（:185-186） -/
theorem l2scInsertOH_free (st : L2scState) (i : Nat)
    (h : (l2scInsertOH st).getLsbD i = true) : st.valids.getLsbD i = false := by
  have h3 : (lbLowestOne (~~~st.valids) &&& ~~~st.valids).getLsbD i = true := by
    rw [(lbLowestOne_spec (~~~st.valids)).2.1]; exact h
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not] at h3
  simp [l2sc_getLsbD_lt32 h] at h3
  exact h3.2
/-- I-39 不变量：ListBuffer 空闲位 ⇒ 对应 MSHR 无待发 A（scheAValid=0） -/
def l2scInv1 (st : L2scState) : Prop :=
  ∀ i, st.valids.getLsbD i = false → (st.mshrs i).scheAValid = false
theorem l2sc_inv1_init : l2scInv1 l2scInit := by
  intro i _
  rfl
/-- I-39 核销（逐拍形式）：不变量下，被分配 entry 当拍不可能 a.fire。
    即 MSHR.scala:110-115 的 allocate×a.fire 优先级反转不可达。 -/
theorem l2sc_i39_no_alloc_afire (st : L2scState) (inp : L2scIn) (i : Nat)
    (hinv : l2scInv1 st)
    (h : l2scAllocValid st inp i = true) : l2scAFire st inp i = false := by
  have hfree : st.valids.getLsbD i = false :=
    l2scInsertOH_free st i (l2scAllocValid_parts h).2.2.1
  have hsa := hinv i hfree
  simp [l2scAFire, l2scAV, hsa]

/-- 不变量保持（E3 是关键环境假设，Q2） -/
theorem l2sc_inv1_preserved (st : L2scState) (inp : L2scIn)
    (hinv : l2scInv1 st) (henv : l2scEnv st inp) :
    l2scInv1 (l2scStep st inp) := by
  intro i hi
  have hdecomp : ((st.valids &&&
        ~~~(if l2scPopValid st inp then l2scSelectOH st inp else 0#32)) |||
      (if l2scPushValid st inp && inp.pushReady then l2scPushOH st inp else 0#32)).getLsbD i
      = false := hi
  rw [BitVec.getLsbD_or] at hdecomp
  have hB : (if l2scPushValid st inp && inp.pushReady then l2scPushOH st inp
      else 0#32).getLsbD i = false := by
    cases hb : (if l2scPushValid st inp && inp.pushReady then l2scPushOH st inp
        else 0#32).getLsbD i
    · rfl
    · rw [hb] at hdecomp; simp at hdecomp
  have hA : (st.valids &&&
      ~~~(if l2scPopValid st inp then l2scSelectOH st inp else 0#32)).getLsbD i = false := by
    cases ha : (st.valids &&&
        ~~~(if l2scPopValid st inp then l2scSelectOH st inp else 0#32)).getLsbD i
    · rfl
    · rw [ha] at hdecomp; simp at hdecomp
  show (if l2mAFire (st.mshrs i) (l2scMshrIn st inp i) then false
        else if l2scAllocValid st inp i then true
        else (st.mshrs i).scheAValid) = false
  -- 先建立 scheAValid i = false（pop 到 i 走 DV，否则 valids 位为 0 走 hinv）
  have hSA : (st.mshrs i).scheAValid = false := by
    by_cases hpop : (l2scPopValid st inp && (l2scSelectOH st inp).getLsbD i) = true
    · -- pop 到 i：DV i ⇒ scheAValid = false
      obtain ⟨hpopv, hsel⟩ := Bool.and_eq_true_iff.mp hpop
      have hsd : l2scSchedDValid st inp = true := (l2scPopValid_parts hpopv).2.1
      have hdv : l2scDV st inp i = true :=
        l2scMux1H_transfer (l2scSelectOH_spec st inp).1 hsd hsel
          (l2sc_getLsbD_lt32 hsel)
      exact (l2scDV_parts hdv).2.2
    · -- 非 pop 到 i：valids 位为 0 ⇒ hinv
      have hv : st.valids.getLsbD i = false := by
        by_cases hi32 : i < 32
        · rw [BitVec.getLsbD_and] at hA
          have hp2 : (if l2scPopValid st inp then l2scSelectOH st inp else 0#32).getLsbD i
              = false := by
            by_cases hpv : l2scPopValid st inp = true
            · rw [if_pos hpv]
              by_cases hs : (l2scSelectOH st inp).getLsbD i = true
              · exfalso
                apply hpop
                simp [hpv, hs]
              · simpa using hs
            · rw [if_neg hpv, BitVec.getLsbD_zero]
          have hp : (~~~(if l2scPopValid st inp then l2scSelectOH st inp else 0#32)).getLsbD i
              = true := by
            rw [BitVec.getLsbD_not, hp2]
            simp [hi32]
          rw [hp] at hA
          simpa using hA
        · exact l2sc_getLsbD_false_of_ge32 (by omega)
      exact hinv i hv
  -- fire 不可能（scheAValid=0）
  have hfire : l2mAFire (st.mshrs i) (l2scMshrIn st inp i) = false := by
    simp [l2mAFire, l2mOut, hSA]
  rw [if_neg (by simp [hfire])]
  -- allocate 不可能（pop 情形与 DV 矛盾；否则 E3 使 push 置位与 hB 矛盾）
  by_cases halloc : l2scAllocValid st inp i = true
  · exfalso
    obtain ⟨hdv, hal, hbit, hhit, hfl⟩ := l2scAllocValid_parts halloc
    by_cases hpop : (l2scPopValid st inp && (l2scSelectOH st inp).getLsbD i) = true
    · obtain ⟨hpopv, hsel⟩ := Bool.and_eq_true_iff.mp hpop
      have hsd : l2scSchedDValid st inp = true := (l2scPopValid_parts hpopv).2.1
      have hdvi : l2scDV st inp i = true :=
        l2scMux1H_transfer (l2scSelectOH_spec st inp).1 hsd hsel
          (l2sc_getLsbD_lt32 hsel)
      have hv1 := (l2scDV_parts hdvi).1
      rw [l2scInsertOH_free st i hbit] at hv1
      exact Bool.false_ne_true hv1
    · have hpr : inp.pushReady = true := henv.2 i halloc
      have hfire2 : (if l2scPushValid st inp && inp.pushReady then l2scPushOH st inp
          else 0#32).getLsbD i = true := by
        have hpv : l2scPushValid st inp = true := by
          simp [l2scPushValid, hdv, hhit, hfl]
        rw [if_pos (by simp [hpv, hpr])]
        show (l2scPushOH st inp).getLsbD i = true
        rw [l2scPushOH, if_pos hal]
        exact hbit
      rw [hfire2] at hB
      exact Bool.false_ne_true hB.symm
  · rw [if_neg (by simpa using halloc)]
    exact hSA

/-- 不变量的轨迹形式：从 init 出发、每拍满足环境假设 ⇒ 不变量恒成立 -/
theorem l2sc_inv1_run : ∀ (st : L2scState) (trace : List L2scIn),
    l2scInv1 st →
    (∀ pre inp post, trace = pre ++ inp :: post → l2scEnv (l2scRun st pre) inp) →
    l2scInv1 (l2scRun st trace) := by
  intro st trace
  induction trace generalizing st with
  | nil => intro h _; exact h
  | cons a l ih =>
    intro hinv henv
    have h0 : l2scEnv st a := henv [] a l rfl
    apply ih (l2scStep st a) (l2sc_inv1_preserved st a hinv h0)
    intro pre inp post hdecomp
    have h2 : a :: l = (a :: pre) ++ inp :: post := by
      rw [hdecomp, List.cons_append]
    exact henv (a :: pre) inp post h2
/-- sinkd 命中 + E1 ⇒ 目标 entry 活跃且 sinkDReg=0（I-41a/b 公共步） -/
theorem l2sc_sinkdV_env {st : L2scState} {inp : L2scIn} {i : Nat}
    (henv : l2scEnv st inp) (hi32 : i < 32)
    (hs : l2scSinkdV st inp i = true) :
    st.valids.getLsbD i = true ∧ (st.mshrs i).sinkDReg = false := by
  obtain ⟨hdv, hsrc, hop⟩ := l2scSinkdV_parts hs
  obtain ⟨j, hj32, hjsrc, hjval, hjsd⟩ := henv.1 hdv hop
  have heq : BitVec.ofNat 16 i = BitVec.ofNat 16 j := by rw [← hsrc, ← hjsrc]
  have hij : i = j := l2sc_ofNat16_inj hi32 hj32 heq
  subst hij
  exact ⟨hjval, hjsd⟩
/-- I-41a 核销：source 唯一性 ⇒ allocate×sinkd 不同拍（MSHR.scala:67-72
    与 :143-147 的 allocate×sinkd 竞争不可达） -/
theorem l2sc_i41a_no_alloc_sinkd (st : L2scState) (inp : L2scIn) (i : Nat)
    (henv : l2scEnv st inp)
    (h : l2scAllocValid st inp i = true) : l2scSinkdV st inp i = false := by
  by_cases hs : l2scSinkdV st inp i = true
  · exfalso
    have hbit := (l2scAllocValid_parts h).2.2.1
    have hv := (l2sc_sinkdV_env henv (l2sc_getLsbD_lt32 hbit) hs).1
    rw [l2scInsertOH_free st i hbit] at hv
    exact Bool.false_ne_true hv
  · simpa using hs

/-- I-41b 核销：merge 时序 ⇒ merge×sinkd 不同拍（merge 需 schedule.d.valid
    ⇒ sinkDReg=1（旧值）；sinkd 为首个响应 ⇒ sinkDReg=0） -/
theorem l2sc_i41b_no_merge_sinkd (st : L2scState) (inp : L2scIn) (i : Nat)
    (henv : l2scEnv st inp)
    (h : l2scMergeValid st inp i = true) : l2scSinkdV st inp i = false := by
  obtain ⟨hsd, hsel_i⟩ := l2scMergeValid_parts h
  -- schedDValid ⇒ selectOH ≠ 0 ⇒ l2scSelect = lbCtz selectOH
  have hsel_ne : l2scSelectOH st inp ≠ 0#32 := by
    intro hc
    unfold l2scSchedDValid at hsd
    rw [hc] at hsd
    simp [l2scMux1H] at hsd
  have hctz : l2scSelect st inp = lbCtz (l2scSelectOH st inp) := by
    show l2scOtu (l2scSelectOH st inp) = lbCtz (l2scSelectOH st inp)
    simp [l2scOtu, hsel_ne]
  have hhit := l2sc_lbCtz_getLsbD hsel_ne
  rw [← hctz, hsel_i] at hhit
  obtain ⟨hi32, hselbit⟩ := hhit
  have hdv : l2scDV st inp i = true :=
    l2scMux1H_transfer (l2scSelectOH_spec st inp).1 hsd hselbit hi32
  have hsdR := (l2scDV_parts hdv).2.1
  by_cases hs : l2scSinkdV st inp i = true
  · exfalso
    rw [(l2sc_sinkdV_env henv hi32 hs).2] at hsdR
    exact Bool.false_ne_true hsdR
  · simpa using hs
/-- Q4 核销：sinkd 通道结构性恒接收（无反压路径，sinkd.valid 直接写寄存器） -/
theorem l2sc_q4_sinkd_always_accepted (st : L2scState) (inp : L2scIn) (i : Nat)
    (h : l2scSinkdV st inp i = true) :
    ((l2scStep st inp).mshrs i).sinkDReg = true := by
  show (if (l2scMshrIn st inp i).sinkdValid then true
        else if (l2scMshrIn st inp i).allocValid then false
        else (st.mshrs i).sinkDReg) = true
  have h' : (l2scMshrIn st inp i).sinkdValid = true := h
  rw [if_pos h']

/- 12. 常规契约 -/
/-- 契约：分配互斥（同拍至多一个 entry 被分配） -/
theorem l2sc_alloc_exclusive (st : L2scState) (inp : L2scIn) (i j : Nat)
    (hi : l2scAllocValid st inp i = true) (hj : l2scAllocValid st inp j = true) :
    i = j := by
  have hon : (l2scInsertOH st) &&& (l2scInsertOH st - 1#32) = 0#32 :=
    (lbLowestOne_spec (~~~st.valids)).1
  exact l2sc_onehot_unique _ i j hon
    (l2scAllocValid_parts hi).2.2.1 (l2scAllocValid_parts hj).2.2.1
/-- 契约：entry 不漏（alloc 分支）——有空闲位时 miss 恰好分配一个 entry -/
theorem l2sc_alloc_exists_unique (st : L2scState) (inp : L2scIn)
    (hv : inp.dirResValid = true) (hhit : inp.dirRes.hit = false)
    (hfl : inp.dirRes.flush = false) (halloc : l2scAlloc st inp = true)
    (hfree : l2scMshrFree st = true) :
    ∃ i, i < 32 ∧ l2scAllocValid st inp i = true ∧
      ∀ j, l2scAllocValid st inp j = true → j = i := by
  have hne : l2scInsertOH st ≠ 0#32 := by
    intro hc
    have h3 := (lbLowestOne_spec (~~~st.valids)).2.2.1
    have hz : ~~~st.valids = 0#32 := h3.mp hc
    simp [l2scMshrFree, hz] at hfree
  obtain ⟨k, hk32, hkb⟩ := l2sc_getLsbD_exists hne
  have hk : l2scAllocValid st inp k = true := by
    simp [l2scAllocValid, hv, hhit, hfl, halloc, hkb]
  exact ⟨k, hk32, hk, fun j hj => l2sc_alloc_exclusive st inp j k hj hk⟩
/-- 契约：source 不被重复使用（sinkd 同拍至多命中一个 entry） -/
theorem l2sc_sinkd_unique (st : L2scState) (inp : L2scIn) (i j : Nat)
    (hi32 : i < 32) (hj32 : j < 32)
    (hi : l2scSinkdV st inp i = true) (hj : l2scSinkdV st inp j = true) :
    i = j := by
  obtain ⟨-, e1, -⟩ := l2scSinkdV_parts hi
  obtain ⟨-, e2, -⟩ := l2scSinkdV_parts hj
  exact l2sc_ofNat16_inj hi32 hj32 (by rw [← e1, ← e2])

/- 13. I-40 witness 与仲裁回归测试（native_decide） -/
/-- witness 拍 0：Get miss 的 directory result（set=5,way=3,tag=0xAB），分配 entry 0 -/
def l2scI40In0 : L2scIn :=
  { l2scInIdle with
    dirResValid := true,
    dirRes := { l2mStatusZero with opcode := l2mOpGet, set := 5#6, way := 3#4, tag := 0xAB#19 } }

/-- witness 拍 1：entry 0 的 refill 响应（AccessAckData, source=0），同拍其 A 发出 -/
def l2scI40In1 : L2scIn :=
  { l2scInIdle with
    sinkdValid := true, sinkdSource := 0#16, sinkdOpcode := l2scOpAccessAckData }

/-- witness 拍 2：SourceD 正读 (set=5,way=3)（输入；SourceD.lean 的 l2s 模型佐证
    s1_valid_r 期间 bs_radr.valid 可持续多拍） -/
def l2scI40In2 : L2scIn :=
  { l2scInIdle with radrValid := true, radrSet := 5#6, radrWay := 3#4 }
/-- witness 两拍后的状态 -/
def l2scI40St2 : L2scState := l2scRun l2scInit [l2scI40In0, l2scI40In1]
/-- 拍 0 环境合法：无 sinkd（E1 vacuous）、pushReady=1（E3） -/
theorem l2sc_i40_env0 : l2scEnv l2scInit l2scI40In0 :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩
/-- 拍 1 环境合法：sinkd 打 entry 0（E1：valids(0)=1 且 sinkDReg(0)=0，
    即首个响应）；in1 无 directory result（E3 vacuous） -/
theorem l2sc_i40_env1 : l2scEnv (l2scRun l2scInit [l2scI40In0]) l2scI40In1 :=
  ⟨fun _ _ => ⟨0, by decide, by native_decide, by native_decide, by native_decide⟩,
   fun _ hi => absurd (l2scAllocValid_parts hi).1 (by decide)⟩
/-- 拍 2 环境合法：无 sinkd、无 directory result（均 vacuous） -/
theorem l2sc_i40_env2 : l2scEnv l2scI40St2 l2scI40In2 :=
  ⟨fun hv _ => absurd hv (by decide),
   fun _ hi => absurd (l2scAllocValid_parts hi).1 (by decide)⟩

/-- I-40 核销（witness 可达）：entry 0 完成 refill 后 dir 写（sinkD_adr，
    set=5,way=3）与 sourceD 读口同地址同拍——Scheduler.scala:276-285 对
    radr 零防护（第三合取：同状态仅关 radrValid 即无冲突，说明冲突与否
    完全由 SourceD 侧输入决定）。 -/
theorem l2sc_i40_witness :
    l2scSinkDAdrValid l2scI40St2 l2scI40In2 = true ∧
    l2scSinkDAdrSet l2scI40St2 l2scI40In2 = 5#6 ∧
    l2scSinkDAdrWay l2scI40St2 l2scI40In2 = 3#4 ∧
    l2scBsCollision l2scI40St2 l2scI40In2 = true ∧
    l2scBsCollision l2scI40St2 { l2scI40In2 with radrValid := false } = false := by
  native_decide

/-- 仲裁回归 拍 1：分配 entry 1（Get set9/way2/tag0xCD）；sourceA 不 ready（A 缓发）。
    拍 0 复用 l2scI40In0（分配 entry 0） -/
def l2scRrIn1 : L2scIn :=
  { l2scInIdle with
    dirResValid := true, sourceAReqReady := false
    dirRes := { l2mStatusZero with
      opcode := l2mOpGet, set := 9#6, way := 2#4, tag := 0xCD#19 } }

/-- 仲裁回归：两 entry 竞争时低下标先授、robin_filter 推进、下一轮授另一 entry -/
theorem l2sc_t_roundrobin :
    l2scSelectOH (l2scRun l2scInit [l2scI40In0, l2scRrIn1]) l2scInIdle = 1#32 ∧
    (l2scRun l2scInit [l2scI40In0, l2scRrIn1, l2scInIdle]).robinFilter = 0xFFFFFFFE#32 ∧
    l2scSelectOH (l2scRun l2scInit [l2scI40In0, l2scRrIn1, l2scInIdle]) l2scInIdle = 2#32 := by
  native_decide

/-- allocate→sinkd→d 请求 流程回归（I-41 的正常时序基线） -/
theorem l2sc_t_alloc_sinkd_flow :
    (l2scRun l2scInit [l2scI40In0, l2scI40In1]).valids = 1#32 ∧
    ((l2scRun l2scInit [l2scI40In0, l2scI40In1]).mshrs 0).sinkDReg = true ∧
    ((l2scRun l2scInit [l2scI40In0, l2scI40In1]).mshrs 0).scheAValid = false ∧
    l2scDV (l2scRun l2scInit [l2scI40In0, l2scI40In1]) l2scInIdle 0 = true := by
  native_decide

/- 14. 公理审计（bv_decide/native_decide 信任公理归档：见文件头 D3 与
    AGENTS.md 公理审计惯例；native_decide 仅用于测试/witness） -/

#print axioms l2sc_i39_no_alloc_afire
#print axioms l2sc_inv1_preserved
#print axioms l2sc_inv1_run
#print axioms l2sc_i41a_no_alloc_sinkd
#print axioms l2sc_i41b_no_merge_sinkd
#print axioms l2sc_q4_sinkd_always_accepted
#print axioms l2sc_alloc_exclusive
#print axioms l2sc_alloc_exists_unique
#print axioms l2sc_sinkd_unique
#print axioms l2sc_i40_witness

end Ventus.L2.L2Scheduler


