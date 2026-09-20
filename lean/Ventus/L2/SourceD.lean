/- ========================================================================= -/
/-                        L2/SourceD.lean                                    -/
/-  Ventus L2Cache SourceD（D 通道数据源：BankedStore 读出/写入 + 响应生成）   -/
/-                                                                           -/
/-  Chisel 源码：opengpgpu/original/ventus-gpgpu/ventus/src/L2cache/         -/
/-    SourceD.scala（全文 281 行；下文 :NNN 均指该文件）                      -/
/-  辅助源码：SinkA.scala:19-30（PutBufferAEntry/PutBufferPop）、             -/
/-    BankedStore.scala（InnerAddress/InnerDecoded/InnerPoison）、            -/
/-    Parameters.scala:233-239（expandAddress）、Directory_test.scala（请求    -/
/-    类型 DirectoryResult_lite 与 flush 契约）                               -/
/-                                                                           -/
/- ======================== 例化核查（2026-08-29 grep） ====================== -/
/-  * SourceD：仅 Scheduler.scala 一处例化；req 来自 Directory result          -/
/-    （TLBundleD_lite_withid = DirectoryResult_lite + from_mem）。           -/
/-  * 参数同 L2/Directory.lean 头部：data_bits=1024、mask_bits=128、           -/
/-    writeBytes=1、beatBytes=128、addressBits=32、l2cBits=0。                -/
/-                                                                           -/
/- ======================== 建模决策 / 偏离点（D 区） ======================== -/
/-  D1. BankedStore 本体不建（属另一模块）；bs_rdat 建模为输入（读数据在建模     -/
/-      时序到达拍由环境供给），bs_radr/bs_wadr/bs_wdat 为输出。读数据到达       -/
/-      时序契约（BankedStore 固定延迟）作为环境假设记录，不在本文件建模。     -/
/-  D2. about_to_not_busy（:103-104）仅出现在被注释的 io.req.ready 中（:105）， -/
/-      为死代码，不建模。sourceA_sent（:114）同样只被注释引用，寄存器建模、     -/
/-      不参与输出。                                                          -/
/-  D3. s1_req_reg 初值的 opcode:=5.U（:71）忠实建模。                         -/
/-  D4. victim_tag 不在 DirectoryResult_lite 中（:78-81 of Directory_test），   -/
/-      SourceD 请求类型无 victim_tag 字段。                                   -/
/-  D5. expandAddress（:269）在 l2cBits=0 时为 Cat(tag,set,offset)=32 位。      -/
/-  D6. stage_5/stage_6（枚举值 4/5）在 switch 中无分支，状态保持；不可达。     -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区） ============================= -/
/-  Q1【I 类 bug，不可满足条件】 :142                                          -/
/-      `when(s1_req.opcode === PutFullData && s1_req.opcode === PutPartialData)` -/
/-      ——PutFullData=0、PutPartialData=1 互斥，&& 恒假，分支为死代码。按注释    -/
/-      （"wait write miss no allocate"）与上下文（:137 mshr_wait 用于阻塞对     -/
/-      victim way 的过早 miss 请求），此处应为 ||。后果：写 miss 不分配          -/
/-      （PutFull/PutPartial miss 且 !dirty，来自 MSHR）时 mshr_wait 不置位，    -/
/-      Scheduler.scala:133 把它广播给所有 MSHR——失去对该 victim way 新 miss     -/
/-      请求的阻塞保护，存在同 way 并发操作竞态窗口。机证：                      -/
/-      l2s_putput_and_false（恒假）/ l2sT_mshr_wait_put_miss（场景 witness：    -/
/-      实际语义 mshr_wait=false，修复后语义=true）。修复：&& 改 ||。            -/
/-  Q2【提示】 :109 sourceA_sent_reg 的置位条件是 (Put*) && io.a.ready 而非      -/
/-      io.a.fire——a.ready 高而 a.valid 低时也置位；但该信号只被注释代码引用，   -/
/-      无实际危害。                                                           -/
/-  Q3【提示】 :218 stage_4 对 Hint 一律要求 d.fire && a.fire（先入 stage_7/8    -/
/-      再等另一个）；非 last_flush 的 Hint 在 stage_4 中 d.valid 被 :264 屏蔽    -/
/-      → 若 Hint && !last_flush 到达 stage_4 将死锁。按 Directory 契约          -/
/-      （result.valid 仅对 dirty 或 last_flush 的 flush 项置位，Directory       -/
/-      :290）该组合不可达；记录为契约依赖。                                   -/
/-  Q4【提示】 stage_1 的两个 when 是顺序执行非 elsewhen（:135 vs :152-201），   -/
/-      对 !hit 且 s1_valid_r 的输入两块都会执行（后者覆盖 stateReg 等），建模    -/
/-      按"后者覆盖"忠实实现；对 !hit && !dirty && !Hint 的输入，第一 when 进     -/
/-      stage_4、第二链 otherwise 又把 busy/tobedone 置 true——组合语义下         -/
/-      stateReg=stage_4 且 tobedone=true，tobedone 在后续拍不再被消费           -/
/-      （stage_4 不看 tobedone），无害但有读者困惑风险。                       -/
/-  Q5【I 类 bug，stage_8 反压下响应被篡改/丢失】 :193-194 flush 末项（clean）    -/
/-      进 stage_8 且 busy:=false → :105 req.ready=!busy 立即为真；d 通道反压      -/
/-      （d.ready=0）期间新请求 fire 会把 s_final_req（:82 无使能 RegNext，每拍    -/
/-      更新）覆盖为新请求——挂起的 d 响应（HintAck）payload 在 valid && !ready   -/
/-      期间被改写，违反 decoupled 契约；flush 的 HintAck 永远丢失（丢响应），     -/
/-      新请求的响应被提前发出且之后还会再发一次（重响应）。触发条件：flush        -/
/-      末项 clean 的下一拍 SourceD 被反压且 Scheduler 立即递新请求（ready 已      -/
/-      拉高，正常 decoupled 行为即可触发）。机证：第 6 节                         -/
/-      l2sT_stage8_accepts_req / l2sT_stage8_payload_clobber。修复：stage_8 的    -/
/-      busy 保持 true（:194 去掉 busy:=false.B），或 s_final_req 加使能。        -/
/- ========================================================================= -/

import Ventus.L2.Directory
import Std.Tactic.BVDecide

namespace Ventus.L2

open Ventus.Base Ventus.Mem

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 类型与常量                                                              -/
/- ========================================================================= -/

/-- SourceD 请求：TLBundleD_lite_withid = DirectoryResult_lite + from_mem
    （SourceD.scala:37-40；DirectoryResult_lite 见 Directory_test.scala:66-76）。 -/
structure L2sReq where
  base : L2FullRequest
  hit : Bool
  way : BitVec 4
  dirtyB : Bool
  flush : Bool
  lastFlush : Bool
  fromMem : Bool
deriving DecidableEq, Repr

def l2sReqZero : L2sReq := ⟨l2reqZero, false, 0#4, false, false, false, false⟩

-- 状态机编码（:68，stage_1=0 … stage_8=7）
def l2sStage1 : BitVec 3 := 0#3
def l2sStage2 : BitVec 3 := 1#3
def l2sStage3 : BitVec 3 := 2#3
def l2sStage4 : BitVec 3 := 3#3
def l2sStage7 : BitVec 3 := 6#3
def l2sStage8 : BitVec 3 := 7#3

/-- SourceD 全部寄存器。 -/
structure L2sState where
  stateReg : BitVec 3              -- :69
  s1ReqReg : L2sReq                -- :73
  pbBeatDataReg : BitVec 1024      -- :66（PutBufferAEntry.data，SinkA.scala:21）
  pbBeatMaskReg : BitVec 128       -- :66（PutBufferAEntry.mask，SinkA.scala:22）
  busy : Bool                      -- :78
  readSentReg : Bool               -- :91
  sourceASentReg : Bool            -- :108（死代码，D2）
  writeSentReg : Bool              -- :117
  tobedone : Bool                  -- :127
  mshrWaitReg : Bool               -- :128
  sFinalReq : L2sReq               -- :82（RegNext(s1_req)）

def l2sInit : L2sState :=
  { stateReg := l2sStage1
    s1ReqReg := { l2sReqZero with base := { l2reqZero with opcode := l2opHint } }  -- :70-73
    pbBeatDataReg := 0#1024
    pbBeatMaskReg := 0#128
    busy := false
    readSentReg := false
    sourceASentReg := false
    writeSentReg := false
    tobedone := false
    mshrWaitReg := false
    sFinalReq := l2sReqZero }

/-- 输入：req + pb_beat + BankedStore/a/d 通道握手。 -/
structure L2sIn where
  reqValid : Bool
  req : L2sReq
  pbBeatData : BitVec 1024
  pbBeatMask : BitVec 128
  bsRadrReady : Bool
  bsRdat : BitVec 1024
  bsWadrReady : Bool
  aReady : Bool
  dReady : Bool
deriving DecidableEq, Repr

def l2sInIdle : L2sIn := ⟨false, l2sReqZero, 0, 0, true, 0, true, true, true⟩

/-- 输出。 -/
structure L2sOut where
  reqReady : Bool              -- :105
  pbPopValid : Bool            -- :63
  pbPopIndex : BitVec 5        -- :64
  bsRadrValid : Bool           -- :98
  bsRadrWay : BitVec 4         -- :99
  bsRadrSet : BitVec 6         -- :100
  bsRadrMask : BitVec 128      -- :101
  bsWadrValid : Bool           -- :257
  bsWadrSet : BitVec 6         -- :258
  bsWadrWay : BitVec 4         -- :259
  bsWadrMask : BitVec 128      -- :261
  bsWdatData : BitVec 1024     -- :260
  dValid : Bool                -- :264
  dSource : BitVec 16          -- :265
  dOpcode : BitVec 3           -- :266
  dSize : BitVec 7             -- :267
  dData : BitVec 1024          -- :268
  dParam : BitVec 3            -- :271
  dAddr : BitVec 32            -- :269
  aValid : Bool                -- :274
  aData : BitVec 1024          -- :277
  aOpcode : BitVec 3           -- :278
  mshrWait : Bool              -- :256
  finishIssue : Bool           -- :280

/-- 一拍内共享组合信号。 -/
structure L2sWires where
  reqReady : Bool
  reqFire : Bool
  s1Req : L2sReq          -- :81
  s1NeedW : Bool          -- :83
  s1NeedR : Bool          -- :85
  s1ValidR : Bool         -- :88
  readSent : Bool         -- :97
  bsRadrValid : Bool      -- :98
  s1WValid : Bool         -- :107
  writeSent : Bool        -- :123
  dValid : Bool           -- :264
  aValid : Bool           -- :274
  dFire : Bool
  aFire : Bool

def l2sWiresOf (st : L2sState) (inp : L2sIn) : L2sWires :=
  let reqReady := !st.busy                                                -- :105
  let reqFire := inp.reqValid && reqReady
  let s1Req := if reqFire then inp.req else st.s1ReqReg                   -- :81
  let op := s1Req.base.opcode
  let s1NeedW := (op == l2opPutFull || op == l2opPutPartial) &&
      !s1Req.fromMem && s1Req.hit                                         -- :83
  let s1NeedR := ((op == l2opGet) && s1Req.hit) ||
      ((!s1Req.hit || op == l2opHint) && s1Req.dirtyB)                    -- :85
  let s1ValidR := s1NeedR                                                 -- :88
  let readSent := if reqFire then false else st.readSentReg               -- :97
  let bsRadrValid := s1ValidR && !readSent                                -- :98
  let s1WValid := s1NeedW                                                 -- :107
  let writeSent := if reqFire then false else st.writeSentReg             -- :123
  let fop := st.sFinalReq.base.opcode
  let dValid := (st.stateReg == l2sStage4 || st.stateReg == l2sStage8) &&
      !(fop == l2opHint && !st.sFinalReq.lastFlush)                       -- :264
  let aValid := (st.stateReg == l2sStage4 || st.stateReg == l2sStage7 ||
      st.stateReg == l2sStage3) &&
      ((!st.sFinalReq.hit || fop == l2opHint) &&
       (st.sFinalReq.dirtyB || fop == l2opPutFull || fop == l2opPutPartial))  -- :274
  let dFire := dValid && inp.dReady
  let aFire := aValid && inp.aReady
  ⟨reqReady, reqFire, s1Req, s1NeedW, s1NeedR, s1ValidR, readSent, bsRadrValid,
   s1WValid, writeSent, dValid, aValid, dFire, aFire⟩

/-- FSM 次态（stateReg, busy, tobedone, mshrWaitReg），:129-255 忠实；
    stage_1 内两个 when 顺序执行、后者覆盖（Q4）。 -/
def l2sFsmNext (st : L2sState) (inp : L2sIn) (w : L2sWires) :
    BitVec 3 × Bool × Bool × Bool :=
  let hold := (st.stateReg, st.busy, st.tobedone, st.mshrWaitReg)
  if st.stateReg == l2sStage1 then                                       -- :130
    let reqGo := w.reqFire || st.tobedone                                -- :133
    let s1 := w.s1Req
    let op := s1.base.opcode
    -- 顶部：busy/mshr_wait 清 0（:131-132）
    let (st1, b1, t1, m1) := (st.stateReg, false, st.tobedone, false)
    -- 第一个 when（:135-146）
    let (st2, b2, t2, m2) :=
      if reqGo && !s1.hit then
        if s1.dirtyB then (st1, b1, t1, true)                            -- :137
        else
          let m' := if (op == l2opPutFull) && (op == l2opPutPartial) then true
                    else m1                                              -- :142（Q1，恒假）
          (l2sStage4, true, false, m')                                   -- :139-141
      else (st1, b1, t1, m1)
    -- 第二个 when 链（:152-201），覆盖前者
    if reqGo then
      if w.s1ValidR && inp.bsRadrReady then                              -- :152
        if (((!s1.hit && op != l2opHint) || (op == l2opHint && !s1.lastFlush)) &&
            s1.dirtyB) then
          (l2sStage3, true, false, m2)                                   -- :153-157
        else (l2sStage4, true, false, m2)                                -- :158-162
      else if (op == l2opPutFull || op == l2opPutPartial) && !s1.fromMem && s1.hit then  -- :163
        if inp.bsWadrReady then (l2sStage4, true, false, m2)             -- :164-168
        else (l2sStage2, true, false, m2)                                -- :169-172
      else if op == l2opHint && s1.lastFlush then                        -- :192
        (l2sStage8, false, false, false)                                 -- :193-196
      else (st2, true, true, m2)                                         -- :197-200
    else (st2, b2, t2, m2)
  else if st.stateReg == l2sStage2 then                                  -- :204
    if inp.bsWadrReady then (l2sStage4, st.busy, st.tobedone, st.mshrWaitReg) else hold
  else if st.stateReg == l2sStage3 then                                  -- :209
    if w.aFire then (l2sStage1, false, false, false) else hold           -- :210-215
  else if st.stateReg == l2sStage4 then                                  -- :217
    let fop := st.sFinalReq.base.opcode
    if (!st.sFinalReq.hit && (fop == l2opPutFull || fop == l2opPutPartial)) ||
        fop == l2opHint then                                             -- :218
      if w.dFire && w.aFire then (l2sStage1, false, false, false)        -- :219-223
      else if w.dFire then (l2sStage7, st.busy, st.tobedone, st.mshrWaitReg)  -- :224-225
      else if w.aFire then (l2sStage8, st.busy, st.tobedone, st.mshrWaitReg)  -- :226-227
      else hold
    else
      if w.dFire then (l2sStage1, false, false, false) else hold         -- :229-235
  else if st.stateReg == l2sStage7 then                                  -- :239
    if w.aFire then (l2sStage1, false, false, false) else hold
  else if st.stateReg == l2sStage8 then                                  -- :247
    if w.dFire then (l2sStage1, false, false, false) else hold
  else hold                                                              -- stage_5/6（D6）

def l2sOut (st : L2sState) (inp : L2sIn) : L2sOut :=
  let w := l2sWiresOf st inp
  let f := st.sFinalReq
  let fop := f.base.opcode
  let pbBeatData := if w.reqFire then inp.pbBeatData else st.pbBeatDataReg  -- :80
  let pbBeatMask := if w.reqFire then inp.pbBeatMask else st.pbBeatMaskReg
  { reqReady := w.reqReady
    pbPopValid := w.reqFire &&
        (inp.req.base.opcode == l2opPutFull || inp.req.base.opcode == l2opPutPartial)  -- :63
    pbPopIndex := inp.req.base.put                                        -- :64
    bsRadrValid := w.bsRadrValid
    bsRadrWay := w.s1Req.way                                              -- :99
    bsRadrSet := w.s1Req.base.set                                         -- :100
    bsRadrMask := w.s1Req.base.mask                                       -- :101
    bsWadrValid := w.s1WValid && !w.writeSent                             -- :257
    bsWadrSet := w.s1Req.base.set                                         -- :258
    bsWadrWay := w.s1Req.way                                              -- :259
    bsWadrMask := pbBeatMask                                              -- :261
    bsWdatData := pbBeatData                                              -- :260
    dValid := w.dValid
    dSource := f.base.source                                              -- :265
    dOpcode := if fop == l2opGet then l2opAccessAckData
               else if f.lastFlush then l2opHintAck else l2opAccessAck    -- :266
    dSize := f.base.size                                                  -- :267
    dData := if fop == l2opGet then (if f.hit then inp.bsRdat else f.base.data)
             else 0#1024                                                  -- :268
    dParam := 0#3                                                         -- :271
    dAddr := (f.base.tag.setWidth 32 <<< 13) ||| (f.base.set.setWidth 32 <<< 7) |||
             f.base.offset.setWidth 32                                    -- :269（D5）
    aValid := w.aValid
    aData := if fop == l2opPutFull || fop == l2opPutPartial then f.base.data
             else inp.bsRdat                                              -- :277
    aOpcode := l2opPutFull                                                -- :278
    mshrWait := st.mshrWaitReg                                            -- :256
    finishIssue := w.dValid && f.lastFlush }                              -- :280

/-- 单拍转移。 -/
def l2sStep (st : L2sState) (inp : L2sIn) : L2sState :=
  let w := l2sWiresOf st inp
  let (nstate, nbusy, ntbd, nmshr) := l2sFsmNext st inp w
  { stateReg := nstate
    s1ReqReg := if w.reqFire then inp.req else st.s1ReqReg                -- :74-77
    pbBeatDataReg := if w.reqFire then inp.pbBeatData else st.pbBeatDataReg  -- :76
    pbBeatMaskReg := if w.reqFire then inp.pbBeatMask else st.pbBeatMaskReg
    busy := nbusy
    readSentReg := if w.s1ValidR && inp.bsRadrReady then true else false  -- :92-96
    sourceASentReg := if (w.s1Req.base.opcode == l2opPutFull ||
        w.s1Req.base.opcode == l2opPutPartial) && inp.aReady then true else false  -- :109-113
    writeSentReg := if w.s1WValid && inp.bsWadrReady then true else false  -- :118-122
    tobedone := ntbd
    mshrWaitReg := nmshr
    sFinalReq := w.s1Req }                                                -- :82

/-- 多拍执行。 -/
def l2sRun (st : L2sState) (is : List L2sIn) : L2sState :=
  is.foldl l2sStep st

/-- 多拍输出轨迹。 -/
def l2sTrace (st : L2sState) : List L2sIn → List L2sOut
  | [] => []
  | i :: is => l2sOut st i :: l2sTrace (l2sStep st i) is

/- ========================================================================= -/
/- 3. Q1：不可满足条件（:142）                                                 -/
/- ========================================================================= -/

/-- :142 的 `PutFullData && PutPartialData` 对全部 3 位操作码恒假——死代码。 -/
theorem l2s_putput_and_false :
    ∀ op : BitVec 3, ((op == l2opPutFull) && (op == l2opPutPartial)) = false := by
  native_decide

/-- Q1 场景 witness：写 miss 不分配（PutFull + !hit + !dirty + from_mem）——
    实际语义 mshr_wait 不置位（应为 true，:142 的 && 系 || 之误）；
    状态机照常进 stage_4。 -/
theorem l2sT_mshr_wait_put_miss :
    let req : L2sReq := { l2sReqZero with
      base := { l2reqZero with opcode := l2opPutFull }, fromMem := true }
    let st := l2sStep l2sInit { l2sInIdle with reqValid := true, req := req }
    (st.mshrWaitReg = false) ∧                 -- 实际（bug）：不置位
    (st.stateReg = l2sStage4) ∧
    (((req.base.opcode == l2opPutFull) ||      -- 修复（||）后该条件为 true
      (req.base.opcode == l2opPutPartial)) = true) := by
  native_decide

/- ========================================================================= -/
/- 4. D 通道响应生成（:264-271）                                               -/
/- ========================================================================= -/

/-- stage_4 中以 f 为 s_final_req 的测试态。 -/
def l2sSt4 (f : L2sReq) : L2sState :=
  { l2sInit with stateReg := l2sStage4, busy := true, sFinalReq := f }

/-- Get+hit：AccessAckData，数据取自 BankedStore 读出（:266,:268）。 -/
theorem l2sT_d_get_hit :
    let f : L2sReq := { l2sReqZero with
      base := { l2reqZero with opcode := l2opGet }, hit := true }
    let o := l2sOut (l2sSt4 f) { l2sInIdle with bsRdat := 0xDEAD#1024 }
    (o.dValid = true) ∧ (o.dOpcode = l2opAccessAckData) ∧ (o.dData = 0xDEAD#1024) := by
  native_decide

/-- Get+miss：数据透传请求自带 data（mshr 供数，:268）。 -/
theorem l2sT_d_get_miss :
    let f : L2sReq := { l2sReqZero with
      base := { l2reqZero with opcode := l2opGet, data := 0xCAFE#1024 } }
    let o := l2sOut (l2sSt4 f) l2sInIdle
    (o.dValid = true) ∧ (o.dOpcode = l2opAccessAckData) ∧ (o.dData = 0xCAFE#1024) := by
  native_decide

/-- 写响应：AccessAck、data=0（:266,:268）。 -/
theorem l2sT_d_write_ack :
    let f : L2sReq := { l2sReqZero with
      base := { l2reqZero with opcode := l2opPutFull } }
    let o := l2sOut (l2sSt4 f) l2sInIdle
    (o.dValid = true) ∧ (o.dOpcode = l2opAccessAck) ∧ (o.dData = 0#1024) := by
  native_decide

/-- last_flush：HintAck（:266）。 -/
theorem l2sT_d_hintack :
    let f : L2sReq := { l2sReqZero with
      base := { l2reqZero with opcode := l2opHint }, lastFlush := true }
    let o := l2sOut (l2sSt4 f) l2sInIdle
    (o.dValid = true) ∧ (o.dOpcode = l2opHintAck) ∧ (o.finishIssue = true) := by
  native_decide

/-- 地址重建：expandAddress = Cat(tag,set,offset)（:269，l2cBits=0）。 -/
theorem l2sT_d_addr :
    let f : L2sReq := { l2sReqZero with base := { l2reqZero with opcode := l2opGet, tag := 0x12345#19, set := 0x21#6, offset := 0x33#7 } }
    (l2sOut (l2sSt4 f) l2sInIdle).dAddr = 0x2468B0B3#32 := by
  native_decide

/- ========================================================================= -/
/- 5. 场景轨迹：响应不丢不重（正常路径）                                       -/
/- ========================================================================= -/

def l2sReqOf (op : BitVec 3) (hit dirtyB lastFlush fromMem : Bool) : L2sReq :=
  { l2sReqZero with base := { l2reqZero with opcode := op }, hit := hit, dirtyB := dirtyB, lastFlush := lastFlush, fromMem := fromMem }

def l2sInReq (r : L2sReq) : L2sIn := { l2sInIdle with reqValid := true, req := r }

/-- 读命中：bs_radr 首拍即发，恰一次 d 响应（AccessAckData + BankedStore 数据），
    之后回 stage_1、reqReady 恢复。 -/
theorem l2sT_trace_read_hit :
    let req := l2sReqOf l2opGet true false false false
    let tr : List L2sIn := [l2sInReq req, { l2sInIdle with bsRdat := 0xBEEF#1024 },
                            l2sInIdle, l2sInIdle]
    let outs := l2sTrace l2sInit tr
    let fin := l2sRun l2sInit tr
    (outs.getD 0 (l2sOut l2sInit l2sInIdle)).bsRadrValid = true ∧
    (outs.filter (·.dValid)).length = 1 ∧
    (outs.getD 1 (l2sOut l2sInit l2sInIdle)).dOpcode = l2opAccessAckData ∧
    (outs.getD 1 (l2sOut l2sInit l2sInIdle)).dData = 0xBEEF#1024 ∧
    fin.stateReg = l2sStage1 ∧ fin.busy = false := by
  native_decide

/-- 写命中：pb_pop 首拍弹出、BankedStore 写口地址/掩码/数据保真
    （:63-64,:257-261），恰一次 AccessAck。 -/
theorem l2sT_trace_write_hit :
    let req : L2sReq := { l2sReqOf l2opPutFull true false false false with way := 5#4, base := { l2reqZero with opcode := l2opPutFull, set := 6#6, put := 9#5 } }
    let in0 : L2sIn := { l2sInReq req with pbBeatData := 0xBEEF#1024, pbBeatMask := BitVec.allOnes 128 }
    let outs := l2sTrace l2sInit [in0, l2sInIdle, l2sInIdle]
    let o0 := outs.getD 0 (l2sOut l2sInit l2sInIdle)
    let o1 := outs.getD 1 (l2sOut l2sInit l2sInIdle)
    (o0.pbPopValid = true) ∧ (o0.pbPopIndex = 9#5) ∧
    (o0.bsWadrValid = true) ∧ (o0.bsWadrWay = 5#4) ∧ (o0.bsWadrSet = 6#6) ∧
    (o0.bsWdatData = 0xBEEF#1024) ∧ (o0.bsWadrMask = BitVec.allOnes 128) ∧
    (outs.filter (·.dValid)).length = 1 ∧
    (o1.dOpcode = l2opAccessAck) ∧ (o1.dData = 0#1024) := by
  native_decide

/-- 读 miss clean（mshr 供数）：恰一次 d，数据透传 req.data，mshr_wait 不置位。 -/
theorem l2sT_trace_miss_clean :
    let req : L2sReq := { l2sReqOf l2opGet false false false true with
      base := { l2reqZero with opcode := l2opGet, data := 0xCAFE#1024 } }
    let outs := l2sTrace l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]
    (outs.filter (·.dValid)).length = 1 ∧
    (outs.getD 1 (l2sOut l2sInit l2sInIdle)).dData = 0xCAFE#1024 ∧
    (outs.filter (·.mshrWait)).length = 0 ∧
    (l2sRun l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]).stateReg = l2sStage1 := by
  native_decide

/-- 读 miss dirty：先读 BankedStore（bs_radr），mshr_wait 置位一拍，
    stage_3 经 a 通道写回 victim（PutFullData + BankedStore 数据），无 d 响应。 -/
theorem l2sT_trace_miss_dirty :
    let req := l2sReqOf l2opGet false true false false
    let tr : List L2sIn := [l2sInReq req, { l2sInIdle with bsRdat := 0xBEEF#1024 },
                            l2sInIdle]
    let outs := l2sTrace l2sInit tr
    let o0 := outs.getD 0 (l2sOut l2sInit l2sInIdle)
    let o1 := outs.getD 1 (l2sOut l2sInit l2sInIdle)
    (o0.bsRadrValid = true) ∧
    (o1.mshrWait = true) ∧
    (o1.aValid = true) ∧ (o1.aOpcode = l2opPutFull) ∧ (o1.aData = 0xBEEF#1024) ∧
    (outs.filter (·.dValid)).length = 0 ∧
    (l2sRun l2sInit tr).stateReg = l2sStage1 := by
  native_decide

/-- 写 miss 不分配：stage_4 同拍 d+a（:218-223），a 通道透传写数据（:277），
    d=AccessAck；Q1：mshr_wait 全程不置位。 -/
theorem l2sT_trace_write_miss_noalloc :
    let req : L2sReq := { l2sReqOf l2opPutFull false false false true with
      base := { l2reqZero with opcode := l2opPutFull, data := 0x1234#1024 } }
    let outs := l2sTrace l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]
    let o1 := outs.getD 1 (l2sOut l2sInit l2sInIdle)
    (outs.filter (·.dValid)).length = 1 ∧ (outs.filter (·.aValid)).length = 1 ∧
    (o1.dOpcode = l2opAccessAck) ∧ (o1.aData = 0x1234#1024) ∧
    (outs.filter (·.mshrWait)).length = 0 ∧
    (l2sRun l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]).stateReg = l2sStage1 := by
  native_decide

/-- flush 末项（dirty）：stage_4 同拍 d+a，HintAck + finish_issue。 -/
theorem l2sT_trace_flush_last_dirty :
    let req := l2sReqOf l2opHint false true true false
    let outs := l2sTrace l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]
    let o1 := outs.getD 1 (l2sOut l2sInit l2sInIdle)
    (outs.filter (·.dValid)).length = 1 ∧ (outs.filter (·.aValid)).length = 1 ∧
    (o1.dOpcode = l2opHintAck) ∧ (o1.finishIssue = true) ∧
    (l2sRun l2sInit [l2sInReq req, l2sInIdle, l2sInIdle]).stateReg = l2sStage1 := by
  native_decide

/- ========================================================================= -/
/- 6. Q-新【I 类 bug】：stage_8 反压下响应被篡改/丢失                          -/
/-    :193-194 flush 末项（clean）进 stage_8 且 busy:=false → :105             -/
/-    req.ready=!busy 立即为真；若 d 通道反压（d.ready=0）期间新请求 fire，     -/
/-    s_final_req（:82 RegNext，每拍更新）被新请求覆盖——挂起的 d 响应           -/
/-    （HintAck）payload 在 valid && !ready 期间被改写，违反 decoupled 契约；   -/
/-    原 flush 请求的 HintAck 永远丢失（响应"丢"），新请求响应可能被             -/
/-    提前/重复发出（响应"重"）。                                              -/
/- ========================================================================= -/

/-- stage_8 期间 reqReady 为真、新请求被捕获（:194 busy:=false 的直接后果）。 -/
theorem l2sT_stage8_accepts_req :
    let flushReq : L2sReq := { l2sReqOf l2opHint false false true false with base := { l2reqZero with opcode := l2opHint, source := 0xF1#16 } }
    let getReq : L2sReq := { l2sReqOf l2opGet true false false false with base := { l2reqZero with opcode := l2opGet, source := 0xA5#16 } }
    let in0 := l2sInReq flushReq
    let in1 : L2sIn := { l2sInReq getReq with dReady := false }
    let o1 := (l2sTrace l2sInit [in0, in1]).getD 1 (l2sOut l2sInit l2sInIdle)
    (o1.reqReady = true) ∧
    ((l2sRun l2sInit [in0, in1]).s1ReqReg.base.source = 0xA5#16) := by
  native_decide

/-- decoupled 契约违反：valid && !ready 期间 d payload 从 HintAck(0xF1)
    变成 AccessAckData(0xA5)；HintAck 全程未 fire → 响应丢失。 -/
theorem l2sT_stage8_payload_clobber :
    let flushReq : L2sReq := { l2sReqOf l2opHint false false true false with base := { l2reqZero with opcode := l2opHint, source := 0xF1#16 } }
    let getReq : L2sReq := { l2sReqOf l2opGet true false false false with base := { l2reqZero with opcode := l2opGet, source := 0xA5#16 } }
    let in0 := l2sInReq flushReq
    let in1 : L2sIn := { l2sInReq getReq with dReady := false }
    let in2 : L2sIn := { l2sInIdle with dReady := true }
    let outs := l2sTrace l2sInit [in0, in1, in2]
    let o1 := outs.getD 1 (l2sOut l2sInit l2sInIdle)
    let o2 := outs.getD 2 (l2sOut l2sInit l2sInIdle)
    -- 第 1 拍：d.valid 高、payload=HintAck/0xF1，但 d.ready=0（未 fire）
    (o1.dValid = true) ∧ (o1.dOpcode = l2opHintAck) ∧ (o1.dSource = 0xF1#16) ∧
    -- 第 2 拍：payload 被新请求覆盖（违反 valid&& !ready 保持契约）
    (o2.dValid = true) ∧ (o2.dOpcode = l2opAccessAckData) ∧ (o2.dSource = 0xA5#16) := by
  native_decide

/- ========================================================================= -/
/- 7. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms l2s_putput_and_false
#print axioms l2sT_mshr_wait_put_miss
#print axioms l2sT_d_get_hit
#print axioms l2sT_d_addr
#print axioms l2sT_trace_read_hit
#print axioms l2sT_trace_write_hit
#print axioms l2sT_trace_miss_dirty
#print axioms l2sT_trace_write_miss_noalloc
#print axioms l2sT_stage8_accepts_req
#print axioms l2sT_stage8_payload_clobber

end Ventus.L2

