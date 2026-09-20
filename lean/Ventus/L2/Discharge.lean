/- ========================================================================= -/
/-                        L2/Discharge.lean                                  -/
/-  L2Cache 联合时序核销：I-43 / E1 / E3 / I-42（doc/03-bug发现报告.md）       -/
/-                                                                           -/
/-  方法（L2 组合定理 + 抽象事件对接，简报核准）：                             -/
/-   * 不联合例化全部状态机；Scheduler（l2sc*）侧用"手构输入轨迹重放"，        -/
/-     输入侧信号的可产生性由 Directory（l2d*）/SourceD（l2s*）/ListBuffer     -/
/-     （lb*）各自的具体轨迹定理独立机证，组合一致性按信号语义逐条对齐（注释）。 -/
/-   * E1 落实为"E1b（外层 TL 纪律，黑盒残余前提）+ 联合不变量 ⇒ E1"的         -/
/-     符号定理（在飞 A 影子 aOut 的逐拍归纳）。                               -/
/-                                                                           -/
/- ===================== Q 区（疑点 / 障碍 / 新踩坑） ======================= -/
/-  Q1. E3（"allocate 命中 ⇒ push 被接受"）在本波被**反例证伪**：读发起门控    -/
/-      （Scheduler.scala:225,:239）比结果拍早一拍看 push.ready，同拍一个       -/
/-      secondary push（:223 Mux(alloc,...) 的 tagMatches 支）可耗尽 entry     -/
/-      池 ⇒ 结果拍 push.ready=0 而 allocate 电平敏感照发（Q2 预言的路径）。   -/
/-      机证：l2dc_e3_counterexample / l2dc_e3_falsified / l2dc_e3_inv1_broken。 -/
/-      连锁影响：I-39/I-41 的"机证不可达"依赖 l2sc_inv1_preserved ← E3，      -/
/-      该角落下不变量可破（重复 allocate ⇒ 重复 A，E1b 亦可被击破）。          -/
/-  Q2【新踩坑】① `swap` 不在核心库（by_cases 分支序用 `32 ≤ j` 反转）。       -/
/-      ② `cases hx : e` 会把 goal 中 e 的实例替换为构造子字面量——false 分支   -/
/-      目标变 `false = false`，收尾用 rfl；误用 exact hx 反而 type mismatch。   -/
/-      ③ simpa 收尾的 assumption 不穿 `(l2scMshrIn ..).field` 投影的 defeq      -/
/-      （show 却能过）——桥接引理 hMinS/hMinA（rfl）先 rw 成裸函数形式再       -/
/-      if_neg (by simp [h])。④ simp 实参传 getLsbD 引理失配（目标已被 simp      -/
/-      预规范化为 v[j] 形式）——改 rw 链手动分解。⑤ 36 拍 runTrace +           -/
/-      native_decide 实测 >600s 超时（求值爆炸前科复现）；改"手构状态 + ≤3     -/
/-      拍步进"后单文件（含 3 个多拍 witness 定理族）构建 ~340s，仍偏慢——      -/
/-      后续波次引用本文件时注意构建预算。                                      -/
/- ========================================================================= -/

import Ventus.L2.Scheduler
import Ventus.L2.Directory
import Ventus.L2.SourceD
import Std.Tactic.BVDecide

namespace Ventus.L2.L2Discharge

open Ventus.L2 Ventus.L2.L2MSHR Ventus.L2.L2Scheduler

/- ========================================================================= -/
/- 1. I-42【witness 机证】mixed 缺 tagMatches.orR 守卫 ⇒ 静默缓存插入失败      -/
/-    Scheduler.scala:214：OHToUInt(tagMatches=0)=0 ⇒ 无匹配 miss 的 result    -/
/-    给 entry 0 误打 mixed ⇒ scheDirValid 永不置位（MSHR.scala:123）⇒        -/
/-    refill 不写 directory / bankedStore（Scheduler.scala:227,:276）。        -/
/- ========================================================================= -/

/-- 拍 0：Get miss 的 directory result（tag 0xAB, set 5, way 3）→ 分配 entry 0。
    各 ready 关闭（A 缓发、无 dir 写、无 d 响应），仅 pushReady=1 -/
def l2dcI42In0 : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with opcode := l2mOpGet, set := 5#6, way := 3#4, tag := 0xAB#19 } }

/-- 拍 1（buggy）：Put miss result（tag 0xCD，与 entry 0 无匹配）——
    OHToUInt(tagMatches=0)=0 且 Put≠Get ⇒ 误打 entry 0 的 mixed -/
def l2dcI42In1Put : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with opcode := l2mOpPutFullData, set := 7#6, way := 1#4, tag := 0xCD#19 } }

/-- 拍 1（对照）：同轨迹仅 result opcode 换 Get（Get≮Get ⇒ 不打 mixed） -/
def l2dcI42In1Get : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with opcode := l2mOpGet, set := 7#6, way := 1#4, tag := 0xCD#19 } }

/-- 拍 2：entry 0 的 refill 响应（AccessAckData, source=0） -/
def l2dcI42In2Sd : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    sinkdValid := true, sinkdSource := 0#16, sinkdOpcode := l2scOpAccessAckData }

/-- 观测拍：dir 写口就绪，观察 schedule.dir.valid 是否发起 -/
def l2dcI42Obs : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := true }

/-- buggy 轨迹三拍后状态 -/
def l2dcI42BugSt3 : L2scState := l2scRun l2scInit [l2dcI42In0, l2dcI42In1Put, l2dcI42In2Sd]
/-- 对照轨迹三拍后状态 -/
def l2dcI42OkSt3 : L2scState := l2scRun l2scInit [l2dcI42In0, l2dcI42In1Get, l2dcI42In2Sd]

/-- I-42 witness：误打 mixed ⇒ entry 0 refill 后 dir 写永不发起；对照组正常。
    后果（Scheduler.scala:227,:276）：directory 与 bankedStore 均不更新 ⇒
    该块后续访问反复 miss（静默插入失败；数据正确性不受损，见报告 I-42）。 -/
theorem l2dc_i42_witness :
    -- 机制第一步：Put result 当拍即给 entry 0 误打 mixed（OHToUInt(0)=0）
    l2scMixedI (l2scRun l2scInit [l2dcI42In0]) l2dcI42In1Put 0 = true ∧
    -- 对照组同拍不打（Get≮Get）
    l2scMixedI (l2scRun l2scInit [l2dcI42In0]) l2dcI42In1Get 0 = false ∧
    -- buggy 终态：refill 数据已收（sinkDReg=1）、mixedReg=1、dir 写资格=0
    (l2dcI42BugSt3.mshrs 0).sinkDReg = true ∧
    (l2dcI42BugSt3.mshrs 0).mixedReg = true ∧
    (l2dcI42BugSt3.mshrs 0).scheDirValid = false ∧
    l2scDirV l2dcI42BugSt3 l2dcI42Obs 0 = false ∧
    l2scSchedDirValid l2dcI42BugSt3 l2dcI42Obs = false ∧
    l2scSinkDAdrValid l2dcI42BugSt3 l2dcI42Obs = false ∧
    -- 对照终态：dir 写正常发起（目录写 + bankedStore 地址，set=5,way=3）
    (l2dcI42OkSt3.mshrs 0).sinkDReg = true ∧
    (l2dcI42OkSt3.mshrs 0).scheDirValid = true ∧
    l2scSchedDirValid l2dcI42OkSt3 l2dcI42Obs = true ∧
    l2scSinkDAdrValid l2dcI42OkSt3 l2dcI42Obs = true ∧
    l2scSinkDAdrSet l2dcI42OkSt3 l2dcI42Obs = 5#6 ∧
    l2scSinkDAdrWay l2dcI42OkSt3 l2dcI42Obs = 3#4 := by
  native_decide

/-- 环境合法性 拍 0：无 sinkd（E1 vacuous）、pushReady=1（E3） -/
theorem l2dc_i42_env0 : l2scEnv l2scInit l2dcI42In0 :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩
/-- 拍 1（buggy）：无 sinkd；pushReady=1 -/
theorem l2dc_i42_env1_put :
    l2scEnv (l2scRun l2scInit [l2dcI42In0]) l2dcI42In1Put :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩
/-- 拍 1（对照）：同上 -/
theorem l2dc_i42_env1_get :
    l2scEnv (l2scRun l2scInit [l2dcI42In0]) l2dcI42In1Get :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩
/-- 拍 2（buggy 轨迹）：sinkd 打 entry 0（valids(0)=1 且 sinkDReg(0)=0，首个响应） -/
theorem l2dc_i42_env2_bug :
    l2scEnv (l2scRun l2scInit [l2dcI42In0, l2dcI42In1Put]) l2dcI42In2Sd :=
  ⟨fun _ _ => ⟨0, by decide, by native_decide, by native_decide, by native_decide⟩,
   fun _ _ => rfl⟩
/-- 拍 2（对照轨迹）：同上 -/
theorem l2dc_i42_env2_ok :
    l2scEnv (l2scRun l2scInit [l2dcI42In0, l2dcI42In1Get]) l2dcI42In2Sd :=
  ⟨fun _ _ => ⟨0, by decide, by native_decide, by native_decide, by native_decide⟩,
   fun _ _ => rfl⟩

/- ========================================================================= -/
/- 2. I-43【witness 机证】miss-dirty 的 result.ready 缺 drb.enq.ready ⇒        -/
/-    脏 victim 写回丢失（Scheduler.scala:246-252）。三腿对接：               -/
/-    腿 C（Scheduler）：drb 满 × miss-dirty result 同拍 ⇒ result 被消费       -/
/-      （allocate+push 照发）而 enq 丢弃——本文件具体轨迹机证；                -/
/-    腿 A（Directory）：连续两拍 miss-dirty result 可产生（l2dc_i43_dir_*）； -/
/-    腿 B（SourceD）：busy 窗口 ≥2 拍使 drb deq 被挡（l2dc_i43_sourced_busy）。 -/
/-    信号对齐：sourceDReqReady ↔ (l2sOut).reqReady；dirRes* ↔ l2dOut.result*；-/
/-    miss 的 result.ready=push.ready（:252）=1 与腿 A 的 resultReady=1 一致； -/
/-    腿 C 拍 0/1 的 sourceDReqReady=0 由腿 B 的 busy 窗口（接受前一笔后        -/
/-    第 1、2 拍）覆盖。                                                       -/
/- ========================================================================= -/

/-- 腿 C 拍 0：miss-dirty result1（Get, tag 0x111, set 9, way 2），drb 空 ⇒
    正常 enq；sourceD 忙（reqReady=0）⇒ deq 被挡，drb 持满 -/
def l2dcI43In0 : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with
                    opcode := l2mOpGet, set := 9#6, way := 2#4, tag := 0x111#19, dirty := true } }

/-- 腿 C 拍 1：miss-dirty result2（Get, tag 0x222, set 10, way 5），drb 满 -/
def l2dcI43In1 : L2scIn :=
  { l2scInIdle with
    sourceAReqReady := false, sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with
                    opcode := l2mOpGet, set := 10#6, way := 5#4, tag := 0x222#19, dirty := true } }

/-- 腿 C 两拍后状态 -/
def l2dcI43St1 : L2scState := l2scRun l2scInit [l2dcI43In0]
def l2dcI43St2 : L2scState := l2scRun l2scInit [l2dcI43In0, l2dcI43In1]

/-- I-43 witness（腿 C）：drb 满时 miss-dirty result 被消费但 enq 丢弃。
    后果：SourceD 只会从 drb 取出 result1 的 victim（set9/way2）写回；
    result2 的 victim（set10/way5）的写回信息从未入队——entry 1 refill 覆盖
    way 5 后内存持陈旧数据（正确性级，见报告 I-43）。 -/
theorem l2dc_i43_witness :
    -- 拍 0：result1 正常 enq（drb 空 → 满）
    l2dcI43St1.drbValid = true ∧
    l2dcI43St1.drbBits.tag = 0x111#19 ∧
    -- 拍 1：result2 的 enq 使能条件为假（drb 满），但 push 照发（消费）
    (l2dcI43In1.dirResValid &&
      (l2dcI43In1.dirRes.hit || l2dcI43In1.dirRes.dirty || l2dcI43In1.dirRes.lastFlush) &&
      !l2dcI43St1.drbValid) = false ∧
    l2scPushValid l2dcI43St1 l2dcI43In1 = true ∧
    -- 消费证据：entry 1 被分配（result2 元数据入 MSHR）、valids 置位
    l2dcI43St2.valids = 3#32 ∧
    (l2dcI43St2.mshrs 1).request.tag = 0x222#19 ∧
    (l2dcI43St2.mshrs 1).request.set = 10#6 ∧
    (l2dcI43St2.mshrs 1).request.way = 5#4 ∧
    (l2dcI43St2.mshrs 1).scheAValid = true ∧
    -- 丢弃证据：drb 仍持 result1 的 victim，result2 的（set10/way5）从未入队
    l2dcI43St2.drbValid = true ∧
    l2dcI43St2.drbBits.tag = 0x111#19 ∧
    l2dcI43St2.drbBits.set = 9#6 ∧
    l2dcI43St2.drbBits.way = 2#4 := by
  native_decide

/-- 腿 C 环境合法性 拍 0：无 sinkd（E1 vacuous）、pushReady=1（E3） -/
theorem l2dc_i43_env0 : l2scEnv l2scInit l2dcI43In0 :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩
/-- 拍 1：同上 -/
theorem l2dc_i43_env1 : l2scEnv l2dcI43St1 l2dcI43In1 :=
  ⟨fun hv _ => absurd hv (by decide), fun _ _ => rfl⟩

/-- 腿 A 的预状态：wipe 完成（wipeCount  bit6=1）、全行 dirty、全行 invalid
    （invalid ⇒ 任何读必 miss；dirty ⇒ victim 写回必要）。手构状态（SM 惯例：
    聚焦 result 流时序；该配置可由"写+Put hit"序列建立，不影响结论）。 -/
def l2dcDirSt0 : L2dState :=
  { l2dInit with
      wipeCount := 64#7, statusD := Array.replicate 64 (Array.replicate 16 true) }

/-- 腿 A 拍 0：Get 读（tag 0x111, set 9），resultReady=1（= miss 时的 push.ready） -/
def l2dcDirInA : L2dIn :=
  { l2dInIdle with
      readValid := true, readBits := l2dReqOf l2opGet 0x111#19 9#6, resultReady := true }
/-- 腿 A 拍 1：Get 读（tag 0x222, set 10）——与拍 1 的 result1 同拍被接受 -/
def l2dcDirInB : L2dIn :=
  { l2dInIdle with
      readValid := true, readBits := l2dReqOf l2opGet 0x222#19 10#6, resultReady := true }

/-- 探测：逐合取定位（Q 区惯例：探测用小定理） -/
theorem l2dc_probe_o1 :
    let outs := l2dTrace l2dcDirSt0 [l2dcDirInA, l2dcDirInB, l2dInIdle]
    let o1 := outs.getD 1 (l2dOut l2dcDirSt0 l2dcDirInA)
    o1.resultValid = true ∧ o1.resultHit = false ∧ o1.resultDirty = true ∧
    o1.resultSet = 9#6 ∧ o1.resultOpcode = l2opGet := by
  native_decide

theorem l2dc_probe_o2 :
    let outs := l2dTrace l2dcDirSt0 [l2dcDirInA, l2dcDirInB, l2dInIdle]
    let o2 := outs.getD 2 (l2dOut l2dcDirSt0 l2dcDirInA)
    o2.resultValid = true ∧ o2.resultHit = false ∧ o2.resultDirty = true ∧
    o2.resultSet = 10#6 ∧ o2.resultOpcode = l2opGet := by
  native_decide

theorem l2dc_probe_fire :
    (l2dWiresOf (l2dStep l2dcDirSt0 l2dcDirInA) l2dcDirInB).readFire = true := by
  native_decide

/-- 腿 A：Directory 连续两拍产出 miss-dirty result（hit=0 且 dirty=1），
    且第二个读在第一个 result 消费拍即被接受（流水线紧密衔接，对应腿 C 的
    拍 0/拍 1 两个 result）。 -/
theorem l2dc_i43_dir_results :
    let outs := l2dTrace l2dcDirSt0 [l2dcDirInA, l2dcDirInB, l2dInIdle]
    let o1 := outs.getD 1 (l2dOut l2dcDirSt0 l2dcDirInA)
    let o2 := outs.getD 2 (l2dOut l2dcDirSt0 l2dcDirInA)
    -- 拍 1：reqA 的 result：valid、miss（hit=0）、dirty=1、set=9、opcode=Get
    o1.resultValid = true ∧ o1.resultHit = false ∧ o1.resultDirty = true ∧
    o1.resultSet = 9#6 ∧ o1.resultOpcode = l2opGet ∧
    -- 拍 2：reqB 的 result：同样 miss-dirty（紧挨一拍）
    o2.resultValid = true ∧ o2.resultHit = false ∧ o2.resultDirty = true ∧
    o2.resultSet = 10#6 ∧ o2.resultOpcode = l2opGet ∧
    -- 拍 1 同拍 reqB 的 read 被接受（readReady 含 resultReady=push.ready=1）
    (l2dWiresOf (l2dStep l2dcDirSt0 l2dcDirInA) l2dcDirInB).readFire = true := by
  native_decide

/-- 腿 B 请求：miss-dirty 的 Get（写回路径：stage_3 发 a） -/
def l2dcSdReq : L2sReq := l2sReqOf l2opGet false true false false
/-- 腿 B 停顿输入：写回 a 通道不ready（write_buffer 满 / 上游反压） -/
def l2dcSdStall : L2sIn := { l2sInIdle with aReady := false }

/-- 腿 B：SourceD 接受一笔 miss-dirty 请求后，a 反压下 reqReady 连续 ≥3 拍
    为 0——drb deq（Scheduler.scala:249 需 sourceD.io.req.ready）被挡，
    drb 持满窗口覆盖腿 C 的拍 0/拍 1。 -/
theorem l2dc_i43_sourced_busy :
    let outs := l2sTrace l2sInit
      [l2sInReq l2dcSdReq, l2dcSdStall, l2dcSdStall, l2dcSdStall]
    let o0 := outs.getD 0 (l2sOut l2sInit (l2sInReq l2dcSdReq))
    let o1 := outs.getD 1 (l2sOut l2sInit (l2sInReq l2dcSdReq))
    let o2 := outs.getD 2 (l2sOut l2sInit (l2sInReq l2dcSdReq))
    let o3 := outs.getD 3 (l2sOut l2sInit (l2sInReq l2dcSdReq))
    o0.reqReady = true ∧ o1.reqReady = false ∧ o2.reqReady = false ∧
    o3.reqReady = false := by
  native_decide

/- ========================================================================= -/
/- 3. E3【反例证伪】"allocate 命中 ⇒ push 被接受"不成立                       -/
/-    机制：读发起门控（Scheduler.scala:225,:239 的 push.ready）比结果拍早一   -/
/-    拍求值；同拍一个 secondary push（:223 的 tagMatches 支，不占新 MSHR      -/
/-    queue 但消耗 entry 池）可耗尽 32 项 entry 池 ⇒ 结果拍 push.ready=0，    -/
/-    而 allocate 电平敏感（:190 不吃 push.ready）照发 ⇒ E3 前件成立后件败。   -/
/-    连锁：valids 影子不落位 ⇒ I-39 不变量破（l2dc_e3_inv1_broken）；result   -/
/-    未被消费保持 valid ⇒ allocate 每拍重复 ⇒ scheAValid 反复置位 ⇒ 同一      -/
/-    source 的 A 重复发（l2dc_e3_counterexample 末两合取）⇒ E1b 亦可被击破。  -/
/- ========================================================================= -/

/-- ListBuffer（requests，queues=32/entries=32 ⇒ qBits=5/eBits=5）侧轨迹：
    31 个 primary push（queue 0..30）+ 1 个 secondary push（queue 0） -/
def l2dcLbPush (q : Nat) : LbIn 5 (BitVec 8) := ⟨true, BitVec.ofNat 5 q, 0#8, false, 0#5⟩
def l2dcLbPrimTrace : List (LbIn 5 (BitVec 8)) := (List.range 31).map l2dcLbPush
def l2dcLbPrim : LbState 5 5 (BitVec 8) := lbRun lbInit l2dcLbPrimTrace
def l2dcLbFull : LbState 5 5 (BitVec 8) := lbRun lbInit (l2dcLbPrimTrace ++ [l2dcLbPush 0])

/-- LB 腿：entry 池可耗尽而 queue 31 仍空闲（valid(31)=0 ⇔ MSHR 31 未用）；
    且耗尽前最后一拍 push.ready 仍为 1（读门控在该拍通过）。 -/
theorem l2dc_lb_pool_exhausted :
    lbPushReady l2dcLbPrim = true ∧
    l2dcLbFull.used = BitVec.allOnes 32 ∧
    l2dcLbFull.valid.getLsbD 31 = false ∧
    lbPushReady l2dcLbFull = false := by
  native_decide

/-- Scheduler 侧拍 0..30：31 个 Get miss primary result（tag=i+1 互异，set=0），
    各分配 entry i；sourceA 就绪（各 entry 的 A 分配后一拍发出并清偿） -/
def l2dcE3AllocIn (i : Nat) : L2scIn :=
  { l2scInIdle with
    sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with
                    opcode := l2mOpGet, set := 0#6, way := 0#4,
                    tag := BitVec.ofNat 19 (i + 1) } }

/-- 拍 31：secondary miss result（tag=1,set=0 匹配 entry 0）——push 落 queue 0，
    耗尽 entry 池（对应 LB 轨迹最后一拍）；当拍读门控见 push.ready=1 通过 -/
def l2dcE3SecIn : L2scIn :=
  { l2scInIdle with
    sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true,
    dirRes := { l2mStatusZero with opcode := l2mOpGet, set := 0#6, way := 0#4, tag := 1#19 } }

/-- 拍 32..35：新 Get miss result（tag=100 无匹配），push.ready=0（池已耗尽，
    Directory 侧 result 未被消费而保持 valid——对应 E3 反例的后果拍） -/
def l2dcE3CexIn : L2scIn :=
  { l2scInIdle with
    sourceDReqReady := false, dirWriteReady := false,
    dirResValid := true, pushReady := false,
    dirRes := { l2mStatusZero with opcode := l2mOpGet, set := 0#6, way := 0#4, tag := 100#19 } }

/-- primary 轨迹（仅符号引用：l2dc_e3_env_allocs 的合法性陈述，不做数值求值） -/
def l2dcE3Trace : List L2scIn :=
  (List.range 31).map l2dcE3AllocIn ++ [l2dcE3SecIn, l2dcE3CexIn, l2dcE3CexIn,
    l2dcE3CexIn, l2dcE3CexIn]
/-- 前 n 拍后的状态（符号形式） -/
def l2dcE3St (n : Nat) : L2scState := l2scRun l2scInit (l2dcE3Trace.take n)

/-- 拍 32 的手构前态（"手构状态单拍"惯例）：entry 0..30 已分配（tag=i+1 互异、
    A 已发出 ⇒ scheAValid=0）、valids=0x7FFFFFFF（仅 entry 31 空闲）。
    可达性对接（抽象事件组合，简报核准）：l2dcE3AllocIn 的 31 拍 primary
    allocate 每拍 push 落最低空闲位（无 pop 轨迹下 valids 影子与 LB valid 位
    逐事件一致）建立 valids=0x7FFFFFFF；entry 池在 queue 31 空闲下耗尽由
    LB 腿 l2dc_lb_pool_exhausted 机证；scheAValid=0 对应各 entry 的 A 已发出
    （sourceAReqReady=1 时分配后一拍即 fire，见 l2mStep :110-116）。 -/
def l2dcE3Entry (i : Nat) : L2mState :=
  { l2mInit with request := { l2mStatusZero with
      opcode := l2mOpGet, set := 0#6, way := 0#4, tag := BitVec.ofNat 19 (i + 1) } }

def l2dcE3Pre : L2scState :=
  { l2scInit with
    mshrs := fun i => if i < 31 then l2dcE3Entry i else l2mInit,
    valids := 0x7FFFFFFF#32 }

/-- 反例拍链：拍 32（allocate 命中、push 被拒）→ 33（A 首发了）→ 34
    （allocate 重复、重新武装）→ 35（A 重发） -/
def l2dcE3St33 : L2scState := l2scStep l2dcE3Pre l2dcE3CexIn
def l2dcE3St34 : L2scState := l2scStep l2dcE3St33 l2dcE3CexIn
def l2dcE3St35 : L2scState := l2scStep l2dcE3St34 l2dcE3CexIn

/-- E3 反例（机证）：allocate 命中但 push 被拒；inv1 破；同一 source 的 A 重复发 -/
theorem l2dc_e3_counterexample :
    -- 拍 32：allocate 命中 entry 31（insertOH 唯一空闲位）而 push.ready=0
    l2scAllocValid l2dcE3Pre l2dcE3CexIn 31 = true ∧
    l2dcE3CexIn.pushReady = false ∧
    -- 拍 32 后：entry 31 已武装（scheAValid=1）但 valids(31)=0（push 未落）
    (l2dcE3St33.mshrs 31).scheAValid = true ∧
    l2dcE3St33.valids.getLsbD 31 = false ∧
    -- 拍 33 与拍 35 各发一次 A（同 entry ⇒ 同 source=31）：重复 A
    l2scAFire l2dcE3St33 l2dcE3CexIn 31 = true ∧
    l2scAFire l2dcE3St35 l2dcE3CexIn 31 = true := by
  native_decide

/-- E3 作为命题被证伪 -/
theorem l2dc_e3_falsified :
    ¬ (∀ i, l2scAllocValid l2dcE3Pre l2dcE3CexIn i = true →
        l2dcE3CexIn.pushReady = true) := by
  intro h
  have h1 : l2scAllocValid l2dcE3Pre l2dcE3CexIn 31 = true := by native_decide
  have h2 := h 31 h1
  rw [show l2dcE3CexIn.pushReady = false from rfl] at h2
  exact Bool.false_ne_true h2

/-- I-39 不变量在该角落被破坏（l2sc_inv1_preserved 的 E3 前提不可去） -/
theorem l2dc_e3_inv1_broken : ¬ l2scInv1 l2dcE3St33 := by
  intro h
  have h1 : l2dcE3St33.valids.getLsbD 31 = false := by native_decide
  have h2 := h 31 h1
  rw [show (l2dcE3St33.mshrs 31).scheAValid = true from by native_decide] at h2
  exact absurd h2 (by decide)

/-- primary 轨迹各拍环境合法（E1：无 sinkd vacuous；E3：pushReady=1）——
    即"前 31 拍完全合法、第 32 拍 E3 才失败"，失败点在规约本身而非轨迹构造。
    （拍 31 secondary 拍同理：alloc=false 使 allocate 前件恒假，E3 vacuous。） -/
theorem l2dc_e3_env_allocs (i : Nat) : l2scEnv (l2dcE3St i) (l2dcE3AllocIn i) := by
  refine ⟨fun hv _ => absurd hv ?_, fun _ _ => rfl⟩
  rw [show (l2dcE3AllocIn i).sinkdValid = false from rfl]
  exact Bool.false_ne_true

/- ========================================================================= -/
/- 4. E1【落实为定理】"sinkD 响应只打活跃 entry 且为首个响应"                  -/
/-    分解：E1 = E1b（外层 TL/fabric 纪律，黑盒残余前提）+ 联合不变量（机证    -/
/-    逐拍保持）。E1b 把"每 A 恰好一个 D、source 指向在飞 A"压缩为可逐拍检查   -/
/-    的最小形式：响应源位必须在在飞位图 aOut 中（响应即清位 ⇒ 第二次响应无位  -/
/-    可依 ⇒ "首个响应"）。aOut 的语义：entry i 的 refill A（schedule.a，      -/
/-    source=mshr_select=i）发出置位、sinkd 接收清位。SourceA/SinkD 侧接线     -/
/-    （L2Channels sourceAAValid/sinkDStep：valid 直通、d.ready 恒 1）不改变    -/
/-    source；写回 A 的 D 响应 opcode=AccessAck≠AccessAckData 被 :127 过滤。    -/
/-    【残余前提】① E1b 本身（外层内存/TL fabric 黑盒，L2 内部不可证）；       -/
/-    ② 每拍 E3——已被第 3 节反例削弱：E3 失败的角落（重复 A）可同时击破 E1b。  -/
/- ========================================================================= -/

/-- 在飞 refill A 影子的单拍推进：sinkd 接收清位、A fire 置位 -/
def l2dcAOutNext (sc : L2scState) (inp : L2scIn) (aOut : BitVec 32) : BitVec 32 :=
  (aOut &&& ~~~(l2scOfPred (l2scSinkdV sc inp))) ||| l2scOfPred (l2scAFire sc inp)

/-- E1b（残余前提）：sinkD 的 AccessAckData 响应源必指向在飞 A -/
def l2dcE1b (aOut : BitVec 32) (inp : L2scIn) : Prop :=
  inp.sinkdValid = true → inp.sinkdOpcode = l2scOpAccessAckData →
    ∃ j, j < 32 ∧ inp.sinkdSource = BitVec.ofNat 16 j ∧ aOut.getLsbD j = true

/-- 联合不变量：I-39 不变量 + 在飞位性质 + 武装 entry 未收响应 -/
def l2dcInvE1 (sc : L2scState) (aOut : BitVec 32) : Prop :=
  l2scInv1 sc ∧
  (∀ j, aOut.getLsbD j = true → sc.valids.getLsbD j = true ∧
      (sc.mshrs j).sinkDReg = false ∧ (sc.mshrs j).scheAValid = false) ∧
  (∀ j, (sc.mshrs j).scheAValid = true → (sc.mshrs j).sinkDReg = false)

/-- E1 落实主定理：不变量 + 本拍 E3 + 本拍 E1b ⇒ 本拍 E1 成立且不变量保持。
    E1 内容（第一合取）：sinkd 命中的 entry 必活跃（valids=1）且 sinkDReg=0
    （即首个响应）——这正是 l2scEnv.1 的实例化。 -/
theorem l2dc_e1_step (sc : L2scState) (aOut : BitVec 32) (inp : L2scIn)
    (hinv : l2dcInvE1 sc aOut)
    (he3 : ∀ i, l2scAllocValid sc inp i = true → inp.pushReady = true)
    (he1b : l2dcE1b aOut inp) :
    (∀ i, i < 32 → l2scSinkdV sc inp i = true →
      sc.valids.getLsbD i = true ∧ (sc.mshrs i).sinkDReg = false) ∧
    l2dcInvE1 (l2scStep sc inp) (l2dcAOutNext sc inp aOut) := by
  obtain ⟨hinv1, hout, hsa⟩ := hinv
  -- 本拍 E1 的 ∃ 形式（同时供 l2scEnv 复用以保持 I-39 不变量）
  have hE1 : inp.sinkdValid = true → inp.sinkdOpcode = l2scOpAccessAckData →
      ∃ j, j < 32 ∧ inp.sinkdSource = BitVec.ofNat 16 j ∧
        sc.valids.getLsbD j = true ∧ (sc.mshrs j).sinkDReg = false := by
    intro hv hop
    obtain ⟨j, hj32, hjsrc, hjout⟩ := he1b hv hop
    obtain ⟨hvj, hsdj, -⟩ := hout j hjout
    exact ⟨j, hj32, hjsrc, hvj, hsdj⟩
  have henv : l2scEnv sc inp := ⟨hE1, he3⟩
  have he1i : ∀ i, i < 32 → l2scSinkdV sc inp i = true →
      sc.valids.getLsbD i = true ∧ (sc.mshrs i).sinkDReg = false := by
    intro i hi32 hs
    obtain ⟨hdv, hsrc, hop⟩ := l2scSinkdV_parts hs
    obtain ⟨j, hj32, hjsrc, hvj, hsdj⟩ := hE1 hdv hop
    have heq : BitVec.ofNat 16 i = BitVec.ofNat 16 j := by rw [← hsrc, ← hjsrc]
    have hij : i = j := l2sc_ofNat16_inj hi32 hj32 heq
    subst hij
    exact ⟨hvj, hsdj⟩
  have hinv1' : l2scInv1 (l2scStep sc inp) := l2sc_inv1_preserved sc inp hinv1 henv
  have hstepM : ∀ k, (l2scStep sc inp).mshrs k =
      l2mStep (sc.mshrs k) (l2scMshrIn sc inp k) := fun _ => rfl
  have hMinS : ∀ k, (l2scMshrIn sc inp k).sinkdValid = l2scSinkdV sc inp k :=
    fun _ => rfl
  have hMinA : ∀ k, (l2scMshrIn sc inp k).allocValid = l2scAllocValid sc inp k :=
    fun _ => rfl
  refine ⟨he1i, hinv1', ?_, ?_⟩
  · -- 第二支保持：aOut' 位 ⇒ valids=1 ∧ sinkDReg=0 ∧ scheAValid=0
    intro j hj
    by_cases hge : 32 ≤ j
    · exfalso
      have hz : (l2dcAOutNext sc inp aOut).getLsbD j = false :=
        l2sc_getLsbD_false_of_ge32 hge
      rw [hz] at hj
      exact absurd hj (by decide)
    · have hj32 : j < 32 := by omega
      unfold l2dcAOutNext at hj
      rw [BitVec.getLsbD_or] at hj
      by_cases hret : (aOut &&& ~~~(l2scOfPred (l2scSinkdV sc inp))).getLsbD j = true
      · -- 保持在飞（本拍无 sinkd 到 j）
        have hret' := hret
        rw [BitVec.getLsbD_and, BitVec.getLsbD_not, l2scOfPred_getLsbD _ j hj32] at hret'
        have h1 := Bool.and_eq_true_iff.mp hret'
        have h2 := Bool.and_eq_true_iff.mp h1.2
        have hao : aOut.getLsbD j = true := h1.1
        have hsd0 : l2scSinkdV sc inp j = false := by
          cases hs : l2scSinkdV sc inp j
          · rfl
          · rw [hs] at h2
            simp at h2
        obtain ⟨hvj, hsdj, hsaj⟩ := hout j hao
        have hpop0 : (if l2scPopValid sc inp then l2scSelectOH sc inp
            else 0#32).getLsbD j = false := by
          by_cases hpv : l2scPopValid sc inp = true
          · rw [if_pos hpv]
            by_cases hsel : (l2scSelectOH sc inp).getLsbD j = true
            · exfalso
              have hsdv := (l2scPopValid_parts hpv).2.1
              have hdv := l2scMux1H_transfer (l2scSelectOH_spec sc inp).1 hsdv hsel hj32
              have h1 := (l2scDV_parts hdv).2.1
              rw [hsdj] at h1
              exact absurd h1 (by decide)
            · cases hx : (l2scSelectOH sc inp).getLsbD j
              · rfl
              · exact (hsel hx).elim
          · rw [if_neg hpv, BitVec.getLsbD_zero]
        have hvj' : (l2scStep sc inp).valids.getLsbD j = true := by
          show ((sc.valids &&& ~~~(if l2scPopValid sc inp then l2scSelectOH sc inp
                else 0#32)) ||| (if l2scPushValid sc inp && inp.pushReady
                then l2scPushOH sc inp else 0#32)).getLsbD j = true
          rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpop0, hvj]
          simp [hj32]
        have hal0 : l2scAllocValid sc inp j = false := by
          by_cases ha : l2scAllocValid sc inp j = true
          · exfalso
            have hfree := l2scInsertOH_free sc j (l2scAllocValid_parts ha).2.2.1
            rw [hvj] at hfree
            exact absurd hfree (by decide)
          · cases hx : l2scAllocValid sc inp j
            · rfl
            · exact (ha hx).elim
        have hsdj' : ((l2scStep sc inp).mshrs j).sinkDReg = false := by
          rw [hstepM j]
          show (if (l2scMshrIn sc inp j).sinkdValid then true
                else if (l2scMshrIn sc inp j).allocValid then false
                else (sc.mshrs j).sinkDReg) = false
          rw [hMinS j, hMinA j, if_neg (by simp [hsd0]), if_neg (by simp [hal0])]
          exact hsdj
        have hsaj' : ((l2scStep sc inp).mshrs j).scheAValid = false := by
          rw [hstepM j]
          show (if l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) then false
                else if (l2scMshrIn sc inp j).allocValid then true
                else (sc.mshrs j).scheAValid) = false
          have haf0 : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) = false := by
            by_cases hf : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) = true
            · exfalso
              have hf' : l2scAFire sc inp j = true := hf
              have hav : (sc.mshrs j).scheAValid = true := by
                unfold l2scAFire l2scAV at hf'
                exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf').1).1
              rw [hsaj] at hav
              exact absurd hav (by decide)
            · cases hx : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j)
              · rfl
              · exact (hf hx).elim
          rw [hMinA j, if_neg (by simp [haf0]), if_neg (by simp [hal0])]
          exact hsaj
        exact ⟨hvj', hsdj', hsaj'⟩
      · -- 新在飞（本拍 A fire 到 j）
        have hfb : (l2scOfPred (l2scAFire sc inp)).getLsbD j = true := by
          cases hx : (aOut &&& ~~~(l2scOfPred (l2scSinkdV sc inp))).getLsbD j
          · rw [hx] at hj
            simpa using hj
          · exact absurd hx hret
        have hfire : l2scAFire sc inp j = true := by
          have h1 := l2scOfPred_getLsbD (l2scAFire sc inp) j hj32
          rw [h1] at hfb
          exact hfb
        have hsaj0 : (sc.mshrs j).scheAValid = true := by
          unfold l2scAFire l2scAV at hfire
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hfire).1).1
        have hvj : sc.valids.getLsbD j = true := by
          by_cases hv : sc.valids.getLsbD j = true
          · exact hv
          · exfalso
            have h0 : sc.valids.getLsbD j = false := by
              cases hx : sc.valids.getLsbD j
              · rfl
              · exact (hv hx).elim
            have h2 := hinv1 j h0
            rw [hsaj0] at h2
            exact absurd h2 (by decide)
        have hsd0 : l2scSinkdV sc inp j = false := by
          by_cases hsw : l2scSinkdV sc inp j = true
          · exfalso
            obtain ⟨hdv, hsrc, hop⟩ := l2scSinkdV_parts hsw
            obtain ⟨k, hk32, hksrc, hkout⟩ := he1b hdv hop
            have heq : BitVec.ofNat 16 j = BitVec.ofNat 16 k := by rw [← hsrc, ← hksrc]
            have hjk : j = k := l2sc_ofNat16_inj hj32 hk32 heq
            subst hjk
            obtain ⟨-, -, hsa0⟩ := hout j hkout
            rw [hsaj0] at hsa0
            exact absurd hsa0 (by decide)
          · cases hx : l2scSinkdV sc inp j
            · rfl
            · exact (hsw hx).elim
        have hpop0 : (if l2scPopValid sc inp then l2scSelectOH sc inp
            else 0#32).getLsbD j = false := by
          by_cases hpv : l2scPopValid sc inp = true
          · rw [if_pos hpv]
            by_cases hsel : (l2scSelectOH sc inp).getLsbD j = true
            · exfalso
              have hsdv := (l2scPopValid_parts hpv).2.1
              have hdv := l2scMux1H_transfer (l2scSelectOH_spec sc inp).1 hsdv hsel hj32
              have h1 := (l2scDV_parts hdv).2.2
              rw [hsaj0] at h1
              exact absurd h1 (by decide)
            · cases hx : (l2scSelectOH sc inp).getLsbD j
              · rfl
              · exact (hsel hx).elim
          · rw [if_neg hpv, BitVec.getLsbD_zero]
        have hvj' : (l2scStep sc inp).valids.getLsbD j = true := by
          show ((sc.valids &&& ~~~(if l2scPopValid sc inp then l2scSelectOH sc inp
                else 0#32)) ||| (if l2scPushValid sc inp && inp.pushReady
                then l2scPushOH sc inp else 0#32)).getLsbD j = true
          rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpop0, hvj]
          simp [hj32]
        have hal0 : l2scAllocValid sc inp j = false := by
          by_cases ha : l2scAllocValid sc inp j = true
          · exfalso
            have hfree := l2scInsertOH_free sc j (l2scAllocValid_parts ha).2.2.1
            rw [hvj] at hfree
            exact absurd hfree (by decide)
          · cases hx : l2scAllocValid sc inp j
            · rfl
            · exact (ha hx).elim
        have hsdj' : ((l2scStep sc inp).mshrs j).sinkDReg = false := by
          rw [hstepM j]
          show (if (l2scMshrIn sc inp j).sinkdValid then true
                else if (l2scMshrIn sc inp j).allocValid then false
                else (sc.mshrs j).sinkDReg) = false
          rw [hMinS j, hMinA j, if_neg (by simp [hsd0]), if_neg (by simp [hal0])]
          exact hsa j hsaj0
        have hsaj' : ((l2scStep sc inp).mshrs j).scheAValid = false := by
          rw [hstepM j]
          show (if l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) then false
                else if (l2scMshrIn sc inp j).allocValid then true
                else (sc.mshrs j).scheAValid) = false
          have haf : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) = true := hfire
          rw [if_pos haf]
        exact ⟨hvj', hsdj', hsaj'⟩
  · -- 第三支保持：scheAValid'=1 ⇒ sinkDReg'=0
    intro j hj
    by_cases hge : 32 ≤ j
    · exfalso
      have hv0 : (l2scStep sc inp).valids.getLsbD j = false :=
        l2sc_getLsbD_false_of_ge32 hge
      have h2 := hinv1' j hv0
      rw [h2] at hj
      exact absurd hj (by decide)
    · have hj32 : j < 32 := by omega
      rw [hstepM j] at hj
      have hj' : (if l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) then false
            else if (l2scMshrIn sc inp j).allocValid then true
            else (sc.mshrs j).scheAValid) = true := hj
      rw [hstepM j]
      show (if (l2scMshrIn sc inp j).sinkdValid then true
            else if (l2scMshrIn sc inp j).allocValid then false
            else (sc.mshrs j).sinkDReg) = false
      by_cases haf : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) = true
      · rw [if_pos haf] at hj'
        exact absurd hj' (by decide)
      · have haf0 : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j) = false := by
          cases hx : l2mAFire (sc.mshrs j) (l2scMshrIn sc inp j)
          · rfl
          · exact (haf hx).elim
        rw [if_neg (by simpa using haf0)] at hj'
        by_cases hal : (l2scMshrIn sc inp j).allocValid = true
        · -- allocate 分支：sinkDReg' = false（I-41a 排除同拍 sinkd）
          have halloc : l2scAllocValid sc inp j = true := hal
          have hnsd : l2scSinkdV sc inp j = false :=
            l2sc_i41a_no_alloc_sinkd sc inp j henv halloc
          rw [hMinS j, hMinA j, if_neg (by simp [hnsd]), if_pos (by simp [halloc])]
        · have hal0 : l2scAllocValid sc inp j = false := by
            cases hx : l2scAllocValid sc inp j
            · rfl
            · exact (hal hx).elim
          rw [hMinA j, if_neg (by simp [hal0])] at hj'
          -- 保持武装：sinkd 到 j 不可能（E1b ⇒ aOut j ⇒ scheAValid=0 矛盾）
          have hsd0 : l2scSinkdV sc inp j = false := by
            by_cases hsw : l2scSinkdV sc inp j = true
            · exfalso
              obtain ⟨hdv, hsrc, hop⟩ := l2scSinkdV_parts hsw
              obtain ⟨k, hk32, hksrc, hkout⟩ := he1b hdv hop
              have heq : BitVec.ofNat 16 j = BitVec.ofNat 16 k := by rw [← hsrc, ← hksrc]
              have hjk : j = k := l2sc_ofNat16_inj hj32 hk32 heq
              subst hjk
              obtain ⟨-, -, hsa0⟩ := hout j hkout
              rw [hj'] at hsa0
              exact absurd hsa0 (by decide)
            · cases hx : l2scSinkdV sc inp j
              · rfl
              · exact (hsw hx).elim
          rw [hMinS j, hMinA j, if_neg (by simp [hsd0]), if_neg (by simp [hal0])]
          exact hsa j hj'

/-- 初始不变量（aOut=0：各支 vacuous 或平凡） -/
theorem l2dc_e1_init : l2dcInvE1 l2scInit 0#32 := by
  refine ⟨l2sc_inv1_init, ?_, ?_⟩
  · intro j hj
    rw [BitVec.getLsbD_zero] at hj
    exact absurd hj (by decide)
  · intro j hj
    rw [show (l2scInit.mshrs j).scheAValid = false from rfl] at hj
    exact absurd hj (by decide)

/-- 在飞 A 影子的多拍推进 -/
def l2dcAOutRun : L2scState → BitVec 32 → List L2scIn → BitVec 32
  | _, a, [] => a
  | sc, a, i :: is => l2dcAOutRun (l2scStep sc i) (l2dcAOutNext sc i a) is

/-- E1 落实的轨迹形式：每拍满足 E3 与 E1b ⇒ 联合不变量恒成立（配合
    l2dc_e1_step 第一合取：轨迹每拍的 sinkd 响应均打活跃 entry 且为首个响应） -/
theorem l2dc_e1_run : ∀ (sc : L2scState) (aOut : BitVec 32) (trace : List L2scIn),
    l2dcInvE1 sc aOut →
    (∀ pre inp post, trace = pre ++ inp :: post →
      (∀ i, l2scAllocValid (l2scRun sc pre) inp i = true → inp.pushReady = true) ∧
      l2dcE1b (l2dcAOutRun sc aOut pre) inp) →
    l2dcInvE1 (l2scRun sc trace) (l2dcAOutRun sc aOut trace) := by
  intro sc aOut trace
  induction trace generalizing sc aOut with
  | nil => intro h _; exact h
  | cons a l ih =>
    intro hinv henv
    have h0 := henv [] a l rfl
    have hstep := (l2dc_e1_step sc aOut a hinv h0.1 h0.2).2
    apply ih _ _ hstep
    intro pre inp post hdecomp
    have h2 : a :: l = (a :: pre) ++ inp :: post := by rw [hdecomp, List.cons_append]
    exact henv (a :: pre) inp post h2

/- ========================================================================= -/
/- 5. 公理审计（native_decide 仅用于 witness/数值回归；符号定理为零信任公理。 -/
/-    预期：witness 族带 _native.native_decide.ax_*，l2dc_e1_step/init/run、    -/
/-    l2dc_e3_falsified、l2dc_e3_env_allocs 仅 propext/Quot.sound 级）          -/
/- ========================================================================= -/

#print axioms l2dc_i42_witness
#print axioms l2dc_i43_witness
#print axioms l2dc_i43_dir_results
#print axioms l2dc_i43_sourced_busy
#print axioms l2dc_lb_pool_exhausted
#print axioms l2dc_e3_counterexample
#print axioms l2dc_e3_falsified
#print axioms l2dc_e3_inv1_broken
#print axioms l2dc_e3_env_allocs
#print axioms l2dc_e1_step
#print axioms l2dc_e1_init
#print axioms l2dc_e1_run

end Ventus.L2.L2Discharge
