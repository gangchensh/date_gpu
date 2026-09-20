/- ========================================================================= -/
/-                          Mem/L1MSHR.lean                                  -/
/-  DCache 的 MSHR（L1Cache/L1MSHR.scala，366 行）的 Lean 4 模型、测试与证明   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/L1Cache/L1MSHR.scala        -/
/-    （注意区分：pipeline/MSHR.scala 的 MSHRv2 是 LSU 侧另一套，模型见        -/
/-     Mem/MSHR.lean；ICache/ICacheMSHR.scala 是第三套，模型见                -/
/-     Mem/ICache.lean。三套结构差异很大，不可互套。）                        -/
/-                                                                           -/
/-  例化与连接（2026-08-27 全仓 grep 核查）：                                  -/
/-  * 唯一例化点 DCache/DCache.scala:178：                                     -/
/-      MSHR(bABits=25(TagBits 17+SetIdxBits 8), tIWidth=tIBits=323           -/
/-        (WIdBits 3 + NLanes 32*(BlockOffsetBits 5+1+BytesOfWord 4)),        -/
/-        WIdBits=3, NMshrEntry=dcache_MshrEntry=4,                           -/
/-        NMshrSubEntry=dcache_MshrSubEntry=2, asidLen)                       -/
/-  * probe ← coreReq st0（:275-277）；missReq ← readMiss_st1 等（:319-326）； -/
/-    missRspIn ← memRsp_Q 队头（:615-617），其 ready 参与 memRsp_Q 出队       -/
/-    （:546-547）；missRspOut → coreRsp_st2（:690,:746）；                    -/
/-    stage1_ready=coreReq_st1_ready（:282）；stage2_ready=MemReqArb.in(1).ready-/
/-    （:331）；releasing_stall/empty/mshrStatus_st0 → coreReq 反压（:212-219）。-/
/-  * MMU_ENABLED=false（top/parameters.scala:15）→ 建模 else 分支（:186-194）。-/
/-  * DCacheWSHR（DCacheWSHR.scala，51 行，写 miss 用）与 L1MSHR 无任何引用    -/
/-    关系（L1MSHR.scala 全文未出现 WSHR），按任务约定不建模（D6）。           -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 参数按唯一例化固化为字面量：bABits=25、tIWidth=323、WIdBits=3、        -/
/-      NMshrEntry=4、NMshrSubEntry=2、MMU 关闭。                              -/
/-  D2. 两个 1 深 Queue(...,1,pipe=true,flow=false)（MSHR_st1 :108 与          -/
/-      missRspOut_st1 :332）建模为 L1mQ（full+bits）：enq.ready=!full；       -/
/-      空时 deq.valid/bits 组合旁路 enq；空且 deqRdy 时抑制入队（穿透），     -/
/-      与 chisel3.util.Queue 的寄存器实现语义一致（同 ICache.lean icQStep）。 -/
/-  D3. OHToUInt/indexWhere 建模为"最低置位/清零位下标，无匹配得 0"。          -/
/-      chisel OHToUInt 对多热输入语义为各置位下标的按位或——仅在违反 :196      -/
/-      assert（entryMatchProbe 多热）时有差异；独热/全零下两语义一致。        -/
/-  D4. Cat/Reverse 组合（:106/:145/:187/:312）按"位 i = 元素 i"建模：Cat 的   -/
/-      首元素占 MSB，Reverse 恰好抵消。                                      -/
/-  D5. 宽度不匹配 := 连接（:138←:192 零扩展、:309 截断、:336 零扩展）按        -/
/-      Chisel 6 隐式截断/零扩展语义建模（chisel 文档：非 Connectable 操作符   -/
/-      允许宽源隐式截断），所涉数值 ≤3，两种语义下无损，见 Q6。               -/
/-  D6. DCacheWSHR 与 L1MSHR 无引用关系，不建模；spike_info 仅 printf，省略。 -/
/-  D7. instrId_Access（:101）写入后全模块无一处读取（唯一读取点 :324 已       -/
/-      注释），probestatus 寄存器（:107）只在 :284-292 自引用、与             -/
/-      io.probestatus（:113，=st1 队列 deq.valid）是不同信号。两者忠实       -/
/-      建模为状态字段，但不影响任何输出（Q7）。                              -/
/-                                                                           -/
/- ======================== 源码审查发现（详见返回报告与 doc/03） ============ -/
/-  Q1（I 类候选，核心）：missReq.ready（:295）与 mshrStatus_st0（:247-265）   -/
/-      反压不一致——当 mshrStatus_st1_r==SECONDARY_AVAIL(2) 且 probe 选中      -/
/-      entry 的 subentry 已满时，:274 的 st1_w 重算条件只覆盖 st1_r∈{0,1}，   -/
/-      st1_w 保持 2 ⇒ missReq.ready=1，但同拍 mshrStatus_st0=3              -/
/-      (SECONDARY_FULL)。此时次级 missReq fire：:354 的 subentry 置位因       -/
/-      st1 冻结的 seIdx=0（满行 indexWhere 缺省 0）而不生效（该 elsewhen 仅   -/
/-      挂 se=1），即请求不被任何 subentry 记录（永无响应，请求丢失）；同时    -/
/-      :299-301 的 targetInfo 写不受状态门控，realDown=0 ⇒ 覆盖              -/
/-      targetInfo[entry][0]，污染既有 subentry 0 的响应路由信息。             -/
/-      模块级 witness：l1mT7_ready_inconsistent / l1mT7_reqLost /            -/
/-      l1mT7_tiCorrupt（三拍合法输入从初态可达）。DCache 集成下大概率被       -/
/-      st0 预测性反压掩蔽（:248/:256 把 missReq.valid 计入 full 判定，        -/
/-      DCache.scala:212-219 用 st0 拦 coreReq，且 coreReq_Q 1 深）——         -/
/-      可容忍性分析见返回报告。修复建议：:274 重算条件放宽到任意 st1_r，       -/
/-      或 :295 ready 并入 (secondaryMiss && subEntryFull) 判定。              -/
/-  Q2（提示性，:319-321）：missRspIn.ready 中析取项                          -/
/-      ((st1_w==4||st1_w==3) && used==1) 被 (used>=1) 蕴含，死逻辑；          -/
/-      等价简化定理 l1m_rspInReady_simplify。                                -/
/-  Q3（提示性，:187/:192）：entryMatchProbe / entryMatchProbeid_reg 不以      -/
/-      probe.valid / missReq.valid 限定，probe.bits 无效时按陈旧/无关地址     -/
/-      参与 st0 状态与 subentrySelectedForReq（:143）。DCache 中 st0 仅在     -/
/-      coreReq.valid 时有意义（此时 probe.bits 即该请求地址），:212-216 在    -/
/-      !probe.valid 时用到的 subEntryAlmFull 可能取自无关行——至多多一拍反压，-/
/-      正确性影响需整机级判定。                                              -/
/-  Q4（提示性，:345-358）：次级合并置位（:354-356）的 .elsewhen 在 Scala      -/
/-      语义上只挂到内层 for 最后一次迭代（se=NMshrSubEntry-1=1）的 when 链，  -/
/-      即次级合并只能写 subentry 1。S=2 固化参数下恰好正确（唯一次级槽）；    -/
/-      若 NMshrSubEntry>2 则为 bug（永远只能合并 1 个次级请求）。模型按       -/
/-      实际挂接忠实建模。                                                    -/
/-  Q5（提示性，:355 vs :297）：次级合并的"目标 entry"用 fire 拍按             -/
/-      missReq.bits.blockAddr 重算的 entryMatchProbeid_reg（:192），而        -/
/-      targetInfo 写地址与 subentry 下标用 probe 拍冻结在 st1 队列里的值；    -/
/-      若 probe 与 fire 之间匹配关系变化（响应排空 entry 等），两者可错位。   -/
/-      DCache 侧 probereadAllocateWriteConflict（DCache.scala:212-213）在     -/
/-      读响应排空期间挡 probe，正常流程下不可达；模块级潜在隐患。合并定理     -/
/-      l1m_secondary_merge 如实给出两处写地址。                              -/
/-  Q6（提示性）：宽度不匹配 :=——:138 Wire 声明 4 位 ← OHToUInt 2 位（:192）； -/
/-      :309 a_source(2 位) ← Mux(2 位, 4 位) 截断；:336 instrId(3 位) ←      -/
/-      rspIdx(2 位)。值域均 ≤3，按 Chisel 6 截断/零扩展语义无损（D5）。       -/
/-  Q7（提示性）：instrId_Access（:101）写后无读（唯一读取点 :324 已注释）；   -/
/-      probestatus 寄存器（:107,:284-292）只自引用，不驱动任何输出。          -/
/-      纯冗余状态（面积/功耗）。                                             -/
/-  Q8（提示性，:360-364）：releasing_stall 在 missRspIn.fire && !releasing    -/
/-      时被置 1（elsewhen 不排斥 fire）——仅"孤儿响应"（used==0 的 entry 来    -/
/-      响应）时可达，正常流程 rsp 先 valid 置位、排空后 fire 清零，不可达；   -/
/-      若发生则该 entry 的 stall 粘住直到下一次同 entry 响应。                -/
/-  对照 I-22（Mem/MSHR.lean Q1：MSHRv2 to_pipe.valid 回撤）：本模块唯一       -/
/-  Decoupled 输出 missRspOut 经 1 深 pipe 队列缓冲，enq.ready=!full 与        -/
/-  deq.ready 解耦，valid 高且未 fire 时数据必被寄存 ⇒ valid 不可回撤、bits   -/
/-  稳定——握手合规，定理 l1m_rspOut_noWithdraw / l1m_rspOut_stable。         -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.Handshake
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 参数（D1：唯一例化固化为字面量，仅作文档性常量）                        -/
/- ========================================================================= -/

def l1mNEntry : Nat := 4        -- NMshrEntry = dcache_MshrEntry = 4
def l1mNSubEntry : Nat := 2     -- NMshrSubEntry = dcache_MshrSubEntry = 2
def l1mBAWidth : Nat := 25      -- bABits = TagBits 17 + SetIdxBits 8
def l1mTIWidth : Nat := 323     -- tIBits = 3 + 32*(5+1+4)
def l1mWIdWidth : Nat := 3      -- WIdBits = log2Up(num_warp=8)

/- ========================================================================= -/
/- 2. 基础工具：函数表更新 / Fin 索引 / PopCount / 最低位查找 / OHToUInt      -/
/- ========================================================================= -/

/-- 函数表更新（同 mshrUpd/sramUpd 风格）。 -/
def l1mUpd (f : Fin n → α) (i : Fin n) (v : α) : Fin n → α :=
  fun j => if i = j then v else f j

@[simp] theorem l1mUpd_self (f : Fin n → α) (i : Fin n) (v : α) :
    l1mUpd f i v i = v := by simp [l1mUpd]

theorem l1mUpd_of_ne (f : Fin n → α) (i j : Fin n) (v : α) (h : j ≠ i) :
    l1mUpd f i v j = f j := by
  simp only [l1mUpd]; exact if_neg (fun hh => h hh.symm)

/-- 2 位下标 → Fin 4（entry 号）。 -/
def l1mOf4 (b : BitVec 2) : Fin 4 := ⟨b.toNat, b.isLt⟩

/-- 2 位下标 → Fin 2（subentry 号；来源恒为 0/1，取模忠实于越界未定义，D3）。 -/
def l1mOf2 (b : BitVec 2) : Fin 2 := ⟨b.toNat % 2, Nat.mod_lt _ (by decide)⟩

@[simp] theorem l1mOf4_ofNat_val (e : Fin 4) :
    l1mOf4 (BitVec.ofNat 2 e.val) = e := by
  apply Fin.ext
  simp [l1mOf4]

@[simp] theorem l1mOf2_zero : l1mOf2 0#2 = (0 : Fin 2) := by decide
@[simp] theorem l1mOf2_one : l1mOf2 1#2 = (1 : Fin 2) := by decide

/-- Fin 2 字面量相异（beq 归约用）。 -/
@[simp] theorem l1mFin2_one_beq_zero : ((1 : Fin 2) == 0) = false := by decide
@[simp] theorem l1mFin2_zero_beq_one : ((0 : Fin 2) == 1) = false := by decide

/-- 2 位 PopCount（subentry 行）。 -/
def l1mCount2 (row : Fin 2 → Bool) : Nat :=
  (if row 0 then 1 else 0) + (if row 1 then 1 else 0)

/-- 4 位 PopCount（entry 列）。 -/
def l1mCount4 (f : Fin 4 → Bool) : Nat :=
  (if f 0 then 1 else 0) + (if f 1 then 1 else 0) +
  (if f 2 then 1 else 0) + (if f 3 then 1 else 0)

/-- indexWhere(_===false) on 2：最低清零位，全置位缺省 0（getEntryStatusReq.next, :60）。 -/
def l1mFirstZero2 (row : Fin 2 → Bool) : Fin 2 :=
  if !row 0 then 0 else if !row 1 then 1 else 0

/-- indexWhere(_===true) on 2：最低置位位，全清零缺省 0（getEntryStatusRsp.next2cancel, :69）。 -/
def l1mFirstOne2 (row : Fin 2 → Bool) : Fin 2 :=
  if row 0 then 0 else if row 1 then 1 else 0

/-- OHToUInt/PriorityEncoder(4→2)：最低置位位下标，全 0 得 0（D3）。 -/
def l1mPriEnc4 (v : BitVec 4) : BitVec 2 :=
  if v &&& 0b0001#4 ≠ 0 then 0
  else if v &&& 0b0010#4 ≠ 0 then 1
  else if v &&& 0b0100#4 ≠ 0 then 2
  else if v &&& 0b1000#4 ≠ 0 then 3
  else 0

/- ========================================================================= -/
/- 3. 1 深 pipe 队列（D2；MSHR_st1 :108 与 missRspOut_st1 :332）              -/
/- ========================================================================= -/

/-- 1 深 Queue(pipe=true, flow=false) 行为模型：maybe_full + 数据寄存器。 -/
structure L1mQ (α : Type) where
  full : Bool
  bits : α

def l1mQInit (b : α) : L1mQ α := ⟨false, b⟩

/-- enq.ready = !full（flow=false）。 -/
def l1mQEnqRdy (q : L1mQ α) : Bool := !q.full
/-- deq.valid：pipe=true，空时组合旁路 enq.valid。 -/
def l1mQDeqValid (q : L1mQ α) (enqV : Bool) : Bool := q.full || enqV
/-- deq.bits：空时旁路 enq.bits。 -/
def l1mQDeqBits (q : L1mQ α) (enqB : α) : α := if q.full then q.bits else enqB
/-- deq.fire。 -/
def l1mQDeqFire (q : L1mQ α) (enqV : Bool) (rdy : Bool) : Bool :=
  l1mQDeqValid q enqV && rdy

/-- 单拍：do_enq 在"空且 deq 就绪"时被抑制（同拍穿透，不落寄存器）。 -/
def l1mQStep (q : L1mQ α) (enqV : Bool) (enqB : α) (deqRdy : Bool) : L1mQ α where
  full := if q.full then !deqRdy else (enqV && !deqRdy)
  bits := if !q.full && enqV && !deqRdy then enqB else q.bits

/- ========================================================================= -/
/- 4. 状态 / 输入 / 初态                                                       -/
/- ========================================================================= -/

/-- MSHRpipe1Reg（:74-77）：entryMatchProbe 4 位 + subEntryIdx 2 位
    （log2Up(2)+1，enq 时由 1 位的 subentryStatus.next 零扩展，值恒 ∈{0,1}）。 -/
structure L1mPipe1Reg where
  matchProbe : BitVec 4
  seIdx : BitVec 2
deriving DecidableEq

/-- MSHRmissRspOut（:39-46）：instrId 字段 WIdBits=3 位，enq 时由 2 位的
    missRspIn.bits.instrId 零扩展（:336，D5/Q6）。 -/
structure L1mRspBits where
  ti : BitVec 323
  ba : BitVec 25
  iid : BitVec 3
deriving DecidableEq

/-- MSHR 状态（:100-109,:156,:332）：blockAddr/instrId/targetInfo 表、
    subentry_valid、st1 流水队列、rspOut 队列、mshrStatus_st1_r、
    probestatus 寄存器（Q7）、releasing_stall。entry_valid 为派生（:106）。 -/
structure L1mState where
  blockAddr : Fin 4 → BitVec 25
  instrId : Fin 4 → BitVec 3               -- 死状态（D7/Q7），忠实建模
  ti : Fin 4 → Fin 2 → BitVec 323
  subValid : Fin 4 → Fin 2 → Bool
  st1Q : L1mQ L1mPipe1Reg
  rspQ : L1mQ L1mRspBits
  statusR : BitVec 3                       -- mshrStatus_st1_r（:156）
  probeSt : Bool                           -- probestatus 寄存器（:107，Q7）
  releasing : Fin 4 → Bool                 -- releasing_stall（:109）

/-- 初态：全部 RegInit 0/false（:100-109,:156）。 -/
def l1mInit : L1mState :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => false,
   l1mQInit ⟨0, 0⟩, l1mQInit ⟨0, 0, 0⟩, 0#3, false, fun _ => false⟩

/-- 每拍输入：probe(ValidIO) / missReq(Decoupled) / missRspIn(Decoupled) /
    missRspOut.ready / stage1_ready / stage2_ready（:81-97）。MMU 关闭，
    无 asid 输入。 -/
structure L1mIn where
  probeV : Bool
  probeBA : BitVec 25
  reqV : Bool
  reqBA : BitVec 25
  reqII : BitVec 3
  reqTI : BitVec 323
  rspInV : Bool
  rspIdx : BitVec 2
  rspOutRdy : Bool
  st1Rdy : Bool
  st2Rdy : Bool

/-- 空输入（stage 就绪置 1，便于测试）。 -/
def l1mInIdle : L1mIn := ⟨false, 0, false, 0, 0, 0, false, 0, false, true, true⟩

/- ========================================================================= -/
/- 5. 组合逻辑（逐行对应 :106-341）                                            -/
/- ========================================================================= -/

/-- entry_valid 第 e 位（:106，D4）：entry e 有任一 subentry 有效。 -/
def l1mEntryValid (s : L1mState) (e : Fin 4) : Bool :=
  s.subValid e 0 || s.subValid e 1

/-- 单项匹配：blockAddr 相等且 entry 有效（:187 的逐位语义，非 MMU 分支）。
    注意不以 probe.valid/missReq.valid 限定（Q3）。 -/
def l1mMatchBit (s : L1mState) (ba : BitVec 25) (e : Fin 4) : Bool :=
  (s.blockAddr e == ba) && l1mEntryValid s e

/-- 匹配位向量（:187/:192 的 Reverse(Cat(...)) & entry_valid，D4）。 -/
def l1mMatchProbe (s : L1mState) (ba : BitVec 25) : BitVec 4 :=
  (if l1mMatchBit s ba 0 then 0b0001#4 else 0#4) |||
  (if l1mMatchBit s ba 1 then 0b0010#4 else 0#4) |||
  (if l1mMatchBit s ba 2 then 0b0100#4 else 0#4) |||
  (if l1mMatchBit s ba 3 then 0b1000#4 else 0#4)

/-- entryMatchProbe（:137/:187，st0，按 probe 地址）。 -/
def l1mMatchProbeSt0 (s : L1mState) (i : L1mIn) : BitVec 4 := l1mMatchProbe s i.probeBA

/-- entryMatchProbeid_reg（:138/:192，按 missReq 地址重算，Q5/Q6）的低 2 位。 -/
def l1mMatchId (s : L1mState) (i : L1mIn) : BitVec 2 := l1mPriEnc4 (l1mMatchProbe s i.reqBA)

/-- subentrySelectedForReq（:143）：probe 匹配行的 subentry 行，无匹配全 false。 -/
def l1mSubSelRow (s : L1mState) (i : L1mIn) : Fin 2 → Bool :=
  if l1mMatchProbeSt0 s i == 0#4 then fun _ => false
  else s.subValid (l1mOf4 (l1mPriEnc4 (l1mMatchProbeSt0 s i)))

/-- subentryStatus（:144-145，getEntryStatusReq(2)）：full / alm_full / next。 -/
def l1mSubFull (s : L1mState) (i : L1mIn) : Bool :=
  l1mSubSelRow s i 0 && l1mSubSelRow s i 1
def l1mSubAlmFull (s : L1mState) (i : L1mIn) : Bool := l1mCount2 (l1mSubSelRow s i) == 1
def l1mSubNext (s : L1mState) (i : L1mIn) : Fin 2 := l1mFirstZero2 (l1mSubSelRow s i)

/-- entryStatus（:152-153，getEntryStatusReq(4)）。 -/
def l1mMainFull (s : L1mState) : Bool :=
  l1mEntryValid s 0 && l1mEntryValid s 1 && l1mEntryValid s 2 && l1mEntryValid s 3
def l1mMainAlmFull (s : L1mState) : Bool := l1mCount4 (l1mEntryValid s) == 3
def l1mEntryNext (s : L1mState) : Fin 4 :=
  if !l1mEntryValid s 0 then 0
  else if !l1mEntryValid s 1 then 1
  else if !l1mEntryValid s 2 then 2
  else if !l1mEntryValid s 3 then 3
  else 0

/-- st1 流水队列（:207-210）：enq.bits = {entryMatchProbe, subentryStatus.next 零扩展}。 -/
def l1mSt1EnqBits (s : L1mState) (i : L1mIn) : L1mPipe1Reg :=
  ⟨l1mMatchProbeSt0 s i, BitVec.ofNat 2 (l1mSubNext s i).val⟩
def l1mSt1DeqValid (s : L1mState) (i : L1mIn) : Bool := l1mQDeqValid s.st1Q i.probeV
def l1mSt1DeqBits (s : L1mState) (i : L1mIn) : L1mPipe1Reg :=
  l1mQDeqBits s.st1Q (l1mSt1EnqBits s i)
def l1mSt1DeqFire (s : L1mState) (i : L1mIn) : Bool := l1mSt1DeqValid s i && i.st1Rdy

/-- secondaryMiss / primaryMiss（:198-201）：st1 队列冻结的 match（deq.valid 不限定）。 -/
def l1mSecondary (s : L1mState) (i : L1mIn) : Bool := (l1mSt1DeqBits s i).matchProbe != 0#4
def l1mPrimary (s : L1mState) (i : L1mIn) : Bool := !l1mSecondary s i
/-- st0 版本（:199-200）：按当前 probe 地址。 -/
def l1mSecondarySt0 (s : L1mState) (i : L1mIn) : Bool := l1mMatchProbeSt0 s i != 0#4
def l1mPrimarySt0 (s : L1mState) (i : L1mIn) : Bool := !l1mSecondarySt0 s i

/-- mshrStatus_st1_w（:274-282）：次级请求且 st1_r∈{PRIMARY_AVAIL,PRIMARY_FULL}
    时按当前 subentry 状态重算，否则保持 st1_r。注意不含 st1_r==2（Q1）。 -/
def l1mSt1W (s : L1mState) (i : L1mIn) : BitVec 3 :=
  if l1mSecondary s i && (s.statusR == 0#3 || s.statusR == 1#3) && i.st2Rdy then
    (if l1mSubFull s i then 3#3 else 2#3)
  else s.statusR

/-- io.probeOut_st1.probeStatus（:283）。 -/
def l1mProbeStatus (s : L1mState) (i : L1mIn) : BitVec 3 := l1mSt1W s i

/-- io.missReq.ready（:295）。 -/
def l1mReqReady (s : L1mState) (i : L1mIn) : Bool :=
  !(l1mSt1W s i == 1#3 || l1mSt1W s i == 3#3)
/-- io.missReq.fire。 -/
def l1mReqFire (s : L1mState) (i : L1mIn) : Bool := i.reqV && l1mReqReady s i

/-- entryMatchMissRsp（:136/:323）：直接取 missRspIn.bits.instrId 为 entry 号。 -/
def l1mRspSel (i : L1mIn) : Fin 4 := l1mOf4 i.rspIdx
/-- subentryStatusForRsp（:148-149,:312，作用于 rsp 选中行）。 -/
def l1mRspRow (s : L1mState) (i : L1mIn) : Fin 2 → Bool := s.subValid (l1mRspSel i)
def l1mRspUsed (s : L1mState) (i : L1mIn) : Nat := l1mCount2 (l1mRspRow s i)
def l1mNext2Cancel (s : L1mState) (i : L1mIn) : Fin 2 := l1mFirstOne2 (l1mRspRow s i)

/-- missRspOut_st1 enq（:333-337）：rsp 有效且该行还有 subentry。 -/
def l1mRspEnqV (s : L1mState) (i : L1mIn) : Bool := i.rspInV && (l1mRspUsed s i != 0)
def l1mRspEnqBits (s : L1mState) (i : L1mIn) : L1mRspBits :=
  ⟨s.ti (l1mRspSel i) (l1mNext2Cancel s i), s.blockAddr (l1mRspSel i), i.rspIdx.zeroExtend 3⟩

/-- io.missRspOut（:339，= missRspOut_st1.io.deq）。 -/
def l1mRspOutValid (s : L1mState) (i : L1mIn) : Bool := l1mQDeqValid s.rspQ (l1mRspEnqV s i)
def l1mRspOutBits (s : L1mState) (i : L1mIn) : L1mRspBits :=
  l1mQDeqBits s.rspQ (l1mRspEnqBits s i)
def l1mRspOutFire (s : L1mState) (i : L1mIn) : Bool := l1mRspOutValid s i && i.rspOutRdy

/-- missRspprobeReqSameBlock（:193，非 MMU 分支）。 -/
def l1mSameBlk (s : L1mState) (i : L1mIn) : Bool := i.probeBA == (l1mRspOutBits s i).ba

/-- io.missRspIn.ready（:319-321，`used >= 1.U` 写作 `!= 0`；中间析取项为死逻辑，Q2）。 -/
def l1mRspInReady (s : L1mState) (i : L1mIn) : Bool :=
  !((l1mRspUsed s i != 0) ||
    ((l1mSt1W s i == 4#3 || l1mSt1W s i == 3#3) && l1mRspUsed s i == 1) ||
    i.reqV)
/-- io.missRspIn.fire。 -/
def l1mRspInFire (s : L1mState) (i : L1mIn) : Bool := i.rspInV && l1mRspInReady s i

/-- mshrStatus_st0（:247-265）：对当前 probe 地址的组合状态（含 missReq.valid
    的预测性 full 判定，:248/:256）。 -/
def l1mStatusSt0 (s : L1mState) (i : L1mIn) : BitVec 3 :=
  if l1mPrimarySt0 s i then
    (if l1mMainFull s || (i.reqV && l1mMainAlmFull s) then 1#3 else 0#3)
  else
    (if l1mSubFull s i || (i.reqV && l1mSubAlmFull s i) then 3#3
     else if l1mSameBlk s i && l1mRspOutValid s i then 4#3
     else 2#3)

/-- mshrStatus_st1_r 更新（:212-245）。 -/
def l1mStatusRN (s : L1mState) (i : L1mIn) : BitVec 3 :=
  if l1mReqFire s i && !i.probeV && i.st2Rdy then
    (if l1mPrimary s i && l1mMainAlmFull s then 1#3
     else if l1mSecondary s i && l1mSubAlmFull s i then 3#3
     else s.statusR)
  else if i.probeV then
    (if l1mPrimarySt0 s i then
       (if l1mMainFull s || (l1mReqFire s i && l1mMainAlmFull s) then 1#3 else 0#3)
     else (if l1mSubFull s i then 3#3 else 2#3))
  else if i.rspInV then
    (if s.statusR == 1#3 || s.statusR == 2#3 then 0#3
     else if s.statusR == 3#3 && l1mRspUsed s i == 1 then 4#3
     else if s.statusR == 4#3 && l1mRspUsed s i == 0 then 0#3
     else s.statusR)
  else s.statusR

/-- real_SRAMAddrUp / real_SRAMAddrDown（:297-298）：targetInfo 写地址。 -/
def l1mRealUp (s : L1mState) (i : L1mIn) : BitVec 2 :=
  if l1mSecondary s i then l1mPriEnc4 (l1mSt1DeqBits s i).matchProbe
  else BitVec.ofNat 2 (l1mEntryNext s).val
def l1mRealDown (s : L1mState) (i : L1mIn) : BitVec 2 :=
  if l1mSecondary s i then (l1mSt1DeqBits s i).seIdx else 0#2

/-- io.probeOut_st1.a_source（:309；Mux 结果按 4 位计算后截断为 2 位，D5/Q6）。 -/
def l1mASource (s : L1mState) (i : L1mIn) : BitVec 2 :=
  if i.reqV then l1mRealUp s i else l1mMatchId s i

/-- io.empty（:112）。 -/
def l1mEmpty (s : L1mState) : Bool :=
  !(l1mEntryValid s 0 || l1mEntryValid s 1 || l1mEntryValid s 2 || l1mEntryValid s 3)
/-- io.probestatus（:113，= st1 队列 deq.valid；与 probeSt 寄存器无关，Q7）。 -/
def l1mProbestatus (s : L1mState) (i : L1mIn) : Bool := l1mSt1DeqValid s i
/-- io.releasing_stall（:111）。 -/
def l1mReleasingStall (s : L1mState) : Bool :=
  s.releasing 0 || s.releasing 1 || s.releasing 2 || s.releasing 3

/- ========================================================================= -/
/- 6. 单拍转移（:175-194,:284-292,:299-301,:345-366 + 两个队列）               -/
/- ========================================================================= -/

/-- 单拍转移。所有 RHS 按旧状态求值（Chisel 寄存器语义）。
    subentry_valid 的双层 for + elsewhen 挂接（:345-358）按 Q4 的实际语义：
    se=0 链为 {主分配置位, rsp 清除}；se=1 链为 {主分配置位(恒假), rsp 清除,
    次级合并置位}。 -/
def l1mStep (s : L1mState) (i : L1mIn) : L1mState where
  blockAddr :=  -- :188-191（非 MMU 分支）：reqFire && st1 队列 deq.ready && st1_w==PRIMARY_AVAIL
    if l1mReqFire s i && i.st1Rdy && l1mSt1W s i == 0#3 then
      l1mUpd s.blockAddr (l1mEntryNext s) i.reqBA
    else s.blockAddr
  instrId :=    -- :190，死状态（D7/Q7）
    if l1mReqFire s i && i.st1Rdy && l1mSt1W s i == 0#3 then
      l1mUpd s.instrId (l1mEntryNext s) i.reqII
    else s.instrId
  ti :=         -- :299-301：reqFire && deq.ready（无状态门控，Q1 的污染源）
    if l1mReqFire s i && i.st1Rdy then
      l1mUpd s.ti (l1mOf4 (l1mRealUp s i))
        (l1mUpd (s.ti (l1mOf4 (l1mRealUp s i))) (l1mOf2 (l1mRealDown s i)) i.reqTI)
    else s.ti
  subValid := fun e se =>  -- :345-358（挂接语义见 Q4）
    if (e == l1mEntryNext s) && (se == 0) && l1mReqFire s i &&
        l1mSt1DeqFire s i && l1mPrimary s i then true                       -- :347-349 主分配
    else if (e == l1mRspSel i) && (se == l1mNext2Cancel s i) && i.rspInV &&
        l1mQEnqRdy s.rspQ then false                                        -- :350-353 rsp 清除
    else if (se == 1) && (l1mOf2 (l1mSt1DeqBits s i).seIdx == 1) &&
        l1mReqFire s i && l1mSecondary s i && l1mSt1DeqFire s i &&
        (e == l1mOf4 (l1mMatchId s i)) then true                            -- :354-356 次级合并
    else s.subValid e se
  st1Q := l1mQStep s.st1Q i.probeV (l1mSt1EnqBits s i) i.st1Rdy             -- :207-210
  rspQ := l1mQStep s.rspQ (l1mRspEnqV s i) (l1mRspEnqBits s i) i.rspOutRdy  -- :332-339
  statusR := l1mStatusRN s i                                              -- :212-245
  probeSt :=  -- :284-292（Q7：只自引用）
    if i.probeV && !s.probeSt then true
    else if s.probeSt then
      (if (i.probeBA != i.reqBA) && l1mReqFire s i then i.probeV
       else if l1mReqFire s i then false
       else s.probeSt)
    else s.probeSt
  releasing := fun e =>  -- :360-366
    if (e == l1mRspSel i) && l1mRspInFire s i && s.releasing e then false
    else if (e == l1mRspSel i) && i.rspInV && !s.releasing e then true
    else s.releasing e

/-- 多拍执行。 -/
def l1mRun (s : L1mState) (is : List L1mIn) : L1mState := is.foldl l1mStep s

/- ========================================================================= -/
/- 7. 具体数值测试                                                            -/
/- ========================================================================= -/

section L1mTests

/- ---- T1：主 miss 分配（DCache 空流水线单拍穿透流程：probe 与 missReq 同拍，
     st1 队列 pipe 旁路） ---- -/

def l1mI1 : L1mIn := ⟨true, 0x10#25, true, 0x10#25, 5#3, 0xBEEF#323, false, 0, false, true, true⟩
def l1mS1 := l1mStep l1mInit l1mI1

-- 同拍输出：probeStatus=PRIMARY_AVAIL(0)，a_source=分配的 entry 0，probestatus=1
theorem l1mT1_outputs :
    l1mProbeStatus l1mInit l1mI1 = 0#3 ∧
    l1mASource l1mInit l1mI1 = 0#2 ∧
    l1mProbestatus l1mInit l1mI1 = true ∧
    l1mReqFire l1mInit l1mI1 = true := by
  native_decide

-- 拍后状态：subentry(0,0) 置位、blockAddr/instrId/targetInfo 落表、st1 队列穿透不积压
theorem l1mT1_alloc :
    l1mS1.subValid ⟨0, by decide⟩ ⟨0, by decide⟩ = true ∧
    l1mEntryValid l1mS1 ⟨0, by decide⟩ = true ∧
    l1mS1.blockAddr ⟨0, by decide⟩ = 0x10#25 ∧
    l1mS1.instrId ⟨0, by decide⟩ = 5#3 ∧
    l1mS1.ti ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xBEEF#323 ∧
    l1mEmpty l1mS1 = false ∧
    l1mEntryNext l1mS1 = ⟨1, by decide⟩ ∧
    l1mS1.st1Q.full = false ∧
    l1mS1.statusR = 0#3 := by
  native_decide

/- ---- T2：次级 miss 合并（同块第二请求：不新占 entry、不重复访存） ---- -/

def l1mI2 : L1mIn := ⟨true, 0x10#25, true, 0x10#25, 6#3, 0xCAFE#323, false, 0, false, true, true⟩
def l1mS2 := l1mStep l1mS1 l1mI2

-- 同拍输出：probeStatus=SECONDARY_AVAIL(2)；a_source=匹配到的 entry 0（不发新 L2 请求）；
-- st0=3（预测性 SECONDARY_FULL：本拍 fire 后 subentry 将满，挡下一同块请求）
theorem l1mT2_outputs :
    l1mProbeStatus l1mS1 l1mI2 = 2#3 ∧
    l1mASource l1mS1 l1mI2 = 0#2 ∧
    l1mStatusSt0 l1mS1 l1mI2 = 3#3 ∧
    l1mReqFire l1mS1 l1mI2 = true := by
  native_decide

-- 拍后状态：subentry(0,1) 置位（合并成功）；blockAddr 表不变（不新占 entry）；
-- targetInfo 记入 (0,1)；statusR=SECONDARY_AVAIL
theorem l1mT2_merge :
    l1mS2.subValid ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
    l1mS2.subValid ⟨0, by decide⟩ ⟨0, by decide⟩ = true ∧
    l1mS2.blockAddr ⟨0, by decide⟩ = 0x10#25 ∧
    l1mS2.ti ⟨0, by decide⟩ ⟨1, by decide⟩ = 0xCAFE#323 ∧
    l1mS2.statusR = 2#3 ∧
    l1mEntryNext l1mS2 = ⟨1, by decide⟩ := by
  native_decide

/- ---- T3（Q1 witness）：st1_r=SECONDARY_AVAIL 且 subentry 已满时，
     missReq.ready 仍为 1（与 st0=SECONDARY_FULL 矛盾），次级 fire 不记录
     任何 subentry 且覆盖 targetInfo[0][0] ---- -/

def l1mI3 : L1mIn := ⟨true, 0x10#25, true, 0x10#25, 7#3, 0xDEAD#323, false, 0, false, true, true⟩
def l1mS3 := l1mStep l1mS2 l1mI3

-- 反压不一致：st0 报告 SECONDARY_FULL(3)，但 missReq.ready=1（fire 成立）
theorem l1mT7_ready_inconsistent :
    l1mStatusSt0 l1mS2 l1mI3 = 3#3 ∧
    l1mReqReady l1mS2 l1mI3 = true ∧
    l1mReqFire l1mS2 l1mI3 = true := by
  native_decide

-- 请求丢失：合并置位不生效（seIdx=0，:354 只挂 se=1），subValid 一行原样保留
theorem l1mT7_reqLost :
    l1mS3.subValid ⟨0, by decide⟩ ⟨0, by decide⟩ = true ∧
    l1mS3.subValid ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
    l1mRspUsed l1mS2 l1mI3 = 2 := by
  native_decide

-- targetInfo 污染：realDown=0 ⇒ reqTI 覆盖 subentry(0,0) 的 targetInfo
theorem l1mT7_tiCorrupt :
    l1mS2.ti ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xBEEF#323 ∧
    l1mS3.ti ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xDEAD#323 ∧
    l1mS3.statusR = 3#3 := by
  native_decide

/- ---- T4：主 entry 满反压（PRIMARY_FULL） ---- -/

def l1mSFull : L1mState := { l1mInit with
  subValid := fun _ se => se == ⟨0, by decide⟩,
  blockAddr := fun e => BitVec.ofNat 25 (e.val + 1),
  statusR := 1#3 }

def l1mI4 : L1mIn := ⟨true, 0x40#25, true, 0x40#25, 0, 0, false, 0, false, true, true⟩

-- 4 个 entry 全有效：st0=PRIMARY_FULL(1)，missReq.ready=0（新块被拒）
theorem l1mT4_full_backpressure :
    l1mMainFull l1mSFull = true ∧
    l1mStatusSt0 l1mSFull l1mI4 = 1#3 ∧
    l1mReqReady l1mSFull l1mI4 = false ∧
    l1mReqFire l1mSFull l1mI4 = false := by
  native_decide

/- ---- T5：响应回放式排空（一个 L2 响应 → 每 subentry 一个 missRspOut，
     低位 subentry 先出；排空后 memRsp 才 pop，releasing_stall 置位/清零配对） ---- -/

def l1mSDrain : L1mState := { l1mInit with
  subValid := fun e _ => e == ⟨0, by decide⟩,
  blockAddr := fun e => if e == ⟨0, by decide⟩ then 0x10#25 else 0,
  ti := fun e se => if e == ⟨0, by decide⟩ then
      (if se == ⟨0, by decide⟩ then 0x111#323 else 0x222#323) else 0,
  statusR := 3#3 }

def l1mI5 : L1mIn := ⟨false, 0, false, 0, 0, 0, true, 0#2, true, true, true⟩

def l1mSD1 := l1mStep l1mSDrain l1mI5
def l1mSD2 := l1mStep l1mSD1 l1mI5
def l1mSD3 := l1mStep l1mSD2 l1mI5

-- 拍 0：rspOut 穿透输出 subentry0 的响应（ti=0x111）；missRspIn.ready=0（used≥1，
-- memRsp 不 pop）；subentry0 清除；releasing_stall(0) 置位
theorem l1mT5_drain0 :
    l1mRspOutValid l1mSDrain l1mI5 = true ∧
    (l1mRspOutBits l1mSDrain l1mI5).ti = 0x111#323 ∧
    (l1mRspOutBits l1mSDrain l1mI5).ba = 0x10#25 ∧
    l1mRspInReady l1mSDrain l1mI5 = false ∧
    l1mSD1.subValid ⟨0, by decide⟩ ⟨0, by decide⟩ = false ∧
    l1mSD1.subValid ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
    l1mSD1.releasing ⟨0, by decide⟩ = true ∧
    l1mReleasingStall l1mSD1 = true ∧
    l1mSD1.statusR = 3#3 := by
  native_decide

-- 拍 1：第二个响应输出 subentry1 的响应（ti=0x222）；used==1 且 statusR==3
-- ⇒ statusR 转 SECONDARY_FULL_RETURN(4)（:240-241）
theorem l1mT5_drain1 :
    l1mRspOutValid l1mSD1 l1mI5 = true ∧
    (l1mRspOutBits l1mSD1 l1mI5).ti = 0x222#323 ∧
    l1mSD2.subValid ⟨0, by decide⟩ ⟨1, by decide⟩ = false ∧
    l1mEmpty l1mSD2 = true ∧
    l1mSD2.statusR = 4#3 := by
  native_decide

-- 拍 2：used==0 ⇒ 不再输出（rspOut.valid=0）；missRspIn.ready=1，memRsp pop
-- （fire）；releasing_stall(0) 清零；statusR 回 PRIMARY_AVAIL(0)（:242-243）
theorem l1mT5_drain2 :
    l1mRspOutValid l1mSD2 l1mI5 = false ∧
    l1mRspInFire l1mSD2 l1mI5 = true ∧
    l1mSD3.releasing ⟨0, by decide⟩ = false ∧
    l1mReleasingStall l1mSD3 = false ∧
    l1mSD3.statusR = 0#3 := by
  native_decide

/- ---- T6：1 深 pipe 队列行为回归 ---- -/

theorem l1mT6_q_passthrough :  -- 空且 deq 就绪：同拍穿透，不落寄存器
    l1mQDeqValid (l1mQInit (0#8)) true = true ∧
    l1mQDeqBits (l1mQInit (0#8)) 0xA5#8 = 0xA5#8 ∧
    (l1mQStep (l1mQInit (0#8)) true 0xA5#8 true).full = false := by
  native_decide

theorem l1mT6_q_hold :  -- deq 不就绪：落寄存器；下一拍可取
    (l1mQStep (l1mQInit (0#8)) true 0xA5#8 false).full = true ∧
    l1mQDeqBits (l1mQStep (l1mQInit (0#8)) true 0xA5#8 false) 0#8 = 0xA5#8 ∧
    (l1mQStep (l1mQStep (l1mQInit (0#8)) true 0xA5#8 false) false 0#8 true).full = false := by
  native_decide

/- ---- 组合逻辑小测试 ---- -/

example : l1mPriEnc4 0b0000#4 = 0#2 := by decide
example : l1mPriEnc4 0b0001#4 = 0#2 := by decide
example : l1mPriEnc4 0b1010#4 = 1#2 := by decide
example : l1mPriEnc4 0b1000#4 = 3#2 := by decide

end L1mTests

/- ========================================================================= -/
/- 8. 符号化定理                                                              -/
/- ========================================================================= -/

section L1mThms

/- ---- 8.1 missRspIn.ready 死逻辑消除（Q2，:319-321） ---- -/

/-- :319 的中间析取项 ((st1_w==4||st1_w==3) && used==1) 被 used≥1 蕴含，
    ready 等价于 !(used≠0 || missReq.valid)。 -/
theorem l1m_rspInReady_simplify (s : L1mState) (i : L1mIn) :
    l1mRspInReady s i = !((l1mRspUsed s i != 0) || i.reqV) := by
  simp only [l1mRspInReady, l1mRspUsed, l1mRspRow, l1mCount2]
  by_cases h0 : s.subValid (l1mRspSel i) 0 <;>
  by_cases h1 : s.subValid (l1mRspSel i) 1 <;>
  by_cases hb : (l1mSt1W s i == 4#3 || l1mSt1W s i == 3#3) <;>
  by_cases hr : i.reqV <;> simp_all

/- ---- 8.2 :296 的 assert（Req 与 Rsp 不同拍 fire） ---- -/

/-- missRspIn.ready 含 !missReq.valid（:321），故 reqFire ⇒ ¬rspInFire，
    :296 的 assert 由构造保证。 -/
theorem l1m_reqFire_not_rspInFire (s : L1mState) (i : L1mIn)
    (hf : l1mReqFire s i = true) :
    l1mRspInFire s i = false := by
  have hreq : i.reqV = true := by simp [l1mReqFire] at hf; exact hf.1
  simp [l1mRspInFire, l1mRspInReady, hreq]

/- ---- 8.3 missRspOut 握手合规（I-22 对照，正面结论） ---- -/

/-- NoWithdraw：missRspOut.valid 高且未 fire 时，下一拍 valid 必保持——
    1 深 pipe 队列 enq.ready=!full 与 deq.ready 解耦，valid 高未接收的数据
    必落入寄存器（对照 Mem/MSHR.lean 的 mshr_noWithdraw_violated）。 -/
theorem l1m_rspOut_noWithdraw (s : L1mState) (i i' : L1mIn)
    (hv : l1mRspOutValid s i = true) (hr : i.rspOutRdy = false) :
    l1mRspOutValid (l1mStep s i) i' = true := by
  cases hf : s.rspQ.full
  · have hev : l1mRspEnqV s i = true := by
      simp [l1mRspOutValid, l1mQDeqValid, hf] at hv; exact hv
    simp [l1mRspOutValid, l1mQDeqValid, l1mStep, l1mQStep, hf, hr, hev]
  · simp [l1mRspOutValid, l1mQDeqValid, l1mStep, l1mQStep, hf, hr]

/-- Stable：valid 高且未 fire 时 bits 不变（同上机理）。 -/
theorem l1m_rspOut_stable (s : L1mState) (i i' : L1mIn)
    (hv : l1mRspOutValid s i = true) (hr : i.rspOutRdy = false) :
    l1mRspOutBits (l1mStep s i) i' = l1mRspOutBits s i := by
  cases hf : s.rspQ.full
  · have hev : l1mRspEnqV s i = true := by
      simp [l1mRspOutValid, l1mQDeqValid, hf] at hv; exact hv
    simp [l1mRspOutBits, l1mQDeqBits, l1mStep, l1mQStep, hf, hr, hev]
  · simp [l1mRspOutBits, l1mQDeqBits, l1mStep, l1mQStep, hf, hr]

/- ---- 8.4 满时反压（st0 组合状态，:247-265） ---- -/

/-- 主 miss 且 4 entry 全有效 ⇒ st0=PRIMARY_FULL(1)，DCache 据此拦 coreReq。 -/
theorem l1m_st0_primary_full (s : L1mState) (i : L1mIn)
    (hp : l1mPrimarySt0 s i = true) (hf : l1mMainFull s = true) :
    l1mStatusSt0 s i = 1#3 := by
  simp [l1mStatusSt0, hp, hf]

/-- 次级 miss 且该行 subentry 满 ⇒ st0=SECONDARY_FULL(3)。 -/
theorem l1m_st0_secondary_full (s : L1mState) (i : L1mIn)
    (hp : l1mPrimarySt0 s i = false) (hf : l1mSubFull s i = true) :
    l1mStatusSt0 s i = 3#3 := by
  simp [l1mStatusSt0, hp, hf]

/- ---- 8.5 分配安全：entryNext 必空闲 ---- -/

/-- 主表未满时 entryStatus.next（indexWhere false，:60）指向无效 entry。 -/
theorem l1mEntryNext_invalid (s : L1mState) (h : l1mMainFull s = false) :
    l1mEntryValid s (l1mEntryNext s) = false := by
  unfold l1mEntryNext l1mMainFull at *
  cases h0 : l1mEntryValid s 0 <;> cases h1 : l1mEntryValid s 1 <;>
    cases h2 : l1mEntryValid s 2 <;> cases h3 : l1mEntryValid s 3 <;>
    simp_all

/- ---- 8.6 next2cancel 必命中有效 subentry ---- -/

/-- 行内有有效 subentry 时，next2cancel（indexWhere true，:69）指向其一。 -/
theorem l1mFirstOne2_spec (row : Fin 2 → Bool)
    (h : row 0 = true ∨ row 1 = true) :
    row (l1mFirstOne2 row) = true := by
  cases h0 : row 0 <;> cases h1 : row 1 <;>
    simp_all [l1mFirstOne2]

/- ---- 8.7 OHToUInt 命中性（D3） ---- -/

/-- 非零匹配向量的 priEnc 结果必指向置位位。 -/
theorem l1mPriEnc4_hit (v : BitVec 4) (h : v ≠ 0#4) :
    (v >>> (l1mPriEnc4 v).zeroExtend 4) &&& 1#4 = 1#4 := by
  simp only [l1mPriEnc4]; bv_decide

/- ---- 8.8 主分配（:188-191,:299-301,:347-349） ---- -/

/-- 主 miss fire：entryNext 的 subentry0 置位、blockAddr/targetInfo 落表。
    （无重复分配：entryNext 空闲由 l1mEntryNext_invalid 保证。） -/
theorem l1m_primary_alloc (s : L1mState) (i : L1mIn)
    (hf : l1mReqFire s i = true) (hprim : l1mSecondary s i = false)
    (hdeq : l1mSt1DeqFire s i = true)
    (hw : l1mSt1W s i = 0#3) (hst1r : i.st1Rdy = true) :
    (l1mStep s i).subValid (l1mEntryNext s) 0 = true ∧
    (l1mStep s i).blockAddr (l1mEntryNext s) = i.reqBA ∧
    (l1mStep s i).ti (l1mEntryNext s) 0 = i.reqTI := by
  have hp : l1mPrimary s i = true := by simp [l1mPrimary, hprim]
  have hru : l1mOf4 (l1mRealUp s i) = l1mEntryNext s := by
    unfold l1mRealUp
    rw [if_neg (by simp [hprim]), l1mOf4_ofNat_val]
  have hrd : l1mOf2 (l1mRealDown s i) = (0 : Fin 2) := by
    unfold l1mRealDown
    rw [if_neg (by simp [hprim]), l1mOf2_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp [l1mStep, hf, hdeq, hp]
  · simp [l1mStep, hf, hst1r, hw, l1mUpd]
  · simp [l1mStep, hf, hst1r, hru, hrd, l1mUpd]

/- ---- 8.9 次级合并（:354-356,:299-301）：不新占 entry、不重发 L2 请求 ---- -/

/-- 次级 miss fire（与 rsp 不同拍，:296 的正常情形）：blockAddr 表不变
    （不新占 entry）；subentry 记入"fire 拍按 reqBA 重算的匹配行"的 se1；
    targetInfo 写入"probe 拍 st1 队列冻结的匹配行"的 seIdx（Q5：两者
    在正常流程一致，异常时序可错位，模型如实给出两处地址）。 -/
theorem l1m_secondary_merge (s : L1mState) (i : L1mIn)
    (hf : l1mReqFire s i = true) (hsec : l1mSecondary s i = true)
    (hdeq : l1mSt1DeqFire s i = true) (hst1r : i.st1Rdy = true)
    (hrsp : i.rspInV = false)
    (hidx : l1mOf2 (l1mSt1DeqBits s i).seIdx = 1)
    (hw : l1mSt1W s i ≠ 0#3) :
    (l1mStep s i).blockAddr = s.blockAddr ∧
    (l1mStep s i).subValid (l1mOf4 (l1mMatchId s i)) 1 = true ∧
    (l1mStep s i).ti (l1mOf4 (l1mPriEnc4 (l1mSt1DeqBits s i).matchProbe))
        1 = i.reqTI := by
  have hcond : (l1mReqFire s i && i.st1Rdy && l1mSt1W s i == 0#3) = false := by
    simp [hf, hst1r, beq_eq_false_iff_ne, hw]
  have hru : l1mRealUp s i = l1mPriEnc4 (l1mSt1DeqBits s i).matchProbe := by
    unfold l1mRealUp; exact if_pos hsec
  have hrd : l1mRealDown s i = (l1mSt1DeqBits s i).seIdx := by
    unfold l1mRealDown; exact if_pos hsec
  refine ⟨?_, ?_, ?_⟩
  · funext e; simp [l1mStep, hcond]
  · simp [l1mStep, hf, hsec, hdeq, hrsp, hidx]
  · simp [l1mStep, hf, hst1r, hru, hrd, hidx, l1mUpd]

/- ---- 8.10 响应消费（:350-353）：分配/释放配对 ---- -/

/-- 清位计数：清掉一个有效位后 PopCount 恰减一。 -/
theorem l1mCount2_clear (row : Fin 2 → Bool) (k : Fin 2) (hk : row k = true) :
    l1mCount2 (fun se => if se == k then false else row se) = l1mCount2 row - 1 := by
  have hk01 : k = 0 ∨ k = 1 := by
    have h : k.val = 0 ∨ k.val = 1 := by have := k.isLt; omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hk01 with rfl | rfl <;>
    cases h0 : row 0 <;> cases h1 : row 1 <;> simp_all [l1mCount2]

/-- rsp 消费拍（rspInValid && rspQ 可入队、无同拍 missReq）：
    最低有效 subentry 被清，该行 used 恰减一（分配/释放严格配对）。 -/
theorem l1m_rsp_consume (s : L1mState) (i : L1mIn)
    (hv : i.rspInV = true) (hq : l1mQEnqRdy s.rspQ = true) (hreq : i.reqV = false)
    (hused : l1mRspUsed s i ≠ 0) :
    (l1mStep s i).subValid (l1mRspSel i) (l1mNext2Cancel s i) = false ∧
    l1mCount2 ((l1mStep s i).subValid (l1mRspSel i)) = l1mRspUsed s i - 1 := by
  have hrf : l1mReqFire s i = false := by simp [l1mReqFire, hreq]
  have hrow : ∀ se, (l1mStep s i).subValid (l1mRspSel i) se =
      (if se == l1mNext2Cancel s i then false else s.subValid (l1mRspSel i) se) := by
    intro se
    simp [l1mStep, hrf, hv, hq]
  have hsom : s.subValid (l1mRspSel i) 0 = true ∨
      s.subValid (l1mRspSel i) 1 = true := by
    cases h0 : s.subValid (l1mRspSel i) 0 <;>
      cases h1 : s.subValid (l1mRspSel i) 1 <;>
      simp_all [l1mRspUsed, l1mRspRow, l1mCount2]
  have hvalid : s.subValid (l1mRspSel i) (l1mNext2Cancel s i) = true :=
    l1mFirstOne2_spec _ hsom
  constructor
  · rw [hrow]; simp
  · rw [funext hrow]
    exact l1mCount2_clear _ _ hvalid

/- ---- 8.11 同块唯一性不变式（:196 assert 的不变式形式） ---- -/

/-- 不变式：任意两个有效 entry 的 blockAddr 不同（环境契约：次级合并只在
    probe 命中时发生，主分配地址必为新块；DCache 由 st0 流控保证）。 -/
def l1mDistinct (s : L1mState) : Prop :=
  ∀ e e' : Fin 4, l1mEntryValid s e = true → l1mEntryValid s e' = true →
    e ≠ e' → s.blockAddr e ≠ s.blockAddr e'

/-- 不变式下同一地址至多匹配一个 entry。 -/
theorem l1mMatchBit_unique (s : L1mState) (ba : BitVec 25) (hd : l1mDistinct s)
    {e e' : Fin 4} (hne : e ≠ e')
    (h1 : l1mMatchBit s ba e = true) (h2 : l1mMatchBit s ba e' = true) : False := by
  simp only [l1mMatchBit, Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact (hd e e' h1.2 h2.2 hne) (h1.1.trans h2.1.symm)

/-- :196 的 assert（PopCount(entryMatchProbe) ≤ 1）在不变式下成立。 -/
theorem l1mMatchProbe_cpop_le_one (s : L1mState) (ba : BitVec 25)
    (hd : l1mDistinct s) : (l1mMatchProbe s ba).cpop ≤ 1#4 := by
  by_cases h0 : l1mMatchBit s ba 0 <;> by_cases h1 : l1mMatchBit s ba 1 <;>
    by_cases h2 : l1mMatchBit s ba 2 <;> by_cases h3 : l1mMatchBit s ba 3 <;>
    simp only [l1mMatchProbe, h0, h1, h2, h3] <;>
    first
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h0 h1)
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h0 h2)
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h0 h3)
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h1 h2)
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h1 h3)
    | (exfalso; exact l1mMatchBit_unique s ba hd (by decide) h2 h3)
    | decide

/-- 不变式保持（主分配拍）：reqBA 对所有有效 entry 为新块时，
    分配后唯一性仍成立（"不重"的归纳步）。 -/
theorem l1mDistinct_step_primary (s : L1mState) (i : L1mIn)
    (hd : l1mDistinct s)
    (hf : l1mReqFire s i = true) (hprim : l1mSecondary s i = false)
    (hdeq : l1mSt1DeqFire s i = true)
    (hw : l1mSt1W s i = 0#3) (hst1r : i.st1Rdy = true)
    (hrsp : i.rspInV = false)
    (hfresh : ∀ e : Fin 4, l1mEntryValid s e = true → s.blockAddr e ≠ i.reqBA) :
    l1mDistinct (l1mStep s i) := by
  have hp' : l1mPrimary s i = true := by simp [l1mPrimary, hprim]
  have hba : ∀ e, (l1mStep s i).blockAddr e =
      (if l1mEntryNext s = e then i.reqBA else s.blockAddr e) := by
    intro e; simp [l1mStep, hf, hst1r, hw, l1mUpd]
  have hsv : ∀ e se, (l1mStep s i).subValid e se =
      (if (e == l1mEntryNext s) && (se == 0) then true
       else s.subValid e se) := by
    intro e se
    simp [l1mStep, hf, hdeq, hp', hrsp, hprim]
  have hev : ∀ e, l1mEntryValid (l1mStep s i) e =
      (if (e == l1mEntryNext s) then true else l1mEntryValid s e) := by
    intro e
    simp only [l1mEntryValid, hsv]
    cases he : (e == l1mEntryNext s) <;>
      cases h0 : s.subValid e 0 <;>
      cases h1 : s.subValid e 1 <;> simp_all
  intro e e' he he' hne
  rw [hev e] at he; rw [hev e'] at he'
  rw [hba e, hba e']
  by_cases hce : l1mEntryNext s = e
  · rw [if_pos hce]
    by_cases hce' : l1mEntryNext s = e'
    · exact absurd (hce ▸ hce') (fun h => hne h)
    · rw [if_neg hce']
      have hbe : (e' == l1mEntryNext s) = false := by
        simp [beq_eq_false_iff_ne]; exact fun h => hce' h.symm
      rw [hbe] at he'; simp at he'
      exact fun h => hfresh e' he' h.symm
  · rw [if_neg hce]
    by_cases hce' : l1mEntryNext s = e'
    · rw [if_pos hce']
      have hbe : (e == l1mEntryNext s) = false := by
        simp [beq_eq_false_iff_ne]; exact fun h => hce h.symm
      rw [hbe] at he; simp at he
      exact hfresh e he
    · rw [if_neg hce']
      have hbe : (e == l1mEntryNext s) = false := by
        simp [beq_eq_false_iff_ne]; exact fun h => hce h.symm
      have hbe' : (e' == l1mEntryNext s) = false := by
        simp [beq_eq_false_iff_ne]; exact fun h => hce' h.symm
      rw [hbe] at he; rw [hbe'] at he'; simp at he he'
      exact hd e e' he he' hne

/- ---- 8.12 Q1 的符号化形式：反压不一致 ---- -/

/-- Q1：st1_r=SECONDARY_AVAIL(2) 且次级匹配行的 subentry 已满时，
    :274 的重算条件不含 st1_r==2 ⇒ missReq.ready=1，而同拍 st0=SECONDARY_FULL(3)。
    （T3/l1mT7_* 给出该状态的从初态三拍可达 witness。） -/
theorem l1m_q1_ready_inconsistent (s : L1mState) (i : L1mIn)
    (hsr : s.statusR = 2#3) (hsec : l1mSecondary s i = true)
    (hprim0 : l1mPrimarySt0 s i = false) (hfull : l1mSubFull s i = true) :
    l1mReqReady s i = true ∧ l1mStatusSt0 s i = 3#3 := by
  have hw : l1mSt1W s i = 2#3 := by
    simp only [l1mSt1W, hsec, hsr]
    bv_decide
  constructor
  · simp only [l1mReqReady, hw]; decide
  · simp [l1mStatusSt0, hprim0, hfull]

end L1mThms

/- ---- 公理审计（native_decide 测试含 Lean.ofReduceBool，属预期） ---- -/

#print axioms l1m_rspInReady_simplify
#print axioms l1m_reqFire_not_rspInFire
#print axioms l1m_rspOut_noWithdraw
#print axioms l1m_rspOut_stable
#print axioms l1m_st0_primary_full
#print axioms l1m_st0_secondary_full
#print axioms l1mEntryNext_invalid
#print axioms l1mFirstOne2_spec
#print axioms l1mPriEnc4_hit
#print axioms l1m_primary_alloc
#print axioms l1m_secondary_merge
#print axioms l1m_rsp_consume
#print axioms l1mMatchProbe_cpop_le_one
#print axioms l1mDistinct_step_primary
#print axioms l1m_q1_ready_inconsistent

end Ventus.Mem
