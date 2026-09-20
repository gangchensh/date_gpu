/- ========================================================================= -/
/-                        L2/L2Channels.lean                                 -/
/-  L2Cache 通道小件群（SinkA/SinkD/SourceA/QueuedRequest/Hold/ListBuffer）   -/
/-  的 Lean 4 模型、数值回归与符号定理                                        -/
/-                                                                           -/
/-  Chisel 源码对照（前缀 opengpgpu/original/ventus-gpgpu/ventus/src/）：      -/
/-    L2cache/SinkA.scala(111)、SinkD.scala(79)、SourceA.scala(55)、          -/
/-    QueuedRequest.scala(64)、Hold.scala(23)、ListBuffer.scala(122)、        -/
/-    L2cache/Parameters.scala(432，参数定义)、top/parameters.scala(例化)      -/
/-                                                                           -/
/- ======================== 例化参数（建模常量以此为准） ===================== -/
/-  top/parameters.scala:99-116：                                             -/
/-    l2cache_NSets=64(:99)、l2cache_NWays=16(:101)、                         -/
/-    l2cache_BlockWords=dcache_BlockWords=32(:103,:75) →                     -/
/-    blockBytes=32<<2=128、beatBytes=128(:113，inner beat=block)             -/
/-    writeBytes=1(:105)、memCycles=32(:107)、portFactor=2(:109)              -/
/-    num_l2cache=1(:132) → l2cBits=log2Ceil(1)=0；MMU_ENABLED=false(:15)     -/
/-    → addressBits=32(Parameters.scala:179)                                  -/
/-  Parameters.scala 派生：op_bits=3(:155)、source_bits=16(:159)、            -/
/-    data_bits=1024(:160)、mask_bits=128(:161)、size_bits=7(:162)、          -/
/-    putLists=32(:166)、putBeats=max(2*1,32)=32(:167)、putBits=5(:193)、     -/
/-    wayBits=4/setBits=6/offsetBits=7/tagBits=19(:188-192)、blockBeats=1     -/
/-    (CacheParameters:43)。mshrs=max(2,32)=32(:427,:429-431)。               -/
/-  ListBuffer 全部例化（2026-08-29 全仓 grep）：                              -/
/-    SinkA.scala:50  putbuffer（queues=32, entries=32, bypass=false,         -/
/-      singleport=true）；Scheduler.scala:89 requests（queues=mshrs=32,      -/
/-      entries=secondary=32, bypass=false, singleport=true）。               -/
/-    → bypass=true 路径（:91 数据旁路、:118 跳过状态更新）与 singleport=false -/
/-    路径（pop2/data2/index，:41-43,:84-88,:97-99,:108-116）全仓无例化，     -/
/-    属死代码，本文件只建模 bypass=false && singleport=true 实例（Q2/Q3）。  -/
/-                                                                           -/
/- ======================== SRAMTemplate.scala 逐行 diff 结论 ================ -/
/-  `diff src/SRAMTemplate/SRAMTemplate.scala src/L2cache/SRAMTemplate.scala` -/
/-  仅两行差异：package 名（:28）与 `import freechips.rocketchip.tilelink.    -/
/-  LFSR64`（L2 版多出的 :32）。结论：与 L1 版结构同构，差异点清单：          -/
/-  1. LFSR64 解析到 rocketchip 版（L1 版解析到同包 SRAMTemplate/LFSR64.scala）-/
/-     ——种子/抽头实现细节不同，"同拍同址读写出与数据无关的伪随机值"定性       -/
/-     结论不变（既有模型 Ventus/Mem/SRAMTemplate.lean 头注 D4 已记载）。     -/
/-  2. 其余 166 行逐字相同：writeBytes 不出现在本文件（掩码粒度由调用方        -/
/-     BankedStore 以 waymask 表达，与本模板无关）；bypassWrite/singlePort     -/
/-     参数语义两版一致。L2 例化 cc_banks(F,F,F,F)、cc_dir(T,T,F,T) 已由       -/
/-     Ventus/Mem/SRAMTemplate.lean 的 sramCfgL2Bank/sramCfgL2Dir 覆盖。      -/
/-  → 本文件不重复建模 SRAMTemplate，直接复用 Ventus.Mem.SRAMTemplate。       -/
/-  Hold.scala 的 ReadAndHold(SyncReadMem) 机制（:22）即 L1 模型中的           -/
/-  holdData/prevRealRen 机制（en=RegNext(realRen)），已由该文件覆盖；        -/
/-  本文件只建模 HoldUnless 本体。                                            -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. spike_info（SPIKE_OUTPUT=true，top/parameters.scala:11）是 spike       -/
/-      协同仿真的带外调试信号，不进入 RTL 功能语义，不建模（SinkA.scala:92、 -/
/-      SourceA.scala:54、QueuedRequest.scala:30 的 .foreach 赋值相应省略）。 -/
/-  D2. l2cBits=0 → FullRequest.l2cidx 为 UInt(0.W)（QueuedRequest.scala:45），-/
/-      建模为 BitVec 0；parseAddress 的 l2c 分量恒 0.U（Parameters.scala:224 -/
/-      的 if(l2cBits!=0) else 分支），模型只返回 tag/set/offset 三个有效量。 -/
/-  D3. Chisel Mem（ListBuffer 的 head/tail/next/data，:46-50）上电初值未定， -/
/-      模型 init 为 0/default（同 L1 SRAM 模型 D8）；valid/used 有 RegInit 0 -/
/-      （:45,:48），复位后未 push 的队列不会被 pop（assert :96 契约），       -/
/-      定理结论不依赖未定初值。                                              -/
/-  D4. SinkA freeOH（SinkA.scala:59）与 ListBuffer freeOH（ListBuffer.scala:52）-/
/-      原文为 (~(leftOR(~x)<<1)) & ~x，左移后 33 位赋给 32 位 wire 有截断    -/
/-      （见 Q1：被截位恒 0，无害）。模型采用等值的无截断形式 x&&&(0-x)      -/
/-      （lowest-set-bit 标准恒等式），正确性由 lbLowestOne_spec 钉死。       -/
/-  D5. OHToUInt（SinkA.scala:60、ListBuffer.scala:53）建模为 lbCtz（数低位   -/
/-      连续 0）；OHToUInt(0)=0，lbCtz(0)=n，但 entries=2^eBits 时             -/
/-      BitVec.ofNat eBits n = 0，取值一致；且 freeOH=0 时 push 本就不 fire。 -/
/-  D6. ListBuffer 同拍 push+pop 的 Mem 同址读写：push 写 entry=freeIdx（used  -/
/-      的空位）、pop 读 entry=head（used 的占位），二者必不同址（:106 的     -/
/-      Mux 又覆盖了"单元素队列同队 push+pop"），故模型按"读旧值"语义无歧义。 -/
/-      head 的两次写（:75 push 支、:106 pop 支）同拍同址仅当 push 队列=pop   -/
/-      队列且该队列无效——违反 :96 assert 契约，模型按源码顺序后写覆盖。    -/
/-  D7. io.empty（SinkA.scala:107）取 lists 的"下一拍值"判零（含当拍           -/
/-      lists_set/lists_clr），模型照此建模（sinkAListsN==0）。               -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区） ============================ -/
/-  Q1（疑点澄清，位宽族对照 I-11/I-21）：SinkA.scala:58-59 显式声明            -/
/-    `freeOH : UInt(putLists.W)` 再赋 33 位的 ~(leftOR(...)<<1)&...，截断    -/
/-    位 = ~leftOR(~lists)(31) & (~lists)(32)，后者为 0（32 位零扩展），故     -/
/-    恒截去 0，无害。ListBuffer.scala:52 同式为 val 自动推断，无截断。        -/
/-    非 bug；模型的 x&&&(0-x) 形式由 lbLowestOne_spec 完整刻画。             -/
/-  Q2（死代码标注）：ListBuffer bypass=true 路径全仓无例化（见例化核查）。    -/
/-    其 :118 跳过状态更新语义已核实为有意 flow-through（空队列 pop 消费当拍  -/
/-    push 的数据，entry 不落地），非 bug；不建模。                           -/
/-  Q3（死代码标注）：ListBuffer singleport=false 的 pop2/data2/index 端口     -/
/-    全仓无例化，不建模。                                                    -/
/-  Q4（契约提示，非 bug）：SinkD 的 io.resp 是 Valid（无 ready，              -/
/-    SinkD.scala:40），d.ready 恒 true（:66）——上游 D 通道无反压、下游       -/
/-    必须恒接收 resp；resp.valid=RegNext(d.fire)（:65）与 resp.bits 的无      -/
/-    条件 RegNext（:68-70）在该契约下自洽。Scheduler 侧是否恒接收由           -/
/-    Scheduler 波次核实。                                                    -/
/-  Q5（移植提示，非 bug）：SinkA.scala:108-110 每次 pb_pop.fire 即清 lists    -/
/-    位，正确性依赖"每个 list 只装 1 个 beat"——本配置 blockBeats=1           -/
/-    （beatBytes=blockBytes=128）成立（pb_pop.fire ⇒ putbuffer 该队列变空）。 -/
/-    若未来 beatBytes<blockBytes（多 beat put），首次 pop 即清位会导致该      -/
/-    list 被 freeOH 重新分配给新请求而旧 beat 未取完——Ventus 修改点，        -/
/-    改动 beatBytes 配置时必须重审。由 sinkAT_pop_clears 数值钉死现状语义。  -/
/-  Q6（契约提示，非 bug）：SinkA req.bits.put 对无数据请求（Get/Hint）取      -/
/-    freeIdx 垃圾值（SinkA.scala:79,:88，put 无 hasData 门控）——消费方       -/
/-    （Scheduler MSHR 分配）须仅在带数据请求时使用 put 字段。                -/
/-  Q7（已核实，非 bug）：SinkA 握手一致性——lists_set≠0 当且仅当 putbuffer    -/
/-    push.fire（见 sinkA_listsSet_iff / sinkA_listsSet_eq_pushFire 定理）：    -/
/-    :76 的条件比 push.valid(:75) 少了 !set_block 但多了 freeOH=0 的自动     -/
/-    归零（lists 全 1 时 ~lists=0），二者等价。valid 回撤族（I-22/I-26）      -/
/-    对照：a.ready/req.valid 均为当拍纯组合，无寄存器回撤路径。              -/
/-  Q8（环境税记录）：bv_decide 仅用于 32 位以下纯 BitVec 恒等式              -/
/-    （parse/expand 回环、lbLowestOne 刻画），且需先把参数 def（l2TagBits 等）-/
/-    simp only 展开到字面宽度，否则报 "None of the hypotheses are in the      -/
/-    supported BitVec fragment"。多拍轨迹全 native_decide 并逐拍手工对齐。    -/
/-  Q9（新踩坑，2026-08-29）：                                                 -/
/-    1. `Array.setD` 是 Batteries 的，核心库只有 `Array.setIfInBounds`        -/
/-       （越界返回原数组；本模型索引恒在界内，语义一致）。                    -/
/-    2. `Array.getD` 三参（arr idx default），[Inhabited] 场景传 `default`。  -/
/-    3. `of_eq_false h` 产出的是 `(b = true) = False` 而非 `¬(b = true)`；    -/
/-       Bool 等式否证用 `fun hc => Bool.noConfusion (h.symm.trans hc)`。       -/
/-    4. simp 会把 if 的 Bool 条件规范化为 `x = true` 形式，`rw [h]` 其中      -/
/-       `h : x = false` 会因 `5#3 : BitVec 3` vs `BitVec l2OpBits` 的 defeq    -/
/-       失配而失败——用 `simp only [def]` 展开后 `rw [if_neg hnc]` 更稳。     -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.L2

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 参数常量（来源行号见文件头）                                            -/
/- ========================================================================= -/

def l2Sets : Nat := 64        -- top/parameters.scala:99
def l2Ways : Nat := 16        -- :101
def l2BlockBytes : Nat := 128 -- :103,:113（dcache_BlockWords=32, :75）
def l2BeatBytes : Nat := 128  -- :113
def l2WriteBytes : Nat := 1   -- :105
def l2MemCycles : Nat := 32   -- :107
def l2PortFactor : Nat := 2   -- :109
def l2OpBits : Nat := 3       -- Parameters.scala:155
def l2SizeBits : Nat := 7     -- :162
def l2SourceBits : Nat := 16  -- :159
def l2DataBits : Nat := 1024  -- :160
def l2MaskBits : Nat := 128   -- :161
def l2WayBits : Nat := 4      -- :188
def l2SetBits : Nat := 6      -- :189
def l2OffsetBits : Nat := 7   -- :190
def l2L2cBits : Nat := 0      -- :191
def l2TagBits : Nat := 19     -- :192
def l2AddrBits : Nat := 32    -- :179（MMU_ENABLED=false）
def l2PutLists : Nat := 32    -- :166
def l2PutBeats : Nat := 32    -- :167
def l2PutBits : Nat := 5      -- :193

/- ========================================================================= -/
/- 2. 请求打包结构（QueuedRequest.scala:19-65）                               -/
/- ========================================================================= -/

/-- QueuedRequest（:19-31）。spike_info 不建模（D1）。 -/
structure QueuedRequest where
  opcode : BitVec l2OpBits
  size : BitVec l2SizeBits
  source : BitVec l2SourceBits
  tag : BitVec l2TagBits
  offset : BitVec l2OffsetBits
  put : BitVec l2PutBits
  data : BitVec l2DataBits
  mask : BitVec l2MaskBits
  param : BitVec 3
deriving DecidableEq

/-- FullRequest（:42-47）：QueuedRequest + set + l2cidx（0 宽，D2）。 -/
structure FullRequest extends QueuedRequest where
  set : BitVec l2SetBits
  l2cidx : BitVec l2L2cBits
deriving DecidableEq

/-- TLBundleA_lite（SourceA.scala:20-30）。mask 宽 = beatBytes/writeBytes
    = 128（:26），与 mask_bits 一致。spike_info 不建模（D1）。 -/
structure TLBundleA where
  opcode : BitVec l2OpBits
  size : BitVec l2SizeBits
  source : BitVec l2SourceBits
  address : BitVec l2AddrBits
  mask : BitVec l2MaskBits
  data : BitVec l2DataBits
  param : BitVec 3
deriving DecidableEq

/-- PutBufferAEntry（SinkA.scala:19-24）。 -/
structure PutBufferAEntry where
  data : BitVec l2DataBits
  mask : BitVec l2MaskBits
deriving DecidableEq, Inhabited

/-- SinkDResponse（SinkD.scala:20-26）。 -/
structure SinkDResponse where
  opcode : BitVec l2OpBits
  source : BitVec l2SourceBits
  data : BitVec l2DataBits
deriving DecidableEq

-- refill_data（SinkD.scala:27-34）：唯一使用处全被注释（:72-78），死代码不建模。
-- ListBufferRequest/DirWriteRequest/AllocateRequest/SubentryRequest
-- （QueuedRequest.scala:33-65）属 Scheduler/MSHR 面，本文件不需要，不建模。

/- ========================================================================= -/
/- 3. 地址解析/装配（Parameters.scala:219-239，l2cBits=0 实例）               -/
/- ========================================================================= -/

/-- parseAddress（:219-225）的 tag 分量：address[31:13]。 -/
def parseTag (x : BitVec l2AddrBits) : BitVec l2TagBits := x.extractLsb' 13 19
/-- set 分量：address[12:7]。 -/
def parseSet (x : BitVec l2AddrBits) : BitVec l2SetBits := x.extractLsb' 7 6
/-- offset 分量：address[6:0]。 -/
def parseOffset (x : BitVec l2AddrBits) : BitVec l2OffsetBits := x.extractLsb' 0 7

/-- expandAddress（:233-239，l2cBits=0 的 else 分支：Cat(tag,set,offset)）。
    widen（:227-231）在各分量已是目标宽度时为恒等，故直接拼接。 -/
def expandAddress (tag : BitVec l2TagBits) (set : BitVec l2SetBits)
    (offset : BitVec l2OffsetBits) : BitVec l2AddrBits :=
  (tag ++ set ++ offset : BitVec (l2TagBits + l2SetBits + l2OffsetBits))

/-- expand 后 parse 回环。 -/
theorem parse_expand (t : BitVec l2TagBits) (s : BitVec l2SetBits) (o : BitVec l2OffsetBits) :
    parseTag (expandAddress t s o) = t ∧ parseSet (expandAddress t s o) = s ∧
    parseOffset (expandAddress t s o) = o := by
  simp only [parseTag, parseSet, parseOffset, expandAddress,
    l2TagBits, l2SetBits, l2OffsetBits, l2AddrBits] <;> bv_decide

/-- parse 后 expand 回环（32 位地址无损分解）。 -/
theorem expand_parse (x : BitVec l2AddrBits) :
    expandAddress (parseTag x) (parseSet x) (parseOffset x) = x := by
  simp only [parseTag, parseSet, parseOffset, expandAddress,
    l2TagBits, l2SetBits, l2OffsetBits, l2AddrBits]; bv_decide

/- ========================================================================= -/
/- 4. HoldUnless（Hold.scala:16-18）                                          -/
/- ========================================================================= -/

/-- HoldUnless 状态：RegEnable(x, 0, en) 的寄存器（初值 0）。 -/
structure HoldState (w : Nat) where
  reg : BitVec w
deriving DecidableEq

/-- HoldUnless 输出（:17）：en 直通 x，否则输出保持寄存器。 -/
def holdOut (s : HoldState w) (x : BitVec w) (en : Bool) : BitVec w :=
  if en then x else s.reg

/-- HoldUnless 寄存器更新（:17 的 RegEnable）：en 时锁存 x。 -/
def holdStep (s : HoldState w) (x : BitVec w) (en : Bool) : HoldState w :=
  ⟨if en then x else s.reg⟩

theorem holdOut_en (s : HoldState w) (x : BitVec w) : holdOut s x true = x := rfl
theorem holdOut_hold (s : HoldState w) (x : BitVec w) : holdOut s x false = s.reg := rfl
theorem holdStep_en (s : HoldState w) (x : BitVec w) : holdStep s x true = ⟨x⟩ := rfl
theorem holdStep_hold (s : HoldState w) (x : BitVec w) : holdStep s x false = s := rfl

/-- 保持性：en 拍锁存的值在后续 !en 拍原样输出。 -/
theorem hold_holds (s : HoldState w) (x y : BitVec w) :
    holdOut (holdStep s x true) y false = x := rfl

-- 数值回归
theorem holdT_seq :
    holdOut (holdStep ⟨0#8⟩ 0xAB#8 true) 0xFF#8 false = 0xAB#8 ∧
    holdOut (holdStep (holdStep ⟨0#8⟩ 0xAB#8 true) 0xCD#8 false) 0xEE#8 false = 0xAB#8 ∧
    holdOut ⟨0#8⟩ 0x55#8 true = 0x55#8 := by
  native_decide

/- ========================================================================= -/
/- 5. ListBuffer（ListBuffer.scala:33-122，bypass=false && singleport=true）  -/
/- ========================================================================= -/

/-- 最低置位 one-hot（:52 的 (~(leftOR(~x)<<1))&~x 的无截断等值形式，D4/Q1）。 -/
def lbLowestOne {n : Nat} (x : BitVec n) : BitVec n := x &&& (0 - x)

/-- lowest-set-bit 完整刻画（32 位 = putLists/putBeats 实例宽度）。 -/
theorem lbLowestOne_spec (x : BitVec 32) :
    lbLowestOne x &&& (lbLowestOne x - 1#32) = 0#32 ∧   -- one-hot
    lbLowestOne x &&& x = lbLowestOne x ∧               -- 是 x 的子集
    (lbLowestOne x = 0#32 ↔ x = 0#32) ∧                 -- 非空当且仅当
    x &&& (lbLowestOne x - 1#32) = 0#32 := by           -- 之下无 x 的位（最低）
  simp only [lbLowestOne]; bv_decide

/-- 按位取反为零当且仅当全 1（free 判别用）。 -/
theorem lb_not_eq_zero (x : BitVec 32) : ~~~x = 0#32 ↔ x = BitVec.allOnes 32 := by
  bv_decide

/-- OHToUInt（:53）：最低置位的下标（D5）。 -/
def lbCtz {n : Nat} (x : BitVec n) : Nat :=
  (List.range n).foldl (fun r i => if r == n && x.getLsbD i then i else r) n

/-- ListBuffer 状态（:45-50）。queues=2^qBits、entries=2^eBits。
    head/tail 尺寸 queues，next/data 尺寸 entries；Chisel Mem 上电未定，
    init 0/default（D3）。 -/
structure LbState (qBits eBits : Nat) (α : Type) where
  valid : BitVec (2 ^ qBits)
  used : BitVec (2 ^ eBits)
  headArr : Array (BitVec eBits)
  tailArr : Array (BitVec eBits)
  nextArr : Array (BitVec eBits)
  dataArr : Array α
deriving DecidableEq

/-- 初始状态（valid/used 为 RegInit 0，:45,:48）。 -/
def lbInit [Inhabited α] : LbState qBits eBits α where
  valid := 0
  used := 0
  headArr := Array.replicate (2 ^ qBits) 0
  tailArr := Array.replicate (2 ^ qBits) 0
  nextArr := Array.replicate (2 ^ eBits) 0
  dataArr := Array.replicate (2 ^ eBits) default

/-- 访问器（D3：可达状态下 BitVec.toNat < 2^bits = 数组尺寸，不越界）。 -/
def lbHead (s : LbState qBits eBits α) (i : Nat) : BitVec eBits := s.headArr.getD i 0
def lbTail (s : LbState qBits eBits α) (i : Nat) : BitVec eBits := s.tailArr.getD i 0
def lbNext (s : LbState qBits eBits α) (i : Nat) : BitVec eBits := s.nextArr.getD i 0

/-- 输入：push（Decoupled，:37）+ pop（Valid，:39）。 -/
structure LbIn (qBits : Nat) (α : Type) where
  pushValid : Bool
  pushIndex : BitVec qBits
  pushData : α
  popValid : Bool
  popBits : BitVec qBits
deriving DecidableEq

/-- io.push.ready = !used.andR（:67）。 -/
def lbPushReady (s : LbState qBits eBits α) : Bool := !(s.used == BitVec.allOnes (2 ^ eBits))

/-- entry 空闲位 one-hot（:52）。 -/
def lbFreeOH (s : LbState qBits eBits α) : BitVec (2 ^ eBits) := lbLowestOne (~~~s.used)

/-- entry 空闲位下标（:53）。 -/
def lbFreeIdx (s : LbState qBits eBits α) : BitVec eBits :=
  BitVec.ofNat eBits (lbCtz (lbFreeOH s))

/-- io.data（:91，bypass=false 分支：data.read(pop_head)）。 -/
def lbOutData [Inhabited α] (s : LbState qBits eBits α) (popBits : BitVec qBits) : α :=
  s.dataArr.getD (lbHead s popBits.toNat).toNat default

/-- io.valid（:93，bypass=false 分支：valid 本体）。 -/
def lbOutValid (s : LbState qBits eBits α) : BitVec (2 ^ qBits) := s.valid

/-- 单拍转移（:64-121，bypass=false && singleport=true）。
    pop 为 Valid 口，fire = valid（:101）；:96 的 assert（pop 必须命中有效队列）
    是上游契约，模型不设防。同拍 push+pop 的 Mem 读写次序见 D6。 -/
def lbStep (s : LbState qBits eBits α) (i : LbIn qBits α) : LbState qBits eBits α :=
  let pushFire := i.pushValid && lbPushReady s
  let popFire := i.popValid
  let freeOH := lbFreeOH s
  let freeIdx := lbFreeIdx s
  let pushValidQ := s.valid.getLsbD i.pushIndex.toNat      -- push_valid（:65）
  let pushTail := lbTail s i.pushIndex.toNat               -- push_tail（:64）
  let popHead := lbHead s i.popBits.toNat                  -- pop_head（:80）
  let popTail := lbTail s i.popBits.toNat
  let usedSet := if pushFire then freeOH else 0            -- used_set（:70）
  let validSet := if pushFire then (1 : BitVec (2 ^ qBits)) <<< i.pushIndex else 0  --（:69）
  let usedClr := if popFire then (1 : BitVec (2 ^ eBits)) <<< popHead else 0        --（:102）
  let validClr := if popFire && popHead == popTail then
    (1 : BitVec (2 ^ qBits)) <<< i.popBits else 0          --（:103-105）
  let dataArr := if pushFire then
    s.dataArr.setIfInBounds freeIdx.toNat i.pushData else s.dataArr  --（:71）
  let nextArr := if pushFire && pushValidQ then
    s.nextArr.setIfInBounds pushTail.toNat freeIdx else s.nextArr   -- next.write（:73）
  let headA1 := if pushFire && !pushValidQ then
    s.headArr.setIfInBounds i.pushIndex.toNat freeIdx else s.headArr  -- head.write（:75）
  let headA2 := if popFire then headA1.setIfInBounds i.popBits.toNat
      (if pushFire && pushValidQ && pushTail == popHead then freeIdx
       else lbNext s popHead.toNat)                        -- head.write（:106）
    else headA1
  let tailArr := if pushFire then
    s.tailArr.setIfInBounds i.pushIndex.toNat freeIdx else s.tailArr  --（:77）
  { valid := (s.valid &&& ~~~validClr) ||| validSet        --（:120，bypass=false 恒更新，:118）
    used := (s.used &&& ~~~usedClr) ||| usedSet            --（:119）
    headArr := headA2
    tailArr := tailArr
    nextArr := nextArr
    dataArr := dataArr }

/-- 多拍执行。 -/
def lbRun (s : LbState qBits eBits α) (is : List (LbIn qBits α)) : LbState qBits eBits α :=
  is.foldl lbStep s

/-- push.ready 的充要刻画（:67）。 -/
theorem lbPushReady_iff (s : LbState qBits eBits α) :
    lbPushReady s = true ↔ s.used ≠ BitVec.allOnes (2 ^ eBits) := by
  simp [lbPushReady]

/- ---- ListBuffer 数值回归（qBits=1 → 2 队列，eBits=2 → 4 entry，α=BitVec 8） ---- -/

def lbTInit : LbState 1 2 (BitVec 8) := lbInit
def lbTPush (q : Nat) (v : BitVec 8) : LbIn 1 (BitVec 8) :=
  { pushValid := true, pushIndex := BitVec.ofNat 1 q, pushData := v,
    popValid := false, popBits := 0 }
def lbTPop (q : Nat) : LbIn 1 (BitVec 8) :=
  { pushValid := false, pushIndex := 0, pushData := 0,
    popValid := true, popBits := BitVec.ofNat 1 q }
def lbTPushPop (q : Nat) (v : BitVec 8) : LbIn 1 (BitVec 8) :=
  { pushValid := true, pushIndex := BitVec.ofNat 1 q, pushData := v,
    popValid := true, popBits := BitVec.ofNat 1 q }
def lbTIdle : LbIn 1 (BitVec 8) :=
  { pushValid := false, pushIndex := 0, pushData := 0, popValid := false, popBits := 0 }

-- push 后同队列 valid 置位、数据可读、entry 占用
theorem lbT_push_visible :
    let s1 := lbStep lbTInit (lbTPush 0 0xAB#8)
    s1.valid.getLsbD 0 = true ∧ lbOutData s1 (0 : BitVec 1) = 0xAB#8 ∧ s1.used = 1#4 := by
  native_decide

-- 同队两 entry FIFO：先推先出；两次 pop 后队列空、entry 全释放
theorem lbT_fifo :
    let s2 := lbRun lbTInit [lbTPush 0 0x11#8, lbTPush 0 0x22#8]
    let s3 := lbStep s2 (lbTPop 0)
    let s4 := lbStep s3 (lbTPop 0)
    lbOutData s2 (0 : BitVec 1) = 0x11#8 ∧ lbOutData s3 (0 : BitVec 1) = 0x22#8 ∧
    s4.valid = 0#2 ∧ s4.used = 0#4 := by
  native_decide

-- 满：4 个 entry 占满后 push.ready 为假，第 5 次 push 被丢弃（状态不变）
theorem lbT_full_block :
    let s4 := lbRun lbTInit [lbTPush 0 0xA0#8, lbTPush 0 0xA1#8, lbTPush 0 0xA2#8, lbTPush 0 0xA3#8]
    lbPushReady s4 = false ∧ s4.used = 0b1111#4 ∧ lbStep s4 (lbTPush 1 0xFF#8) = s4 := by
  native_decide

-- pop 空队列后 entry 回收：再次 push 复用 entry 0
theorem lbT_recycle :
    let s2 := lbRun lbTInit [lbTPush 0 0x55#8, lbTPop 0]
    let s3 := lbStep s2 (lbTPush 0 0x66#8)
    s2.valid = 0#2 ∧ s2.used = 0#4 ∧ s3.used = 1#4 ∧
    lbHead s3 0 = 0#2 ∧ lbOutData s3 (0 : BitVec 1) = 0x66#8 := by
  native_decide

-- 单元素队列同拍 push+pop（:106 的 Mux 支）：当拍 pop 看到旧数据 v1，
-- 下一拍 head 指向新 entry（数据 v2），valid 保持，used 一清一占总量不变
theorem lbT_sim_pushpop :
    let s1 := lbStep lbTInit (lbTPush 0 0x77#8)
    let s2 := lbStep s1 (lbTPushPop 0 0x88#8)
    lbOutData s1 (0 : BitVec 1) = 0x77#8 ∧ s2.valid.getLsbD 0 = true ∧
    lbOutData s2 (0 : BitVec 1) = 0x88#8 ∧ s2.used = 0b0010#4 := by
  native_decide

-- 双队列交叉：队列各自 FIFO、互不影响
theorem lbT_two_queues :
    let s3 := lbRun lbTInit [lbTPush 0 0x01#8, lbTPush 1 0x02#8, lbTPush 0 0x03#8]
    let s4 := lbStep s3 (lbTPop 0)
    let s5 := lbStep s4 (lbTPop 1)
    lbOutData s3 (0 : BitVec 1) = 0x01#8 ∧ lbOutData s3 (1 : BitVec 1) = 0x02#8 ∧
    lbOutData s4 (0 : BitVec 1) = 0x03#8 ∧ s5.valid = 0b01#2 ∧
    (lbStep s5 (lbTPop 0)).valid = 0#2 := by
  native_decide

/- ========================================================================= -/
/- 6. SinkA（SinkA.scala:33-111）                                             -/
/- ========================================================================= -/

/-- SinkA 状态：lists（:51，与 putbuffer 内部 valid 同义的分配位图）+ putbuffer。 -/
structure SinkAState where
  lists : BitVec l2PutLists
  pb : LbState l2PutBits l2PutBits PutBufferAEntry
deriving DecidableEq

/-- 初始状态（lists RegInit 0，:51）。 -/
def sinkAInit : SinkAState := ⟨0, lbInit⟩

/-- SinkA 输入：a 通道（Decoupled）+ req 反压 + pb_pop（:41）。 -/
structure SinkAIn where
  aValid : Bool
  a : TLBundleA
  reqReady : Bool
  pbPopValid : Bool
  pbPopIndex : BitVec l2PutBits
deriving DecidableEq

/-- hasData（Parameters.scala:173-175）：PutFullData=0 / PutPartialData=1。 -/
def sinkAHasData (op : BitVec l2OpBits) : Bool := op == 0#3 || op == 1#3

/-- SinkA 的 list 空闲 one-hot（:58-59 的 freeOH，D4/Q1）。 -/
def sinkAFreeOH (s : SinkAState) : BitVec l2PutLists := lbLowestOne (~~~s.lists)

/-- SinkA 的 list 空闲下标（:60 的 freeIdx，:79 的 put）。 -/
def sinkAFreeIdx (s : SinkAState) : BitVec l2PutBits :=
  BitVec.ofNat l2PutBits (lbCtz (sinkAFreeOH s))

/-- buf_block（:69）。 -/
def sinkABufBlock (s : SinkAState) (i : SinkAIn) : Bool :=
  sinkAHasData i.a.opcode && !lbPushReady s.pb

/-- set_block（:70）：free = !lists.andR（:57）。 -/
def sinkASetBlock (s : SinkAState) (i : SinkAIn) : Bool :=
  sinkAHasData i.a.opcode && (s.lists == BitVec.allOnes l2PutLists)

/-- pb_pop.ready（:102）：putbuffer 对应队列有效（bypass=false → io.valid=valid）。 -/
def sinkAPbPopReady (s : SinkAState) (i : SinkAIn) : Bool :=
  s.pb.valid.getLsbD i.pbPopIndex.toNat

/-- lists_set（:53,:76）：当拍 push.fire 当且仅当非零（Q7）。 -/
def sinkAListsSet (s : SinkAState) (i : SinkAIn) : BitVec l2PutLists :=
  if i.aValid && sinkAHasData i.a.opcode && i.reqReady && !sinkABufBlock s i then
    sinkAFreeOH s else 0

/-- lists_clr（:54,:108-110）：pb_pop.fire 即清（Q5）。 -/
def sinkAListsClr (s : SinkAState) (i : SinkAIn) : BitVec l2PutLists :=
  if i.pbPopValid && sinkAPbPopReady s i then (1 : BitVec l2PutLists) <<< i.pbPopIndex else 0

/-- lists 下一拍值（:55）。 -/
def sinkAListsN (s : SinkAState) (i : SinkAIn) : BitVec l2PutLists :=
  (s.lists ||| sinkAListsSet s i) &&& ~~~(sinkAListsClr s i)

/-- io.empty（:107）：下一拍 lists 判零（D7）。 -/
def sinkAEmpty (s : SinkAState) (i : SinkAIn) : Bool := sinkAListsN s i == 0

/-- a.ready（:73）：opcode 5（Hint）额外要求 putbuffer  drained（io.empty）。 -/
def sinkAARdy (s : SinkAState) (i : SinkAIn) : Bool :=
  let base := i.reqReady && !sinkABufBlock s i && !sinkASetBlock s i
  if i.a.opcode == 5#3 then base && sinkAEmpty s i else base

/-- io.req.valid（:74）。 -/
def sinkAReqValid (s : SinkAState) (i : SinkAIn) : Bool :=
  let base := i.aValid && !sinkABufBlock s i && !sinkASetBlock s i
  if i.a.opcode == 5#3 then base && sinkAEmpty s i else base

/-- putbuffer push 输入（:75,:94-96）：index=put=freeIdx（SinkA 的 lists 视角）。 -/
def sinkALbIn (s : SinkAState) (i : SinkAIn) : LbIn l2PutBits PutBufferAEntry where
  pushValid := i.aValid && sinkAHasData i.a.opcode && i.reqReady && !sinkASetBlock s i
  pushIndex := sinkAFreeIdx s
  pushData := ⟨i.a.data, i.a.mask⟩
  popValid := i.pbPopValid && sinkAPbPopReady s i   -- pop.valid = pb_pop.fire（:99）
  popBits := i.pbPopIndex                            -- pop.bits（:98）

/-- io.pb_beat（:104）。 -/
def sinkAPbBeat (s : SinkAState) (i : SinkAIn) : PutBufferAEntry :=
  lbOutData s.pb i.pbPopIndex

/-- io.req.bits（:78,:81-92；地址切分 :78 见 parse*；put=freeIdx :79,:88）。 -/
def sinkAReqBits (s : SinkAState) (i : SinkAIn) : FullRequest where
  opcode := i.a.opcode
  size := i.a.size
  source := i.a.source
  tag := parseTag i.a.address
  offset := parseOffset i.a.address
  put := sinkAFreeIdx s
  data := i.a.data
  mask := i.a.mask
  param := i.a.param
  set := parseSet i.a.address
  l2cidx := 0

/-- 单拍转移（:55 lists 更新 + putbuffer lbStep）。 -/
def sinkAStep (s : SinkAState) (i : SinkAIn) : SinkAState :=
  ⟨sinkAListsN s i, lbStep s.pb (sinkALbIn s i)⟩

/-- 多拍执行。 -/
def sinkARun (s : SinkAState) (is : List SinkAIn) : SinkAState :=
  is.foldl sinkAStep s

/- ---- SinkA 符号定理 ---- -/

/-- hasData 的 opcode 不是 Hint=5。 -/
theorem sinkAHasData_not_hint (op : BitVec 3) :
    sinkAHasData op = true → (op == 5#3) = false := by
  simp only [sinkAHasData]; bv_decide

/-- 带数据请求的 a.ready 公式（:73 非 Hint 支化简）。 -/
theorem sinkA_aReady_data (s : SinkAState) (i : SinkAIn)
    (h : sinkAHasData i.a.opcode = true) :
    sinkAARdy s i =
      (i.reqReady && !sinkABufBlock s i && !sinkASetBlock s i) := by
  have h5 := sinkAHasData_not_hint _ h
  have hnc : ¬ ((i.a.opcode == 5#3) = true) := fun hc => Bool.noConfusion (h5.symm.trans hc)
  simp only [sinkAARdy]
  rw [if_neg hnc]

/-- Hint（opcode=5）在 putbuffer 未 drained 时被整体阻断（a.ready 与 req.valid
    同时为低）——Ventus 加的 io.empty 门控（:73-74）。 -/
theorem sinkA_hint_gated (s : SinkAState) (i : SinkAIn)
    (hop : i.a.opcode = 5#3) (hempty : sinkAEmpty s i = false) :
    sinkAARdy s i = false ∧ sinkAReqValid s i = false := by
  simp [sinkAARdy, sinkAReqValid, hop, hempty]

/-- lists_set 非零 ⇔ 当拍确实在分配（Q7：:76 缺 !set_block 但 freeOH 自动归零，
    二者等价）。 -/
theorem sinkA_listsSet_iff (s : SinkAState) (i : SinkAIn) :
    sinkAListsSet s i ≠ 0 ↔
      i.aValid = true ∧ sinkAHasData i.a.opcode = true ∧ i.reqReady = true ∧
      sinkABufBlock s i = false ∧ s.lists ≠ BitVec.allOnes l2PutLists := by
  unfold sinkAListsSet
  by_cases h : (i.aValid && sinkAHasData i.a.opcode && i.reqReady && !sinkABufBlock s i) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hv, hd⟩, hr⟩, hb⟩ := h
    have hlo : (sinkAFreeOH s ≠ 0) ↔ s.lists ≠ BitVec.allOnes l2PutLists := by
      constructor
      · intro h1 hall
        apply h1
        rw [sinkAFreeOH, hall]
        native_decide
      · intro hne h0
        have hz : ~~~s.lists = (0 : BitVec 32) :=
          ((lbLowestOne_spec (~~~s.lists)).2.2.1).mp h0
        exact hne ((lb_not_eq_zero s.lists).mp hz)
    constructor
    · intro h2; exact ⟨hv, hd, hr, hb, hlo.mp h2⟩
    · intro ⟨_, _, _, _, hne⟩; exact hlo.mpr hne
  · rw [if_neg h]
    refine iff_of_false (fun f => f rfl) ?_
    rintro ⟨hv, hd, hr, hb, -⟩
    apply h
    simp [hv, hd, hr, hb]

/-- a.fire 且带数据 ⇒ putbuffer push.fire，且两者下标一致（put 字段一致性，
    :79,:88,:94）。 -/
theorem sinkA_put_consistent (s : SinkAState) (i : SinkAIn) :
    (sinkALbIn s i).pushIndex = sinkAFreeIdx s ∧
    (sinkAReqBits s i).put = sinkAFreeIdx s := by
  exact ⟨rfl, rfl⟩

/-- 空闲拍（a 无效且 pb_pop 无效）状态不变。 -/
theorem sinkA_step_idle (s : SinkAState) (i : SinkAIn)
    (hv : i.aValid = false) (hp : i.pbPopValid = false) :
    sinkAStep s i = s := by
  have hls : sinkAListsN s i = s.lists := by
    simp [sinkAListsN, sinkAListsSet, sinkAListsClr, hv, hp]
  have hpb : lbStep s.pb (sinkALbIn s i) = s.pb := by
    obtain ⟨valid, used, headA, tailA, nextA, dataA⟩ := s.pb
    simp [sinkALbIn, lbStep, hv, hp]
  rw [sinkAStep, hls, hpb]

/- ---- SinkA 数值回归（真实维度：lists/queues/entries 全 32） ---- -/

def mkA (op : Nat) (addr : BitVec 32) (d : BitVec 1024) (m : BitVec 128) : TLBundleA :=
  { opcode := BitVec.ofNat 3 op, size := 7#7, source := 3#16, address := addr,
    mask := m, data := d, param := 0#3 }

def sinkAInA (op : Nat) (addr : BitVec 32) (d : BitVec 1024) (m : BitVec 128) : SinkAIn :=
  { aValid := true, a := mkA op addr d m, reqReady := true, pbPopValid := false, pbPopIndex := 0 }

def sinkAInPop (idx : Nat) : SinkAIn :=
  { aValid := false, a := mkA 0 0 0 0, reqReady := false,
    pbPopValid := true, pbPopIndex := BitVec.ofNat 5 idx }

-- Put 全写（opcode=0）：当拍 a.ready/req.valid 高、put=0；步进后 lists 位 0 置位、
-- putbuffer 队列 0 有效、数据可读
theorem sinkAT_put_alloc :
    let i := sinkAInA 0 0x00021040#32 0xDEAD#1024 0xF0F0#128
    sinkAARdy sinkAInit i = true ∧ sinkAReqValid sinkAInit i = true ∧
    (sinkAReqBits sinkAInit i).put = 0#5 ∧
    (sinkAReqBits sinkAInit i).tag = parseTag 0x00021040#32 ∧
    (sinkAReqBits sinkAInit i).set = parseSet 0x00021040#32 ∧
    (sinkAReqBits sinkAInit i).offset = parseOffset 0x00021040#32 ∧
    let s1 := sinkAStep sinkAInit i
    s1.lists = 1#32 ∧ s1.pb.valid = 1#32 ∧
    lbOutData s1.pb (0 : BitVec 5) = ⟨0xDEAD#1024, 0xF0F0#128⟩ := by
  native_decide

-- 两个连续 Put：list 按下标递增分配（0、1）
theorem sinkAT_two_puts :
    let s2 := sinkARun sinkAInit
      [sinkAInA 0 0x1000#32 0xAA#1024 1#128, sinkAInA 1 0x2000#32 0xBB#1024 2#128]
    s2.lists = 0b11#32 ∧ s2.pb.valid = 0b11#32 ∧
    lbOutData s2.pb (0 : BitVec 5) = ⟨0xAA#1024, 1#128⟩ ∧
    lbOutData s2.pb (1 : BitVec 5) = ⟨0xBB#1024, 2#128⟩ := by
  native_decide

-- pb_pop：ready 高、pb_beat 数据正确；步进后 lists 位与 putbuffer 队列同步清空（Q5）
theorem sinkAT_pop_clears :
    let s1 := sinkAStep sinkAInit (sinkAInA 0 0x1000#32 0xCC#1024 3#128)
    let ip := sinkAInPop 0
    sinkAPbPopReady s1 ip = true ∧ sinkAPbBeat s1 ip = ⟨0xCC#1024, 3#128⟩ ∧
    let s2 := sinkAStep s1 ip
    s2.lists = 0#32 ∧ s2.pb.valid = 0#32 ∧ s2.pb.used = 0#32 := by
  native_decide

-- pop 后再次 Put：list/entry 0 被回收重用
theorem sinkAT_put_pop_reuse :
    let s2 := sinkARun sinkAInit [sinkAInA 0 0x1000#32 0x11#1024 1#128, sinkAInPop 0]
    let i3 := sinkAInA 0 0x2000#32 0x22#1024 2#128
    (sinkAReqBits s2 i3).put = 0#5 ∧
    let s3 := sinkAStep s2 i3
    s3.lists = 1#32 ∧ lbOutData s3.pb (0 : BitVec 5) = ⟨0x22#1024, 2#128⟩ := by
  native_decide

-- Get（opcode=4，无数据）：req 通过但不占 list、不进 putbuffer
theorem sinkAT_get_no_alloc :
    let i := sinkAInA 4 0x3000#32 0 0
    sinkAARdy sinkAInit i = true ∧ sinkAReqValid sinkAInit i = true ∧
    let s1 := sinkAStep sinkAInit i
    s1.lists = 0#32 ∧ s1.pb.valid = 0#32 ∧ s1.pb.used = 0#32 := by
  native_decide

-- Hint（opcode=5）：putbuffer 非空时被 io.empty 阻断；drained 后放行（:73-74）
theorem sinkAT_hint_gate :
    let s1 := sinkAStep sinkAInit (sinkAInA 0 0x1000#32 0x33#1024 1#128)
    let ih := sinkAInA 5 0x4000#32 0 0
    sinkAARdy s1 ih = false ∧ sinkAReqValid s1 ih = false ∧
    let s2 := sinkAStep s1 (sinkAInPop 0)
    sinkAARdy s2 ih = true ∧ sinkAReqValid s2 ih = true ∧
    sinkAStep s1 ih = s1 := by
  native_decide

-- req 反压（reqReady=false）：a.ready 低、状态不变（sinkA_step_idle 的数值版）
theorem sinkAT_backpressure :
    let i := { sinkAInA 0 0x1000#32 0x44#1024 1#128 with reqReady := false }
    sinkAARdy sinkAInit i = false ∧ sinkAStep sinkAInit i = sinkAInit := by
  native_decide

-- lists 全满（set_block）：Put 被阻断
theorem sinkAT_lists_full :
    let s : SinkAState := ⟨BitVec.allOnes 32, lbInit⟩
    let i := sinkAInA 0 0x1000#32 0x55#1024 1#128
    sinkASetBlock s i = true ∧ sinkAARdy s i = false ∧ sinkAReqValid s i = false := by
  native_decide

/- ========================================================================= -/
/- 7. SinkD（SinkD.scala:37-79）                                              -/
/- ========================================================================= -/

/-- SinkD 状态：resp 的 RegNext 链（:65,:68-70）+ source 的 RegEnable（:61）。 -/
structure SinkDState where
  respValid : Bool
  respOpcode : BitVec l2OpBits
  respSource : BitVec l2SourceBits
  respData : BitVec l2DataBits
  srcHold : BitVec l2SourceBits
deriving DecidableEq

/-- 初始状态（respValid RegNext init false，:65；其余 RegNext/RegEnable 无显式
    初值，建模为 0——只在 respValid=false 时可观测，契约上无效，D3 同类）。 -/
def sinkDInit : SinkDState := ⟨false, 0, 0, 0, 0⟩

/-- SinkD 单拍（d.ready 恒 true，:66 → d.fire=d.valid）。
    way/set/opcode/put 输入与 io.index=io.put（:60）为纯连线，不单列。 -/
def sinkDStep (s : SinkDState) (dValid : Bool) (op : BitVec l2OpBits)
    (src : BitVec l2SourceBits) (dat : BitVec l2DataBits) : SinkDState where
  respValid := dValid                       -- RegNext(d.fire)（:65）
  respOpcode := op                          -- RegNext（:68-70，无 enable）
  respSource := src
  respData := dat
  srcHold := if dValid then src else s.srcHold  -- RegEnable en=d.valid（:61）

/-- io.source（:61）：d.valid 直通，否则保持上次 valid 的 source。 -/
def sinkDSource (s : SinkDState) (dValid : Bool) (src : BitVec l2SourceBits) :
    BitVec l2SourceBits :=
  if dValid then src else s.srcHold

/-- io.resp（:40,:65,:68-70）：valid 与 bits 均来自状态寄存器。 -/
def sinkDResp (s : SinkDState) : Bool × SinkDResponse :=
  (s.respValid, ⟨s.respOpcode, s.respSource, s.respData⟩)

/- ========================================================================= -/
/- 8. SourceA（SourceA.scala:35-55）                                          -/
/- ========================================================================= -/

/-- io.a.valid = io.req.valid（:45）；io.req.ready = io.a.ready（:44）。 -/
def sourceAAValid (reqValid : Bool) : Bool := reqValid
def sourceAReqReady (aReady : Bool) : Bool := aReady

/-- io.a.bits（:46-54）：地址由 tag/set/offset 重新装配（:49，expandAddress）；
    param 硬连 0（:53）。 -/
def sourceAABits (r : FullRequest) : TLBundleA where
  opcode := r.opcode
  size := r.size
  source := r.source
  address := expandAddress r.tag r.set r.offset
  mask := r.mask
  data := r.data
  param := 0

/-- SourceA→（下游 SinkA 视角）地址无损：a.bits.address 再 parse 回到原
    tag/set/offset（expand_parse 的直连实例）。 -/
theorem sourceA_addr_roundtrip (t : BitVec l2TagBits) (s : BitVec l2SetBits)
    (o : BitVec l2OffsetBits) :
    parseTag (expandAddress t s o) = t ∧ parseSet (expandAddress t s o) = s ∧
    parseOffset (expandAddress t s o) = o :=
  parse_expand t s o

/- ---- SinkD/SourceA 数值回归 ---- -/

-- SinkD：valid 拍直通 + 下一拍 resp；空闲拍 source 保持
theorem sinkDT_pass_through :
    let s1 := sinkDStep sinkDInit true 4#3 0x123#16 0xBEEF#1024
    let s2 := sinkDStep s1 false 0#3 0xFFF#16 0#1024
    sinkDSource sinkDInit true 0x123#16 = 0x123#16 ∧
    s1.respValid = true ∧ s1.respOpcode = 4#3 ∧ s1.respSource = 0x123#16 ∧
    s1.respData = 0xBEEF#1024 ∧
    s2.respValid = false ∧ sinkDSource s2 false 0x000#16 = 0x123#16 := by
  native_decide

-- SourceA：valid/ready 直连 + bits 装配
theorem sourceAT_connect :
    let r : FullRequest :=
      { opcode := 4#3, size := 7#7, source := 5#16, tag := 0x12345#19,
        offset := 0x40#7, put := 0#5, data := 0x77#1024, mask := 0xFF#128,
        param := 0#3, set := 0x21#6, l2cidx := 0 }
    sourceAAValid true = true ∧ sourceAReqReady false = false ∧
    (sourceAABits r).address = expandAddress 0x12345#19 0x21#6 0x40#7 ∧
    parseTag (sourceAABits r).address = 0x12345#19 ∧
    parseSet (sourceAABits r).address = 0x21#6 ∧
    parseOffset (sourceAABits r).address = 0x40#7 ∧
    (sourceAABits r).param = 0#3 := by
  native_decide

/- ---- 公理审计（native_decide 定理含 Lean.ofReduceBool，属预期） ---- -/

#print axioms parse_expand
#print axioms expand_parse
#print axioms lbLowestOne_spec
#print axioms lbPushReady_iff
#print axioms sinkA_listsSet_iff
#print axioms sinkA_hint_gated
#print axioms sinkA_step_idle
#print axioms lbT_sim_pushpop
#print axioms sinkAT_put_pop_reuse
#print axioms sinkAT_hint_gate
#print axioms hold_holds

end Ventus.L2
