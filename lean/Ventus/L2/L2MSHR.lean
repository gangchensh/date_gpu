/- ========================================================================= -/
/-                          L2/L2MSHR.lean                                   -/
/-  L2Cache 的 MSHR 与 BankedStore 的 Lean 4 模型、测试与证明                 -/
/-  Chisel 源码（opengpgpu/original/ventus-gpgpu/ventus/src/L2cache/）：      -/
/-    MSHR.scala(150 行)、BankedStore.scala(118 行)；相关定义：               -/
/-    Parameters.scala:138-264（InclusiveCacheParameters_lite）、             -/
/-    QueuedRequest.scala:19-47、Directory_test.scala:41-76、                 -/
/-    SinkD.scala:20-26、SRAMTemplate.scala:89-147（cc_banks SRAM 语义）、    -/
/-    Scheduler.scala（连接关系仅作上下文核查，不建模）。                     -/
/-                                                                           -/
/-  例化参数（top/parameters.scala 固化）：l2cache_NSets=64 (:99)、           -/
/-    l2cache_NWays=16 (:101)、l2cache_BlockWords=dcache_BlockWords=32        -/
/-    (:103,:75) ⇒ blockBytes=beatBytes=128 (:113)、l2cache_writeBytes=1      -/
/-    (:105)、memCycles=32 (:107)、portFactor=2 (:109)、num_l2cache=1 (:132)  -/
/-    ⇒ l2cBits=0；num_sm=2/num_cluster=1/num_sm_in_cluster=2 (:7,:27,:29)、 -/
/-    dcache_MshrEntry=4 (:88)、dcache_NSets=256 (:71)、MMU_ENABLED=false     -/
/-    (:15) ⇒ addressBits=32 (Parameters.scala:179)。                        -/
/-  派生位宽（Parameters.scala:155-201）：op_bits=3、source_bits=             -/
/-    3+2+8+1+0+1+1=16 (:159)、data_bits=1024 (:160)、mask_bits=128 (:161)、  -/
/-    size_bits=7 (:162)、putLists=32 (:166) ⇒ putBits=5 (:193)、wayBits=4、  -/
/-    setBits=6、offsetBits=7、l2cBits=0、tagBits=32-6-7-0=19 (:188-193)、    -/
/-    inner/outerMaskBits=128 (:200-201)。                                   -/
/-  BankedStore 派生（BankedStore.scala:84-94）：rowBytes=128、               -/
/-    rowEntries=1024 (:88)、numBanks=128 (:90)、codeBits=8 (:91) ⇒ SRAM 为   -/
/-    1024 行 × 128 字节 bank，waymask 即 128 位字节掩码（writeBytes=1 ⇒      -/
/-    字节粒度写）。                                                         -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 参数固化为字面量；l2cBits=0 ⇒ l2cidx 建模为 `BitVec 0`（唯一取值）。  -/
/-  D2. spike_info（MSHR.scala:109，仅 printf 直通）省略（同 L1MSHR D6）。    -/
/-  D3. schedule.d.fire 在 MSHR 内不被任何寄存器引用（弹 entry 由 Scheduler   -/
/-      的 requests ListBuffer 完成，Scheduler.scala:235），step 不消费       -/
/-      dReady；dFire 仅作输出观测。                                         -/
/-  D4. sink_d_reg 两处 when 赋值（MSHR.scala:67-72 与 :143-147）按 Chisel    -/
/-      "后写覆盖先写"：sinkd.valid 优先于 allocate.valid。                  -/
/-  D5. cc_banks（SyncReadMem，holdRead/singlePort/bypassWrite=false）读数据  -/
/-      建模为一拍延迟寄存器 rdata：读 fire 下一拍呈现读时刻内容；无读时      -/
/-      保持（真实硬件"未定义"的保守具体化；定理只在确有读 fire 时陈述）。   -/
/-  D6. 同拍读写同行冲突：bypassWrite=false ⇒ 冲突字节读数据被 LFSR64 毒化    -/
/-      （SRAMTemplate.scala:129-136），模型取"写前旧值"并给出冲突检测       -/
/-      l2mBsCollision；正确性定理以无冲突为前提（Q5）。                     -/
/-  D7. 数据存储（128KB）走 MemLaws 接口抽象（AGENTS.md 纪律）：定理对任意    -/
/-      [MemLaws M L2mBsAddr (BitVec 8)] 全称量化，测试用 SparseMem 实例；    -/
/-      字节地址 = (行, 字节下标)。                                         -/
/-  D8. 1024 位数据总线按字节拼接：字节 k 占 bit [8k+7:8k]（LSB-first，与     -/
/-      asUInt/asTypeOf 一致，BankedStore.scala:108/:112）。                 -/
/-  D9. sinkD 写优先于 sourceD 写（:102-104,:109）：sourceD_wadr.ready =      -/
/-      !sinkD_adr.valid，同拍时 sourceD 被反压不丢。                        -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区，详见返回报告） =============== -/
/-  Q1（I 类候选，握手族，MSHR.scala:97 vs :110-116）：a.fire 优先于          -/
/-      allocate：同拍时 scheAValid' 被 fire 分支清 0，新分配请求的对外 Get   -/
/-      永远发不出 ⇒ miss 无响应、MSHR 挂死。触发前提：Scheduler 重新分配一   -/
/-      个 scheAValid 仍为 1 的 MSHR；Scheduler.scala:188-191 只在 directory  -/
/-      miss 时分配且应避开忙 entry，整机级大概率不可达。witness：            -/
/-      l2mT_alloc_fire_collision。修复：elsewhen 顺序对调。                 -/
/-  Q2（I 类候选，MSHR.scala:67-72 与 :143-147）：allocate 与 sinkd 同拍 ⇒    -/
/-      sink_d_reg'=1（后写覆盖），新 entry 未收内存响应即具备 d 响应资格     -/
/-      （:89 只查 sink_d_reg 与 sche_a_valid）。sinkd 按 source 路由         -/
/-      （Scheduler.scala:127），source 唯一性应使该组合不可达——"依赖外部     -/
/-      不变量"型隐患。witness：l2mT_alloc_sinkd_collision。                 -/
/-  Q3（I 类候选，MSHR.scala:81-87）：data_reg 优先级 allocate>merge>sinkd： -/
/-      merge 与 sinkd 同拍（无 allocate）时 Grant 数据被丢弃。               -/
/-      Scheduler.scala:134 的 merge.valid 要求同拍 d.valid（sink_d_reg 已    -/
/-      置位），同 source 第二次 sinkd 正常不存在，整机级大概率不可达。       -/
/-      witness：l2mT_merge_sinkd_priority。                                 -/
/-  Q4（I 类候选，I-22 族对照，MSHR.scala:89）：d.valid = io.valid &&         -/
/-      sink_d_reg && !sche_a_valid，io.valid 是**输入**（Scheduler.scala:132 -/
/-      接 requests.io.valid(i)）而非本地寄存器——NoWithdraw 依赖外部"不 fire -/
/-      不弹 entry"（:235 只在 d.fire 时 pop，形式上满足）。与 L1 I-22 同族   -/
/-      的结构性风险。witness：l2mT_dvalid_withdraw。L2 版未见 I-26 型         -/
/-      "ready 与状态推进不一致"（本模块无 missReq.ready 输出）。             -/
/-  Q5（I 类候选，BankedStore.scala:105-112 + SRAMTemplate）：同拍            -/
/-      sourceD_radr 读与 (sinkD|sourceD_wadr) 写同一行时 cc_banks 无冲突     -/
/-      保护，被写字节读数据下一拍为 LFSR64 毒化值；BankedStore 自身不设防    -/
/-      （radr.ready 恒 1，:111），正确性依赖未文档化的外部调度不变量。       -/
/-      检测函数：l2mBsCollision。                                           -/
/-  Q6（提示性，MSHR.scala:34-40）：Merge_meta 的 opcode/put/source 在 MSHR   -/
/-      内无读取点（merge 只消费 mask/data）；响应路由由 Scheduler 侧         -/
/-      （:269 requests.io.data.source）完成。冗余但无害。                   -/
/-  Q7（提示性，MSHR.scala:106）：a.bits.data := request.data 而非 data_reg   -/
/-      （a.opcode 恒为 Get，data 无语义，无害但与直觉相反）。               -/
/-  Q8（提示性，BankedStore.scala:102-104）：选择信号用 valid 而非 fire——    -/
/-      ready 恒 true（:110-111），valid≡fire，无差异。                      -/
/-  Q9（新踩坑）：BitVec 0（零宽 l2cidx）参与 deriving DecidableEq 与         -/
/-      native_decide 正常；omega 不把 def（l2mDataBits 等）展开为字面量，    -/
/-      含这些 def 的算术目标先 unfold 或 rw 成字面量再 omega；               -/
/-      BitVec.allOnes 8 在目标中显示为 255#8 且 getLsbD_allOnes 不匹配       -/
/-      字面量形式，需 getLsbD_ofNat + Nat.testBit_two_pow_sub_one。          -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.MemLaws
import Ventus.Base.Handshake

namespace Ventus.L2.L2MSHR

open Ventus.Base

set_option linter.unusedVariables false

/- 1. 固化参数（来源行号见文件头；op/source/data/mask/size/put/way/set/      -/
/-    offset/tag 位宽对应 Parameters.scala:155-193，TL 操作码取值见 TLMessages） -/
def l2mOpBits : Nat := 3
def l2mSourceBits : Nat := 16
def l2mDataBits : Nat := 1024
def l2mMaskBits : Nat := 128
def l2mSizeBits : Nat := 7
def l2mPutBits : Nat := 5
def l2mWayBits : Nat := 4
def l2mSetBits : Nat := 6
def l2mOffsetBits : Nat := 7
def l2mTagBits : Nat := 19
/-- TLMessages.Get = 4（MSHR.scala:99 的 a.bits.opcode 强制值） -/
def l2mOpGet : BitVec l2mOpBits := 4
/-- TLMessages.PutFullData = 0 -/
def l2mOpPutFullData : BitVec l2mOpBits := 0
/-- TLMessages.PutPartialData = 1 -/
def l2mOpPutPartialData : BitVec l2mOpBits := 1

/- 2. 记录类型（逐字段对应 Chisel Bundle） -/

/-- Status = DirectoryResult_lite（Directory_test.scala:66-76）
    = QueuedRequest（QueuedRequest.scala:19-31）+ FullRequest 扩展
    （QueuedRequest.scala:42-47）+ hit/way/dirty/flush/last_flush。
    spike_info 省略（D2）。 -/
structure L2mStatus where
  opcode    : BitVec l2mOpBits      -- QueuedRequest.scala:21
  size      : BitVec l2mSizeBits    -- :22
  source    : BitVec l2mSourceBits  -- :23
  tag       : BitVec l2mTagBits     -- :24
  offset    : BitVec l2mOffsetBits  -- :25
  put       : BitVec l2mPutBits     -- :26
  data      : BitVec l2mDataBits    -- :27
  mask      : BitVec l2mMaskBits    -- :28
  param     : BitVec 3              -- :29
  set       : BitVec l2mSetBits     -- FullRequest, QueuedRequest.scala:44
  l2cidx    : BitVec 0              -- :45，l2cBits=0（D1）
  hit       : Bool                  -- DirectoryResult_lite, Directory_test.scala:69
  way       : BitVec l2mWayBits     -- :70
  dirty     : Bool                  -- :71
  flush     : Bool                  -- :72
  lastFlush : Bool                  -- :73
  deriving DecidableEq, Repr

/-- Merge_meta（MSHR.scala:34-40）。opcode/put/source 在 MSHR 内无读取点（Q6） -/
structure L2mMergeMeta where
  mask   : BitVec l2mMaskBits   -- MSHR.scala:35
  data   : BitVec l2mDataBits   -- :36
  opcode : BitVec l2mOpBits     -- :37
  put    : BitVec l2mPutBits    -- :38
  source : BitVec l2mSourceBits -- :39
  deriving DecidableEq, Repr

/-- SinkDResponse（SinkD.scala:20-26） -/
structure L2mSinkDResp where
  opcode : BitVec l2mOpBits     -- SinkD.scala:22
  source : BitVec l2mSourceBits -- :23
  data   : BitVec l2mDataBits   -- :24
  deriving DecidableEq, Repr

/-- schedule.a.bits 的字段集（MSHR.scala:98-109），FullRequest 平铺 -/
structure L2mABits where
  set    : BitVec l2mSetBits
  opcode : BitVec l2mOpBits
  tag    : BitVec l2mTagBits
  l2cidx : BitVec 0
  param  : BitVec 3
  put    : BitVec l2mPutBits
  offset : BitVec l2mOffsetBits
  source : BitVec l2mSourceBits
  data   : BitVec l2mDataBits
  size   : BitVec l2mSizeBits
  mask   : BitVec l2mMaskBits
  deriving DecidableEq, Repr

/-- schedule.dir.bits（DirectoryWrite_lite，Directory_test.scala:52-59；
    MSHR.scala:135-137 只赋 set/data.tag/way） -/
structure L2mDirBits where
  set : BitVec l2mSetBits
  tag : BitVec l2mTagBits   -- data.tag（DirectoryEntry_lite 仅含 tag，:41-47）
  way : BitVec l2mWayBits
  deriving DecidableEq, Repr

/-- MSHR 时序状态（MSHR.scala:55-65 的六个寄存器） -/
structure L2mState where
  mixedReg     : Bool                  -- :55
  dataReg      : BitVec l2mDataBits    -- :56
  request      : L2mStatus             -- :57
  scheAValid   : Bool                  -- :63
  scheDirValid : Bool                  -- :64
  sinkDReg     : Bool                  -- :65
  deriving DecidableEq, Repr

/-- 每拍输入（io 的输入侧 + 各通道 ready） -/
structure L2mInput where
  allocValid : Bool          -- io.allocate.valid，MSHR.scala:44
  allocBits  : L2mStatus     -- io.allocate.bits
  valid      : Bool          -- io.valid，:47（Scheduler 的 requests.io.valid(i)）
  mshrWait   : Bool          -- io.mshr_wait，:48
  mixed      : Bool          -- io.mixed，:49
  aReady     : Bool          -- io.schedule.a.ready
  dReady     : Bool          -- io.schedule.d.ready（仅观测，D3）
  dirReady   : Bool          -- io.schedule.dir.ready
  mergeValid : Bool          -- io.merge.valid，:51
  mergeBits  : L2mMergeMeta  -- io.merge.bits
  sinkdValid : Bool          -- io.sinkd.valid，:52
  sinkdBits  : L2mSinkDResp  -- io.sinkd.bits
  deriving DecidableEq, Repr

/-- 每拍组合输出 -/
structure L2mOutput where
  status     : L2mStatus          -- io.status，MSHR.scala:66
  schedData  : BitVec l2mDataBits -- io.schedule.data，:95
  aValid     : Bool               -- :97
  aBits      : L2mABits           -- :98-109
  dValid     : Bool               -- :89
  dBits      : L2mStatus          -- :90-93
  dirValid   : Bool               -- :134
  dirBits    : L2mDirBits         -- :135-137
  deriving DecidableEq, Repr

/-- 全零 Status（RegInit 0.U.asTypeOf，MSHR.scala:57） -/
def l2mStatusZero : L2mStatus where
  opcode := 0
  size := 0
  source := 0
  tag := 0
  offset := 0
  put := 0
  data := 0
  mask := 0
  param := 0
  set := 0
  l2cidx := BitVec.ofNat 0 0
  hit := false
  way := 0
  dirty := false
  flush := false
  lastFlush := false

/-- 复位态（MSHR.scala:55-65 各 RegInit） -/
def l2mInit : L2mState where
  mixedReg := false
  dataReg := 0
  request := l2mStatusZero
  scheAValid := false
  scheDirValid := false
  sinkDReg := false

/- 3. 组合逻辑 -/

/-- 字节通道拼接：第 i 字节通道（值 f i）占 bit [8i+7:8i] 的前 k 通道拼接。
    FillInterleaved（MSHR.scala:59）与 SRAM 读数据拼接（D8）共用的基础构造 -/
def l2mByteLanes (f : Nat → BitVec 8) : Nat → BitVec l2mDataBits
  | 0 => 0
  | (k+1) => l2mByteLanes f k ||| ((f k).setWidth l2mDataBits <<< (8*k))

/-- full_mask = FillInterleaved(writeBytes*8=8, merge.bits.mask)
    （MSHR.scala:59）：mask 第 i 位复制为第 i 个字节通道的 8 位 -/
def l2mFullMask (mask : BitVec l2mMaskBits) : BitVec l2mDataBits :=
  l2mByteLanes (fun i => if mask.getLsbD i then BitVec.allOnes 8 else 0#8) l2mMaskBits

/-- merge_data = (merge.data & full_mask) | (data_reg & ~full_mask)
    （MSHR.scala:60） -/
def l2mMergeData (mergeData : BitVec l2mDataBits) (dataReg : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) : BitVec l2mDataBits :=
  (mergeData &&& l2mFullMask mask) ||| (dataReg &&& ~~~(l2mFullMask mask))

/-- 组合输出（MSHR.scala:66,:89-109,:134-137） -/
def l2mOut (st : L2mState) (inp : L2mInput) : L2mOutput where
  status := st.request                                -- :66
  schedData := st.dataReg                             -- :95
  aValid := st.scheAValid && !inp.mshrWait            -- :97
  aBits :=                                            -- :98-109
    { set := st.request.set                           -- :98
      opcode := l2mOpGet                              -- :99
      tag := st.request.tag                           -- :100
      l2cidx := st.request.l2cidx                     -- :101
      param := st.request.param                       -- :102
      put := st.request.put                           -- :103
      offset := st.request.offset                     -- :104
      source := st.request.source                     -- :105
      data := st.request.data                         -- :106（Q7）
      size := st.request.size                         -- :107
      mask := BitVec.allOnes l2mMaskBits }            -- :108
  dValid := inp.valid && st.sinkDReg && !st.scheAValid -- :89（Q4）
  dBits :=                                            -- :90-93
    { st.request with
      hit := false                                    -- :91
      dirty := false                                  -- :92
      data := st.dataReg }                            -- :93
  dirValid := st.scheDirValid && (st.request.opcode == l2mOpGet) -- :134
  dirBits :=                                          -- :135-137
    { set := st.request.set
      tag := st.request.tag
      way := st.request.way }

/-- schedule.a.fire（MSHR.scala:110 的 io.schedule.a.fire） -/
def l2mAFire (st : L2mState) (inp : L2mInput) : Bool :=
  (l2mOut st inp).aValid && inp.aReady

/-- schedule.dir.fire（MSHR.scala:119） -/
def l2mDirFire (st : L2mState) (inp : L2mInput) : Bool :=
  (l2mOut st inp).dirValid && inp.dirReady

/-- schedule.d.fire（观测用，D3） -/
def l2mDFire (st : L2mState) (inp : L2mInput) : Bool :=
  (l2mOut st inp).dValid && inp.dReady

/-- 状态转移（MSHR.scala:67-72,:81-87,:110-125,:128-132,:143-147） -/
def l2mStep (st : L2mState) (inp : L2mInput) : L2mState where
  -- :143-147 + :67-72：sinkd 的 when 在后，覆盖 allocate 分支（D4/Q2）
  sinkDReg := if inp.sinkdValid then true
              else if inp.allocValid then false else st.sinkDReg
  -- :81-87：allocate > merge > sinkd（Q3）
  dataReg := if inp.allocValid then inp.allocBits.data
             else if inp.mergeValid then l2mMergeData inp.mergeBits.data st.dataReg inp.mergeBits.mask
             else if inp.sinkdValid then inp.sinkdBits.data
             else st.dataReg
  -- :67-72
  request := if inp.allocValid then inp.allocBits else st.request
  -- :110-116：fire 优先于 allocate（Q1）
  scheAValid := if l2mAFire st inp then false
                else if inp.allocValid then true else st.scheAValid
  -- :117-125
  scheDirValid := if inp.allocValid then false
                  else if l2mDirFire st inp then false
                  else if inp.mixed then false
                  else if inp.sinkdValid && !(inp.mixed || st.mixedReg) then true
                  else st.scheDirValid
  -- :128-132
  mixedReg := if inp.allocValid then false
              else if inp.mixed then true else st.mixedReg

/-- 迭代运行 -/
def l2mRun : L2mState → List L2mInput → L2mState
  | st, [] => st
  | st, i :: is => l2mRun (l2mStep st i) is

/- 4. BankedStore 模型 -/

/-- BankedStore 字节地址：(行, 行内字节下标)。行 = set*ways+way
    （BankedStore.scala:101/:104），共 1024 行 × 128 字节 -/
abbrev L2mBsAddr : Type := BitVec 10 × BitVec 7

/-- 行地址 = set * NWays + way（BankedStore.scala:101,:104；ways=16） -/
def l2mBsRowAddr (set : BitVec l2mSetBits) (way : BitVec l2mWayBits) : BitVec 10 :=
  BitVec.ofNat 10 (set.toNat * 16 + way.toNat)

/-- 从 1024 位数据中取第 k 字节（bit [8k+7:8k]，D8） -/
def l2mByteOf (d : BitVec l2mDataBits) (k : Nat) : BitVec 8 :=
  d.extractLsb' (8*k) 8

/-- 字节掩码写：对前 k 个字节通道，mask 置位者写入新字节
    （BankedStore.scala:108 的 waymask 写，经 SRAMTemplate.scala:115
    array.write(setIdx, wdata, waymask.asBools)） -/
def l2mBsWriteLanes {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row : BitVec 10) (data : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) : Nat → M
  | 0 => m
  | (k+1) =>
    let m' := if mask.getLsbD k
              then MemLaws.write m (row, BitVec.ofNat 7 k) (l2mByteOf data k)
              else m
    l2mBsWriteLanes m' row data mask k

/-- 整行（128 字节）掩码写 -/
def l2mBsWriteRow {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row : BitVec 10) (data : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) : M :=
  l2mBsWriteLanes m row data mask l2mMaskBits

/-- 读整行为 1024 位总线值（BankedStore.scala:112 的 asUInt，D8） -/
def l2mBsReadRow {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row : BitVec 10) : BitVec l2mDataBits :=
  l2mByteLanes (fun k => MemLaws.read m (row, BitVec.ofNat 7 k)) l2mMaskBits

/-- BankedStore 输入（BankedStore.scala:73-82）。
    三个地址口的 ready 恒 true 或由 sinkD 反压（:109-111），故 valid≡fire（Q8） -/
structure L2mBsInput where
  sinkDValid : Bool               -- io.sinkD_adr.valid，:75
  sinkDSet   : BitVec l2mSetBits  -- sinkD_adr.bits.set
  sinkDWay   : BitVec l2mWayBits  -- sinkD_adr.bits.way
  sinkDMask  : BitVec l2mMaskBits -- sinkD_adr.bits.mask
  sinkDData  : BitVec l2mDataBits -- io.sinkD_dat.data，:76
  radrValid  : Bool               -- io.sourceD_radr.valid，:78
  radrSet    : BitVec l2mSetBits
  radrWay    : BitVec l2mWayBits
  wadrValid  : Bool               -- io.sourceD_wadr.valid，:80
  wadrSet    : BitVec l2mSetBits
  wadrWay    : BitVec l2mWayBits
  wadrMask   : BitVec l2mMaskBits -- sourceD_wadr.bits.mask
  wadrData   : BitVec l2mDataBits -- io.sourceD_wdat.data，:81
  deriving DecidableEq, Repr

/-- BankedStore 状态：存储（MemLaws 抽象，D7）+ 读数据一拍延迟寄存器（D5） -/
structure L2mBsState (M : Type) where
  mem   : M
  rdata : BitVec l2mDataBits  -- cc_banks.io.r.resp.data 的呈现（D5）

/-- 写口 valid（BankedStore.scala:107） -/
def l2mBsWValid (inp : L2mBsInput) : Bool :=
  inp.wadrValid || inp.sinkDValid

/-- 写行选择：sinkD 优先（BankedStore.scala:104，D9/Q8） -/
def l2mBsWRow (inp : L2mBsInput) : BitVec 10 :=
  if inp.sinkDValid then l2mBsRowAddr inp.sinkDSet inp.sinkDWay
  else l2mBsRowAddr inp.wadrSet inp.wadrWay

/-- 写数据选择（BankedStore.scala:102） -/
def l2mBsWData (inp : L2mBsInput) : BitVec l2mDataBits :=
  if inp.sinkDValid then inp.sinkDData else inp.wadrData

/-- 写掩码选择（BankedStore.scala:103） -/
def l2mBsWMask (inp : L2mBsInput) : BitVec l2mMaskBits :=
  if inp.sinkDValid then inp.sinkDMask else inp.wadrMask

/-- sourceD_wadr.ready := !sinkD_adr.valid（BankedStore.scala:109，D9） -/
def l2mBsWadrReady (inp : L2mBsInput) : Bool := !inp.sinkDValid

/-- 同拍读写同行冲突检测（Q5）：真实硬件此时读数据被 LFSR64 毒化 -/
def l2mBsCollision (inp : L2mBsInput) : Bool :=
  inp.radrValid && l2mBsWValid inp &&
  (l2mBsRowAddr inp.radrSet inp.radrWay == l2mBsWRow inp)

/-- 状态转移（D5/D6）：写入本拍生效；rdata 下一拍呈现读时刻内容；
    冲突时模型取"写前旧值"（真实硬件为毒化值，定理以无冲突为前提） -/
def l2mBsStep {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (st : L2mBsState M) (inp : L2mBsInput) : L2mBsState M where
  mem := if l2mBsWValid inp
         then l2mBsWriteRow st.mem (l2mBsWRow inp) (l2mBsWData inp) (l2mBsWMask inp)
         else st.mem
  rdata := if inp.radrValid
           then l2mBsReadRow st.mem (l2mBsRowAddr inp.radrSet inp.radrWay)
           else st.rdata

/- 5. MSHR 数值回归测试（全部 native_decide：1024 位数据 + 多合取） -/

/-- 测试用 allocate 请求：Get、source=0x1234、set=5、way=3、tag=0xAB -/
def l2mTAlloc : L2mStatus :=
  { l2mStatusZero with
    opcode := l2mOpGet
    source := 0x1234#16
    set := 5#6
    way := 3#4
    tag := 0xAB#19
    data := 0xDEAD#1024
    size := 7#7 }

def l2mTInAlloc : L2mInput where
  allocValid := true
  allocBits := l2mTAlloc
  valid := false
  mshrWait := false
  mixed := false
  aReady := false
  dReady := false
  dirReady := false
  mergeValid := false
  mergeBits := ⟨0, 0, 0, 0, 0⟩
  sinkdValid := false
  sinkdBits := ⟨0, 0, 0⟩

/-- 空输入（所有 valid/ready 拉低） -/
def l2mTInIdle : L2mInput := { l2mTInAlloc with allocValid := false }

/-- sinkd 响应输入（AccessAckData，data=0xCAFE） -/
def l2mTInSinkd : L2mInput :=
  { l2mTInIdle with
    valid := true
    sinkdValid := true
    sinkdBits := ⟨1#3, 0x1234#16, 0xCAFE#1024⟩ }

-- T1：allocate 拍：request 装载、scheAValid 置位、其余寄存器清零
theorem l2mT1_alloc :
    let st := l2mStep l2mInit l2mTInAlloc
    st.request = l2mTAlloc ∧ st.scheAValid = true ∧ st.sinkDReg = false ∧
    st.scheDirValid = false ∧ st.mixedReg = false ∧
    st.dataReg = l2mTAlloc.data := by
  native_decide

-- T1b：allocate 后 aValid 立即拉高（mshrWait=0），a.bits.opcode=Get、mask 全 1
theorem l2mT1b_aOut :
    let st := l2mStep l2mInit l2mTInAlloc
    let out := l2mOut st l2mTInIdle
    out.aValid = true ∧ out.aBits.opcode = l2mOpGet ∧
    out.aBits.mask = BitVec.allOnes l2mMaskBits ∧ out.aBits.source = 0x1234#16 ∧
    out.aBits.set = 5#6 ∧ out.aBits.tag = 0xAB#19 := by
  native_decide

-- T2：a.fire 清 scheAValid
theorem l2mT2_aFire :
    let st1 := l2mStep l2mInit l2mTInAlloc
    let st2 := l2mStep st1 { l2mTInIdle with aReady := true }
    st1.scheAValid = true ∧ st2.scheAValid = false := by
  native_decide

-- T2b（Q1 witness）：allocate 与 a.fire 同拍 ⇒ scheAValid' = false，
-- 新请求的对外 Get 永远发不出
theorem l2mT_alloc_fire_collision :
    let st1 := l2mStep l2mInit l2mTInAlloc          -- 已分配，scheAValid=1
    let inp := { l2mTInAlloc with aReady := true }  -- 同拍 allocate + aReady
    let st2 := l2mStep st1 inp
    l2mAFire st1 inp = true ∧ st2.scheAValid = false ∧
    (l2mOut st2 l2mTInIdle).aValid = false := by
  native_decide

-- T2c（Q2 witness）：allocate 与 sinkd 同拍 ⇒ sinkDReg' = true
theorem l2mT_alloc_sinkd_collision :
    let inp := { l2mTInAlloc with
                 sinkdValid := true
                 sinkdBits := ⟨1#3, 0x1234#16, 0xBEEF#1024⟩ }
    (l2mStep l2mInit inp).sinkDReg = true := by
  native_decide

-- T3：merge 字节选择：mask=0x5 ⇒ 字节 0、2 取 merge.data，其余保持
theorem l2mT3_merge :
    let st1 := l2mStep l2mInit l2mTInAlloc   -- dataReg = 0xDEAD
    let inp := { l2mTInIdle with
                 mergeValid := true
                 mergeBits := ⟨0x5#128, 0xFF00#1024, 0, 0, 0⟩ }
    let st2 := l2mStep st1 inp
    l2mByteOf st2.dataReg 0 = l2mByteOf 0xFF00#1024 0 ∧
    l2mByteOf st2.dataReg 1 = l2mByteOf 0xDEAD#1024 1 ∧
    l2mByteOf st2.dataReg 2 = l2mByteOf 0xFF00#1024 2 ∧
    l2mByteOf st2.dataReg 3 = l2mByteOf 0xDEAD#1024 3 ∧
    st2.request = st1.request := by
  native_decide

-- T3b（Q3 witness）：merge 与 sinkd 同拍（无 allocate）⇒ sinkd 数据被丢弃
theorem l2mT_merge_sinkd_priority :
    let st1 := l2mStep l2mInit l2mTInAlloc
    let inp := { l2mTInIdle with
                 mergeValid := true
                 mergeBits := ⟨0x5#128, 0xFF00#1024, 0, 0, 0⟩
                 sinkdValid := true
                 sinkdBits := ⟨1#3, 0#16, 0xBEEF#1024⟩ }
    (l2mStep st1 inp).dataReg =
      l2mMergeData 0xFF00#1024 st1.dataReg 0x5#128 := by
  native_decide

-- T4：sinkd（Get 请求）⇒ sinkDReg 置位、dataReg 更新、scheDirValid 置位
theorem l2mT4_sinkd :
    let st1 := l2mStep l2mInit l2mTInAlloc
    let st2 := l2mStep st1 { l2mTInIdle with aReady := true }  -- a 发出
    let st3 := l2mStep st2 l2mTInSinkd
    st3.sinkDReg = true ∧ st3.dataReg = 0xCAFE#1024 ∧
    st3.scheDirValid = true ∧
    (l2mOut st3 l2mTInSinkd).dValid = true ∧ (l2mOut st3 l2mTInSinkd).dirValid = true ∧
    (l2mOut st3 l2mTInSinkd).dBits.data = 0xCAFE#1024 ∧
    (l2mOut st3 l2mTInSinkd).dBits.hit = false ∧
    (l2mOut st3 l2mTInSinkd).dBits.dirty = false := by
  native_decide

-- T4b：写 miss（PutFullData）⇒ dir.valid 被 opcode 门控（MSHR.scala:134）
theorem l2mT4b_put_no_dir :
    let allocPut := { l2mTAlloc with opcode := l2mOpPutFullData }
    let st1 := l2mStep l2mInit { l2mTInAlloc with allocBits := allocPut }
    let st2 := l2mStep st1 { l2mTInIdle with aReady := true }
    let st3 := l2mStep st2 l2mTInSinkd
    st3.scheDirValid = true ∧                 -- 寄存器置位（:123-124）
    (l2mOut st3 l2mTInSinkd).dirValid = false ∧ -- 但 dir.valid 被门控（:134）
    (l2mOut st3 l2mTInSinkd).dValid = true := by
  native_decide

-- T4c：mixed（同块读写混合）⇒ scheDirValid 不置位（:123 的 mixed 条件）
theorem l2mT4c_mixed_no_dir :
    let st1 := l2mStep l2mInit l2mTInAlloc
    let st2 := l2mStep st1 { l2mTInIdle with aReady := true }
    let st3 := l2mStep st2 { l2mTInSinkd with mixed := true }
    st3.scheDirValid = false ∧ st3.mixedReg = true ∧ st3.sinkDReg = true := by
  native_decide

-- T5（Q4 witness，I-22 族）：d.valid 依赖输入 io.valid——同一状态下
-- 仅翻转 io.valid，dValid 在无 fire 情况下被回撤
theorem l2mT_dvalid_withdraw :
    let st1 := l2mStep l2mInit l2mTInAlloc
    let st2 := l2mStep st1 { l2mTInIdle with aReady := true }
    let st3 := l2mStep st2 l2mTInSinkd
    let inpV := { l2mTInIdle with valid := true }    -- dReady=false ⇒ 不 fire
    (l2mOut st3 inpV).dValid = true ∧ l2mDFire st3 inpV = false ∧
    (l2mOut st3 l2mTInIdle).dValid = false := by
  native_decide

-- T6：多拍完整轨迹：allocate → a 反压保持 → a fire → sinkd → d/dir 输出
theorem l2mT6_trace :
    let st0 := l2mInit
    let st1 := l2mStep st0 l2mTInAlloc
    let o1 := l2mOut st1 l2mTInIdle                       -- aValid=1，等 ready
    let st2 := l2mStep st1 l2mTInIdle                     -- aReady=0：保持
    let o2 := l2mOut st2 l2mTInIdle
    let st3 := l2mStep st2 { l2mTInIdle with aReady := true }  -- a fire
    let i3 := { l2mTInIdle with
                valid := true
                sinkdValid := true
                sinkdBits := ⟨1#3, 0x1234#16, 0xCAFE#1024⟩ }
    let st4 := l2mStep st3 i3
    let i4 := { i3 with
                dReady := true
                dirReady := true }
    let o4 := l2mOut st4 i4
    o1.aValid = true ∧ o2.aValid = true ∧ o2.aBits = o1.aBits ∧  -- 反压下稳定
    st3.scheAValid = false ∧
    o4.dValid = true ∧ o4.dirValid = true ∧
    o4.dBits.data = 0xCAFE#1024 ∧ o4.dBits.source = 0x1234#16 ∧
    o4.dirBits.way = 3#4 ∧ o4.dirBits.tag = 0xAB#19 ∧
    l2mDFire st4 i4 = true := by
  native_decide

/- 6. MSHR 符号定理 -/

/-- allocate 拍的完整效果（MSHR.scala:67-72,:81-87,:110-125,:128-132）：
    request/dataReg 装载、pending 寄存器按优先级复位/置位。
    分配/释放配对的基础：分配必置 a-pending（scheAValid）、清 d/dir/mixed -/
theorem l2m_step_alloc (st : L2mState) (inp : L2mInput)
    (ha : inp.allocValid = true) (hs : inp.sinkdValid = false)
    (hf : l2mAFire st inp = false) :
    (l2mStep st inp).request = inp.allocBits ∧
    (l2mStep st inp).dataReg = inp.allocBits.data ∧
    (l2mStep st inp).scheAValid = true ∧
    (l2mStep st inp).scheDirValid = false ∧
    (l2mStep st inp).mixedReg = false ∧
    (l2mStep st inp).sinkDReg = false := by
  simp [l2mStep, ha, hs, hf]

/-- 无 allocate 时 request 不变（:67-72 唯一写点）——合并/响应不改元数据，
    即"合并不丢不重"的元数据侧：被合并 entry 的身份字段保持稳定 -/
theorem l2m_request_stable (st : L2mState) (inp : L2mInput)
    (ha : inp.allocValid = false) :
    (l2mStep st inp).request = st.request := by
  simp [l2mStep, ha]

/-- a 通道 NoWithdraw：当拍不 fire、无 allocate，下一拍 scheAValid 保持
    （:110-116 otherwise 分支；aValid 还依赖输入 mshrWait，需外部稳定） -/
theorem l2m_scheA_noWithdraw (st : L2mState) (inp : L2mInput)
    (hf : l2mAFire st inp = false) (ha : inp.allocValid = false) :
    (l2mStep st inp).scheAValid = st.scheAValid := by
  simp [l2mStep, hf, ha]

/-- a 通道 Stable：无 allocate 时 a.bits 不变（只依赖 request，:98-109） -/
theorem l2m_aBits_stable (st : L2mState) (inp : L2mInput)
    (ha : inp.allocValid = false) :
    (l2mOut (l2mStep st inp) inp).aBits = (l2mOut st inp).aBits := by
  have hreq := l2m_request_stable st inp ha
  simp [l2mOut, hreq]

/-- sinkd 拍的效果（无 allocate、无 merge）：sinkDReg 置位、dataReg 装载 -/
theorem l2m_sinkd_effect (st : L2mState) (inp : L2mInput)
    (ha : inp.allocValid = false) (hm : inp.mergeValid = false)
    (hs : inp.sinkdValid = true) :
    (l2mStep st inp).sinkDReg = true ∧
    (l2mStep st inp).dataReg = inp.sinkdBits.data := by
  simp [l2mStep, ha, hm, hs]

/-- sinkd 且非 mixed 时 scheDirValid 置位（:123-124） -/
theorem l2m_sinkd_dir_set (st : L2mState) (inp : L2mInput)
    (ha : inp.allocValid = false) (hf : l2mDirFire st inp = false)
    (hx : inp.mixed = false) (hm : st.mixedReg = false)
    (hs : inp.sinkdValid = true) :
    (l2mStep st inp).scheDirValid = true := by
  simp [l2mStep, ha, hf, hx, hm, hs]

/-- dir.valid 蕴含 opcode = Get：写 miss 不写目录（:134） -/
theorem l2m_dirValid_get (st : L2mState) (inp : L2mInput)
    (h : (l2mOut st inp).dirValid = true) :
    st.request.opcode = l2mOpGet := by
  have h2 : (st.scheDirValid && (st.request.opcode == l2mOpGet)) = true := h
  rw [Bool.and_eq_true] at h2
  exact beq_iff_eq.mp h2.2

/-- d.valid 定义（:89）——Q4 的结构性陈述：dValid 依赖输入 valid -/
theorem l2m_dValid_def (st : L2mState) (inp : L2mInput) :
    (l2mOut st inp).dValid = (inp.valid && st.sinkDReg && !st.scheAValid) := rfl

/- 7. 字节通道拼接与 merge 的位/字节级规约 -/

/-- 拼接的位级规约：第 n 位属于第 n/8 个字节通道（n/8 < k 时），
    取该通道值的第 n%8 位；通道外为 0 -/
theorem l2mByteLanes_getLsbD (f : Nat → BitVec 8) (k n : Nat) :
    (l2mByteLanes f k).getLsbD n =
      (decide (n / 8 < k) && decide (n < l2mDataBits) && (f (n/8)).getLsbD (n % 8)) := by
  induction k with
  | zero => simp [l2mByteLanes, BitVec.getLsbD_zero]
  | succ k ih =>
    show ((l2mByteLanes f k) ||| ((f k).setWidth l2mDataBits <<< (8*k))).getLsbD n = _
    rw [BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h1 : n / 8 < k
    · have h2 : n / 8 < k + 1 := by omega
      have h3 : n < 8 * k := by omega
      simp [h1, h2, h3]
    · by_cases h4 : n / 8 = k
      · subst h4
        have h5 : n - 8 * (n / 8) = n % 8 := by omega
        have h7 : n / 8 < n / 8 + 1 := by omega
        have h8 : ¬ n < 8 * (n / 8) := by omega
        have h9 : ¬ n / 8 < n / 8 := by omega
        have h10 : n % 8 < l2mDataBits := by unfold l2mDataBits; omega
        simp [h9, h7, h8, h5, h10]
      · have h8 : ¬ n / 8 < k + 1 := by omega
        simp [h1, h8]
        intro _ _ _
        apply BitVec.getLsbD_of_ge
        have : 8 ≤ n - 8 * k := by omega
        exact this

/-- full_mask 的位级规约（FillInterleaved，MSHR.scala:59）：第 n 位 = mask 第 n/8 位 -/
theorem l2mFullMask_getLsbD (mask : BitVec l2mMaskBits) (n : Nat)
    (hn : n < l2mDataBits) :
    (l2mFullMask mask).getLsbD n = mask.getLsbD (n / 8) := by
  have eD : l2mDataBits = 1024 := rfl
  have eM : l2mMaskBits = 128 := rfl
  rw [eD] at hn
  unfold l2mFullMask
  rw [l2mByteLanes_getLsbD, eD]
  have h1 : n / 8 < l2mMaskBits := by rw [eM]; omega
  have h2 : n % 8 < 8 := by omega
  rw [decide_eq_true h1, decide_eq_true hn, Bool.true_and]
  cases h : mask.getLsbD (n / 8)
  · simp [BitVec.getLsbD_zero]
  · have h3 : (255#8 : BitVec 8).getLsbD (n % 8) = true := by
      rw [BitVec.getLsbD_ofNat, show (255 : Nat) = 2^8 - 1 by decide,
          Nat.testBit_two_pow_sub_one]
      simp [h2]
    simp [h3]

/-- merge_data 的位级规约（MSHR.scala:60）：mask 选通按字节生效 -/
theorem l2mMergeData_getLsbD (md dd : BitVec l2mDataBits) (mask : BitVec l2mMaskBits)
    (n : Nat) (hn : n < l2mDataBits) :
    (l2mMergeData md dd mask).getLsbD n =
      (if mask.getLsbD (n/8) then md.getLsbD n else dd.getLsbD n) := by
  unfold l2mMergeData
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_not,
      l2mFullMask_getLsbD mask n hn]
  cases h : mask.getLsbD (n / 8) <;> simp [h, hn]  -- NOTE: linter 误报 hn unused，实为 false 分支所需

/-- merge_data 的字节级规约：第 j 字节 = mask 第 j 位 ? merge.data[j] : data_reg[j]。
    合并"不丢不重"的数据侧：未选通字节原样保持，选通字节整体替换 -/
theorem l2mMergeData_byte (md dd : BitVec l2mDataBits) (mask : BitVec l2mMaskBits)
    (j : Nat) (hj : j < l2mMaskBits) :
    l2mByteOf (l2mMergeData md dd mask) j =
      (if mask.getLsbD j then l2mByteOf md j else l2mByteOf dd j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold l2mByteOf
  simp only [BitVec.getLsbD_extractLsb']
  have hj8 : 8 * j + i < l2mDataBits := by
    have : 8 * j + i < 1024 := by have hj' : j < 128 := hj; omega
    exact this
  rw [l2mMergeData_getLsbD md dd mask (8*j+i) hj8]
  have hdiv : (8 * j + i) / 8 = j := by have hi' : i < 8 := hi; omega
  rw [hdiv]
  cases h : mask.getLsbD j <;> simp

/-- full_mask 端点：mask 全 1 ⇒ full_mask 全 1 -/
theorem l2mFullMask_allOnes :
    l2mFullMask (BitVec.allOnes l2mMaskBits) = BitVec.allOnes l2mDataBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [l2mFullMask_getLsbD _ i hi, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes]
  have h1 : i / 8 < l2mMaskBits := by
    have : i / 8 < 128 := by have h' : i < 1024 := hi; omega
    exact this
  simp [hi, h1]

/-- merge 端点：mask 全 1 ⇒ merge_data = merge.data（整行替换） -/
theorem l2mMergeData_allOnes (md dd : BitVec l2mDataBits) :
    l2mMergeData md dd (BitVec.allOnes l2mMaskBits) = md := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [l2mMergeData_getLsbD md dd _ i hi, BitVec.getLsbD_allOnes]
  have h1 : i / 8 < l2mMaskBits := by
    have : i / 8 < 128 := by have h' : i < 1024 := hi; omega
    exact this
  simp [h1]

/-- merge 端点：mask 全 0 ⇒ merge_data = data_reg（无效果） -/
theorem l2mMergeData_zero (md dd : BitVec l2mDataBits) :
    l2mMergeData md dd 0 = dd := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [l2mMergeData_getLsbD md dd _ i hi,
      show (0 : BitVec l2mMaskBits).getLsbD (i / 8) = false from BitVec.getLsbD_zero]
  simp

/- 8. BankedStore 定理与测试 -/

/-- 行地址注入性：set*16+way 不同的 (set,way) 给出不同行（BankedStore.scala:101） -/
theorem l2mBsRowAddr_inj (s s' : BitVec l2mSetBits) (w w' : BitVec l2mWayBits)
    (h : l2mBsRowAddr s w = l2mBsRowAddr s' w') : s = s' ∧ w = w' := by
  have ht := congrArg BitVec.toNat h
  unfold l2mBsRowAddr at ht
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at ht
  have hs : s.toNat < 64 := s.isLt
  have hw : w.toNat < 16 := w.isLt
  have hs' : s'.toNat < 64 := s'.isLt
  have hw' : w'.toNat < 16 := w'.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  have h1 : s.toNat = s'.toNat := by omega
  have h2 : w.toNat = w'.toNat := by omega
  exact ⟨BitVec.toNat_inj.mp h1, BitVec.toNat_inj.mp h2⟩

/-- 字节掩码写的写后读一致性（核心，归纳形式）：写前 k 个通道后读字节 j：
    同行、j < k 且 mask[j] 置位 ⇒ 读到新字节；否则读到写前内容 -/
theorem l2mBsWriteLanes_read {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row row' : BitVec 10) (data : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) (k j : Nat) (hj : j < 128) :
    MemLaws.read (l2mBsWriteLanes m row data mask k) (row', BitVec.ofNat 7 j) =
      (if row' = row ∧ j < k ∧ mask.getLsbD j
       then l2mByteOf data j
       else MemLaws.read m (row', BitVec.ofNat 7 j)) := by
  induction k generalizing m with
  | zero => simp [l2mBsWriteLanes]
  | succ k ih =>
    show MemLaws.read
      (l2mBsWriteLanes
        (if mask.getLsbD k then MemLaws.write m (row, BitVec.ofNat 7 k) (l2mByteOf data k)
         else m)
        row data mask k) _ = _
    rw [ih]
    by_cases hmk : mask.getLsbD k
    · -- mask.getLsbD k = true ⇒ k < 128（超宽读出恒 false）
      have hk128 : k < 128 := by
        by_cases hkc : k < 128
        · exact hkc
        · exfalso
          have hge : l2mMaskBits ≤ k := by unfold l2mMaskBits; omega
          have hz := BitVec.getLsbD_of_ge mask k hge
          rw [hz] at hmk
          exact Bool.noConfusion hmk
      by_cases hrow : row' = row
      · subst row'
        by_cases hjk : j < k
        · have hne : (row, BitVec.ofNat 7 k) ≠ (row, BitVec.ofNat 7 j) := by
            intro h; rw [Prod.mk.injEq] at h
            have h1 := congrArg BitVec.toNat h.2
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
            rw [Nat.mod_eq_of_lt hk128, Nat.mod_eq_of_lt hj] at h1
            omega
          simp [hmk, hjk, show j < k + 1 by omega, hne, MemLaws.read_write_diff]
        · by_cases hjek : j = k
          · subst hjek
            have hlt : j < j + 1 := by omega
            have hnlt : ¬ j < j := by omega
            simp [hmk, hlt, hnlt, MemLaws.read_write_same]
          · have hgt : ¬ j < k + 1 := by omega
            have hne : (row, BitVec.ofNat 7 k) ≠ (row, BitVec.ofNat 7 j) := by
              intro h; rw [Prod.mk.injEq] at h
              have h1 := congrArg BitVec.toNat h.2
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
              rw [Nat.mod_eq_of_lt hk128, Nat.mod_eq_of_lt hj] at h1
              omega
            simp [hmk, hgt, show ¬ j < k by omega, hne, MemLaws.read_write_diff]
      · have hne : (row, BitVec.ofNat 7 k) ≠ (row', BitVec.ofNat 7 j) := by
          intro h; rw [Prod.mk.injEq] at h; exact hrow h.1.symm
        simp [hmk, hrow, hne, MemLaws.read_write_diff]
    · by_cases hrow : row' = row
      · subst row'
        by_cases hjek : j = k
        · subst hjek
          have hnlt : ¬ j < j := by omega
          have hlt : j < j + 1 := by omega
          simp [hmk, hnlt, hlt]
        · by_cases h1 : j < k
          · have h2 : j < k + 1 := by omega
            simp [hmk, h1, h2]
          · have h2 : ¬ j < k + 1 := by omega
            simp [hmk, h1, h2]
      · simp [hmk, hrow]

/-- 整行掩码写后读同字节：mask 置位 ⇒ 新字节，未置位 ⇒ 旧字节 -/
theorem l2mBsWriteRow_read_same {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row : BitVec 10) (data : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) (j : Nat) (hj : j < 128) :
    MemLaws.read (l2mBsWriteRow m row data mask) (row, BitVec.ofNat 7 j) =
      (if mask.getLsbD j then l2mByteOf data j
       else MemLaws.read m (row, BitVec.ofNat 7 j)) := by
  unfold l2mBsWriteRow
  rw [l2mBsWriteLanes_read m row row data mask l2mMaskBits j hj]
  have hjk : j < l2mMaskBits := hj
  by_cases hm : mask.getLsbD j <;> simp [hm, hjk]

/-- 整行掩码写不影响其他行 -/
theorem l2mBsWriteRow_read_diff {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row row' : BitVec 10) (data : BitVec l2mDataBits)
    (mask : BitVec l2mMaskBits) (j : Nat) (hj : j < 128) (hrow : row' ≠ row) :
    MemLaws.read (l2mBsWriteRow m row data mask) (row', BitVec.ofNat 7 j) =
      MemLaws.read m (row', BitVec.ofNat 7 j) := by
  unfold l2mBsWriteRow
  rw [l2mBsWriteLanes_read m row row' data mask l2mMaskBits j hj]
  simp [hrow]

/-- 读数据总线的字节级规约（BankedStore.scala:112，D8）：
    rdata 第 j 字节 = 存储 (row, j) 的内容 -/
theorem l2mBsReadRow_byte {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (m : M) (row : BitVec 10) (j : Nat) (hj : j < 128) :
    l2mByteOf (l2mBsReadRow m row) j = MemLaws.read m (row, BitVec.ofNat 7 j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold l2mByteOf l2mBsReadRow
  rw [BitVec.getLsbD_extractLsb', l2mByteLanes_getLsbD]
  have hj8 : 8 * j + i < l2mDataBits := by
    have : 8 * j + i < 1024 := by have hj' : j < 128 := hj; have hi' : i < 8 := hi; omega
    exact this
  have hdiv : (8 * j + i) / 8 = j := by have hi' : i < 8 := hi; omega
  have hmod : (8 * j + i) % 8 = i := by omega
  simp only [hdiv, hmod]
  have hj' : j < l2mMaskBits := hj
  have hi8 : i < 8 := hi
  rw [decide_eq_true hj8, decide_eq_true hj', decide_eq_true hi8]
  simp

/-- sinkD 写优先（D9）：sinkD valid 时 sourceD_wadr 被反压，写不丢 -/
theorem l2mBs_wadrReady (inp : L2mBsInput) (h : inp.sinkDValid = true) :
    l2mBsWadrReady inp = false := by
  simp [l2mBsWadrReady, h]

/-- 读口一拍延迟的正确性（D5/D6）：读 fire 且无同拍写冲突时，下一拍
    rdata 第 j 字节 = 读时刻存储内容（冲突情形见 Q5，真实硬件为毒化值） -/
theorem l2mBsStep_rdata {M : Type} [MemLaws M L2mBsAddr (BitVec 8)]
    (st : L2mBsState M) (inp : L2mBsInput)
    (hr : inp.radrValid = true) (j : Nat) (hj : j < 128) :
    l2mByteOf (l2mBsStep st inp).rdata j =
      MemLaws.read st.mem (l2mBsRowAddr inp.radrSet inp.radrWay, BitVec.ofNat 7 j) := by
  show l2mByteOf (if inp.radrValid = true then _ else st.rdata) j = _
  rw [if_pos hr]
  exact l2mBsReadRow_byte st.mem _ j hj

/-- BankedStore 测试用存储：SparseMem 实例 -/
abbrev L2mBsTestMem : Type := SparseMem L2mBsAddr (BitVec 8)

-- BsT1：全掩码写后读：写字节可读回，其他行不受影响
theorem l2mBsT1_full_write :
    let m0 : L2mBsTestMem := MemLaws.init
    let row := l2mBsRowAddr 5#6 3#4
    let m1 := l2mBsWriteRow m0 row 0xABCD#1024 (BitVec.allOnes l2mMaskBits)
    MemLaws.read m1 (row, BitVec.ofNat 7 0) = l2mByteOf 0xABCD#1024 0 ∧
    MemLaws.read m1 (row, BitVec.ofNat 7 127) = l2mByteOf 0xABCD#1024 127 ∧
    MemLaws.read m1 (l2mBsRowAddr 5#6 4#4, BitVec.ofNat 7 0) = 0#8 := by
  native_decide

-- BsT2：字节粒度掩码：先写低两字节，再写第 2、3 字节，验证逐字节独立
theorem l2mBsT2_byte_mask :
    let m0 : L2mBsTestMem := MemLaws.init
    let row := l2mBsRowAddr 0#6 0#4
    let m1 := l2mBsWriteRow m0 row 0xAABB#1024 0x3#128
    let m2 := l2mBsWriteRow m1 row 0xCCDD0000#1024 0xC#128
    MemLaws.read m2 (row, BitVec.ofNat 7 0) = 0xBB#8 ∧
    MemLaws.read m2 (row, BitVec.ofNat 7 1) = 0xAA#8 ∧
    MemLaws.read m2 (row, BitVec.ofNat 7 2) = 0xDD#8 ∧
    MemLaws.read m2 (row, BitVec.ofNat 7 3) = 0xCC#8 ∧
    MemLaws.read m2 (row, BitVec.ofNat 7 4) = 0#8 := by
  native_decide

-- BsT3：step 级：写后读一拍延迟呈现；sinkD 优先反压 sourceD_wadr
theorem l2mBsT3_step :
    let st0 : L2mBsState L2mBsTestMem := ⟨MemLaws.init, 0⟩
    let wIn : L2mBsInput :=
      ⟨false, 0, 0, 0, 0, false, 0, 0, true, 5#6, 3#4, BitVec.allOnes l2mMaskBits, 0xABCD#1024⟩
    let st1 := l2mBsStep st0 wIn
    let rIn : L2mBsInput :=
      ⟨false, 0, 0, 0, 0, true, 5#6, 3#4, false, 0, 0, 0, 0⟩
    let st2 := l2mBsStep st1 rIn
    l2mByteOf st2.rdata 0 = l2mByteOf 0xABCD#1024 0 ∧
    l2mByteOf st2.rdata 127 = l2mByteOf 0xABCD#1024 127 ∧
    l2mBsWadrReady { rIn with sinkDValid := true } = false := by
  native_decide

-- BsT4（Q5 检测）：同拍读写同行 ⇒ l2mBsCollision = true（真实硬件读毒化值）
theorem l2mBsT4_collision :
    let inp : L2mBsInput :=
      ⟨true, 5#6, 3#4, BitVec.allOnes l2mMaskBits, 0#1024,
       true, 5#6, 3#4, false, 0, 0, 0, 0⟩
    l2mBsCollision inp = true := by
  native_decide

/- 9. 公理审计（native_decide 定理带 _native.native_decide 信任公理，归档惯例；
   其余符号定理应只有 propext/Classical.choice/Quot.sound 标准公理） -/
#print axioms l2m_step_alloc
#print axioms l2m_scheA_noWithdraw
#print axioms l2m_sinkd_effect
#print axioms l2m_sinkd_dir_set
#print axioms l2m_dirValid_get
#print axioms l2mByteLanes_getLsbD
#print axioms l2mFullMask_getLsbD
#print axioms l2mMergeData_getLsbD
#print axioms l2mMergeData_byte
#print axioms l2mFullMask_allOnes
#print axioms l2mMergeData_allOnes
#print axioms l2mMergeData_zero
#print axioms l2mBsRowAddr_inj
#print axioms l2mBsWriteLanes_read
#print axioms l2mBsWriteRow_read_same
#print axioms l2mBsWriteRow_read_diff
#print axioms l2mBsReadRow_byte
#print axioms l2mBsStep_rdata
#print axioms l2mT6_trace
#print axioms l2mBsT2_byte_mask

end Ventus.L2.L2MSHR
