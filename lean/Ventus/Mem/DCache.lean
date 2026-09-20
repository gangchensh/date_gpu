/- ========================================================================= -/
/-                         Mem/DCache.lean                                   -/
/-  Ventus L1 DCache（L1Cache/DCache/DCache.scala，946 行）的 Lean 4 模型、   -/
/-  测试与证明。配套：DCacheParameters.scala（67 行）、DCacheWSHR.scala        -/
/-  （51 行）。WP4 访存群收官文件。                                          -/
/-                                                                           -/
/-  Chisel 源码对照（下文 :NNN 均指 DCache.scala；WSHR:NNN 指                 -/
/-  DCacheWSHR.scala；TA:NNN 指 L1TagAccess.scala）：                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/L1Cache/DCache/DCache.scala  -/
/-                                                                           -/
/-  例化配置（parameters.scala:71-91 + L1MSHR.lean 头部核查，2026-08-27）：   -/
/-    NSets=256, NWays=2, BlockWords=32, WordLength=32, NLanes=num_thread=32, -/
/-    BytesOfWord=4, SetIdxBits=8, BlockOffsetBits=5, WordOffsetBits=2,       -/
/-    TagBits=17, NMshrEntry=4, NMshrSubEntry=2, NWshrEntry=4,               -/
/-    MMU_ENABLED=false（:15）→ memReq 走 :868 分支（无 TLB 等待）。          -/
/-  注意：L1TagAccess.scala:63 的 num_lane = num_thread（parameters.scala:57  -/
/-    的 `// 2` 是 Scala 行注释而非除法！）= 32 = NLanes，与 DCache.scala:267  -/
/-    的 32 lane 连接一致（核实于 2026-08-27，排除"16/32 失配"疑点）。        -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 参数按唯一例化固化为字面量（见上）。                                  -/
/-  D2. 数据通路（genControl/genDataMapPerByte/relocateDataByte/              -/
/-      genDataMapSameWord/getDataAccessBankEn）为纯组合，逐行对应建模。      -/
/-      relocateDataByte（:136-153）的两个例化点（:445-446）均被注释——        -/
/-      死代码，建模但不参与集成。                                            -/
/-  D3. 时序控制核（§5）收窄建模：DCache 自有寄存器（st1 占位、               -/
/-      tagReplaceStatus、waitforL2flush、flushL2Reg、prevAllocWriteV、       -/
/-      coreRsp_st2/coreRsp_st2_valid 影队列、memRsp_Q 队头滞留）忠实建模；   -/
/-      L1MSHR/L1TagAccess/外部队列的内部状态抽象为输入（每拍的 hit/          -/
/-      waymask/needReplace/missRspOut/hasDirty 等），其可实现性由源码行号    -/
/-      与 L1MSHR.lean/L1TagAccess.lean 既有模型佐证。这样足以表达三条        -/
/-      挂账问题（I-28 可达性、LFSR 旁路、Q15 flush 响应）的完整时序链。      -/
/-  D4. coreRsp_Q（:191，32 深）不建模存储，只记录入队事件序列 rspLog        -/
/-      （响应正确性的考察对象就是"入队了什么 instrId"）。                    -/
/-  D5. coreRsp_st2（:246 Queue(1,pipe)）占位建模为 Option + 残留值          -/
/-      stale（Chisel 队列寄存器无复位，出队后 bits 保持——:754 的正确性       -/
/-      依赖这一保持语义，见 Q2）。                                           -/
/-  D6. 数据 SRAM（:637-659，32 bank 的 SRAMTemplate(UInt(8),512,4)）复用     -/
/-      SRAMTemplate.lean 的 sramCfgDCacheData（F,F,F,F），冲突读出语义用      -/
/-      sram_lfsr_bypass 对接，不重建阵列。                                   -/
/-  D7. miss 分配-回填-重放的 MSHR 内部行为不重复建模，直接对接               -/
/-      L1MSHR.lean 的既有定理；本文件只建 DCache 侧接口时序（:319-326、      -/
/-      :616-617、:690）。                                                   -/
/-  D8. AMO/LR/SC：genControl 译码忠实建模；DCache 对 opcode=2(AMO) 的        -/
/-      st1 处理落入 :477 的默认分支（ready:=true，无 tag/data/memReq/        -/
/-      coreRsp 效果）——与 I-16 结论一致：AtomicUnit 通路无消费者，AMO        -/
/-      请求在 DCache 内被静默吞掉。LR/SC 同。建模为 dcSt1Ready 的默认真。    -/
/-  D9. readHit_st2_valid 的保持重发分支（:700-704，coreRsp_Q 满时把 st2      -/
/-      数据重新入队）不建模——它只是同一数据的延迟重发，不影响本文件           -/
/-      考察的响应内容正确性。                                                -/
/-                                                                           -/
/- ======================== 源码审查发现（Q 区，详见返回报告） =============== -/
/-  Q1【I 类，I-28 可达性确认】见 §3：同请求内两 lane 同 blockOffset 不同      -/
/-      字节是合法输入（LSU.scala:273-279 按地址直出，genDataMapSameWord      -/
/-      :104-134 即为该情形存在）；数据/写掩码路径用 remap 后值（:410,:617）， -/
/-      dirtyMask 路径用未 remap 的 perLaneAddr（:267 → TA:241-245 覆盖       -/
/-      写）→ 先 lane 字节的脏位丢失 → 该字节在替换/flush 写回时被跳过，      -/
/-      L2 残留陈旧字节。机证：dcT_i28_asymmetry。                             -/
/-  Q2【I 类候选，flush/invalidate 响应路径】见 §5：flush/invalidate 的        -/
/-      coreRsp 唯一产生点是 :754 的 hintAck（memRsp d_opcode=2）项，其       -/
/-      bits 取自 coreRsp_st2.io.deq.bits；正常时序靠 :695-699 的 ghost        -/
/-      表项（fluCoreRsp_st1 等，无需 fire 即入队）提前把正确 instrId 预置    -/
/-      进 coreRsp_st2。两个脆点：(a) :425 的 memRspIsFluOrInv 无 valid        -/
/-      限定——memRsp_Q 消费 hintAck 后队头寄存器滞留 d_opcode=2，之后每次     -/
/-      flush/invalidate 的 waitforL2flush 只维持一拍就被误清（:423-427       -/
/-      when/elsewhen 链），st1 提前放行，ghost 预置停止，真 hintAck 到达时    -/
/-      coreRsp_st2 已被中间其他响应占用 → :754 入队携带**其他指令的**        -/
/-      instrId/isWrite/activeMask/数据（dcT_w2b_stale_instrId）；            -/
/-      (b) hintAck 当拍若 coreRsp_st2_valid=1（其他响应同拍出队），:754 的   -/
/-      OR 合并使 flush 响应整体丢失（dcT_w2c_rsp_lost）。对 LSU Q15：        -/
/-      release-invalidate 响应确实晚于 AMO 数据通路（要等 L2 hintAck），     -/
/-      不污染写回数据（响应数据不回写），但响应元数据在 (a)(b) 下错乱，      -/
/-      经 Coalscer 按 instrId 记账（pipeline/MSHR.scala:50-71）会污染        -/
/-      他指令表项或使目标指令永不完结。                                      -/
/-  Q3【I 类候选，LFSR 旁路可达性】见 §5/§6：SRAMTemplate.lean Q1 已钉死       -/
/-      dataReplaceReadValid × writeHit_st1 同拍同址读出 LFSR 值；本文件       -/
/-      证明该时序组合**可达**——probereadAllocateWriteConflict（:623）只拦     -/
/-      "allocateWrite 同拍的 coreReq.fire"（dc_fire_excludes_allocWrite），   -/
/-      但对"前一拍已进入 st1、因 coreRsp_st2 反压滞留的写请求"无拦截：       -/
/-      allocateWrite 拍 writer 在 st1 滞留，次拍 dataReplaceReadValid 与      -/
/-      writer 的 writeHit_st1 同拍同 (set,way)（dcT_w1_collision_reachable），-/
/-      victim 写回数据被 LFSR 污染（dcT_w1_sram_lfsr）。                      -/
/-  Q4【提示】:425 memRspIsFluOrInv 缺 valid 除 Q2(a) 外还使 flushL2_Reg       -/
/-      （:769-773）在 memRsp_Q 队头滞留 d_opcode=2 期间被反复清零，flushL2   -/
/-      的"只发一次"保护失效（靠 flushL2_Reg 重新置位兜底，功能上仍只发       -/
/-      一次，但依赖时序巧合）。                                              -/
/-  Q5【提示】:476 waitMSHR 分支的响应同样走 ghost 机制，但 waitMSHR 不发      -/
/-      L2 请求、无 hintAck → 其 coreRsp 永不产生（:754 的 hintAck 项不       -/
/-      触发，:695 的 ghost valid 影位为 false）。LSU 现行不发出 (3,2)         -/
/-      （LSU.scala:247-254 param 恒 0），故无实际死锁；属断臂路径。          -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Mem.SRAMTemplate
import Ventus.Mem.L1TagAccess
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 参数与地址路径（D1）                                                    -/
/- ========================================================================= -/

def dcNSets : Nat := 256          -- parameters.scala:71
def dcNWays : Nat := 2            -- :73
def dcBlockWords : Nat := 32      -- :75
def dcNLanes : Nat := 32          -- NLanes=num_thread=32（RVGParameter.scala:24,:9）
def dcWordLength : Nat := 32      -- xLen
def dcBytesOfWord : Nat := 4      -- WordLength/8
def dcSetIdxBits : Nat := 8       -- :78
def dcBlockOffsetBits : Nat := 5  -- :84
def dcWordOffsetBits : Nat := 2   -- :82
def dcTagBits : Nat := 17         -- :86 = 32-(8+5+2)
def dcNWshrEntry : Nat := 4       -- :76
def dcNMshrEntry : Nat := 4       -- :88
def dcNMshrSubEntry : Nat := 2    -- :90

/-- blockAddr = Cat(tag, setIdx)（:276、:325 等），bABits=17+8=25。 -/
def dcBlockAddr (tag : BitVec 17) (setIdx : BitVec 8) : BitVec 25 :=
  (tag.zeroExtend 25 <<< 8) ||| setIdx.zeroExtend 25

/-- get_tag（L1CacheParameters.scala:54）。 -/
def dcGetTag (ba : BitVec 25) : BitVec 17 := ba.extractLsb' 8 17

/-- get_setIdx 的 blockAddr 分支（L1CacheParameters.scala:57-58）。 -/
def dcGetSetIdx (ba : BitVec 25) : BitVec 8 := ba.extractLsb' 0 8

/-- memRsp d_source 低 8 位 = setIdx（:621 的 allocateWrite setIdx、:578）。 -/
def dcMemRspSetIdx (dSource : BitVec 12) : BitVec 8 := dSource.extractLsb' 0 8

/-- memRsp d_source 的 WSHR 下标段（:550，SetIdxBits 之上 log2Up(4)=2 位）。 -/
def dcWshrIdx (dSource : BitVec 12) : BitVec 2 := dSource.extractLsb' 8 2

/-- 地址路径装配/分解往返。 -/
theorem dc_blockAddr_roundtrip (tag : BitVec 17) (setIdx : BitVec 8) :
    dcGetTag (dcBlockAddr tag setIdx) = tag ∧
    dcGetSetIdx (dcBlockAddr tag setIdx) = setIdx := by
  constructor <;> simp [dcGetTag, dcGetSetIdx, dcBlockAddr] <;> bv_decide

/-- 数值回归：tag=0x1ABCD, setIdx=0x5A。 -/
theorem dcT_blockAddr :
    dcBlockAddr 0x1ABCD#17 0x5A#8 = 0x1ABCD5A#25 ∧
    dcGetTag 0x1ABCD5A#25 = 0x1ABCD#17 ∧
    dcGetSetIdx 0x1ABCD5A#25 = 0x5A#8 ∧
    dcMemRspSetIdx 0x35A#12 = 0x5A#8 ∧
    dcWshrIdx 0x35A#12 = 0b11#2 := by native_decide

/- ========================================================================= -/
/- 2. genControl：opcode/param → 控制（:40-83，D2）                           -/
/- ========================================================================= -/

/-- DCacheControl（:29-38）。 -/
structure DcCtrl where
  isRead : Bool
  isWrite : Bool
  isLR : Bool
  isSC : Bool
  isAMO : Bool
  isFlush : Bool
  isInvalidate : Bool
  isWaitMSHR : Bool
deriving DecidableEq, Repr

def dcCtrlIdle : DcCtrl :=
  { isRead := false, isWrite := false, isLR := false, isSC := false,
    isAMO := false, isFlush := false, isInvalidate := false, isWaitMSHR := false }

/-- genControl（:55-82 的 switch 链，逐项展开）。 -/
def dcGenControl (op : BitVec 3) (prm : BitVec 4) : DcCtrl :=
  if op = 0#3 then
    if prm = 0#4 then { dcCtrlIdle with isRead := true }
    else if prm = 1#4 then { dcCtrlIdle with isLR := true }
    else dcCtrlIdle
  else if op = 1#3 then
    if prm = 0#4 then { dcCtrlIdle with isWrite := true }
    else if prm = 1#4 then { dcCtrlIdle with isSC := true }
    else dcCtrlIdle
  else if op = 2#3 then { dcCtrlIdle with isAMO := true }
  else if op = 3#3 then
    if prm = 0#4 then { dcCtrlIdle with isInvalidate := true }
    else if prm = 1#4 then { dcCtrlIdle with isFlush := true }
    else if prm = 2#4 then { dcCtrlIdle with isWaitMSHR := true }
    else dcCtrlIdle
  else dcCtrlIdle

/-- 数值回归：八种控制各一条。 -/
theorem dcT_genControl :
    dcGenControl 0#3 0#4 = { dcCtrlIdle with isRead := true } ∧
    dcGenControl 0#3 1#4 = { dcCtrlIdle with isLR := true } ∧
    dcGenControl 1#3 0#4 = { dcCtrlIdle with isWrite := true } ∧
    dcGenControl 1#3 1#4 = { dcCtrlIdle with isSC := true } ∧
    dcGenControl 2#3 7#4 = { dcCtrlIdle with isAMO := true } ∧
    dcGenControl 3#3 0#4 = { dcCtrlIdle with isInvalidate := true } ∧
    dcGenControl 3#3 1#4 = { dcCtrlIdle with isFlush := true } ∧
    dcGenControl 3#3 2#4 = { dcCtrlIdle with isWaitMSHR := true } := by
  native_decide

/-- 至多一个控制位为真（3+4=7 位全枚举）。 -/
theorem dc_genControl_onehot : ∀ (op : BitVec 3) (prm : BitVec 4),
    (if dcGenControl op prm |>.isRead then 1 else 0) +
    (if dcGenControl op prm |>.isWrite then 1 else 0) +
    (if dcGenControl op prm |>.isLR then 1 else 0) +
    (if dcGenControl op prm |>.isSC then 1 else 0) +
    (if dcGenControl op prm |>.isAMO then 1 else 0) +
    (if dcGenControl op prm |>.isFlush then 1 else 0) +
    (if dcGenControl op prm |>.isInvalidate then 1 else 0) +
    (if dcGenControl op prm |>.isWaitMSHR then 1 else 0) ≤ 1 := by
  native_decide

/-- AMO 译码（op=2）不携带任何读/写/维护语义——配合 :477 默认分支即 I-16 的
    "AMO 在 DCache 内被吞掉"（D8）。 -/
theorem dc_genControl_amo_noop : ∀ (prm : BitVec 4),
    let c := dcGenControl 2#3 prm
    c.isAMO = true ∧ c.isRead = false ∧ c.isWrite = false ∧
    c.isFlush = false ∧ c.isInvalidate = false ∧ c.isWaitMSHR = false := by
  native_decide

/- ========================================================================= -/
/- 3. 数据通路（D2）：per-lane 字节对齐、同字多 lane 合并、bank 使能          -/
/- ========================================================================= -/

/-- DCachePerLaneAddr（L1Interfaces.scala:29-33）：activeMask + blockOffset(5) +
    wordOffset1H(4)。 -/
structure DcLane where
  activeMask : Bool
  blockOffset : BitVec 5
  wordOffset1H : BitVec 4
deriving DecidableEq, Repr

/-- 单热判定（PopCount(m)=1 的等价形式，避开 cpop 位宽问题）。 -/
def dcOneHot4 (m : BitVec 4) : Bool := m ≠ 0#4 && (m &&& (m - 1#4)) = 0#4

/-- OHToUInt（4 位输入）：bit0 = m[1]||m[3]，bit1 = m[2]||m[3]（多热时为下标
    按位或，与 Chisel OHToUInt 语义一致）。 -/
def dcOHToUInt4 (m : BitVec 4) : BitVec 2 :=
  (if ((m >>> 2) &&& 1#4 = 1#4) || ((m >>> 3) &&& 1#4 = 1#4) then 0b10#2 else 0#2) |||
  (if ((m >>> 1) &&& 1#4 = 1#4) || ((m >>> 3) &&& 1#4 = 1#4) then 0b01#2 else 0#2)

/-- 字节左移对齐：oh ∈ 0..3 → 移位量 oh*8（字面移位链，bv_decide 友好）。 -/
def dcShiftByteL (ori : BitVec 32) (oh : BitVec 2) : BitVec 32 :=
  if oh = 0#2 then ori
  else if oh = 1#2 then ori <<< 8
  else if oh = 2#2 then ori <<< 16
  else ori <<< 24

def dcShiftByteR (ori : BitVec 32) (oh : BitVec 2) : BitVec 32 :=
  if oh = 0#2 then ori
  else if oh = 1#2 then ori >>> 8
  else if oh = 2#2 then ori >>> 16
  else ori >>> 24

/-- genDataMapPerByte（:91-101）：写路径字节对齐（左移）。移位量语义
    （OHToUInt 值 ×8，:95）由 dc_mapByte_onehot 钉死（避免 toNat 进 bv_decide）。 -/
def dcMapByte (ori : BitVec 32) (m : BitVec 4) : BitVec 32 :=
  if m = 0b1111#4 then ori                                        -- andR
  else if dcOneHot4 m then dcShiftByteL ori (dcOHToUInt4 m)       -- PopCount=1
  else if (m >>> 2) &&& 0b11#4 = 0b11#4 then ori <<< 16           -- m(3,2)==3
  else ori

/-- relocateDataByte（:142-152）：读路径字节归位（右移）。注意两个例化点
    （:445-446）均被注释——死代码（D2）。 -/
def dcRelocByte (ori : BitVec 32) (m : BitVec 4) : BitVec 32 :=
  if m = 0b1111#4 then ori
  else if dcOneHot4 m then dcShiftByteR ori (dcOHToUInt4 m)
  else if (m >>> 2) &&& 0b11#4 = 0b11#4 then ori >>> 16
  else ori

/-- 同字多 lane 匹配（:114-122）：双 active 且 blockOffset 相等。 -/
def dcBlockMatch (lanes : Fin 32 → DcLane) (i j : Fin 32) : Bool :=
  (lanes i).activeMask && (lanes j).activeMask && ((lanes i).blockOffset == (lanes j).blockOffset)

/-- genDataMapSameWord 的 perLaneAddrRemap(i).wordOffset1H（:126,:129）：
    所有与 lane i 同字的活跃 lane 的字节掩码按位或。 -/
def dcRemapMask (lanes : Fin 32 → DcLane) (i : Fin 32) : BitVec 4 :=
  (List.finRange 32).foldl (fun acc j =>
    if dcBlockMatch lanes i j then acc ||| (lanes j).wordOffset1H else acc) 0#4

/-- genDataMapSameWord 的 dataout(i)（:127,:130）。 -/
def dcRemapData (lanes : Fin 32 → DcLane) (dat : Fin 32 → BitVec 32) (i : Fin 32) : BitVec 32 :=
  (List.finRange 32).foldl (fun acc j =>
    if dcBlockMatch lanes i j then acc ||| dat j else acc) 0#32

/-- writeMissReq.a_mask(j)（:616-619）：word j 的掩码 = 所有落在 word j 的活跃
    lane 的 **remap 后** 掩码之或。 -/
def dcWriteMissMaskWord (lanes : Fin 32 → DcLane) (j : BitVec 5) : BitVec 4 :=
  (List.finRange 32).foldl (fun acc i =>
    if (lanes i).activeMask && (lanes i).blockOffset == j
    then acc ||| dcRemapMask lanes i else acc) 0#4

/-- getDataAccessBankEn 的 perBankValid（:884）。 -/
def dcBankValid (lanes : Fin 32 → DcLane) (b : BitVec 5) : Bool :=
  (List.finRange 32).any (fun l => (lanes l).activeMask && (lanes l).blockOffset == b)

/-- getDataAccessBankEn 的 perBankBlockIdx（:885，PriorityEncoder = 最低下标）。 -/
def dcBankLane (lanes : Fin 32 → DcLane) (b : BitVec 5) : Fin 32 :=
  ((List.finRange 32).find? (fun l =>
    (lanes l).activeMask && (lanes l).blockOffset == b)).getD ⟨0, by decide⟩

/- ---- 字节对齐/归位数值测试 ---- -/

theorem dcT_onehot4 : ∀ m : BitVec 4,
    dcOneHot4 m = true ↔ (m = 1#4 ∨ m = 2#4 ∨ m = 4#4 ∨ m = 8#4) := by native_decide

theorem dcT_ohToUInt4 :
    dcOHToUInt4 0b0001#4 = 0#2 ∧ dcOHToUInt4 0b0010#4 = 1#2 ∧
    dcOHToUInt4 0b0100#4 = 2#2 ∧ dcOHToUInt4 0b1000#4 = 3#2 := by native_decide

/-- 字节对齐：单热 mask 把 byte0 搬到对应字节位（全 32 位数据 ∀ 量化 + bv_decide）。 -/
theorem dc_mapByte_onehot : ∀ ori : BitVec 32,
    (dcMapByte ori 0b0001#4) &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    (dcMapByte ori 0b0010#4) >>> 8 &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    (dcMapByte ori 0b0100#4) >>> 16 &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    (dcMapByte ori 0b1000#4) >>> 24 &&& 0xFF#32 = ori &&& 0xFF#32 := by
  intro ori
  simp only [dcMapByte, dcOneHot4, dcOHToUInt4, dcShiftByteL]
  bv_decide

/-- 归位为其逆。 -/
theorem dc_relocByte_onehot : ∀ ori : BitVec 32,
    dcRelocByte (ori <<< 0) 0b0001#4 &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    dcRelocByte (ori <<< 8) 0b0010#4 &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    dcRelocByte (ori <<< 16) 0b0100#4 &&& 0xFF#32 = ori &&& 0xFF#32 ∧
    dcRelocByte (ori <<< 24) 0b1000#4 &&& 0xFF#32 = ori &&& 0xFF#32 := by
  intro ori
  simp only [dcRelocByte, dcOneHot4, dcOHToUInt4, dcShiftByteR]
  bv_decide

theorem dcT_mapByte :
    dcMapByte 0x000000AB#32 0b0010#4 = 0x0000AB00#32 ∧   -- byte1
    dcMapByte 0x0000ABCD#32 0b1100#4 = 0xABCD0000#32 ∧   -- half 高半字
    dcMapByte 0x89ABCDEF#32 0b1111#4 = 0x89ABCDEF#32 ∧   -- 整字
    dcMapByte 0x89ABCDEF#32 0b0011#4 = 0x89ABCDEF#32 := by native_decide

/- ---- or-折叠通用引理 ---- -/

theorem dcAnd_or_self {w : Nat} (a b : BitVec w) : ((a ||| b) &&& b) = b := by
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> rfl

theorem dcOr_sup {w : Nat} (a b c : BitVec w) (h : (a &&& c) = c) :
    ((a ||| b) &&& c) = c := by
  ext i
  have hi : (a &&& c)[i] = c[i] := by rw [h]
  simp only [BitVec.getElem_and] at hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases ha : a[i] <;> cases hb : b[i] <;> cases hc : c[i] <;> simp_all

theorem dcAnd_sup_trans {w : Nat} (a b c : BitVec w)
    (h1 : (a &&& b) = b) (h2 : (b &&& c) = c) : (a &&& c) = c := by
  ext i
  have h1' : (a &&& b)[i] = b[i] := by rw [h1]
  have h2' : (b &&& c)[i] = c[i] := by rw [h2]
  simp only [BitVec.getElem_and] at h1' h2'
  simp only [BitVec.getElem_and]
  cases ha : a[i] <;> cases hb : b[i] <;> cases hc : c[i] <;> simp_all

/-- List.mem_split 的本地版（核心库无此名）。 -/
theorem dcMemSplit {α : Type} {l : List α} {a : α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨[], l, rfl⟩
    · obtain ⟨s, t, rfl⟩ := ih h'
      exact ⟨b :: s, t, rfl⟩

/-- 条件 or-折叠的保持性：一旦 x 已被并入（(init &&& x) = x），后续折叠保持。 -/
theorem dcFoldl_cor_sup {w : Nat} (xs : List (Fin 32)) (c : Fin 32 → Bool)
    (f : Fin 32 → BitVec w) (init x : BitVec w) (h : (init &&& x) = x) :
    ((xs.foldl (fun acc i => if c i then acc ||| f i else acc) init) &&& x) = x := by
  induction xs generalizing init with
  | nil => exact h
  | cons a t ih =>
    rw [List.foldl_cons]
    by_cases hc : c a = true
    · rw [if_pos hc]; exact ih (init ||| f a) (dcOr_sup init (f a) x h)
    · rw [if_neg hc]; exact ih init h

/-- 条件 or-折叠的上集性：若 l ∈ xs 且 c l，则 f l 是折叠结果的子集。 -/
theorem dcFoldl_cor_mem {w : Nat} (xs : List (Fin 32)) (c : Fin 32 → Bool)
    (f : Fin 32 → BitVec w) (l : Fin 32) (init : BitVec w)
    (hl : l ∈ xs) (hc : c l = true) :
    ((xs.foldl (fun acc i => if c i then acc ||| f i else acc) init) &&& f l) = f l := by
  obtain ⟨pre, suf, rfl⟩ := dcMemSplit hl
  rw [List.foldl_append, List.foldl_cons, if_pos hc]
  exact dcFoldl_cor_sup suf c f _ _ (dcAnd_or_self _ _)

/- ---- 同字多 lane 合并的正确性 ---- -/

/-- **数据路径合并不漏字节**（:126-130）：lane l 与 lane i 同字（双活跃）时，
    l 的字节掩码 ⊂ remap 后 lane i 的掩码。 -/
theorem dcRemapMask_includes (lanes : Fin 32 → DcLane) (i l : Fin 32)
    (hm : dcBlockMatch lanes i l = true) :
    (dcRemapMask lanes i &&& (lanes l).wordOffset1H) = (lanes l).wordOffset1H :=
  dcFoldl_cor_mem (List.finRange 32) (dcBlockMatch lanes i)
    (fun j => (lanes j).wordOffset1H) l 0#4 (List.mem_finRange l) hm

theorem dcRemapData_includes (lanes : Fin 32 → DcLane) (dat : Fin 32 → BitVec 32) (i l : Fin 32)
    (hm : dcBlockMatch lanes i l = true) :
    (dcRemapData lanes dat i &&& dat l) = dat l :=
  dcFoldl_cor_mem (List.finRange 32) (dcBlockMatch lanes i) dat l 0#32
    (List.mem_finRange l) hm

/-- **写 miss 掩码完整**（:616-619）：活跃 lane l 落在 word j 时，其字节掩码
    ⊂ writeMissReq.a_mask(j)——数据/掩码路径对同字多 lane 是**正确合并**的。 -/
theorem dcWriteMissMask_complete (lanes : Fin 32 → DcLane) (j : BitVec 5) (l : Fin 32)
    (hact : (lanes l).activeMask = true) (hbo : (lanes l).blockOffset = j) :
    (dcWriteMissMaskWord lanes j &&& (lanes l).wordOffset1H) = (lanes l).wordOffset1H := by
  unfold dcWriteMissMaskWord
  apply dcAnd_sup_trans _ (dcRemapMask lanes l) _
  · apply dcFoldl_cor_mem (List.finRange 32)
      (fun i => (lanes i).activeMask && (lanes i).blockOffset == j)
      (fun i => dcRemapMask lanes i) l 0#4 (List.mem_finRange l)
    simp [hact, hbo]
  · exact dcRemapMask_includes lanes l l (by simp [dcBlockMatch, hact])

/- ---- bank 使能 ---- -/

/-- perBankValid 语义：bank b 有效 ⟺ 存在活跃 lane 落在 b。 -/
theorem dcBankValid_iff (lanes : Fin 32 → DcLane) (b : BitVec 5) :
    dcBankValid lanes b = true ↔
      ∃ l : Fin 32, (lanes l).activeMask = true ∧ (lanes l).blockOffset = b := by
  unfold dcBankValid
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, hx⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨l, ha, hb⟩
    exact ⟨l, List.mem_finRange l, by simp [ha, hb]⟩

/-- perBankBlockIdx 选中合法 lane（最低性只做数值抽查）。 -/
theorem dcBankLane_spec (lanes : Fin 32 → DcLane) (b : BitVec 5)
    (hv : dcBankValid lanes b = true) :
    (lanes (dcBankLane lanes b)).activeMask = true ∧
    (lanes (dcBankLane lanes b)).blockOffset = b := by
  unfold dcBankLane
  have hany : ∃ l ∈ List.finRange 32,
      ((lanes l).activeMask && (lanes l).blockOffset == b) = true :=
    List.any_eq_true.mp hv
  have hne : (List.finRange 32).find? (fun l =>
      (lanes l).activeMask && (lanes l).blockOffset == b) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    obtain ⟨l, hl, hp⟩ := hany
    exact absurd hp (hnone l hl)
  have hex : ∃ y, (List.finRange 32).find? (fun l =>
      (lanes l).activeMask && (lanes l).blockOffset == b) = some y := by
    cases h : (List.finRange 32).find? (fun l =>
      (lanes l).activeMask && (lanes l).blockOffset == b) with
    | none => exact absurd h hne
    | some y => exact ⟨y, rfl⟩
  obtain ⟨y, hy⟩ := hex
  rw [hy, Option.getD_some]
  have hp := List.find?_some hy
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

/- ---- I-28 可达性 witness（Q1） ---- -/

/-- witness 输入：lane5 写 block3 的 byte0，lane27 写同 block3 的 byte1，
    其余 lane 不活跃——LSU 对相邻地址的两次 SB 即产生此形（LSU.scala:273-279
    按地址直出 blockOffset/wordOffset1H，无同字合并；合并由 DCache 的
    genDataMapSameWord 在数据路径上补做）。 -/
def dcI28Lanes : Fin 32 → DcLane := fun i =>
  if i = ⟨5, by decide⟩ then ⟨true, 3#5, 0b0001#4⟩
  else if i = ⟨27, by decide⟩ then ⟨true, 3#5, 0b0010#4⟩
  else ⟨false, 0#5, 0#4⟩

/-- **Q1 / I-28 可达性确认**：同一拍 st1 输入下——
    * 数据路径（:410 的写命中 waymask、:617 的写 miss a_mask，均用 remap 后值）
      两 lane 的字节齐全（0b0011）；
    * dirtyMask 路径（:267 把**未 remap** 的 perLaneAddr 送入 TagAccess，
      TA:241-245 lane 升序覆盖）只剩 lane27 的 byte1，lane5 的 byte0 脏位丢失。
    后果：该行被替换/flush 时写回 L2 的掩码（:605 dirtyReplace、:501 InvOrFlu）
    缺 byte0 → L2 残留陈旧字节（L1 内数据本身已正确合并写入）。 -/
theorem dcT_i28_asymmetry :
    dcWriteMissMaskWord dcI28Lanes 3#5 = 0b0011#4 ∧
    dcRemapMask dcI28Lanes ⟨5, by decide⟩ = 0b0011#4 ∧
    dcRemapMask dcI28Lanes ⟨27, by decide⟩ = 0b0011#4 ∧
    l1taDmBuild ((fun i =>
      if i = 5 then (true, 3, 0b0001#4)
      else if i = 27 then (true, 3, 0b0010#4)
      else (false, 0, 0#4)) : Fin 32 → L1taLane 32 4) = (0b0010#4).zeroExtend 128 <<< 12 := by
  refine ⟨?_, ?_, ?_, l1taT_dmBuild_overwrite_real⟩ <;> native_decide

/- ========================================================================= -/
/- 4. DCacheWSHR（DCacheWSHR.scala 全文 51 行）：写 miss 在飞写回登记表        -/
/- ========================================================================= -/

/-- WSHR 状态（WSHR:25-26）：4 项 blockAddr(25b) + valid。 -/
structure DcwState where
  entries : Fin 4 → BitVec 25
  valid : Fin 4 → Bool

/-- RegInit 全 0/全 invalid（WSHR:25-26）。 -/
def dcwInit : DcwState := ⟨fun _ => 0#25, fun _ => false⟩

/-- io.empty（WSHR:27）。 -/
def dcwEmpty (s : DcwState) : Bool := !(List.finRange 4).any (fun i => s.valid i)

/-- io.conflict（WSHR:30-34）：某有效项 blockAddr 相等。 -/
def dcwConflict (s : DcwState) (ba : BitVec 25) : Bool :=
  (List.finRange 4).any (fun i => s.valid i && (s.entries i == ba))

/-- pushReq.ready = !full（WSHR:37）。 -/
def dcwFull (s : DcwState) : Bool := (List.finRange 4).all (fun i => s.valid i)

/-- nextEntryIdx = indexWhere(!valid)（WSHR:39，无空位时为 0——此时 full，
    pushReq.ready=false 不会 fire，取值无关）。 -/
def dcwNextFree (s : DcwState) : Fin 4 :=
  ((List.finRange 4).find? (fun i => !(s.valid i))).getD ⟨0, by decide⟩

/-- io.pushedIdx（WSHR:41）：同拍 push+pop 复用 pop 槽，否则最低空槽。 -/
def dcwPushedIdx (s : DcwState) (pushV popV : Bool) (popIdx : Fin 4) : Fin 4 :=
  if pushV && !dcwFull s && popV then popIdx else dcwNextFree s

/-- 单拍转移（WSHR:42-50）。pushFire = pushReq.fire = pushV && !full；
    popReq 是 ValidIO，valid 即生效（WSHR:48 用 valid 而非 fire）。 -/
def dcwStep (s : DcwState) (pushV : Bool) (ba : BitVec 25) (popV : Bool)
    (popIdx : Fin 4) : DcwState :=
  let pushFire := pushV && !dcwFull s
  if pushFire && popV then
    ⟨sramUpd s.entries popIdx ba, sramUpd s.valid popIdx true⟩
  else if pushFire then
    ⟨sramUpd s.entries (dcwNextFree s) ba, sramUpd s.valid (dcwNextFree s) true⟩
  else if popV then
    ⟨s.entries, sramUpd s.valid popIdx false⟩
  else s

/-- conflict 的命题形式：结果 bit 精确对应"某有效项同址"。 -/
theorem dcw_conflict_iff (s : DcwState) (ba : BitVec 25) :
    dcwConflict s ba = true ↔ ∃ i : Fin 4, s.valid i = true ∧ s.entries i = ba := by
  unfold dcwConflict
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, hx⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨i, hv, he⟩
    exact ⟨i, List.mem_finRange i, by simp [hv, he]⟩

/-- 无冲突 ⇒ 任何有效项都不同址（上游 wshrProtect :806 依赖此判定）。 -/
theorem dcw_not_conflict (s : DcwState) (ba : BitVec 25) (h : dcwConflict s ba = false) :
    ∀ i : Fin 4, s.valid i = true → s.entries i ≠ ba := by
  intro i hv he
  have : dcwConflict s ba = true := (dcw_conflict_iff s ba).mpr ⟨i, hv, he⟩
  rw [h] at this
  exact Bool.noConfusion this

/-- 非满 ⇒ nextFree 槽原本无效。 -/
theorem dcw_nextFree_invalid (s : DcwState) (h : dcwFull s = false) :
    s.valid (dcwNextFree s) = false := by
  have hany : (List.finRange 4).any (fun i => !s.valid i) = true := by
    cases hany : (List.finRange 4).any (fun i => !s.valid i) with
    | true => rfl
    | false =>
      exfalso
      have hall : dcwFull s = true := by
        rw [dcwFull, List.all_eq_true]
        intro x _
        cases hx : s.valid x with
        | true => rfl
        | false =>
          have hxf := List.any_eq_false.mp hany x (List.mem_finRange x)
          rw [hx] at hxf
          simp at hxf
      rw [hall] at h
      exact Bool.noConfusion h
  obtain ⟨x, -, hx⟩ := List.any_eq_true.mp hany
  have hne : (List.finRange 4).find? (fun i => !s.valid i) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    exact absurd hx (hnone x (List.mem_finRange x))
  unfold dcwNextFree
  have hex : ∃ y, (List.finRange 4).find? (fun i => !s.valid i) = some y := by
    cases hf : (List.finRange 4).find? (fun i => !s.valid i) with
    | none => exact absurd hf hne
    | some y => exact ⟨y, rfl⟩
  obtain ⟨y, hy⟩ := hex
  rw [hy, Option.getD_some]
  have hs := List.find?_some hy
  simpa using hs

/-- 纯 pop：该槽清零（WSHR:48-49）。 -/
theorem dcw_pop_clears (s : DcwState) (ba : BitVec 25) (i : Fin 4) :
    (dcwStep s false ba true i).valid i = false := by
  simp [dcwStep, sramUpd]

/-- 纯 push（非满）：写入 nextFree 槽并置位（WSHR:45-46）。 -/
theorem dcw_push_sets (s : DcwState) (ba : BitVec 25) (h : dcwFull s = false) :
    (dcwStep s true ba false ⟨0, by decide⟩).entries (dcwNextFree s) = ba ∧
    (dcwStep s true ba false ⟨0, by decide⟩).valid (dcwNextFree s) = true := by
  simp [dcwStep, h, sramUpd]

/-- 同拍 push+pop：pop 槽被新请求复用（WSHR:42-44）。 -/
theorem dcw_pushpop_recycle (s : DcwState) (ba : BitVec 25) (i : Fin 4)
    (h : dcwFull s = false) :
    (dcwStep s true ba true i).entries i = ba ∧
    (dcwStep s true ba true i).valid i = true := by
  simp [dcwStep, h, sramUpd]

/-- WSHR:33 断言的前 half：状态无重复有效项。 -/
def dcwDistinct (s : DcwState) : Prop :=
  ∀ i j : Fin 4, s.valid i = true → s.valid j = true → s.entries i = s.entries j → i = j

/-- 无冲突的 push 保持无重复（WSHR:33 的 assert 在 wshrProtect 守护下成立）。 -/
theorem dcwDistinct_push (s : DcwState) (ba : BitVec 25)
    (hd : dcwDistinct s) (hfull : dcwFull s = false) (hconf : dcwConflict s ba = false) :
    dcwDistinct (dcwStep s true ba false ⟨0, by decide⟩) := by
  have hnc := dcw_not_conflict s ba hconf
  have hve : ∀ k : Fin 4, (dcwStep s true ba false ⟨0, by decide⟩).valid k =
      sramUpd s.valid (dcwNextFree s) true k := by
    intro k; simp [dcwStep, hfull]
  have hee : ∀ k : Fin 4, (dcwStep s true ba false ⟨0, by decide⟩).entries k =
      sramUpd s.entries (dcwNextFree s) ba k := by
    intro k; simp [dcwStep, hfull]
  intro i j hi hj he
  rw [hve i] at hi; rw [hve j] at hj; rw [hee i, hee j] at he
  by_cases hii : dcwNextFree s = i <;> by_cases hjj : dcwNextFree s = j
  · exact hii.symm.trans hjj
  · subst hii
    rw [sramUpd_self, sramUpd_of_ne _ _ _ _ (Ne.symm hjj)] at he
    rw [sramUpd_of_ne _ _ _ _ (Ne.symm hjj)] at hj
    exact absurd he.symm (hnc j hj)
  · subst hjj
    rw [sramUpd_self, sramUpd_of_ne _ _ _ _ (Ne.symm hii)] at he
    rw [sramUpd_of_ne _ _ _ _ (Ne.symm hii)] at hi
    exact absurd he (hnc i hi)
  · rw [sramUpd_of_ne _ _ _ _ (Ne.symm hii), sramUpd_of_ne _ _ _ _ (Ne.symm hjj)] at he
    rw [sramUpd_of_ne _ _ _ _ (Ne.symm hii)] at hi
    rw [sramUpd_of_ne _ _ _ _ (Ne.symm hjj)] at hj
    exact hd i j hi hj he

/- ---- WSHR 数值回归 ---- -/

/-- 轨迹：push A → push B → 查冲突 → pop 槽1 → push C（落到槽1）。 -/
def dcwT1 := dcwStep dcwInit true 0x111#25 false ⟨0, by decide⟩
def dcwT2 := dcwStep dcwT1 true 0x222#25 false ⟨0, by decide⟩
def dcwT3 := dcwStep dcwT2 false 0#25 true ⟨1, by decide⟩
def dcwT4 := dcwStep dcwT3 true 0x333#25 false ⟨0, by decide⟩

theorem dcT_wshr_flow :
    dcwEmpty dcwInit = true ∧
    dcwConflict dcwT2 0x222#25 = true ∧
    dcwConflict dcwT2 0x333#25 = false ∧
    dcwFull dcwT2 = false ∧
    (dcwT3.valid ⟨1, by decide⟩) = false ∧
    dcwT4.entries ⟨1, by decide⟩ = 0x333#25 ∧
    dcwT4.valid ⟨1, by decide⟩ = true ∧
    dcwPushedIdx dcwT2 true true ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
  native_decide

/- ========================================================================= -/
/- 5. 时序控制核（D3-D5、D8、D9）                                              -/
/- ========================================================================= -/

/-- coreRsp_st2 数据队列表项（:246 的 DCacheCoreRsp_d 收窄到 instrId/isWrite——
    data/activeMask 不影响响应路由正确性的判定）。 -/
structure DcRspSt2 where
  instrId : BitVec 3
  isWrite : Bool
deriving DecidableEq, Repr

/-- st1 驻留请求（coreReq_Q :188 与 coreReqControl_st1_Q :232 同拍入/出，
    对齐性论证见 D3 注：:261 的 opcode3 分歧条件因 genControl 下 op3 ⟹ !isRead
    而恒假，两队列不会错位）。 -/
structure DcSt1 where
  ctrl : DcCtrl
  opcode3 : Bool
  setIdx : BitVec 8
  instrId : BitVec 3
deriving DecidableEq, Repr

/-- DCache 自有寄存器（D3）。 -/
structure DcState where
  st1 : Option DcSt1            -- coreReq_Q+ctrl_Q 占位
  tagReplaceStatus : Bool       -- :440
  waitforL2flush : Bool         -- :207
  flushL2Reg : Bool             -- :768
  prevAllocWriteV : Bool        -- RegNext(allocateWrite.valid)（:579/:633）
  prevProbeStatus4 : Bool       -- secondaryFullReturn（:228）
  fromMemRsp : Bool             -- coreRsp_st2_valid_from_memRsp（:745 RegEnable）
  rspSt2 : Option DcRspSt2      -- coreRsp_st2 占位（:246）
  rspSt2Stale : BitVec 3        -- 空时 deq.bits 残留 instrId（D5）
  rspVld : Option Bool          -- coreRsp_st2_valid_from_coreReq_Reg 占位（:243）
  rspLog : List (BitVec 3)      -- coreRsp_Q 入队 instrId 事件序列（D4，:753-754）
deriving DecidableEq, Repr

/-- 每拍输入：环境与子模块抽象信号（行号见各字段注）。 -/
structure DcIn where
  fire : Option DcSt1        -- 本拍 io.coreReq.fire 进入的请求（:212-219 全项成立）
  missRspOutV : Bool         -- MSHR missRspOut.valid（:314）
  missRspInstrId : BitVec 3  -- missRspTI_st1.instrId（:714）
  probeStatus4 : Bool        -- probeOut_st1.probeStatus===4（:228 的 RegNext 源）
  allocWriteV : Bool         -- TagAccess.allocateWrite.valid（:620）
  needReplace : Bool         -- TagAccess.needReplace（:581）
  memArb0Rdy : Bool          -- MemReqArb.in(0).ready（:567）
  arb2Rdy : Bool             -- MemReqArb.in(2).ready（:775）
  arb2Fire : Bool            -- MemReqArb.in(2).fire（:769）
  cacheHit : Bool            -- TagAccess.hit_st1（:237；滞留时由 cachehit_hold 保持）
  injectTagProbe : Bool      -- :256
  coreRspQEnqRdy : Bool      -- coreRsp_Q.io.enq.ready
  missReqRdy : Bool          -- MSHR missReq.ready（:449）
  memArb1Rdy : Bool          -- MemReqArb.in(1).ready（:449）
  probeStat02 : Bool         -- mshrProbeStatus===0||===2（:449）
  inflightRWw : Bool         -- inflightreadwritemiss_w（:210）
  hasDirtySt1 : Bool         -- coreReqTagHasDirty_st1（:291）
  mshrEmpty : Bool           -- :465
  wshrEmpty : Bool           -- :465
  memRspHeadV : Bool         -- memRsp_Q deq.valid
  memRspHeadOp : BitVec 3    -- memRsp_Q deq.bits.d_opcode（空时 = 残留值，Q4 关键）
  missRspSet : BitVec 8      -- missRspSetIdx_st1（:578）
  waymaskHit : BitVec 2      -- :408
  waymaskRepl : BitVec 2     -- :583
  fromMemReqV : Bool         -- coreRsp_st2_valid_from_memReq（:818）
  fromMemReqInstrId : BitVec 3 -- coreRspFromMemReq.instrId（:912）
deriving DecidableEq, Repr

def dcInNop : DcIn :=
  { fire := none
    missRspOutV := false
    missRspInstrId := 0#3
    probeStatus4 := false
    allocWriteV := false
    needReplace := false
    memArb0Rdy := false
    arb2Rdy := false
    arb2Fire := false
    cacheHit := false
    injectTagProbe := false
    coreRspQEnqRdy := true
    missReqRdy := false
    memArb1Rdy := false
    probeStat02 := false
    inflightRWw := false
    hasDirtySt1 := false
    mshrEmpty := true
    wshrEmpty := true
    memRspHeadV := false
    memRspHeadOp := 1#3
    missRspSet := 0#8
    waymaskHit := 0#2
    waymaskRepl := 0#2
    fromMemReqV := false
    fromMemReqInstrId := 0#3 }

def dcInit : DcState :=
  { st1 := none
    tagReplaceStatus := false
    waitforL2flush := false
    flushL2Reg := false
    prevAllocWriteV := false
    prevProbeStatus4 := false
    fromMemRsp := false
    rspSt2 := none
    rspSt2Stale := 0#3
    rspVld := none
    rspLog := [] }

/-- coreReq_st1_valid（:314）。 -/
def dcSt1Valid (s : DcState) (i : DcIn) : Bool :=
  s.st1.isSome && !(i.missRspOutV && !s.prevProbeStatus4)

/-- coreRsp_st2 的 deq.ready（:747）。 -/
def dcRspSt2DeqRdy (s : DcState) (i : DcIn) : Bool := i.coreRspQEnqRdy && !i.fromMemReqV
def dcRspSt2DeqFire (s : DcState) (i : DcIn) : Bool := s.rspSt2.isSome && dcRspSt2DeqRdy s i
/-- 1 深 pipe 队列 enq.ready = !full || deq.ready（与 deq.fire 等价，见 D5 注）。 -/
def dcRspSt2EnqRdy (s : DcState) (i : DcIn) : Bool := !s.rspSt2.isSome || dcRspSt2DeqRdy s i

/-- coreRsp_st2_valid_from_coreReq_Reg 的 deq.ready（:732）。 -/
def dcRspVldDeqRdy (s : DcState) (i : DcIn) : Bool :=
  !(i.fromMemReqV || s.fromMemRsp) && i.coreRspQEnqRdy
def dcRspVldDeqFire (s : DcState) (i : DcIn) : Bool := s.rspVld.isSome && dcRspVldDeqRdy s i
def dcRspVldEnqRdy (s : DcState) (i : DcIn) : Bool := !s.rspVld.isSome || dcRspVldDeqRdy s i

/-- coreReq_st1_ready（:442-478 的 when/elsewhen 链；默认 false，:442）。 -/
def dcSt1Ready (s : DcState) (i : DcIn) : Bool :=
  match s.st1 with
  | none => false
  | some r =>
    if r.ctrl.isRead || r.ctrl.isWrite then
      if i.cacheHit then                                                       -- :444-447 命中
        dcRspSt2EnqRdy s i && dcRspVldEnqRdy s i && !(i.missRspOutV && !s.prevProbeStatus4)
      else if r.ctrl.isRead then                                               -- :449-452 读 miss
        i.missReqRdy && i.memArb1Rdy && i.probeStat02 && !(i.missRspOutV && !s.prevProbeStatus4)
      else                                                                     -- :455-457 写 miss
        i.coreRspQEnqRdy && i.memArb1Rdy && !(i.missRspOutV && !s.prevProbeStatus4) && !i.inflightRWw
    else if r.ctrl.isInvalidate then                                           -- :464
      !i.hasDirtySt1 && i.mshrEmpty && i.wshrEmpty && !s.waitforL2flush
    else if r.ctrl.isFlush then                                                -- :468
      !i.hasDirtySt1 && i.wshrEmpty && !s.waitforL2flush
    else if r.ctrl.isWaitMSHR then i.mshrEmpty                                 -- :472
    else true                                                                  -- :477 AMO/LR/SC 吞掉（D8）

/-- coreReqControl_st1_Q deq.fire（:275，deq.ready = coreReq_st1_ready）。 -/
def dcCtrlFire (s : DcState) (i : DcIn) : Bool := dcSt1Valid s i && dcSt1Ready s i

/-- readHit_st1 / writeHit_st1（:241,:243）。 -/
def dcReadHit (s : DcState) (i : DcIn) : Bool :=
  i.cacheHit && (match s.st1 with | some r => r.ctrl.isRead | none => false) && dcCtrlFire s i
def dcWriteHit (s : DcState) (i : DcIn) : Bool :=
  i.cacheHit && (match s.st1 with | some r => r.ctrl.isWrite | none => false) && dcCtrlFire s i

/-- coreReq_Q deq.fire（:260-261）。 -/
def dcCoreQFire (s : DcState) (i : DcIn) : Bool :=
  dcCtrlFire s i &&
    !(match s.st1 with | some r => r.opcode3 && dcReadHit s i && dcSt1Valid s i | none => false)

/-- dataReplaceReadValid（:579-581）。 -/
def dcDataReplaceReadV (s : DcState) (i : DcIn) : Bool :=
  s.prevAllocWriteV && !s.tagReplaceStatus && i.needReplace

/-- **Q3 冲突事件**：写命中 SRAM 写 与 淘汰 victim SRAM 读 同拍同 (set,way)
    （:646-648 写口 vs :583 读口，同一 bank 阵列）。 -/
def dcCollision (s : DcState) (i : DcIn) : Bool :=
  dcWriteHit s i && dcDataReplaceReadV s i &&
    (match s.st1 with | some r => r.setIdx == i.missRspSet | none => false) &&
    (i.waymaskHit == i.waymaskRepl)

/-- waitMSHRCoreRsp_st1 / fluCoreRsp_st1 / invCOreRsp_st1（:481-485）——
    注意均**不要求** st1 fire，stall 期间每拍为真（ghost 预置的来源）。 -/
def dcWaitMshrRsp (s : DcState) (i : DcIn) : Bool :=
  dcSt1Valid s i && (match s.st1 with | some r => r.ctrl.isWaitMSHR | none => false) && i.mshrEmpty
def dcFluRsp (s : DcState) (i : DcIn) : Bool :=
  dcSt1Valid s i && (match s.st1 with | some r => r.ctrl.isFlush | none => false) &&
    !i.hasDirtySt1 && i.wshrEmpty
def dcInvRsp (s : DcState) (i : DcIn) : Bool :=
  dcSt1Valid s i && (match s.st1 with | some r => r.ctrl.isInvalidate | none => false) &&
    !i.hasDirtySt1 && i.mshrEmpty && i.wshrEmpty

/-- coreRsp_st2 入队（:685-707 的 when 链；D9 的 :700-704 保持重发分支不建模）。 -/
def dcRspSt2Enq (s : DcState) (i : DcIn) : Option DcRspSt2 :=
  match s.st1 with
  | none => if i.missRspOutV then some ⟨i.missRspInstrId, false⟩ else none
  | some r =>
    if i.cacheHit && (dcCoreQFire s i || i.injectTagProbe) && dcRspVldEnqRdy s i then
      some ⟨r.instrId, r.ctrl.isWrite⟩                                        -- :685-689,:709
    else if i.missRspOutV then some ⟨i.missRspInstrId, false⟩                 -- :690-694,:714
    else if dcWaitMshrRsp s i || dcFluRsp s i || dcInvRsp s i then
      some ⟨r.instrId, false⟩                                                 -- :695-699
    else none

/-- memRspIsFluOrInv（:544）——**无 deq.valid 限定**（Q4/Q2a 的根源）。 -/
def dcMemRspIsFluOrInv (i : DcIn) : Bool := i.memRspHeadOp == 2#3

/-- hintAck 实际出队（:546 的 deq.ready 对 hintAck 恒真，fire = headV）。 -/
def dcHintAckFire (i : DcIn) : Bool := i.memRspHeadV && (i.memRspHeadOp == 2#3)

/-- coreRsp_st2_valid_from_coreReq（:743）。 -/
def dcFromCoreReq (s : DcState) (i : DcIn) : Bool :=
  (s.rspVld == some true) && dcRspVldDeqFire s i

/-- coreRsp_st2_valid（:751）。 -/
def dcSt2Valid (s : DcState) (i : DcIn) : Bool :=
  dcFromCoreReq s i || s.fromMemRsp || i.fromMemReqV

/-- coreRsp_Q 入队事件（:753-757）：instrId 三选一（memReq 路径 / st2 占位 /
    st2 残留）。 -/
def dcCoreRspEnq (s : DcState) (i : DcIn) : Option (BitVec 3) :=
  if dcSt2Valid s i || dcHintAckFire i then
    some (if i.fromMemReqV then i.fromMemReqInstrId
          else match s.rspSt2 with | some e => e.instrId | none => s.rspSt2Stale)
  else none

/-- invalidatenodirty（:428）与 flushL2（:775）。 -/
def dcInvalidateNoDirty (s : DcState) (i : DcIn) : Bool :=
  dcSt1Valid s i &&
    (match s.st1 with | some r => r.ctrl.isInvalidate || r.ctrl.isFlush | none => false) &&
    !i.hasDirtySt1
def dcFlushL2 (s : DcState) (i : DcIn) : Bool :=
  dcInvalidateNoDirty s i && i.arb2Rdy && !s.flushL2Reg && i.wshrEmpty

/-- 单拍转移。 -/
def dcStep (s : DcState) (i : DcIn) : DcState :=
  let enq := dcRspSt2Enq s i
  { st1 := if i.fire.isSome then i.fire else if dcCoreQFire s i then none else s.st1
    tagReplaceStatus :=                                                       -- :562-568
      if s.tagReplaceStatus then (if i.memArb0Rdy then false else true)
      else i.needReplace
    waitforL2flush :=                                                         -- :423-427
      if (match i.fire with
          | some r => r.ctrl.isInvalidate || r.ctrl.isFlush
          | none => false) then true
      else if dcMemRspIsFluOrInv i then false                                 -- ← Q4：无 valid 限定
      else s.waitforL2flush
    flushL2Reg :=                                                             -- :769-773
      if i.arb2Fire then dcFlushL2 s i
      else if dcMemRspIsFluOrInv i then false
      else s.flushL2Reg
    prevAllocWriteV := i.allocWriteV
    prevProbeStatus4 := i.probeStatus4
    fromMemRsp := if dcRspSt2EnqRdy s i then i.missRspOutV else s.fromMemRsp  -- :745
    rspSt2 :=
      if enq.isSome && dcRspSt2EnqRdy s i then enq
      else if dcRspSt2DeqFire s i then none
      else s.rspSt2
    rspSt2Stale :=
      match enq with
      | some e => if dcRspSt2EnqRdy s i then e.instrId else s.rspSt2Stale
      | none => s.rspSt2Stale
    rspVld :=                                                                 -- :730-731
      if dcSt1Valid s i && dcRspVldEnqRdy s i then some (dcReadHit s i || dcWriteHit s i)
      else if dcRspVldDeqFire s i then none
      else s.rspVld
    rspLog := s.rspLog ++ (dcCoreRspEnq s i).toList }

def dcRun (s : DcState) (is : List DcIn) : DcState := is.foldl dcStep s

/- ---- Q3 前提：唯一的同拍互斥及其局限 ---- -/

/-- io.coreReq.ready 的九项合取（:218；probereadAllocateWriteConflict=:623）。 -/
def dcCoreReqReady (coreValid allocWriteV enqRdy inflightRWw readmissSame probeRdy
    mshrStatus3 mshrStatus1 op3MshrNonEmpty releasingStall : Bool) : Bool :=
  enqRdy && !(coreValid && allocWriteV) && !inflightRWw && !readmissSame && probeRdy &&
    !mshrStatus3 && !mshrStatus1 && !op3MshrNonEmpty && !releasingStall

/-- 同拍互斥（:218 含 !probereadAllocateWriteConflict）：fire 与 allocateWrite.valid
    不能同拍。**但**这对"已在 st1 滞留的写请求"毫无约束——dcT_w1 即利用此缺口。 -/
theorem dc_fire_excludes_allocWrite :
    ∀ (v aw e f g h m3 m1 o r : Bool),
      dcCoreReqReady v aw e f g h m3 m1 o r = true → (v && aw) = false := by
  native_decide

/-- D8：AMO 请求在 st1 落入 :477 默认分支——无条件 ready，无任何副作用。 -/
theorem dc_st1Ready_amo_swallowed (s : DcState) (i : DcIn) :
    s.st1 = some ⟨dcGenControl 2#3 0#4, false, 0#8, 0#3⟩ →
    dcSt1Ready s i = true := by
  intro h; simp [dcSt1Ready, h, dcGenControl, dcCtrlIdle]

/- ========================================================================= -/
/- 6. 三条挂账的机证 witness（Q1 已在 §3；此处 Q2/Q3）                          -/
/- ========================================================================= -/

/- ---- Q3（LFSR 旁路可达性）：滞留写 × 淘汰读 同拍同址 ---- -/

/-- 写请求：isWrite、set5、instrId 1。 -/
def dcW1Req : DcSt1 := ⟨dcGenControl 1#3 0#4, false, 5#8, 1#3⟩

/-- T0：写请求 fire（:218 全项成立；当拍无 allocateWrite——dc_fire_excludes_allocWrite）。 -/
def dcW1I0 : DcIn := { dcInNop with fire := some dcW1Req }

/-- T1：missRspOut 占用响应通道（!secondaryFullReturn）→ 写请求在 st1 滞留
    （:445 的 !(missRspOut && !sec) 项）；同拍 memRsp 读数据返回 →
    allocateWrite.valid=1（tag 分配，:620）。 -/
def dcW1I1 : DcIn := { dcInNop with
  missRspOutV := true
  cacheHit := true
  allocWriteV := true
  missRspSet := 5#8
  waymaskHit := 0b01#2
  waymaskRepl := 0b01#2 }

/-- T2：missRspOut 已离开 → 写命中放行；victim 脏 → needReplace=1 →
    dataReplaceReadValid=1（:579-581，RegNext(allocWriteV) 已在 T1 种下）。
    写口地址 Cat(setIdx=5, waymaskHit=way0)（:648）与淘汰读口地址
    Cat(missRspSet=5, waymaskRepl=way0)（:583）相同。 -/
def dcW1I2 : DcIn := { dcInNop with
  cacheHit := true
  needReplace := true
  missRspSet := 5#8
  waymaskHit := 0b01#2
  waymaskRepl := 0b01#2 }

def dcW1S1 := dcStep dcInit dcW1I0
def dcW1S2 := dcStep dcW1S1 dcW1I1

/-- **Q3 可达性 witness**：滞留写 × 淘汰读同拍同 (set,way) 可达。
    后果链：dcCollision 拍 SRAM 同址读写 → 次拍读出 = LFSR（dcT_w1_sram_lfsr）→
    dirtyReplace_st1.a_data := DataAccessReadSRAMRRsp（:764）→ victim 写回 L2
    的数据被 LFSR 垃圾污染。 -/
theorem dcT_w1_collision_reachable :
    dcW1S2.st1 = some dcW1Req ∧              -- 写请求在 allocateWrite 拍滞留 st1
    dcW1S2.prevAllocWriteV = true ∧
    dcCollision dcW1S2 dcW1I2 = true ∧       -- 次拍同拍同址
    dcWriteHit dcW1S2 dcW1I2 = true ∧
    dcDataReplaceReadV dcW1S2 dcW1I2 = true := by native_decide

/-- Q3 后果钉死（sramCfgDCacheData = F,F,F,F，:637-659）：同拍同址读写，
    掩码命中 way 的读出 = LFSR 值 0x43B2A190，既非写入值也非原值
    （机制定理为 SRAMTemplate.lean 的 sram_lfsr_bypass）。 -/
def dcW1Sram := sramStep sramCfgDCacheData (sramInit 4 2 32)
  (sramInRW ⟨1, by decide⟩ (fun _ => 0xAAAA0000#32) 0b01#2)

theorem dcT_w1_sram_lfsr :
    sramRespData sramCfgDCacheData dcW1Sram ⟨0, by decide⟩ = 0x43B2A190#32 ∧
    sramRespData sramCfgDCacheData dcW1Sram ⟨0, by decide⟩ ≠ 0xAAAA0000#32 ∧
    dcW1Sram.mem ⟨1, by decide⟩ ⟨0, by decide⟩ = 0xAAAA0000#32 := by native_decide

/- ---- Q2（flush/invalidate 响应路径） ---- -/

/-- flush 请求（opcode3,param1），instrId 5。 -/
def dcFlushReq : DcSt1 := ⟨dcGenControl 3#3 1#4, true, 0#8, 5#3⟩
/-- 普通读请求，instrId 3。 -/
def dcReadReq3 : DcSt1 := ⟨dcGenControl 0#3 0#4, false, 7#8, 3#3⟩
/-- L2 hintAck 到达（d_opcode=2 且 valid）。 -/
def dcInAck : DcIn := { dcInNop with memRspHeadV := true, memRspHeadOp := 2#3 }
/-- memRsp_Q 队头**滞留** d_opcode=2（上一 hintAck 消费后的寄存器残留，D5 同理）。 -/
def dcInStaleAck : DcIn := { dcInNop with memRspHeadOp := 2#3 }

/-- W2a 正常时序（首次 flush，队头无残留）：F0 fire → F1..F3 stall（ghost 每拍
    预置 instrId 5 进 coreRsp_st2）→ F4 hintAck → 响应。 -/
def dcW2aTrace := dcRun dcInit
  [{ dcInNop with fire := some dcFlushReq }, dcInNop, dcInNop, dcInNop, dcInAck, dcInNop, dcInNop]

/-- **Q2 正常路径**：响应晚于 L2 hintAck（前 4 拍无响应），且恰好一次、
    instrId 正确——靠 ghost 预置（:695-699 不需 fire 的分支）+ 队列保持（D5）。 -/
theorem dcT_w2a_normal :
    (dcRun dcInit
      [{ dcInNop with fire := some dcFlushReq }, dcInNop, dcInNop, dcInNop]).rspLog = [] ∧
    dcW2aTrace.rspLog = [5#3] := by native_decide

/-- W2b：**第二次及以后的 flush/invalidate**（memRsp_Q 队头滞留 d_opcode=2，
    :425 无 valid 限定）→ waitforL2flush 一拍即被误清 → st1 提前放行 →
    ghost 预置停止 → 真 hintAck 到达时 coreRsp_st2 已被中间 load 响应占用。 -/
def dcW2bTrace := dcRun dcInit
  [{ dcInNop with fire := some dcFlushReq, memRspHeadOp := 2#3 },  -- F0 fire flush(5)
   dcInStaleAck,                                                  -- F1 误清 waitforL2flush
   dcInStaleAck,                                                  -- F2 flush 提前 fire
   { dcInStaleAck with fire := some dcReadReq3 },                 -- F3 load(3) 进入
   { dcInStaleAck with cacheHit := true },                        -- F4 load 命中
   dcInStaleAck,                                                  -- F5 load 响应出队（log [3]）
   dcInAck ]                                                      -- F6 真 hintAck

/-- **Q2a witness**：waitforL2flush 一拍即被误清（Q4 的直接后果）。 -/
theorem dcT_w2b_early_clear :
    (dcRun dcInit
      [{ dcInNop with fire := some dcFlushReq, memRspHeadOp := 2#3 },
       dcInStaleAck]).waitforL2flush = false := by native_decide

/-- **Q2b witness**：flush(5) 的响应携带 load(3) 的 instrId；5 从未出现。
    LSU 侧 Coalscer 按 instrId 记账（pipeline/MSHR.scala:50-71）→ 错误表项
    被清 mask/写数据，目标指令（如 AMO release 的尾 invalidate）永不完结。 -/
theorem dcT_w2b_stale_instrId :
    dcW2bTrace.rspLog = [3#3, 3#3] ∧ ¬ (5#3 ∈ dcW2bTrace.rspLog) := by native_decide

/-- W2c：flush stall 期间 coreRsp_Q 反压使 coreRsp_st2 被前序 load 响应占满
    （ghost 无法预置），hintAck 与 load 响应同拍出队 → :754 的 OR 合并。 -/
def dcW2cTrace := dcRun dcInit
  [{ dcInNop with fire := some dcReadReq3 },                     -- F0 load(3) 进入
   { dcInNop with fire := some dcFlushReq, cacheHit := true, coreRspQEnqRdy := false },  -- F1 load 命中出 st1，flush 进入
   { dcInNop with coreRspQEnqRdy := false },                     -- F2 响应滞留，flush stall
   { dcInNop with coreRspQEnqRdy := false },                     -- F3
   { dcInNop with coreRspQEnqRdy := false },                     -- F4
   { dcInNop with coreRspQEnqRdy := true, memRspHeadV := true, memRspHeadOp := 2#3 },  -- F5 hintAck × load 响应同拍
   dcInNop, dcInNop ]

/-- **Q2c witness**：flush(5) 的响应**整体丢失**（log 只有 load 的 [3]）。
    若该 invalidate 是 AMO aq&&rl 序列的尾部 release（LSU.scala:247-248，
    instrId 与 AMO 相同），AMO 在 Coalscer 永不完结 → 挂死。 -/
theorem dcT_w2c_rsp_lost :
    dcW2cTrace.rspLog = [3#3] ∧ ¬ (5#3 ∈ dcW2cTrace.rspLog) := by native_decide

/- ---- 公理审计（native_decide 测试含 Lean.ofReduceBool，bv_decide 定理含
   _native.bv_decide.ax_* 信任公理，均属预期） ---- -/

#print axioms dc_blockAddr_roundtrip
#print axioms dc_genControl_onehot
#print axioms dcRemapMask_includes
#print axioms dcWriteMissMask_complete
#print axioms dcT_i28_asymmetry
#print axioms dcwDistinct_push
#print axioms dc_fire_excludes_allocWrite
#print axioms dcT_w1_collision_reachable
#print axioms dcT_w1_sram_lfsr
#print axioms dcT_w2a_normal
#print axioms dcT_w2b_stale_instrId
#print axioms dcT_w2c_rsp_lost

end Ventus.Mem
