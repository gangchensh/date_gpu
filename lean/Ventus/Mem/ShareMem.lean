/- ========================================================================= -/
/-                        Mem/ShareMem.lean                                    -/
/-  ShareMem（L1 共享存储/scratchpad）的 Lean 4 模型、测试与证明                -/
/-  namespace Ventus.Mem；全部辅助定义带 sm 前缀。                             -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/L1Cache/ShareMem/            -/
/-      ShareMemParameters.scala（:20-52 参数与位段划分）                      -/
/-      ShareMem.scala（:33-53 Bundle；:55-195 SharedMemory 顶层）             -/
/-      BankConflictArbiter.scala（:60-69 DataCrossbar；:75-78 L2BCrossbar；   -/
/-        :102-194 BankConflictArbiter）                                       -/
/-    对接：GPGPU_top.scala:484-491（coreReq 直连 pipe.shared_req，            -/
/-      :488 setIdx 8→10 零扩展）；pipe.scala:40,414（shared_req 来源 LSU）；  -/
/-      LSU.scala:66-77（ShareMemCoreReq_np：setIdx = dcache_SetIdxBits=8      -/
/-      位）、:171（setIdx := addr(14,7)）、:177（blockOffset := addr(10,2)    -/
/-      装入 5 位字段，实际取 addr(6,2)）、:216-220（to_shared 装配）。        -/
/-                                                                           -/
/- ======================== 参数核查（top/parameters.scala + L1Cache） =======- -/
/-  sharedmem_depth=1024(:93) → ShareMem NSets=1024 → SetIdxBits=10            -/
/-    (L1CacheParameters.scala:43 SetIdxBits=log2Up(NSets)；                   -/
/-     ShareMemParameters.scala:22 NSets=sharedmem_depth）                     -/
/-  sharedmem_BlockWords=dcache_BlockWords=32(:95) → BlockOffsetBits=5         -/
/-  NWays=1（ShareMemParameters.scala:37 "direct mapped"），无 tag（           -/
/-    ShareMem.scala:42 tag 字段注释掉、:63 L1TagAccess 例化注释掉）           -/
/-  NBanks=NLanes=num_thread=32(:40,:9) → BankIdxBits=5、BankOffsetBits=0、    -/
/-    BankWords=1 → AddrBundle1T.bankOffset=None（BankConflictArbiter.scala:72）-/
/-  BytesOfWord=4、WordLength=32、WIdBits=log2Up(8)=3（RVGParameter.scala:44） -/
/-  每 bank SRAM：gen=UInt(8.W)、set=NSets*NWays*BankWords=1024、way=4、       -/
/-    cfg=F,F,F,T（ShareMem.scala:146-154 → sramCfgShareMem，复用              -/
/-    Mem/SRAMTemplate.lean 的 sramStep）                                      -/
/-                                                                           -/
/- ======================== 建模决策 =========================================- -/
/-  D1. 参数固定为上述具体值（全仓唯一配置）。NLanes=NBanks=32。               -/
/-  D2. BankOffsetBits=0 → bankOffset 字段不存在，SRAM 行址 = setIdx 本身      -/
/-      （ShareMem.scala:158-162,167-171 的 if 分支取 else）。                 -/
/-  D3. 向量用 Fin 32 → · 函数；bank 数据阵 = Fin 32 → SramState 1024 4 8，    -/
/-      复用 SRAMTemplate.lean（sramCfgShareMem = F,F,F,T：双端口+bypass）。   -/
/-  D4. coreRsp_Q（Queue depth=32, pipe=true, flow=false）建模为 List：        -/
/-      enq.ready = len<32；almostFull = (len==30)（ShareMem.scala:190）；     -/
/-      pipe 旁路：队空时 deq.valid/bits 直通 enq；队空且同拍 enq+deq 时该     -/
/-      项被消费且不入队（Chisel pipe queue 语义：do_enq/do_deq 同发时指针     -/
/-      同进、count 不变，写入项立即可被越过）。                               -/
/-  D5. 无 RegInit 的寄存器（conflictReqIsW_reg、perLaneConflictReq_reg、      -/
/-      coreReq_st1、ShiftRegister 链、dataAccess_data_st2 等）上电值建模为    -/
/-      0/false；上电不定值不进入任何定理结论。                                -/
/-  D6. PriorityEncoderOH 建模为 lowbit 提取 x &&& (0-x)（BankConflictArbiter -/
/-      .scala:164；perBankReq_Bin 经 :146 Reverse 后 bit j = lane j，         -/
/-      PriorityEncoderOH 取最低置位 = 最低 lane 号）。                        -/
/-  D7. Mux1H(sel, in)（独热或全零选择器）建模为按位 OR 折叠：全零 sel 得 0。  -/
/-  D8. LSU 侧地址函数直接复用 Mem/LSU.lean 的 lsuSetOf/lsuBlkOf/              -/
/-      lsuWordOff1H/lsuMemW/lsuLdsBase/lsuSmaxDefault（I-21 组合定理所据）。  -/
/-  D9. 读侧 rValid 用 coreReqisValidRead_comb（:123）；写侧 wValid 用         -/
/-      coreReqisValidWrite_st1 且 dataArrayEn 经 RegNext（:155）——写比读      -/
/-      滞后一拍执行，与本模块流水线一致。                                     -/
/-                                                                           -/
/- ======================== I-21 核销结论（详见定理 smI21_*） ================ -/
/-  别名成立。链路：LSU setIdx=addr(14,7)（8 位，LSU.scala:171）→              -/
/-  GPGPU_top.scala:488 零扩展为 10 位 → ShareMem 唯一直接用作 SRAM 行址       -/
/-  （:159-171）。ShareMemCoreReq 无 tag 字段（:42 注释掉）、无 TagAccess      -/
/-  （:63 注释掉）、全模块再无任何对地址高位（addr(16,15)）的使用——无拦截。   -/
/-  后果：smSetIdxOfAddr 恒 < 256（smI21_dead_rows），每 bank 1024 行中仅      -/
/-  低 256 行可达；LDS 偏移 o 与 o+32KB/o+64KB/o+96KB 落到同一物理字节         -/
/-  （smI21_alias），端到端 witness：写 0x70008040 后读 0x70000040 返回新值    -/
/-  （smI21_witness）。is_shared 判界（LSU.scala:162，smax=128KB）不拦截       -/
/-  高区地址（smI21_window）。注：LSU 的 same_tag 分组（LSU.scala:220）把      -/
/-  addr(31,15) 不同的 lane 拆成多拍请求，但每拍 setIdx 仍是 8 位截断值，      -/
/-  不能消除别名——别名发生在请求之间（高区请求与低区请求踩同一行）。         -/
/-                                                                           -/
/- ======================== 其他源码审查发现 ================================= -/
/-  Q1【观察】bypassWrite=true 在本例化下结构性不可达：读口发射需 fire 或      -/
/-      读冲突保持（vRcomb），写执行需 vW1=1，而 coreReq.ready 在 vW1=1 时     -/
/-      为 0（:194）且写冲突保持期间 bankConflict_isWrite=1 使 vRcomb=0        -/
/-      （:123）——同拍读写同行不发生，SRAM bypass 通路闲置（测试 smT5_*）。    -/
/-      非 bug，属配置冗余。                                                   -/
/-  Q2【观察】写吞吐上限 1 请求/2 拍：vW1 占用 st1 期间 ready=0（:194 的       -/
/-      !coreReqisValidWrite_st1）。读请求无此项，可背靠背（smT6_*）。         -/
/-  Q3【提示】ShareMem.scala:141-144 注释自相矛盾（作者自注"上述注释似乎       -/
/-      写反了"）；代码行为：同拍读写同行时 bypass 前递新数据（sramCfgShareMem -/
/-      bypassWrite=true），但由 Q1 该情形不可达，注释之争无实际影响。         -/
/-  Q4【提示】coreRsp_Q 满（len=32）时 enq 被丢弃；ready 用 almostFull=30      -/
/-      （:190）预留 2 拍在飞余量（st1/st2 各一拍），正常流水下 enq 不会       -/
/-      溢出。未形式化该不变量（留待整机波次）。                               -/
/-  Q5【提示】BankConflictArbiter.scala:24-25 自注：同地址读不做合并，逐拍     -/
/-      串行服务；:19-23 同 bank 不同字节的写合并"失败"按冲突处理——均为      -/
/-      性能损失而非正确性问题（smT4_* 钉死串行化语义）。                      -/
/- ========================================================================= -/

import Ventus.Mem.LSU
import Ventus.Mem.SRAMTemplate
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- ========================================================================= -/
/- 1. 参数常量（核查见头部）                                                  -/
/- ========================================================================= -/

def smNLanes : Nat := 32
def smNBanks : Nat := 32
def smNSets : Nat := 1024
def smSramSets : Nat := 1024   -- NSets*NWays*BankWords = 1024*1*1
def smRspQDepth : Nat := 32    -- num_thread（ShareMem.scala:72）

/- ========================================================================= -/
/- 2. Bundle 与地址映射                                                      -/
/- ========================================================================= -/

/-- ShareMemPerLaneAddr（ShareMem.scala:33-37）。 -/
structure SmPerLaneAddr where
  activeMask : Bool
  blockOffset : BitVec 5      -- BlockOffsetBits=5
  wordOffset1H : BitVec 4     -- BytesOfWord=4
deriving DecidableEq

/-- ShareMemCoreReq（ShareMem.scala:38-46；无 tag 字段）。 -/
structure SmCoreReq where
  instrId : BitVec 3          -- WIdBits=3
  isWrite : Bool
  setIdx : BitVec 10          -- SetIdxBits=log2Up(1024)=10
  perLaneAddr : Fin 32 → SmPerLaneAddr
  data : Fin 32 → BitVec 32

/-- ShareMemCoreRsp（ShareMem.scala:48-53）。 -/
structure SmCoreRsp where
  instrId : BitVec 3
  isWrite : Bool
  data : Fin 32 → BitVec 32
  activeMask : Fin 32 → Bool

/-- 模块输入：coreReq.valid/bits + coreRsp.ready。 -/
structure SmIn where
  reqValid : Bool
  req : SmCoreReq
  rspReady : Bool

/-- setIdx(10 位) → SRAM 行号（ShareMem.scala:159-162,167-171，D2）。 -/
def smRowOfSetIdx (x : BitVec 10) : Fin 1024 :=
  ⟨x.toNat, Nat.lt_of_lt_of_le x.isLt (by decide)⟩

/-- GPGPU_top.scala:488 的对接：LSU 8 位 setIdx 零扩展为 10 位。
    这是 I-21 的断点：addr(16,15) 在此被丢弃。 -/
def smSetIdxOfAddr (a : BitVec 32) : BitVec 10 := (lsuSetOf a).zeroExtend 10

/-- is_shared 判界（LSU.scala:162，mask=1 lane 的析取支）：地址落在
    [LDS_BASE, LDS_BASE+128KB) 即被路由到 ShareMem。 -/
def smIsShared (a : BitVec 32) : Bool :=
  decide (lsuLdsBase ≤ a) && decide (a < lsuLdsBase + lsuSmaxDefault)

/-- 字 → 4 字节（ShareMem.scala:156 的 asTypeOf(Vec(4,UInt(8.W)))，小端：
    byte j = 字 bits(8j+7, 8j)）。 -/
def smWordToBytes (w : BitVec 32) : Fin 4 → BitVec 8 :=
  fun j => (w >>> (8 * j.val)).extractLsb' 0 8

/-- 4 字节 → 字（ShareMem.scala:172 的 Cat(resp.data.reverse)）。 -/
def smBytesToWord (bs : Fin 4 → BitVec 8) : BitVec 32 :=
  (bs ⟨0, by decide⟩).zeroExtend 32 |||
  ((bs ⟨1, by decide⟩).zeroExtend 32 <<< 8) |||
  ((bs ⟨2, by decide⟩).zeroExtend 32 <<< 16) |||
  ((bs ⟨3, by decide⟩).zeroExtend 32 <<< 24)

/-- 字节拼装回归（方向性钉死：写后按字读回应为原字）。 -/
theorem sm_bytes_word_roundtrip (w : BitVec 32) :
    smBytesToWord (smWordToBytes w) = w := by
  unfold smBytesToWord smWordToBytes; bv_decide

/- ========================================================================= -/
/- 3. BankConflictArbiter（BankConflictArbiter.scala:102-194）                -/
/- ========================================================================= -/

/-- PriorityEncoderOH（:164）：最低置位独热（D6）。 -/
def smPrioOH (x : BitVec 32) : BitVec 32 := x &&& (0#32 - x)

/-- 置位数 ≥ 2（perBankReqCount(i) > 1，:147,:158）。 -/
def smTwoOrMore (x : BitVec 32) : Bool := (x &&& (x - 1#32)) != 0#32

/-- Mux1H（独热/全零选择，D7；:67,:181 等）。 -/
def smMux1H (sel : BitVec 32) (din : Fin 32 → BitVec n) : BitVec n :=
  (List.finRange 32).foldl
    (fun acc l => if ((sel >>> l.val) &&& 1#32) == 1#32 then acc ||| din l else acc)
    (0#n)

/-- DataCrossbar（:60-69）：每 lane/ bank 一路 Mux1H。 -/
def smXbar (sel : Fin 32 → BitVec 32) (din : Fin 32 → BitVec 32) (l : Fin 32) :
    BitVec 32 := smMux1H (sel l) din

/-- 仲裁器寄存器（:116-119；无 RegInit 者初值取 0/false，D5）。 -/
structure SmArbState where
  bcReg : Bool                    -- RegNext(bankConflict, false.B)（:116）
  bcIsWReg : Bool                 -- conflictReqIsW_reg（:117）
  holdBankIdx : Fin 32 → BitVec 5 -- perLaneConflictReq_reg.bankIdx（:119）
  holdWord1H : Fin 32 → BitVec 4  -- perLaneConflictReq_reg.AddrBundle.wordOffset1H
  holdActive : Fin 32 → Bool      -- perLaneConflictReq_reg.activeMask

/-- 仲裁器组合输出（:106-112）。 -/
structure SmArbOut where
  addrWord1H : Fin 32 → BitVec 4     -- addrCrsbarOut(i).wordOffset1H（:181）
  dataSel1H : Fin 32 → BitVec 32     -- dataCrsbarSel1H（:185）
  dataArrayEn : Fin 32 → Bool        -- :188
  activeLane : Fin 32 → Bool         -- :193
  bankConflict : Bool                -- :189
  bankConflictIsWrite : Bool         -- :190

/-- 仲裁器组合逻辑 + 寄存器更新（:121-193 全文）。
    输入 enable = io.coreReq.fire（ShareMem.scala:79）；
    isWrite = ShareMem.scala:80 的 Mux 输出。 -/
def smArbComb (st : SmArbState) (enable isWrite : Bool)
    (perLane : Fin 32 → SmPerLaneAddr) : SmArbOut × SmArbState :=
  -- perLaneConflictReq（:170）：冲突保持期用 hold 寄存器
  let mask : Fin 32 → Bool := fun l =>
    if st.bcReg then st.holdActive l else (perLane l).activeMask
  let bankIdx : Fin 32 → BitVec 5 := fun l =>
    if st.bcReg then st.holdBankIdx l else (perLane l).blockOffset
  let w1H : Fin 32 → BitVec 4 := fun l =>
    if st.bcReg then st.holdWord1H l else (perLane l).wordOffset1H
  -- bankIdxMasked（:138-142）；UIntToOH(bankIdx) & Fill(mask)
  let masked : Fin 32 → BitVec 32 := fun l =>
    if mask l then (1#32 <<< (bankIdx l).toNat) else 0#32
  -- perBankReq_Bin（:143,:146 的 Reverse(Cat(...)) 转置，bit l = lane l）
  let perBankReq : Fin 32 → BitVec 32 := fun b =>
    (List.finRange 32).foldl
      (fun acc l => if mask l && ((bankIdx l).toNat == b.val)
        then acc ||| (1#32 <<< l.val) else acc) 0#32
  -- 冲突检测（:157-159）
  let conflictAny : Bool := (List.finRange 32).any (fun b => smTwoOrMore (perBankReq b))
  let bankConflict : Bool := conflictAny && (enable || st.bcReg)
  -- isWrite（:134）
  let isWriteA : Bool := if st.bcReg then st.bcIsWReg else isWrite
  -- 每 bank 本拍服务 lane（:163-164）：PriorityEncoderOH
  let serve : Fin 32 → BitVec 32 := fun b => smPrioOH (perBankReq b)
  -- ActiveLaneWhenConflict1H（:165-167）：lane l 被某 bank 服务
  let activeLane : Fin 32 → Bool := fun l =>
    (List.finRange 32).any (fun b => ((serve b >>> l.val) &&& 1#32) == 1#32)
  -- ReserveLaneWhenConflict1H（:168）：未服务但活跃的 lane 留下拍
  let reserve : Fin 32 → Bool := fun l => !(activeLane l) && mask l
  let out : SmArbOut :=
    { addrWord1H := fun b => smMux1H (serve b) w1H          -- :181（L2BCrossbar）
      dataSel1H := fun b => if isWriteA then serve b else masked b  -- :185
      dataArrayEn := fun b => serve b != 0#32               -- :188
      activeLane := activeLane                              -- :193
      bankConflict := bankConflict                          -- :189
      bankConflictIsWrite := isWriteA }                     -- :190
  let st' : SmArbState :=
    { bcReg := bankConflict                                 -- :116
      bcIsWReg := if bankConflict then isWrite else st.bcIsWReg  -- :178
      holdBankIdx := fun l => if reserve l then bankIdx l else st.holdBankIdx l  -- :174
      holdWord1H := fun l => if reserve l then w1H l else st.holdWord1H l        -- :175
      holdActive := reserve }                               -- :176
  (out, st')

/- ---- 仲裁器符号引理（prioOH 性质，bv_decide） ---- -/

theorem smPrioOH_sub (x : BitVec 32) : smPrioOH x &&& x = smPrioOH x := by
  unfold smPrioOH; bv_decide

theorem smPrioOH_onehot (x : BitVec 32) :
    smPrioOH x &&& (smPrioOH x - 1#32) = 0#32 := by
  unfold smPrioOH; bv_decide

theorem smPrioOH_ne_zero (x : BitVec 32) (h : x ≠ 0#32) : smPrioOH x ≠ 0#32 := by
  unfold smPrioOH; bv_decide

theorem smTwoOrMore_not_onehot (x : BitVec 32) (h : smTwoOrMore x = true) :
    x ≠ 0#32 ∧ x &&& (x - 1#32) ≠ 0#32 := by
  unfold smTwoOrMore at h; bv_decide

/- ========================================================================= -/
/- 4. SharedMemory 顶层（ShareMem.scala:55-195）                              -/
/- ========================================================================= -/

/-- 顶层状态。寄存器初值：RegInit 忠实；无 RegInit 者取 0/false（D5）。 -/
structure SmState where
  st1Req : SmCoreReq              -- coreReq_st1（:78，RegEnable）
  vW1 : Bool                      -- coreReqisValidWrite_st1（:121，RegInit false）
  vR1 : Bool                      -- coreReqisValidRead_st1（:124，RegInit false）
  vR2 : Bool                      -- coreReqisValidRead_st2（:128）
  vW2 : Bool                      -- coreReqisValidWrite_st2（:129）
  instrId2 : BitVec 3             -- coreReqInstrId_st2（:131）
  actvM1 : Fin 32 → Bool          -- ShiftRegister 第 1 级（:132）
  actvM2 : Fin 32 → Bool          -- coreReqActvMask_st2（:132 第 2 级）
  isW2 : Bool                     -- coreReqIsWrite_st2（:133）
  addrW1 : Fin 32 → BitVec 4      -- arbAddrCrsbarOut_st1.wordOffset1H（:135）
  selW1 : Fin 32 → BitVec 32      -- arbDataCrsbarSel1H_st1（:136）
  selW2 : Fin 32 → BitVec 32      -- arbDataCrsbarSel1H_st2（:137）
  daEnW : Fin 32 → Bool           -- RegNext(dataArrayEn, false.B)（:155）
  prevBCisW : Bool                -- RegNext(bankConflict_isWrite)（:123 的右半）
  rdata2 : Fin 32 → BitVec 32     -- dataAccess_data_st2（:174）
  arb : SmArbState
  banks : Fin 32 → SramState 1024 4 8   -- DataAccesses（:145-154）
  rspQ : List SmCoreRsp           -- coreRsp_Q（:73，D4）

def smCoreReqZero : SmCoreReq :=
  ⟨0#3, false, 0#10, fun _ => ⟨false, 0#5, 0#4⟩, fun _ => 0#32⟩

def smInit : SmState :=
  { st1Req := smCoreReqZero
    vW1 := false, vR1 := false, vR2 := false, vW2 := false
    instrId2 := 0#3
    actvM1 := fun _ => false, actvM2 := fun _ => false
    isW2 := false
    addrW1 := fun _ => 0#4
    selW1 := fun _ => 0#32, selW2 := fun _ => 0#32
    daEnW := fun _ => false
    prevBCisW := false
    rdata2 := fun _ => 0#32
    arb := ⟨false, false, fun _ => 0#5, fun _ => 0#4, fun _ => false⟩
    banks := fun _ => sramInit 1024 4 8
    rspQ := [] }

/-- io.coreReq.ready（:194 + :190 的 almostFull）。 -/
def smReqReady (s : SmState) : Bool :=
  !s.arb.bcReg && !(s.rspQ.length == smRspQDepth - 2) && !s.vW1

/-- io.coreReq.fire。 -/
def smFire (s : SmState) (i : SmIn) : Bool := i.reqValid && smReqReady s

/-- ShareMem.scala:80：仲裁器 isWrite 输入。 -/
def smArbInIsWrite (s : SmState) (i : SmIn) : Bool :=
  if s.arb.bcReg then s.st1Req.isWrite else i.req.isWrite

/-- 仲裁器输出观测（与 smStep 内部计算一致）。 -/
def smObsArb (s : SmState) (i : SmIn) : SmArbOut :=
  (smArbComb s.arb (smFire s i) (smArbInIsWrite s i) i.req.perLaneAddr).1

/-- coreReqisValidRead_comb（:123）。 -/
def smVRcomb (s : SmState) (i : SmIn) : Bool :=
  (smFire s i && !i.req.isWrite) || (s.arb.bcReg && !s.prevBCisW)

/-- st2 入队内容（:185-189）。 -/
def smEnqBits (s : SmState) : SmCoreRsp :=
  ⟨s.instrId2, s.isW2, fun l => smXbar s.selW2 s.rdata2 l, s.actvM2⟩

/-- coreRsp_Q enq.valid（:185）。 -/
def smEnqValid (s : SmState) : Bool := s.vR2 || s.vW2

/-- io.coreRsp.valid（Queue pipe=true：队空时直通 enq）。 -/
def smRspValid (s : SmState) : Bool := !s.rspQ.isEmpty || smEnqValid s

/-- io.coreRsp.bits。 -/
def smRspBits (s : SmState) : SmCoreRsp :=
  match s.rspQ with
  | [] => smEnqBits s
  | r :: _ => r

/-- 单拍转移（ShareMem.scala:78-194 全文）。 -/
def smStep (s : SmState) (i : SmIn) : SmState :=
  let fire := smFire s i
  let (ao, arb') := smArbComb s.arb fire (smArbInIsWrite s i) i.req.perLaneAddr
  let vRcomb := smVRcomb s i
  -- coreRsp_Q（D4：pipe 直通 + 队空同拍 enq/deq 不入队）
  let rspV := smRspValid s
  let deqF := i.rspReady && rspV
  let q1 := if deqF && !s.rspQ.isEmpty then s.rspQ.tail else s.rspQ
  let q2 := if smEnqValid s && s.rspQ.length < smRspQDepth &&
               !(s.rspQ.isEmpty && deqF)
            then q1 ++ [smEnqBits s] else q1
  { st1Req := if fire then i.req else s.st1Req                     -- :78
    vW1 := (fire && i.req.isWrite) || (s.vW1 && s.arb.bcReg)      -- :122
    vR1 := (fire && !i.req.isWrite) || (s.vR1 && s.arb.bcReg)     -- :125
    vR2 := s.vR1                                                  -- :128
    vW2 := s.vW1                                                  -- :129
    instrId2 := s.st1Req.instrId                                  -- :131
    actvM1 := ao.activeLane                                       -- :132 第 1 级
    actvM2 := s.actvM1                                            -- :132 第 2 级
    isW2 := s.st1Req.isWrite                                      -- :133
    addrW1 := ao.addrWord1H                                       -- :135
    selW1 := ao.dataSel1H                                         -- :136
    selW2 := s.selW1                                              -- :137
    daEnW := ao.dataArrayEn                                       -- :155
    prevBCisW := ao.bankConflictIsWrite                           -- :123 的 RegNext
    rdata2 := if s.vR1                                            -- :174
              then fun b => smBytesToWord (fun j =>
                     sramRespData sramCfgShareMem (s.banks b) j)
              else s.rdata2
    arb := arb'
    banks := fun b =>
      -- 写口（:155-164）：st1 拍执行；setIdx 来自 st1 保持的请求
      let wv := s.vW1 && s.daEnW b
      let wdata := smWordToBytes (smXbar s.selW1 s.st1Req.data b)  -- :156,:177-178
      let waddr := smRowOfSetIdx s.st1Req.setIdx                   -- :159-162（D2）
      let wm := s.addrW1 b                                         -- :163-164
      -- 读口（:166-171）：comb 拍发射；fire 时直取当前请求 setIdx
      let rv := vRcomb && ao.dataArrayEn b
      let raddr := if fire then smRowOfSetIdx i.req.setIdx
                   else smRowOfSetIdx s.st1Req.setIdx              -- :167-171
      sramStep sramCfgShareMem (s.banks b) ⟨rv, raddr, wv, waddr, wdata, wm⟩
    rspQ := q2 }

/-- 多拍执行。 -/
def smRun (s : SmState) (is : List SmIn) : SmState := is.foldl smStep s

/- ---- 顶层机制引理 ---- -/

/-- 写占用互斥（:194）：ready=1 ⇒ 上一拍无写在 st1。 -/
theorem smReqReady_no_vW1 (s : SmState) (h : smReqReady s = true) :
    s.vW1 = false := by
  cases hv : s.vW1
  · rfl
  · simp [smReqReady, hv] at h

/-- ready=1 ⇒ 仲裁器不在冲突保持期。 -/
theorem smReqReady_no_hold (s : SmState) (h : smReqReady s = true) :
    s.arb.bcReg = false := by
  cases hv : s.arb.bcReg
  · rfl
  · simp [smReqReady, hv] at h

/-- Q1 的机制半：fire 发生的拍，写口不执行（vW1=0）。 -/
theorem smFire_no_write_exec (s : SmState) (i : SmIn) (h : smFire s i = true) :
    s.vW1 = false :=
  smReqReady_no_vW1 s ((Bool.and_eq_true _ _).mp h).2

/- ========================================================================= -/
/- 5. I-21 核销：LDS setIdx 位宽别名                                          -/
/- ========================================================================= -/

/-- 别名（切片级，符号）：两个地址若低 15 位相同（即仅 addr(31:15) 可不同，
    含关键位 addr(16,15)），则经 LSU 切片 + GPGPU_top 零扩展后，ShareMem
    可见的全部寻址字段（setIdx/bank=blockOffset/字节使能）完全相同。 -/
theorem smI21_alias (a b : BitVec 32) (whb : BitVec 2)
    (h : a &&& 0x00007FFF#32 = b &&& 0x00007FFF#32) :
    smSetIdxOfAddr a = smSetIdxOfAddr b ∧
    lsuBlkOf a = lsuBlkOf b ∧
    lsuWordOff1H whb a = lsuWordOff1H whb b := by
  simp only [smSetIdxOfAddr, lsuSetOf, lsuBlkOf, lsuWordOff1H,
    lsuMemW, lsuMemH, lsuMemB]
  bv_decide

/-- 死区（符号）：零扩展后的 setIdx 高 2 位恒 0 —— 每 bank 1024 行 SRAM
    中仅低 256 行可达，3/4 容量（96KB）硬件上永远无法寻址。 -/
theorem smI21_dead_rows (a : BitVec 32) :
    smSetIdxOfAddr a &&& 0x300#10 = 0#10 := by
  simp only [smSetIdxOfAddr, lsuSetOf]; bv_decide

/-- witness 地址：同 bank(16)、同 LSU-setIdx(0)、同字节，真实行址
    （addr(16,7)）分别为 0 / 0x100 / 0x200 / 0x300 —— 恰差 32KB/64KB/96KB。 -/
def smAlo  : BitVec 32 := 0x70000040   -- LDS_BASE + 0x00040
def smAhi  : BitVec 32 := 0x70008040   -- LDS_BASE + 0x08040（bit15）
def smAhi2 : BitVec 32 := 0x70010040   -- LDS_BASE + 0x10040（bit16）
def smAhi3 : BitVec 32 := 0x70018040   -- LDS_BASE + 0x18040（bit16+15）

/-- 四个 witness 地址都通过 is_shared 判界（LSU.scala:162，smax=128KB）：
    高区访问不会被路由去 DCache，别名畅通。 -/
theorem smI21_window :
    smIsShared smAlo = true ∧ smIsShared smAhi = true ∧
    smIsShared smAhi2 = true ∧ smIsShared smAhi3 = true := by
  native_decide

/-- witness 地址的"正确"行址互不相同（若硬件按 addr(16,7) 寻址本不该混）。 -/
theorem smI21_true_rows_differ :
    smAlo.extractLsb' 7 10 ≠ smAhi.extractLsb' 7 10 ∧
    smAlo.extractLsb' 7 10 ≠ smAhi2.extractLsb' 7 10 ∧
    smAlo.extractLsb' 7 10 ≠ smAhi3.extractLsb' 7 10 := by
  native_decide

/-- witness 地址经 LSU+对接后的 ShareMem 寻址字段完全相同（smI21_alias 的
    具体实例）。 -/
theorem smI21_witness_fields :
    smSetIdxOfAddr smAlo = smSetIdxOfAddr smAhi ∧
    smSetIdxOfAddr smAlo = smSetIdxOfAddr smAhi2 ∧
    smSetIdxOfAddr smAlo = smSetIdxOfAddr smAhi3 ∧
    lsuBlkOf smAlo = lsuBlkOf smAhi := by
  native_decide

/-- 由 LSU 侧地址构造函数装配的单 lane 请求（lane0 活跃，字访问）。
    setIdx 走 GPGPU_top.scala:488 的零扩展对接。 -/
def smReqOfAddr (a : BitVec 32) (wr : Bool) (iid : BitVec 3) (d : BitVec 32) :
    SmCoreReq :=
  { instrId := iid
    isWrite := wr
    setIdx := smSetIdxOfAddr a
    perLaneAddr := fun l => ⟨l.val == 0, lsuBlkOf a, lsuWordOff1H lsuMemW a⟩
    data := fun _ => d }

def smInNop : SmIn := ⟨false, smCoreReqZero, true⟩
def smInOf (r : SmCoreReq) : SmIn := ⟨true, r, true⟩

/-- I-21 端到端 witness 轨迹：
    t0 写低区 smAlo ← 0x11111111；t3 写高区 smAhi ← 0x22222222；
    t6 读低区 smAlo。t8 拍（状态 smW2s8）核心读响应。 -/
def smW2s1  := smStep smInit  (smInOf (smReqOfAddr smAlo true 5#3 0x11111111#32))
def smW2s2  := smStep smW2s1 smInNop
def smW2s3  := smStep smW2s2 smInNop
def smW2s4  := smStep smW2s3 (smInOf (smReqOfAddr smAhi true 6#3 0x22222222#32))
def smW2s5  := smStep smW2s4 smInNop
def smW2s6  := smStep smW2s5 smInNop
def smW2s7  := smStep smW2s6 (smInOf (smReqOfAddr smAlo false 7#3 0#32))
def smW2s8  := smStep smW2s7 smInNop   -- t8 拍：读响应（vR2=1）

/-- **I-21 witness 定理**：高区（LDS_BASE+32KB 处）写入后，读低区返回的是
    高区写入值 0x22222222，而不是低区自己写入的 0x11111111 —— 高区写
    静默覆盖了低区数据。物理位置：bank16、SRAM 行 0、4 字节全使能，
    两笔请求在 ShareMem 内不可区分。 -/
theorem smI21_witness :
    smRspValid smW2s8 = true ∧
    (smRspBits smW2s8).isWrite = false ∧
    (smRspBits smW2s8).instrId = 7#3 ∧
    (smRspBits smW2s8).data ⟨0, by decide⟩ = 0x22222222#32 ∧
    (smRspBits smW2s8).data ⟨0, by decide⟩ ≠ 0x11111111#32 := by
  native_decide

/-- witness 的补充：两个写请求的 ShareMem 寻址字段逐位相同（请求级别名）。 -/
theorem smI21_req_alias :
    (smReqOfAddr smAlo true 0#3 0#32).setIdx =
      (smReqOfAddr smAhi true 0#3 0#32).setIdx ∧
    (smReqOfAddr smAlo true 0#3 0#32).perLaneAddr ⟨0, by decide⟩ =
      (smReqOfAddr smAhi true 0#3 0#32).perLaneAddr ⟨0, by decide⟩ := by
  native_decide

/- ========================================================================= -/
/- 6. 功能测试（先测试后证明；多拍轨迹一律 native_decide）                    -/
/- ========================================================================= -/

/- ---- T1：单 lane 写后读（RAW 基本通路 + 响应格式 + 阵列落点） ---- -/

def smT1d : BitVec 32 := 0xCAFEBABE
def smT1s1 := smStep smInit (smInOf (smReqOfAddr smAlo true 5#3 smT1d))  -- t0 fire
def smT1s2 := smStep smT1s1 smInNop   -- t1：写执行拍（vW1=1）；t2 态见 s2
def smT1s3 := smStep smT1s2 smInNop   -- t2：写响应拍（vW2=1）→ s3 前可见于 s2
def smT1s4 := smStep smT1s3 (smInOf (smReqOfAddr smAlo false 7#3 0#32))  -- t3 读 fire
def smT1s5 := smStep smT1s4 smInNop   -- t4：读数据捕获（vR1=1 → rdata2）
def smT1s6 := smStep smT1s5 smInNop   -- t5：读响应可见于 s5

-- 写落入 bank16 行0（字节小端；t1 拍末写入，s2 可见）
theorem smT1_mem :
    (smT1s2.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩ ⟨0, by decide⟩ = 0xBE#8 ∧
    (smT1s2.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩ ⟨1, by decide⟩ = 0xBA#8 ∧
    (smT1s2.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩ ⟨2, by decide⟩ = 0xFE#8 ∧
    (smT1s2.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩ ⟨3, by decide⟩ = 0xCA#8 ∧
    -- 其他 bank 未被触碰
    (smT1s2.banks ⟨17, by decide⟩).mem ⟨0, by decide⟩ ⟨0, by decide⟩ = 0#8 := by
  native_decide

-- 写响应（t2 拍，状态 s2）：pipe 直通、isWrite/instrId 正确
theorem smT1_write_rsp :
    smRspValid smT1s2 = true ∧ (smRspBits smT1s2).isWrite = true ∧
    (smRspBits smT1s2).instrId = 5#3 ∧
    (smRspBits smT1s2).activeMask ⟨0, by decide⟩ = true ∧
    (smRspBits smT1s2).activeMask ⟨1, by decide⟩ = false := by
  native_decide

-- 读响应（t5 拍，状态 s5）：写后读回同一数据
theorem smT1_read_rsp :
    smRspValid smT1s5 = true ∧ (smRspBits smT1s5).isWrite = false ∧
    (smRspBits smT1s5).instrId = 7#3 ∧
    (smRspBits smT1s5).data ⟨0, by decide⟩ = smT1d ∧
    (smRspBits smT1s5).activeMask ⟨0, by decide⟩ = true := by
  native_decide

-- 写占用期间（t1，状态 s1）ready 拉低（Q2：写 2 拍吞吐）；t2 恢复
theorem smT1_ready :
    smReqReady smInit = true ∧ smReqReady smT1s1 = false ∧
    smReqReady smT1s2 = true := by
  native_decide

/- ---- T3：无冲突并行（4 lane 分属 4 bank，单拍服务） ---- -/

/-- 4 lane 并发请求：lane l 地址 = smAlo + 4l（bank 16..19，同行 0）。 -/
def smReqParallel (wr : Bool) (iid : BitVec 3) : SmCoreReq :=
  { instrId := iid
    isWrite := wr
    setIdx := smSetIdxOfAddr smAlo
    perLaneAddr := fun l =>
      let a := smAlo + BitVec.ofNat 32 (4 * l.val)
      ⟨l.val < 4, lsuBlkOf a, lsuWordOff1H lsuMemW a⟩
    data := fun l => BitVec.ofNat 32 (0x1000 + l.val) }

def smT3s1 := smStep smInit (smInOf (smReqParallel true 1#3))
def smT3s2 := smStep smT3s1 smInNop   -- 4 bank 同拍写入

theorem smT3_no_conflict :
    (smObsArb smInit (smInOf (smReqParallel true 1#3))).bankConflict = false ∧
    (smObsArb smInit (smInOf (smReqParallel true 1#3))).dataArrayEn ⟨16, by decide⟩ = true ∧
    (smObsArb smInit (smInOf (smReqParallel true 1#3))).dataArrayEn ⟨19, by decide⟩ = true ∧
    (smObsArb smInit (smInOf (smReqParallel true 1#3))).dataArrayEn ⟨20, by decide⟩ = false ∧
    (smObsArb smInit (smInOf (smReqParallel true 1#3))).activeLane ⟨3, by decide⟩ = true := by
  native_decide

theorem smT3_parallel_mem :
    smBytesToWord ((smT3s2.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩) = 0x1000#32 ∧
    smBytesToWord ((smT3s2.banks ⟨17, by decide⟩).mem ⟨0, by decide⟩) = 0x1001#32 ∧
    smBytesToWord ((smT3s2.banks ⟨18, by decide⟩).mem ⟨0, by decide⟩) = 0x1002#32 ∧
    smBytesToWord ((smT3s2.banks ⟨19, by decide⟩).mem ⟨0, by decide⟩) = 0x1003#32 := by
  native_decide

/- ---- T4：bank 冲突串行化（2 lane 同 bank16、不同字节使能） ---- -/

/-- lane0 写字节0=0xA5，lane1 写字节1=0x5A（同 bank 同行不同 byte lane；
    BankConflictArbiter.scala:19-23 注明此类合并失败 → 按冲突两拍服务）。 -/
def smReqConflict : SmCoreReq :=
  { instrId := 3#3
    isWrite := true
    setIdx := smSetIdxOfAddr smAlo
    perLaneAddr := fun l =>
      if l.val == 0 then ⟨true, lsuBlkOf smAlo, 0b0001#4⟩
      else if l.val == 1 then ⟨true, lsuBlkOf smAlo, 0b0010#4⟩
      else ⟨false, 0#5, 0#4⟩
    data := fun l => if l.val == 0 then 0xA5#32 else 0x5A00#32 }

def smT4s1 := smStep smInit (smInOf smReqConflict)  -- t0 fire，检出冲突，服务 lane0
def smT4s2 := smStep smT4s1 smInNop  -- t1：保持期服务 lane1；写拍1（lane0）执行
def smT4s3 := smStep smT4s2 smInNop  -- t2：写拍2（lane1）执行；rsp0（mask={0}）
def smT4s4 := smStep smT4s3 smInNop  -- t3：rsp1（mask={1}）于 s3 可见

theorem smT4_conflict_detect :
    (smObsArb smInit (smInOf smReqConflict)).bankConflict = true ∧
    -- t0 只服务 lane0（PriorityEncoderOH 取最低 lane）
    (smObsArb smInit (smInOf smReqConflict)).activeLane ⟨0, by decide⟩ = true ∧
    (smObsArb smInit (smInOf smReqConflict)).activeLane ⟨1, by decide⟩ = false ∧
    -- t1 冲突保持：服务 lane1
    (smObsArb smT4s1 smInNop).activeLane ⟨1, by decide⟩ = true ∧
    (smObsArb smT4s1 smInNop).activeLane ⟨0, by decide⟩ = false ∧
    -- t1 期间 ready 拉低（:194 的 !RegNext(bankConflict)）
    smReqReady smT4s1 = false := by
  native_decide

-- 两拍写都落盘（t2 拍末，s3 可见）：字节合并 0x00005AA5
theorem smT4_serialized_mem :
    smBytesToWord ((smT4s3.banks ⟨16, by decide⟩).mem ⟨0, by decide⟩) = 0x00005AA5#32 := by
  native_decide

-- 冲突写拆成两个响应（t2/s2 与 t3/s3）：mask 先 {0} 后 {1}
theorem smT4_two_rsps :
    smRspValid smT4s2 = true ∧
    (smRspBits smT4s2).activeMask ⟨0, by decide⟩ = true ∧
    (smRspBits smT4s2).activeMask ⟨1, by decide⟩ = false ∧
    (smRspBits smT4s2).isWrite = true ∧
    smRspValid smT4s3 = true ∧
    (smRspBits smT4s3).activeMask ⟨0, by decide⟩ = false ∧
    (smRspBits smT4s3).activeMask ⟨1, by decide⟩ = true := by
  native_decide

/- ---- T5：Q1 读口静默 —— 写服务拍（含冲突保持拍）读口不发射 ---- -/

theorem smT5_read_port_quiet :
    (∀ b : Fin 32, (smVRcomb smT4s1 smInNop &&
      (smObsArb smT4s1 smInNop).dataArrayEn b) = false) ∧
    (∀ b : Fin 32, (smVRcomb smT4s2 smInNop &&
      (smObsArb smT4s2 smInNop).dataArrayEn b) = false) ∧
    (∀ b : Fin 32, (smVRcomb smT1s1 smInNop &&
      (smObsArb smT1s1 smInNop).dataArrayEn b) = false) := by
  native_decide

/- ---- T6：读背靠背全流水（Q2 对照：读不受 vW1 阻塞） ---- -/

def smT6s1 := smStep smInit (smInOf (smReqOfAddr smAlo true 1#3 0xAAAA0000#32))
def smT6s2 := smStep smT6s1 smInNop
def smT6s3 := smStep smT6s2 smInNop
def smT6a2 : BitVec 32 := 0x70000044  -- bank17 行0
def smT6s4 := smStep smT6s3 (smInOf (smReqOfAddr smT6a2 true 2#3 0xBBBB1111#32))
def smT6s5 := smStep smT6s4 smInNop
def smT6s6 := smStep smT6s5 smInNop
def smT6s7 := smStep smT6s6 (smInOf (smReqOfAddr smAlo false 3#3 0#32))  -- t6 读A
def smT6s8 := smStep smT6s7 (smInOf (smReqOfAddr smT6a2 false 4#3 0#32)) -- t7 读B（紧邻）
def smT6s9 := smStep smT6s8 smInNop   -- t8：rspA 于 s8 可见；t9：rspB 于 s9 可见

theorem smT6_read_pipelined :
    -- t7 拍 ready 为高：第二笔读紧邻第一笔发射
    smReqReady smT6s7 = true ∧
    -- t8/t9 连续两拍出响应，数据各回其主
    smRspValid smT6s8 = true ∧
    (smRspBits smT6s8).data ⟨0, by decide⟩ = 0xAAAA0000#32 ∧
    (smRspBits smT6s8).instrId = 3#3 ∧
    smRspValid smT6s9 = true ∧
    (smRspBits smT6s9).data ⟨0, by decide⟩ = 0xBBBB1111#32 ∧
    (smRspBits smT6s9).instrId = 4#3 := by
  native_decide

/- ---- 公理审计（native_decide 定理含 Lean.ofReduceBool，属预期） ---- -/

#print axioms smI21_alias
#print axioms smI21_dead_rows
#print axioms smI21_witness
#print axioms smPrioOH_onehot
#print axioms sm_bytes_word_roundtrip
#print axioms smT1_read_rsp
#print axioms smT4_serialized_mem
#print axioms smT6_read_pipelined

end Ventus.Mem
