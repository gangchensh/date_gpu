/- ========================================================================= -/
/-                          Mem/MSHR.lean                                    -/
/-  LSU miss 信息表 MSHRv2 的 Lean 4 模型、测试与证明                          -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/MSHR.scala:22-109   -/
/-    依赖类型：pipeline/LSU.scala — MshrTag(:82-93)、DCacheCoreRsp_np(:50-60)、-/
/-      object ByteExtract(:95-112)                                           -/
/-  例化关系核查（2026-08-26 全仓 grep）：                                     -/
/-  * MSHRv2 仅在 pipeline/LSU.scala:565 例化（LSUexe 内，名为 Coalscer），    -/
/-    参数取全局配置：lsu_nMshrEntry = num_warp = 8、num_thread = 32、         -/
/-    xLen = 32（top/parameters.scala）。                                     -/
/-  * ByteExtract 仅 MSHR.scala:102 一处使用（LSU 侧后续可复用 bexByteExtract）。-/
/-  连接（LSU.scala:565-570）：from_dcache ← rspArbiter(dcache/shared 仲裁)；  -/
/-    from_addr ← AddrCalculate.to_mshr；idx_entry → AddrCalculate；          -/
/-    to_pipe → LSU2WB（LSU.scala:490-529），其 ready 组合依赖                -/
/-    lsu_rsp.bits.tag.wxd/wfd/isWrite 与 out_x/out_v.ready。                 -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. data/tag 两个 Mem（:31-32）建模为函数（Fin 8 → …）；tag 在 Chisel 中   -/
/-      以 asUInt 位串存储、asTypeOf 还原（:77,:97），只作整体搬运，本模型     -/
/-      直接存结构化 MshrTag，无信息损失。Mem 未初始化读出为未定值，模型取     -/
/-      全 0；仅在 used=0 或 mask 未覆盖时不可观测（见 Q4/Q5 与               -/
/-      mshr_outFire_entry_cleared）。                                        -/
/-  D2. MshrTag.spike_info（:92，SPIKE_OUTPUT=true 时存在）只用于 printf 与    -/
/-      写回信息透传，不影响 MSHR 状态机/数据通路行为，省略。                  -/
/-  D3. FSM s_idle/s_add/s_out（:42）建模为归纳类型 MshrFSM；状态编码值无      -/
/-      外部可观测性。                                                        -/
/-  D4. PriorityEncoder（:38-39）建模为 mshrPriEnc（最低置位位下标，全 0 得 0），-/
/-      与 chisel3.util.PriorityEncoder 对 UInt 的语义一致（LSB 优先）。       -/
/-  D5. ByteExtract（LSU.scala:95-111）的 MuxCase 缺省分支（sel ∉              -/
/-      {F,C,3,8,4,2,1}，如 0x0/0x5）返回 in 原值，模型忠实保留。              -/
/-      wordOffset1H 设计上恒为独热（AddrCalculate :179-193 由 mem_whb 生成    -/
/-      15/3/12/1<<addr(1,0)），但 MSHR 模型不假设这一点。                     -/
/-  D6. to_pipe.bits（:107-108）在 valid 之外也组合计算，消费方仅在 valid      -/
/-      时采样；模型同样常算。                                                -/
/-                                                                           -/
/- ======================== 源码审查发现（详见各节与返回报告） =============== -/
/-  Q1（I 类候选，to_pipe.valid 回撤，违反 Decoupled NoWithdraw）：            -/
/-      io.to_pipe.valid = complete.orR && state===s_out（:106），而进入       -/
/-      s_out 的每条路径（:53,:56,:62,:64）都要求当拍 io.to_pipe.ready=1。     -/
/-      故 valid 拉高当拍若 ready 掉落，:62 otherwise 回 s_idle，valid 在      -/
/-      未 fire 的情况下撤高。第 7 节给出具体 witness 轨迹                     -/
/-      （mshrT_withdraw_witness）并证 ¬ NoWithdraw（mshr_noWithdraw_violated）；-/
/-      mshr_withdraw / mshr_out_entry_needs_ready 钉死机理："进 s_out 必      -/
/-      曾见 ready=1；s_out 内 ready=0 即回撤"。下游 LSU2WB.ready 组合依赖     -/
/-      lsu_rsp.bits.tag（回撤期间 complete/used 不变 ⇒ bits 不变）与          -/
/-      out_x/out_v.ready（写回仲裁，可独立回撤）——是否真实触发需主会话        -/
/-      结合写回级判定。                                                      -/
/-  Q2（提示性，:62 valid_entry/output_entry 混用）：s_out 滞留条件写的是       -/
/-      complete.bitSet(valid_entry, false.B).orR，意图应为 output_entry。     -/
/-      逐情形：表不满时 valid_entry 指向空闲项（必非 complete），bitSet 为    -/
/-      恒等 ⇒ 滞留条件 = complete.orR；表满时 valid_entry=0，若                -/
/-      output_entry=0 则恰好清对位，若 ≠0 则 entry0 必非 complete（优先级     -/
/-      编码取最低置位），bitSet 仍是恒等。结论：与正确写法唯一差别是"本拍      -/
/-      fire 掉最后一个 complete 项"时多滞留 s_out 一拍（当拍 valid 低、        -/
/-      from_dcache.ready 低，多一拍反压），无正确性问题。                     -/
/-  Q3（提示性，:53 快速通道只认严格相等）：currentMask(instrId)===activeMask  -/
/-      才提前转 s_out；响应 mask 是剩余 mask 的严格超集时本拍同样补齐         -/
/-      （:71 后 currentMask=0），但走 :56 慢路径晚一拍进 s_out。行为正确，     -/
/-      仅慢一拍。mshr_fastpath_complete_next（正面）与                        -/
/-      mshrFastpath_subset_cntex（数值反例）给出两种情形。                    -/
/-  Q4（提示性，:45 注释掉的 && used.orR）：空表也会接受 dcache 响应：写       -/
/-      data[instrId]、currentMask &= ~activeMask（空项 cm 本就为 0，不变），   -/
/-      不产生 complete，无害。                                               -/
/-  Q5（提示性，mask=0 分配）：AddrCalculate 对 mask=0 的请求仍会分配表项       -/
/-      （:81 currentMask := 0），该项立即 complete（:37），不经任何 dcache     -/
/-      响应即可被输出（输出数据因 tag.mask=0 全为 0，:101-103）。行为自洽；    -/
/-      是否真会出现 mask=0 的访存指令由主会话结合译码判定。                   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.Handshake
import Std.Tactic.BVDecide

namespace Ventus.Mem

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 参数常量（top/parameters.scala；lsu_nMshrEntry = num_warp = 8）          -/
/- ========================================================================= -/

def mshrNEntry : Nat := 8      -- lsu_nMshrEntry = num_warp = 8
def mshrNumThread : Nat := 32  -- num_thread = 32
def mshrXLen : Nat := 32       -- xLen = 32
def mshrDepthWarp : Nat := 3   -- depth_warp = log2Ceil 8
def mshrRegIdxW : Nat := 8     -- regidx_width + regext_width = 5 + 3

/- ========================================================================= -/
/- 2. MshrTag / 响应 / ByteExtract（LSU.scala:82-112）                        -/
/- ========================================================================= -/

/-- MshrTag（LSU.scala:82-93），省略 spike_info（D2）。
    mask 打包为 BitVec 32；wordOffset1H 为 32 lane 的 4 位独热选择。 -/
structure MshrTag where
  warp_id : BitVec 3
  wfd : Bool
  wxd : Bool
  reg_idxw : BitVec 8
  mask : BitVec 32
  unsigned : Bool
  isvec : Bool
  wordOffset1H : Fin 32 → BitVec 4
  isWrite : Bool

def mshrTagDefault : MshrTag := ⟨0, false, false, 0, 0, false, false, fun _ => 0xF#4, false⟩

/-- 字段抽取的扩展（LSU.scala:101-106 各分支 Mux 的两臂合并形式）：
    isUInt=true 恒零扩展；isUInt=false 按字段自身符号位扩展
    （等价于源码 `Mux(!符号位||isUInt, Cat(0,f), Cat(全1,f))`）。 -/
def bexExt {n : Nat} (isUInt : Bool) (f : BitVec n) : BitVec 32 :=
  if isUInt then f.zeroExtend 32 else f.signExtend 32

/-- ByteExtract（LSU.scala:95-111）：按独热 sel 抽取 word/half/byte 并扩展。
    MuxCase 缺省（sel 非枚举值）返回 in 原值（D5）。 -/
def bexByteExtract (isUInt : Bool) (x : BitVec 32) (sel : BitVec 4) : BitVec 32 :=
  if sel = 0xF#4 then x                                            -- "hf"，lw
  else if sel = 0xC#4 then bexExt isUInt (x.extractLsb' 16 16)     -- "hc"，lh 高半
  else if sel = 0x3#4 then bexExt isUInt (x.extractLsb' 0 16)      -- "h3"，lh 低半
  else if sel = 0x8#4 then bexExt isUInt (x.extractLsb' 24 8)      -- "h8"，lb byte3
  else if sel = 0x4#4 then bexExt isUInt (x.extractLsb' 16 8)      -- "h4"，lb byte2
  else if sel = 0x2#4 then bexExt isUInt (x.extractLsb' 8 8)       -- "h2"，lb byte1
  else if sel = 0x1#4 then bexExt isUInt (x.extractLsb' 0 8)       -- "h1"，lb byte0
  else x                                                           -- MuxCase 缺省

/- ---- ByteExtract 测试 ---- -/

-- lw：恒等
example : bexByteExtract false 0x80008001#32 0xF#4 = 0x80008001#32 := by decide
-- lh 高半（sel=0xC）：扩展看 in(31) 与 isUInt
example : bexByteExtract true 0xFFFF1234#32 0xC#4 = 0x0000FFFF#32 := by decide
example : bexByteExtract false 0xFFFF1234#32 0xC#4 = 0xFFFFFFFF#32 := by decide
example : bexByteExtract false 0x7FFF0000#32 0xC#4 = 0x00007FFF#32 := by decide
-- lh 低半（sel=0x3）：看 in(15)
example : bexByteExtract false 0x00008001#32 0x3#4 = 0xFFFF8001#32 := by decide
example : bexByteExtract true 0x00008001#32 0x3#4 = 0x00008001#32 := by decide
-- lb byte3（sel=0x8）：看 in(31)
example : bexByteExtract false 0x80000000#32 0x8#4 = 0xFFFFFF80#32 := by decide
example : bexByteExtract true 0x80000000#32 0x8#4 = 0x00000080#32 := by decide
-- lb byte2（sel=0x4）：看 in(23)
example : bexByteExtract false 0x00800000#32 0x4#4 = 0xFFFFFF80#32 := by decide
-- lb byte1/byte0（sel=0x2/0x1）：看 in(15)/in(7)
example : bexByteExtract true 0x0000FF00#32 0x2#4 = 0x000000FF#32 := by decide
example : bexByteExtract false 0x00000080#32 0x1#4 = 0xFFFFFF80#32 := by decide
example : bexByteExtract false 0x0000007F#32 0x1#4 = 0x0000007F#32 := by decide
-- MuxCase 缺省：sel=0x0 / 非独热（0x5）均返回原值（D5）
example : bexByteExtract false 0xDEADBEEF#32 0x0#4 = 0xDEADBEEF#32 := by decide
example : bexByteExtract true 0xDEADBEEF#32 0x5#4 = 0xDEADBEEF#32 := by decide

/-- lw（sel=0xF）恒为原值（符号化）。 -/
theorem bex_lw (isUInt : Bool) (x : BitVec 32) : bexByteExtract isUInt x 0xF#4 = x := by
  simp [bexByteExtract]

/-- lh 低半：结果恒为低 16 位的零/符号扩展（符号化）。 -/
theorem bex_lh_low (isUInt : Bool) (x : BitVec 32) :
    bexByteExtract isUInt x 0x3#4 = bexExt isUInt (x.extractLsb' 0 16) := by
  simp [bexByteExtract]

/- ========================================================================= -/
/- 3. 状态与组合逻辑（MSHR.scala:31-47, 97-108）                              -/
/- ========================================================================= -/

/-- FSM（:42）：s_idle / s_add / s_out（D3）。 -/
inductive MshrFSM where
  | idle | add | out
deriving DecidableEq, Repr

def MshrFSM.isIdle : MshrFSM → Bool | .idle => true | _ => false
def MshrFSM.isAdd  : MshrFSM → Bool | .add  => true | _ => false
def MshrFSM.isOut  : MshrFSM → Bool | .out  => true | _ => false

/-- MSHRv2 状态（:31-40）：data / tag / currentMask / used / reg_req / state。 -/
structure MshrState where
  data : Fin 8 → Fin 32 → BitVec 32      -- data Mem（:31，组合读）
  tag : Fin 8 → MshrTag                  -- tag Mem（:32）
  currentMask : Fin 8 → BitVec 32        -- 剩余待服务 lane（:34），0=complete
  used : BitVec 8                        -- 占用位向量（:36）
  regReq : MshrTag                       -- reg_req（:40），同拍双 fire 的暂存
  state : MshrFSM

/-- 初始状态：currentMask/used RegInit 0（:34,:36），state=s_idle（:43）；
    data/tag/reg_req 未初始化，建模为全 0（D1）。 -/
def mshrInit : MshrState :=
  ⟨fun _ _ => 0, fun _ => mshrTagDefault, fun _ => 0, 0#8, mshrTagDefault, .idle⟩

/-- 输入（io.from_addr / io.from_dcache / io.to_pipe.ready，:24-29）。 -/
structure MshrIn where
  addrValid : Bool
  addrTag : MshrTag
  dcValid : Bool
  rspId : BitVec 3
  rspData : Fin 32 → BitVec 32
  rspMask : BitVec 32
  outReady : Bool

def mshrInIdle : MshrIn := ⟨false, mshrTagDefault, false, 0, fun _ => 0, 0, false⟩

/-- 3 位表项号 → Fin 8。 -/
def mshrIdx3 (b : BitVec 3) : Fin 8 := ⟨b.toNat, b.isLt⟩

/-- 函数表更新（Function.update 的本项目手写版，与 Ventus.Base.Defs 的 rf_write 同风格）。 -/
def mshrUpd (f : Fin 8 → α) (i : Fin 8) (v : α) : Fin 8 → α :=
  fun j => if i = j then v else f j

@[simp] theorem mshrUpd_self (f : Fin 8 → α) (i : Fin 8) (v : α) :
    mshrUpd f i v i = v := by simp [mshrUpd]

theorem mshrUpd_of_ne (f : Fin 8 → α) (i j : Fin 8) (v : α) (h : j ≠ i) :
    mshrUpd f i v j = f j := by
  simp only [mshrUpd]; exact if_neg (fun hh => h hh.symm)

/-- PriorityEncoder（8 → 3）：最低置位位下标，全 0 得 0（D4）。 -/
def mshrPriEnc (v : BitVec 8) : BitVec 3 :=
  if v &&& 0x01#8 ≠ 0 then 0
  else if v &&& 0x02#8 ≠ 0 then 1
  else if v &&& 0x04#8 ≠ 0 then 2
  else if v &&& 0x08#8 ≠ 0 then 3
  else if v &&& 0x10#8 ≠ 0 then 4
  else if v &&& 0x20#8 ≠ 0 then 5
  else if v &&& 0x40#8 ≠ 0 then 6
  else if v &&& 0x80#8 ≠ 0 then 7
  else 0

/-- 同宽 ofNat-toNat 引理（位读取的索引桥接）。 -/
theorem mshr_ofNat_toNat3 (e : BitVec 3) : BitVec.ofNat 3 e.toNat = e := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- 占用位读取（BitVec 3 索引，移位形式取位，规避 bv_decide 变量下标限制）。 -/
def mshrUsedBit3 (s : MshrState) (e : BitVec 3) : Bool :=
  ((s.used >>> e.zeroExtend 8) &&& 1#8) == 1#8

/-- 占用位读取（Fin 8 索引版）。 -/
def mshrUsedBit (s : MshrState) (i : Fin 8) : Bool :=
  mshrUsedBit3 s (BitVec.ofNat 3 i.val)

/-- 表项 i 完成（:37 的逐项定义）：剩余 mask 为 0 且已占用。 -/
def mshrEntryComplete (s : MshrState) (i : Fin 8) : Bool :=
  (s.currentMask i == 0#32) && mshrUsedBit s i

/-- complete 位向量（:37，VecInit(...).asUInt & used 的展开）。 -/
def mshrComplete8 (s : MshrState) : BitVec 8 :=
  (if mshrEntryComplete s (0 : Fin 8) then 0x01#8 else 0#8) |||
  (if mshrEntryComplete s (1 : Fin 8) then 0x02#8 else 0#8) |||
  (if mshrEntryComplete s (2 : Fin 8) then 0x04#8 else 0#8) |||
  (if mshrEntryComplete s (3 : Fin 8) then 0x08#8 else 0#8) |||
  (if mshrEntryComplete s (4 : Fin 8) then 0x10#8 else 0#8) |||
  (if mshrEntryComplete s (5 : Fin 8) then 0x20#8 else 0#8) |||
  (if mshrEntryComplete s (6 : Fin 8) then 0x40#8 else 0#8) |||
  (if mshrEntryComplete s (7 : Fin 8) then 0x80#8 else 0#8)

/-- complete.orR（:37,:56,:64,:106）。 -/
def mshrCompleteOrR (s : MshrState) : Bool := mshrComplete8 s != 0#8

/-- output_entry = Mux(complete.orR, PriorityEncoder(complete), 0)（:38）。 -/
def mshrOutputEntry (s : MshrState) : BitVec 3 :=
  if mshrComplete8 s == 0#8 then 0#3 else mshrPriEnc (mshrComplete8 s)

/-- valid_entry = Mux(used.andR, 0, PriorityEncoder(~used))（:39）。 -/
def mshrValidEntry (s : MshrState) : BitVec 3 :=
  if s.used == 0xFF#8 then 0#3 else mshrPriEnc (~~~s.used)

/-- io.from_addr.ready（:46）。 -/
def mshrAddrRdy (s : MshrState) : Bool := s.state.isIdle && (s.used != 0xFF#8)
/-- io.from_dcache.ready（:45，注释掉的 && used.orR 见 Q4）。 -/
def mshrDcRdy (s : MshrState) : Bool := s.state.isIdle

def mshrAddrFire (s : MshrState) (i : MshrIn) : Bool := i.addrValid && mshrAddrRdy s
def mshrDcFire (s : MshrState) (i : MshrIn) : Bool := i.dcValid && mshrDcRdy s
/-- io.to_pipe.valid（:106）。 -/
def mshrOutValid (s : MshrState) : Bool := (mshrComplete8 s != 0#8) && s.state.isOut
/-- io.to_pipe.fire。 -/
def mshrOutFire (s : MshrState) (i : MshrIn) : Bool := mshrOutValid s && i.outReady

/-- io.idx_entry（:47）：仅在 from_addr.fire 时被 AddrCalculate 采样（LSU.scala:386）。 -/
def mshrIdxEntry (s : MshrState) (i : MshrIn) : BitVec 3 :=
  if mshrAddrFire s i then mshrValidEntry s else 0#3

/-- output_tag = tag.read(output_entry)（:97）。 -/
def mshrOutTag (s : MshrState) : MshrTag := s.tag (mshrIdx3 (mshrOutputEntry s))

/-- 输出级（:98-105）：mask 覆盖的 lane 经 ByteExtract，其余为 0。 -/
def mshrOutData (s : MshrState) : Fin 32 → BitVec 32 :=
  let oe := mshrIdx3 (mshrOutputEntry s)
  let t := s.tag oe
  fun l => if (t.mask >>> l.val) &&& 1#32 = 1#32
    then bexByteExtract t.unsigned (s.data oe l) (t.wordOffset1H l)
    else 0#32

/- ========================================================================= -/
/- 4. 单拍转移（MSHR.scala:49-96）                                            -/
/- ========================================================================= -/

/-- FSM 状态转移（:49-65）。注意 :62 滞留条件用 valid_entry 而非
    output_entry（疑点 Q2，模型忠实复现）。 -/
def mshrStateN (s : MshrState) (i : MshrIn) : MshrFSM :=
  if s.state.isIdle then
    if mshrDcFire s i then
      if mshrAddrFire s i then .add                                            -- :51-52
      else if i.outReady && (s.currentMask (mshrIdx3 i.rspId) == i.rspMask)    -- :53-54
      then .out
      else .idle                                                              -- :55
    else if (mshrComplete8 s != 0#8) && i.outReady then .out                    -- :56-57
    else .idle                                                                -- :58-59
  else if s.state.isOut then
    if i.outReady &&
        ((mshrComplete8 s &&& ~~~(1#8 <<< (mshrValidEntry s).zeroExtend 8)) != 0#8)
    then .out else .idle                                                      -- :62
  else
    if i.outReady && (mshrComplete8 s != 0#8) then .out else .idle             -- :64

/-- data 更新（:70）：s_idle 且响应 fire 时按 activeMask 逐 lane 写入。 -/
def mshrDataN (s : MshrState) (i : MshrIn) : Fin 8 → Fin 32 → BitVec 32 :=
  if s.state.isIdle && mshrDcFire s i then
    mshrUpd s.data (mshrIdx3 i.rspId)
      (fun l => if (i.rspMask >>> l.val) &&& 1#32 = 1#32 then i.rspData l
                else s.data (mshrIdx3 i.rspId) l)
  else s.data

/-- currentMask 更新（:71 响应清批 / :81 分配初始化 / :91 s_add 延迟初始化）。 -/
def mshrCmN (s : MshrState) (i : MshrIn) : Fin 8 → BitVec 32 :=
  if s.state.isIdle && mshrDcFire s i then
    mshrUpd s.currentMask (mshrIdx3 i.rspId)
      (s.currentMask (mshrIdx3 i.rspId) &&& ~~~i.rspMask)                      -- :71
  else if s.state.isIdle && mshrAddrFire s i then
    mshrUpd s.currentMask (mshrIdx3 (mshrValidEntry s)) i.addrTag.mask -- :81
  else if s.state.isAdd then
    mshrUpd s.currentMask (mshrIdx3 (mshrValidEntry s)) s.regReq.mask  -- :91
  else s.currentMask

/-- tag 更新（:75-78 / :86-89）。 -/
def mshrTagN (s : MshrState) (i : MshrIn) : Fin 8 → MshrTag :=
  if s.state.isIdle && !mshrDcFire s i && mshrAddrFire s i then
    mshrUpd s.tag (mshrIdx3 (mshrValidEntry s)) i.addrTag              -- :75-78
  else if s.state.isAdd then
    mshrUpd s.tag (mshrIdx3 (mshrValidEntry s)) s.regReq               -- :86-89
  else s.tag

/-- used 更新（:74 / :85 / :94）。 -/
def mshrUsedN (s : MshrState) (i : MshrIn) : BitVec 8 :=
  if s.state.isIdle && !mshrDcFire s i && mshrAddrFire s i then
    s.used ||| (1#8 <<< (mshrValidEntry s).zeroExtend 8)                       -- :74
  else if s.state.isAdd then
    s.used ||| (1#8 <<< (mshrValidEntry s).zeroExtend 8)                       -- :85
  else if s.state.isOut && mshrOutFire s i then
    s.used &&& ~~~(1#8 <<< (mshrOutputEntry s).zeroExtend 8)                   -- :94
  else s.used

/-- reg_req 更新（:72）：同拍双 fire 时暂存分配请求。 -/
def mshrRegReqN (s : MshrState) (i : MshrIn) : MshrTag :=
  if s.state.isIdle && mshrDcFire s i && mshrAddrFire s i then i.addrTag else s.regReq

/-- 单拍转移（:49-96，FSM 与数据通路均按旧状态求值）。 -/
def mshrStep (s : MshrState) (i : MshrIn) : MshrState :=
  ⟨mshrDataN s i, mshrTagN s i, mshrCmN s i, mshrUsedN s i, mshrRegReqN s i, mshrStateN s i⟩

/-- 多拍执行。 -/
def mshrRun (s : MshrState) (is : List MshrIn) : MshrState := is.foldl mshrStep s

/- ========================================================================= -/
/- 5. 具体数值测试                                                            -/
/- ========================================================================= -/

section MshrTests

/-- 测试用 tag：warp 2、向量写回、mask=0b…0011（lane 0,1），
    lane0 按 lh 低半抽取、其余按 lw。 -/
def mshrTagT1 : MshrTag :=
  { warp_id := 2, wfd := true, wxd := false, reg_idxw := 5, mask := 0x00000003#32,
    unsigned := false, isvec := true,
    wordOffset1H := fun l => if l.val = 0 then 0x3#4 else 0xF#4, isWrite := false }

/- ---- T1：分配 → 响应（:53 快速通道）→ 输出 fire 释放 ---- -/

def mshrT1I0 : MshrIn := ⟨true, mshrTagT1, false, 0, fun _ => 0, 0, false⟩
def mshrT1I1 : MshrIn := ⟨false, mshrTagDefault, true, 0#3,
  fun l => if l.val = 0 then 0x00008001#32 else 0x7FFF0000#32, 0x00000003#32, true⟩
def mshrT1I2 : MshrIn := ⟨false, mshrTagDefault, false, 0, fun _ => 0, 0, true⟩

def mshrT1S1 := mshrStep mshrInit mshrT1I0
def mshrT1S2 := mshrStep mshrT1S1 mshrT1I1
def mshrT1S3 := mshrStep mshrT1S2 mshrT1I2

-- 拍 0：分配 entry0（idx_entry=0），used=01，cm[0]=3，tag[0] 就位
theorem mshrT1_alloc :
    mshrT1S1.used = 0x01#8 ∧ mshrT1S1.state = .idle ∧
    mshrT1S1.currentMask ⟨0, by decide⟩ = 0x00000003#32 ∧
    (mshrT1S1.tag ⟨0, by decide⟩).warp_id = 2#3 ∧
    mshrIdxEntry mshrInit mshrT1I0 = 0#3 := by
  native_decide

-- 拍 1：响应覆盖全部剩余 lane 且 ready=1 → :53 快速通道转 s_out；cm[0] 清零
theorem mshrT1_fastpath :
    mshrT1S2.state = .out ∧ mshrOutValid mshrT1S2 = true ∧
    mshrT1S2.currentMask ⟨0, by decide⟩ = 0#32 := by
  native_decide

-- 拍 2 输出数据：lane0 = lbu?（unsigned=false, sel=0x3 → lb? lh 低半符号扩展 0x8001）；
-- lane1 = lw 原值；lane2 不在 mask 内为 0（:101-103）
theorem mshrT1_outdata :
    mshrOutData mshrT1S2 ⟨0, by decide⟩ = 0xFFFF8001#32 ∧
    mshrOutData mshrT1S2 ⟨1, by decide⟩ = 0x7FFF0000#32 ∧
    mshrOutData mshrT1S2 ⟨2, by decide⟩ = 0#32 ∧
    (mshrOutTag mshrT1S2).reg_idxw = 5#8 := by
  native_decide

-- 拍 2 fire（ready=1）：拍 3 used 清零。注意 Q2：:62 的滞留条件错用 valid_entry
-- （=1，bitSet 清的是位 1 而非 output_entry=0），滞留条件误判为真 → 多停 s_out
-- 一拍（当拍 valid 为低、from_dcache.ready 为低），拍 4 才回 s_idle。
theorem mshrT1_release :
    mshrT1S3.used = 0#8 ∧ mshrT1S3.state = .out ∧ mshrOutValid mshrT1S3 = false ∧
    (mshrStep mshrT1S3 mshrInIdle).state = .idle := by
  native_decide

/- ---- T2：同拍 from_dcache.fire & from_addr.fire（:51-55,:72）→ s_add 延迟分配 ---- -/

def mshrT2I0 : MshrIn := ⟨true, mshrTagT1, true, 5#3, fun _ => 0xEE#32, 0x00000000#32, false⟩
def mshrT2S1 := mshrStep mshrInit mshrT2I0    -- 双 fire → s_add，reg_req 暂存，used 不变
def mshrT2S2 := mshrStep mshrT2S1 mshrInIdle  -- s_add 分配（ready=0 → :64 回 s_idle）

theorem mshrT2_bothfire :
    mshrT2S1.state = .add ∧ mshrT2S1.used = 0#8 ∧
    (mshrT2S1.regReq).warp_id = 2#3 ∧ mshrIdxEntry mshrInit mshrT2I0 = 0#3 := by
  native_decide

-- s_add 拍分配 entry0（与接受拍上报的 idx_entry 一致，定理 mshr_sadd_alloc_consistent
-- 给出一般性保证）
theorem mshrT2_sadd_alloc :
    mshrT2S2.used = 0x01#8 ∧ (mshrT2S2.tag ⟨0, by decide⟩).reg_idxw = 5#8 ∧
    mshrT2S2.currentMask ⟨0, by decide⟩ = 0x00000003#32 ∧ mshrT2S2.state = .idle := by
  native_decide

/- ---- T4：表满反压（:39,:46） ---- -/

def mshrSFull : MshrState := { mshrInit with used := 0xFF#8 }

theorem mshrT4_full_backpressure :
    mshrAddrRdy mshrSFull = false ∧ mshrDcRdy mshrSFull = true ∧
    mshrValidEntry mshrSFull = 0#3 ∧ mshrComplete8 mshrSFull = 0xFF#8 := by
  native_decide

/- ---- T5：mask=0 分配立即 complete（Q5） ---- -/

def mshrTagZero : MshrTag := { mshrTagDefault with mask := 0#32 }
def mshrT5S1 := mshrStep mshrInit ⟨true, mshrTagZero, false, 0, fun _ => 0, 0, false⟩

-- 分配当拍后该项已 complete，但 state=idle ⇒ to_pipe.valid 仍为低（valid 门控 :106）
theorem mshrT5_immediate_complete :
    mshrComplete8 mshrT5S1 = 0x01#8 ∧ mshrOutValid mshrT5S1 = false := by
  native_decide

-- 下一拍 ready 高即经 :56 转 s_out
theorem mshrT5_output_next :
    (mshrStep mshrT5S1 { mshrInIdle with outReady := true }).state = .out := by
  native_decide

/- ---- 组合逻辑小测试 ---- -/

example : mshrPriEnc 0x00#8 = 0#3 := by decide
example : mshrPriEnc 0x01#8 = 0#3 := by decide
example : mshrPriEnc 0x14#8 = 2#3 := by decide
example : mshrPriEnc 0x80#8 = 7#3 := by decide
example : mshrPriEnc 0xFF#8 = 0#3 := by decide

-- complete 位向量与 output_entry（entry2 完成）
def mshrSC2 : MshrState :=
  { mshrInit with currentMask := fun e => if e.val = 2 then 0#32 else 1#32,
                  used := 0b00000100#8 }

theorem mshrT_complete8 :
    mshrComplete8 mshrSC2 = 0b00000100#8 ∧ mshrOutputEntry mshrSC2 = 2#3 := by
  native_decide

-- PriorityEncoder 退化值不被消费：complete 全 0 时 output_entry=0 但 valid=0
theorem mshrT_degenerate_safe :
    mshrOutputEntry mshrInit = 0#3 ∧ mshrOutValid mshrInit = false := by
  native_decide

end MshrTests

/- ========================================================================= -/
/- 6. 符号化定理                                                              -/
/- ========================================================================= -/

/-- PriorityEncoder 命中性：非零输入时选中位必置位。 -/
theorem mshrPriEnc_bit (v : BitVec 8) :
    v ≠ 0#8 → (v >>> (mshrPriEnc v).zeroExtend 8) &&& 1#8 = 1#8 := by
  simp only [mshrPriEnc]; bv_decide

/-- PriorityEncoder 最小性：选中位之下无置位位。 -/
theorem mshrPriEnc_min (v : BitVec 8) :
    v ≠ 0#8 → v &&& ((1#8 <<< (mshrPriEnc v).zeroExtend 8) - 1#8) = 0#8 := by
  simp only [mshrPriEnc]; bv_decide

/-- 清位自明：bitSet(x, false) 清掉的位读出必为 0（:94 释放语义的位级形式）。 -/
theorem mshr_bit_clear (u : BitVec 8) (e : BitVec 3) :
    ((u &&& ~~~(1#8 <<< e.zeroExtend 8)) >>> e.zeroExtend 8) &&& 1#8 = 0#8 := by
  bv_decide

/-- complete ⇒ used（:37 定义即含 used 合取）。 -/
theorem mshrEntryComplete_used (s : MshrState) (i : Fin 8)
    (h : mshrEntryComplete s i = true) : mshrUsedBit s i = true := by
  simp [mshrEntryComplete] at h; exact h.2

/-- isOut 的构造器刻画。 -/
theorem MshrFSM.out_of_isOut {f : MshrFSM} (h : f.isOut = true) : f = .out := by
  cases f <;> simp_all [MshrFSM.isOut]

/-- Q1 机理（逆否形式）：ready=0 ⇒ 下一拍必不在 s_out
    （:53,:56,:62,:64 的转 s_out 条件全部含 to_pipe.ready）。 -/
theorem mshr_stateN_ne_out_of_not_ready (s : MshrState) (i : MshrIn)
    (hr : i.outReady = false) : (mshrStep s i).state ≠ .out := by
  cases hs : s.state <;>
    simp [mshrStep, mshrStateN, hs, hr, MshrFSM.isIdle, MshrFSM.isOut] <;>
    by_cases hdc : mshrDcFire s i = true <;>
    by_cases haf : mshrAddrFire s i = true <;>
    simp [hdc, haf]

/-- Q1 机理（正面）：进 s_out 的每条路径都要求当拍 to_pipe.ready = 1。 -/
theorem mshr_out_entry_needs_ready (s : MshrState) (i : MshrIn)
    (h : (mshrStep s i).state = .out) : i.outReady = true := by
  cases hr : i.outReady with
  | false => exact absurd h (mshr_stateN_ne_out_of_not_ready s i hr)
  | true => rfl

/-- Q1 机理（回撤）：s_out 内 ready=0 ⇒ 下拍回 s_idle，valid 未 fire 撤低。 -/
theorem mshr_withdraw (s : MshrState) (i : MshrIn)
    (hs : s.state = .out) (hr : i.outReady = false) :
    mshrOutValid (mshrStep s i) = false := by
  have hne := mshr_stateN_ne_out_of_not_ready s i hr
  have h2 : (mshrStep s i).state.isOut = false := by
    cases hst : (mshrStep s i).state with
    | idle => rfl
    | add => rfl
    | out => exact absurd hst hne
  simp [mshrOutValid, h2]

/-- valid 仅在 s_out（:106 定义即含 state===s_out）。 -/
theorem mshr_outValid_isOut (s : MshrState) (h : mshrOutValid s = true) :
    s.state.isOut = true := by
  simp [mshrOutValid] at h; exact h.2

/-- 响应拍 used 不变（:69-72 的 s_idle 响应分支不触碰 used）——
    s_add 延迟分配一致性的基础。 -/
theorem mshr_used_unchanged_of_idle_dcFire (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true) :
    (mshrStep s i).used = s.used := by
  simp [mshrStep, mshrUsedN, hs, MshrFSM.isIdle, MshrFSM.isAdd, MshrFSM.isOut, hdc]

/-- s_add 延迟分配一致性（:51-55,:72 与 :84-91 联立）：同拍双 fire 当拍 used 不变，
    故 s_add 拍重算的 valid_entry 与接受拍相同；AddrCalculate 在接受拍采样的
    idx_entry 与实际分配项一致。 -/
theorem mshr_sadd_alloc_consistent (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true) :
    mshrValidEntry (mshrStep s i) = mshrValidEntry s ∧
    mshrIdxEntry s i =
      (if mshrAddrFire s i then mshrValidEntry (mshrStep s i) else 0#3) := by
  have hu := mshr_used_unchanged_of_idle_dcFire s i hs hdc
  constructor
  · simp [mshrValidEntry, hu]
  · simp [mshrIdxEntry, mshrValidEntry, hu]

/-- valid_entry 必指向空闲项（:39 的 PriorityEncoder(~used) 与 :46 的
    !used.andR 联立）——分配安全性（无重复分配）。 -/
theorem mshr_priEnc_free (u : BitVec 8) :
    u ≠ 0xFF#8 → (u >>> (mshrPriEnc (~~~u)).zeroExtend 8) &&& 1#8 = 0#8 := by
  simp only [mshrPriEnc]; bv_decide

theorem mshr_addrFire_entry_free (s : MshrState) (i : MshrIn)
    (hf : mshrAddrFire s i = true) :
    mshrUsedBit3 s (mshrValidEntry s) = false := by
  have hr : s.used ≠ 0xFF#8 := by
    simp [mshrAddrFire, mshrAddrRdy] at hf
    exact hf.2.2
  have hve : mshrValidEntry s = mshrPriEnc (~~~s.used) := by simp [mshrValidEntry, hr]
  simp only [mshrUsedBit3, hve, beq_eq_false_iff_ne]
  rw [mshr_priEnc_free s.used hr]
  decide

/-- s_out 释放（:94）：fire 后 output_entry 的 used 位被清零。 -/
theorem mshr_outFire_used_cleared (s : MshrState) (i : MshrIn)
    (hs : s.state = .out) (hf : mshrOutFire s i = true) :
    (mshrStep s i).used = s.used &&& ~~~(1#8 <<< (mshrOutputEntry s).zeroExtend 8) := by
  simp [mshrStep, mshrUsedN, hs, hf, MshrFSM.isIdle, MshrFSM.isAdd, MshrFSM.isOut]

/-- s_out 释放（:94）：fire 后 output_entry 不再是 complete 项——
    项复用安全性：被释放项在重新分配前不会被再次选中输出。 -/
theorem mshr_outFire_entry_cleared (s : MshrState) (i : MshrIn)
    (hs : s.state = .out) (hf : mshrOutFire s i = true) :
    mshrEntryComplete (mshrStep s i) (mshrIdx3 (mshrOutputEntry s)) = false := by
  have hub : mshrUsedBit3 (mshrStep s i) (mshrOutputEntry s) = false := by
    simp only [mshrUsedBit3, mshr_outFire_used_cleared s i hs hf, beq_eq_false_iff_ne]
    rw [mshr_bit_clear]
    decide
  simp [mshrEntryComplete, mshrUsedBit, mshrIdx3, hub]

/-- 响应拍的 mask 更新（:71）：剩余 mask 清除本批 lane。 -/
theorem mshr_rsp_cm_update (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true) :
    (mshrStep s i).currentMask (mshrIdx3 i.rspId) =
      s.currentMask (mshrIdx3 i.rspId) &&& ~~~i.rspMask := by
  simp [mshrStep, mshrCmN, hs, MshrFSM.isIdle, hdc, mshrUpd_self]

/-- 响应拍的数据更新（:70）：activeMask 覆盖的 lane 写入响应数据，其余不变。 -/
theorem mshr_rsp_data_update (s : MshrState) (i : MshrIn) (l : Fin 32)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true) :
    (mshrStep s i).data (mshrIdx3 i.rspId) l =
      (if (i.rspMask >>> l.val) &&& 1#32 = 1#32 then i.rspData l
       else s.data (mshrIdx3 i.rspId) l) := by
  simp [mshrStep, mshrDataN, hs, MshrFSM.isIdle, hdc, mshrUpd_self]

/-- 分配拍的 mask 初始化（:81）。 -/
theorem mshr_alloc_cm_init (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = false) (ha : mshrAddrFire s i = true) :
    (mshrStep s i).currentMask (mshrIdx3 (mshrValidEntry s)) = i.addrTag.mask := by
  simp [mshrStep, mshrCmN, hs, MshrFSM.isIdle, hdc, ha, mshrUpd_self]

/-- 分配拍的 used 置位（:74）。 -/
theorem mshr_alloc_used_set (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = false) (ha : mshrAddrFire s i = true) :
    (mshrStep s i).used = s.used ||| (1#8 <<< (mshrValidEntry s).zeroExtend 8) := by
  simp [mshrStep, mshrUsedN, hs, MshrFSM.isIdle, hdc, ha]

/-- 快速通道一致性（Q3 正面）：:53 严格相等条件成立时，本拍响应后该项确实
    complete（:71 的 mask 更新与 :37 的 complete 判定一致）。 -/
theorem mshr_fastpath_complete_next (s : MshrState) (i : MshrIn)
    (hs : s.state = .idle) (hdc : mshrDcFire s i = true)
    (hused : mshrUsedBit s (mshrIdx3 i.rspId) = true)
    (hfp : s.currentMask (mshrIdx3 i.rspId) = i.rspMask) :
    mshrEntryComplete (mshrStep s i) (mshrIdx3 i.rspId) = true := by
  have hcm : (mshrStep s i).currentMask (mshrIdx3 i.rspId) = 0#32 := by
    rw [mshr_rsp_cm_update s i hs hdc, hfp]
    bv_decide
  have hu : (mshrStep s i).used = s.used := mshr_used_unchanged_of_idle_dcFire s i hs hdc
  have hub : mshrUsedBit (mshrStep s i) (mshrIdx3 i.rspId) = true := by
    simp only [mshrUsedBit, mshrUsedBit3]; rw [hu]; exact hused
  simp [mshrEntryComplete, hcm, hub]

/-- Q3 反例（数值）：响应 mask 为剩余 mask 的严格超集时本拍同样补齐
    （cm & ~am = 0），但 :53 的严格相等不成立 → 走 :56 慢路径晚一拍。 -/
theorem mshrFastpath_subset_cntex :
    (0x00000003#32) &&& ~~~(0x00000007#32) = 0#32 ∧
    (0x00000003#32 ≠ 0x00000007#32) := by
  decide

/-- 输出级：mask 覆盖 lane 经 ByteExtract（:101-102）。 -/
theorem mshr_outData_masked (s : MshrState) (l : Fin 32)
    (hm : ((mshrOutTag s).mask >>> l.val) &&& 1#32 = 1#32) :
    mshrOutData s l = bexByteExtract (mshrOutTag s).unsigned
      (s.data (mshrIdx3 (mshrOutputEntry s)) l) ((mshrOutTag s).wordOffset1H l) := by
  simp only [mshrOutTag] at hm
  simp only [mshrOutData, mshrOutTag]
  exact if_pos hm

/-- 输出级：mask 未覆盖 lane 恒为 0（:103）。 -/
theorem mshr_outData_unmasked (s : MshrState) (l : Fin 32)
    (hm : ((mshrOutTag s).mask >>> l.val) &&& 1#32 ≠ 1#32) :
    mshrOutData s l = 0#32 := by
  simp only [mshrOutData]
  exact if_neg hm

/- ========================================================================= -/
/- 7. Q1 witness：to_pipe.valid 回撤违反 NoWithdraw                           -/
/- ========================================================================= -/

/-- to_pipe 通道 bits（:107-108 的组合输出）。 -/
structure MshrOutBits where
  tag : MshrTag
  data : Fin 32 → BitVec 32

/-- to_pipe 通道的逐拍观测：valid/bits 由状态驱动（:106-108），ready 为当拍输入。 -/
def mshrTraceOf (is : List MshrIn) : Ventus.Base.Handshake.Trace MshrOutBits :=
  fun t =>
    let s := mshrRun mshrInit (is.take t)
    ⟨mshrOutValid s, (is.getD t mshrInIdle).outReady, ⟨mshrOutTag s, mshrOutData s⟩⟩

/-- 回撤 witness 输入序列：
    拍 0：分配 entry0（mask=3）；拍 1：响应补齐（cm[0]==rspMask=3）且 ready=1
          → :53 快速通道，拍 2 进 s_out；
    拍 2：valid=1，但 ready 掉落为 0 → 未 fire，:62 otherwise 回 s_idle；
    拍 3：state=s_idle → valid=0。 -/
def mshrTrWAlloc : MshrIn := ⟨true, mshrTagT1, false, 0, fun _ => 0, 0, false⟩
def mshrTrWRsp : MshrIn := ⟨false, mshrTagDefault, true, 0#3, fun _ => 0, 0x00000003#32, true⟩
def mshrTrWDrop : MshrIn := ⟨false, mshrTagDefault, false, 0, fun _ => 0, 0, false⟩

def mshrTrWithdraw : List MshrIn := [mshrTrWAlloc, mshrTrWRsp, mshrTrWDrop, mshrInIdle]

/-- witness 数值判收：拍 2 valid=1/ready=0/未 fire，拍 3 valid=0。 -/
theorem mshrT_withdraw_witness :
    (mshrTraceOf mshrTrWithdraw 2).valid = true ∧
    (mshrTraceOf mshrTrWithdraw 2).ready = false ∧
    (mshrTraceOf mshrTrWithdraw 2).fires = false ∧
    (mshrTraceOf mshrTrWithdraw 3).valid = false := by
  native_decide

/-- Q1 结论：MSHRv2 的 to_pipe 通道不满足 Handshake.NoWithdraw
    （Decoupled 不允许 valid 在未 fire 时撤高）。 -/
theorem mshr_noWithdraw_violated :
    ¬ Ventus.Base.Handshake.NoWithdraw (mshrTraceOf mshrTrWithdraw) := by
  intro h
  have h2v : (mshrTraceOf mshrTrWithdraw 2).valid = true := by native_decide
  have h2r : (mshrTraceOf mshrTrWithdraw 2).ready = false := by native_decide
  have h3v : (mshrTraceOf mshrTrWithdraw 3).valid = false := by native_decide
  have hcon := h 2 h2v h2r
  rw [h3v] at hcon
  exact Bool.noConfusion hcon

/- ---- 公理审计（native_decide 定理含 Lean.ofReduceBool，属预期） ---- -/

#print axioms mshrPriEnc_bit
#print axioms mshr_out_entry_needs_ready
#print axioms mshr_withdraw
#print axioms mshr_sadd_alloc_consistent
#print axioms mshr_addrFire_entry_free
#print axioms mshr_outFire_entry_cleared
#print axioms mshr_fastpath_complete_next
#print axioms mshr_noWithdraw_violated

end Ventus.Mem
