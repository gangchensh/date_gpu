/- ========================================================================= -/
/-                        Mem/LSU.lean                                       -/
/-  访存单元（LSU.scala 全文）的 Lean 4 模型、测试与证明                        -/
/-  namespace Ventus.Mem；全部辅助定义带 lsu 前缀。                            -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/LSU.scala           -/
/-      :20-93   Bundle 定义（toShared/DCachePerLaneAddr/DCacheCoreReq_np/    -/
/-               DCacheCoreRsp_np/ShareMem*/MshrTag）                          -/
/-      :95-112  object ByteExtract（按 wordOffset1H 抽字节/半字，本地建模）   -/
/-      :113-489 class AddrCalculate（地址计算 + 调度 FSM，本文件核心）        -/
/-      :490-529 class LSU2WB（LSU→写回级组合桥）                              -/
/-      :530-586 class LSUexe（顶层组装；建模范围见 D8）                       -/
/-      :587-604 class ShiftBoard（每 warp 在飞事务计数移位寄存器）            -/
/-  例化点（活代码判定）：pipe.scala:79 `lsu=Module(new LSUexe)`、:83 LSU2WB； -/
/-    flush_dcache 接 warp_sche（pipe.scala:169-171）。ShiftBoard 在           -/
/-    LSUexe:572 被例化 num_warp=8 份（活代码）。                              -/
/-  参数（top/parameters.scala，已核实）：num_thread=32(:9) num_warp=8(:8)     -/
/-    xLen=32(:47) depth_warp=3(:30) regidx_width+regext_width=8(:23,25)       -/
/-    lsu_num_entry_each_warp=4(:67) lsu_nMshrEntry=8→instrId 3 位(:69)        -/
/-    dcache_NSets=256→SetIdxBits=8(:71,78) dcache_BlockWords=32→              -/
/-    BlockOffsetBits=5(:75,84) BytesOfWord=4(:80) TagBits=32-8-5-2=17(:86)    -/
/-    LDS_BASE=0x70000000(:136) sharemem_size=1024*32*4=131072(:93-97)         -/
/-    MMU_ENABLED=false(:15) SPIKE_OUTPUT=true(:11，仅调试输出)                -/
/-  译码常量（DecodeUnit.scala:54-60,62-83,149-150；IDecodeLUT_A :456-466）：  -/
/-    MEM_X=0 MEM_H=1 MEM_B=2 MEM_W=3；M_X=0 M_XRD=1 M_XWR=2；                 -/
/-    FN_ADD=0 FN_XOR=4 FN_OR=6 FN_AND=7 FN_MAX=16 FN_MIN=17 FN_MAXU=18        -/
/-    FN_MINU=19 FN_SWAP=28 FN_AMOADD=29。                                     -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 参数固定为上列值；AddrCalculate 的 sharedmemory_maxsize 建模为显式     -/
/-      参数 smax（:113 默认 4096 无例化使用，唯一例化 LSUexe:548/554 传       -/
/-      sharemem_size=131072=0x20000）。                                       -/
/-  D2. MMU_ENABLED=false → DCacheCoreReq_np.asid 不存在，不建模。             -/
/-      SPIKE_OUTPUT=true 但 spike_info/pc/inst 仅用于 printf 与透传，不建模。 -/
/-  D3. CtrlSigs（scoreboard.scala:19-65）只保留 LSU 行为相关 16 字段：        -/
/-      wid/reg_idxw/mem_cmd/mop/mem_whb/alu_fn/isvec/disable_mask/is_vls12/   -/
/-      mem_unsigned/atomic/aq/rl/fence/wxd/wvd。其余字段（pc/inst/reg_idx1-3/ -/
/-      sel_*/branch/csr/...）不影响 LSU 数据通路行为，省略。                  -/
/-  D4. 地址算术全程模 2^32（BitVec 32）：Chisel 中间结果有更宽位（如 :150     -/
/-      vls12 路径的 *csr_numw 为 64 位、<<5 为 69 位），但最终赋给            -/
/-      UInt(xLen.W) 截断低 32 位；mod 2^32 下截断与加/乘/移位可交换，故       -/
/-      直接以 32 位运算建模，语义一致。                                       -/
/-  D5. blockOffset 字段宽 5（DCachePerLaneAddr:33）而 :178 赋值为             -/
/-      addr(x)(10,2)（9 位）：FIRRTL connect 对宽 RHS 截断（Chisel 6.4.0，    -/
/-      build.sc:31-35）→ 实际值 = addr(6,2)。模型取 addr(6,2)。见 Q3。        -/
/-  D6. param_wire_alt（:241-243）的 FN_SWAP 分支为 16.U（5 位）截断进 4 位    -/
/-      → 0；模型直接取 0#4。见 Q4。                                           -/
/-  D7. MSHRv2（pipeline/MSHR.scala）由姊妹子代理建模（Ventus/Mem/MSHR.lean，  -/
/-      本文件不 import、不依赖）。LSU.scala:95-112 的 ByteExtract 与 :82-93    -/
/-      的 MshrTag 在本文件自建本地版本（lsu 前缀）。                          -/
/-  D8. LSUexe（:530-586）不做全组合建模：InputFIFO（:551，Queue 1 pipe）、    -/
/-      rspArbiter（:560，chisel Arbiter n=2）与 MSHRv2（:565）的组合留待与    -/
/-      MSHR 模型集成。本文件建模 LSUexe 内属于本模块的部分：ShiftBoard 阵列   -/
/-      （:572-577）、lsu_req 的 full 门控（:578-579）、fence_end（:577）。    -/
/-  D9. cnt = Counter(32)（:129）→ BitVec 5，inc 在 31 回绕（与 5 位 +1 截断   -/
/-      一致）；`cnt.value >= num_thread.U`（:314,332,349,360）恒假，见 Q2    -/
/-      与定理 lsuCntDone_false。                                              -/
/-  D10. 三个 switch(state)（:291/:369/:406）均无 otherwise：state ∈ {6,7}     -/
/-      （3 位编码的非法态）时全部寄存器保持；模型 else 分支 = 保持。          -/
/-  D11. 上电初值：state=s_idle(RegInit :130)、is_flush=false(:133)、          -/
/-      reg_entryID=0(:138)、cnt=0（Counter 内置 RegInit）；reg_save（:132）   -/
/-      无 RegInit，建模为全 0，本文件定理均不依赖其初值。                     -/
/-  D12. ByteExtract 的 Mux 条件 `!in(k)||isUInt`（:101-106）选符号扩展分支时 -/
/-      该 slice 符号位必为 1，故 Cat(全 1, slice) ≡ signExtend slice；模型    -/
/-      用 signExtend，位级等价由定理 lsuBex_* 钉死。                          -/
/-  D13. mask 用 `Fin 32 → Bool` 逐 lane 谓词表示（对应 Vec(num_thread,       -/
/-      Bool())）；asUInt.andR/orR 用 List.finRange 的 all/any；优先编码器     -/
/-      用 List.find? 建模并附规格引理（lsuPrioEncF_spec*）。                   -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类·设计假设】shared/global 混合向量访存错路由：all_shared 为         -/
/-      andR（:164-167），任一活动 lane 落在 LDS 区间外即整笔送 DCache；落在   -/
/-      LDS 区间的 lane 会以 LDS 地址（0x70000000+）进 L1D 当全局地址处理 →    -/
/-      错地址空间读写。触发需程序生成混合地址（ABI 一般禁止），记设计假设。   -/
/-  Q2【I 类·死硬件】cnt（:129）的唯一用途 `cnt.value >= num_thread.U`         -/
/-      （:314,332,349,360）恒假：Counter(32) 值域 0..31（5 位），num_thread   -/
/-      =32 为 6 位字面量，零扩展比较恒假 → 终止条件只剩 mask_next==0；cnt     -/
/-      的 inc/reset 无任何可观察效果。机证 lsuCntDone_false。                 -/
/-  Q3【I 类·代码误导】blockOffset(x) := addr(x)(10,2)（:177-178）：9 位表达   -/
/-      式截断进 5 位字段，实际为 addr(6,2)（128B 块的正确字偏移）。功能正确   -/
/-      但字面误导，维护风险。                                                 -/
/-  Q4【I 类·截断巧合】param_wire_alt 的 FN_SWAP 分支 16.U（:241）截断进 4     -/
/-      位 param 得 0；TileLink SWAP 的 param 恰为 0，结果正确但依赖截断。     -/
/-  Q5【I 类·候选，条件触发，重点】LDS 高位地址别名：to_shared.setIdx 只有     -/
/-      dcache_SetIdxBits=8 位（addr(14,7)，:71,:171,:216），而 SharedMemory   -/
/-      的 NSets=sharedmem_depth=1024 需 10 位 setIdx                          -/
/-      （ShareMem/ShareMemParameters.scala:22, L1Cache/L1CacheParameters.     -/
/-      scala:43），GPGPU_top.scala:488 直接对接（8→10 零扩展）→ 地址位        -/
/-      addr(16:15) 被丢弃：LDS 偏移 ≥ 32KB（sharemem_size=128KB 的高 3/4      -/
/-      区域）与低 32KB 逐字节别名互踩。is_shared 判界（:162）用 smax=128KB     -/
/-      放行高区地址；分组（tag=addr(31,15)）会把不同 32KB 页的地址拆成不同    -/
/-      请求，但每拍请求携带的 8 位 setIdx 相同 → 静默写坏低区数据。触发条     -/
/-      件：SM 上 LDS 用量 > 32KB（CTA 调度 NUM_LDS_MAX=128KB 允许）。建       -/
/-      议：ShareMemCoreReq_np.setIdx 加宽到 10 位并同步分组比较。             -/
/-  Q6【I 类·潜伏死锁，需译码配合】LSU2WB :520：¬wxd ∧ ¬wfd 时                 -/
/-      lsu_rsp.ready = isWrite；若出现 wxd=wfd=isWrite=0 的畸形 tag，该响应   -/
/-      永不 ready → MSHR 条目永不释放 → 8 项耗尽后 AddrCalculate 卡 s_save    -/
/-      → LSU 全局阻塞。正常译码不可达（LW 置 wxd、VLE 置 wvd、store 的        -/
/-      isWrite=mem_cmd(1)=1）。                                               -/
/-  Q7【I 类·死逻辑】opcode_wire 的 fence 分支（:259-261）不可达：fence=1 的   -/
/-      指令 mem_cmd=M_X=0（DecodeUnit.scala:190）→ s_save 直接回 s_idle       -/
/-      （:310），不进任何 s_dcache 态。FENCE 实际靠 fence_end/ShiftBoard 排   -/
/-      空实现（scoreboard.scala:119-120）。                                   -/
/-  Q8【I 类·候选·低危】flush 请求携带残留 reg_entryID（:227 不区分 flush）； -/
/-      DCache 对 flush/invalidate 会回 coreRsp（DCache.scala:504,517          -/
/-      hasCoreRsp=true）→ MSHR 收到 instrId=残留条目的伪响应。缓解事实：      -/
/-      flush 接受拍 reg_save 清零（:372-373）→ 请求 activeMask 全 0 → 响应    -/
/-      activeMask 全 0 → MSHR 的 data.write 全掩蔽、currentMask 按位与全 1    -/
/-      恒等（MSHR.scala:70-71）。仅剩 MSHR 状态机被 from_dcache.fire 推一     -/
/-      拍的可能（:53-54 需 currentMask(残留)===0 才进 s_out，且 valid 仍由     -/
/-      complete.orR 控制）。危害≈0，但依赖"flush 与在飞事务不并发"（flush 由  -/
/-      warp_schedule.scala:169-173 在整 wg endprg 后发出；多 wg 并发时其他     -/
/-      wg 的在飞事务可与 flush 并存——靠 activeMask 全 0 兜底）。             -/
/-  Q9【观察】mem_cmd=0 的数据进 LSU：s_save→s_idle（:310）无 MSHR 分配、无     -/
/-      写回；上游 issue 只在 ctrl.mem=1 时送 LSU（issue.scala:114-117，        -/
/-      DecodeUnit.scala:597 mem=mem_cmd.orR）→ 不可达。                       -/
/-  Q10【观察】s_idle 空转拍 reg_save 清零（:382）→ csr_wid 输出为 0（:134）； -/
/-      消费侧为组合选择，无锁存风险。                                         -/
/-  Q11【观察】共享存储路径无 atomic 特判：atomic && all_shared → s_shared，   -/
/-      但 ShareMemCoreReq_np 无 opcode 字段，原子操作退化为普通读写；且        -/
/-      mask_next（:285-287）在 s_shared 也按 atomic 形式每拍只清优先 lane。   -/
/-      AMO 到 LDS 属编程错误；记录。                                         -/
/-  Q12【观察】lsu_req 的 full 门控（:578-579）用 ShiftBoard 的寄存器输出       -/
/-      taps(3)；同拍响应到达（right_move）不能解除当拍阻塞——保守、安全。      -/
/-  Q13【MSHR valid 回撤的下游影响结论（回答主会话问题）】MSHRv2.scala:106      -/
/-      `to_pipe.valid = complete.orR && state===s_out`、:62 显示 s_out 中      -/
/-      ready 掉落即退回 s_idle → valid 可回撤，违反 Decoupled 的              -/
/-      NoWithdraw（非 Irrevocable 源）。下游链全程"同拍 valid&&ready 才消费"： -/
/-      LSU2WB 纯组合透传（LSU.scala:509-520，ready=out_x/out_v.ready 或       -/
/-      isWrite）→ writeback 的 0 深 Queue（writeback.scala:52-59）→           -/
/-      count=1 的 chisel Arbiter（:60-61，无跨拍锁定，当拍组合优先级）→       -/
/-      operandCollector 的 writeScalarCtrl/writeVecCtrl ready 恒 1            -/
/-      （operandCollector.scala:623-624）；寄存器堆写使能 rdwen 在 wb.io.out   -/
/-      层取 valid（:621），该层 valid⇔fire。MSHR 侧 used 仅在 to_pipe.fire    -/
/-      时释放（MSHR.scala:94），complete 保持 → 回撤后 s_idle 可再进 s_out     -/
/-      （:56）重发同一条目，数据/标签不变。结论：现集成下不丢不重；LSU 侧     -/
/-      定理 lsu2wb_rspFire_iff 钉死"只在 fire 消费"。风险仅在未来插入非透     -/
/-      明寄存器级或按 valid 采样的消费者。                                   -/
/-  Q14【I 类·语义审查点】AMO 的 32 次执行：AMO 系指令（IDecodeLUT_A            -/
/-      DecodeUnit.scala:456-466）isvec=N → 接受拍 mask 强制全 1（:381）→       -/
/-      atomic 路径每拍只发优先 lane（:275）、每拍只清一 lane（:286）→          -/
/-      一条标量 AMO 实际向同一地址（in1(0)+in2(0)，标量指令 in1/in2 为广播）   -/
/-      发起 32 次原子操作（aaq 被 :376-379 强制 → 每 lane 还带 2-3 拍的        -/
/-      aq/rl fence 拆分）。若软件语义是"32 个线程各做一次同地址 AMO"则行为     -/
/-      正确（写回 data(0)=第一次旧值，wxd 标量）；若期望整 warp 一次，则       -/
/-      操作数被放大 32 倍。另：吞吐 64-96 拍/条。需 ISA 语义裁定，记审查点。   -/
/-  Q15【I 类·候选·低危】AMO aq/rl 拆分中 opcode=3（L1D flush/invalidate，      -/
/-      L1Interfaces.scala:37）的请求也产生 coreRsp（DCache.scala:504,517），   -/
/-      且其 activeMask = 当拍 AMO 的优先 lane（:272-279 不区分 flush 拍）→     -/
/-      MSHR 会把该响应数据写入对应 lane（MSHR.scala:70）。注意 :376-379 对      -/
/-      atomic 强制 aq=true，故可达序列只有 [3,2]（aq）与 [3,2,3]（aq&&rl）；   -/
/-      后者尾部的 release-invalidate 响应晚于同 lane 的 AMO 响应，若其 data    -/
/-      非旧值且按序覆盖 MSHR 该 lane → 写回数据被尾部 flush 响应污染。是否     -/
/-      成害取决于 L1D 对 invalidate 的 coreRsp 数据内容与响应保序，超出本文    -/
/-      件范围，上报待 L1D 波次核实。                                         -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Mem

set_option linter.unusedVariables false
-- FSM 定理的 simp 参数表按全部六个状态分支统一给出，单分支会留 unused 参数
set_option linter.unusedSimpArgs false

/- ========================================================================= -/
/- 1. 常量                                                                   -/
/- =========================================================================-/

/-- FSM 状态编码（:128 `s_idle :: s_save :: s_shared :: s_dcache :: s_dcache_1
    :: s_dcache_2 :: Nil = Enum(6)`，3 位） -/
def lsuSIdle   : BitVec 3 := 0
def lsuSSave   : BitVec 3 := 1
def lsuSShared : BitVec 3 := 2
def lsuSDcache : BitVec 3 := 3
def lsuSD1     : BitVec 3 := 4
def lsuSD2     : BitVec 3 := 5

/-- mem_cmd（DecodeUnit.scala:58-60） -/
def lsuMXrd : BitVec 2 := 1
def lsuMXwr : BitVec 2 := 2

/-- mem_whb（DecodeUnit.scala:54-57） -/
def lsuMemX : BitVec 2 := 0
def lsuMemH : BitVec 2 := 1
def lsuMemB : BitVec 2 := 2
def lsuMemW : BitVec 2 := 3

/-- alu_fn 子集（DecodeUnit.scala:62-83,149-150） -/
def lsuFnAdd    : BitVec 6 := 0
def lsuFnXor    : BitVec 6 := 4
def lsuFnOr     : BitVec 6 := 6
def lsuFnAnd    : BitVec 6 := 7
def lsuFnMax    : BitVec 6 := 16
def lsuFnMin    : BitVec 6 := 17
def lsuFnMaxu   : BitVec 6 := 18
def lsuFnMinu   : BitVec 6 := 19
def lsuFnSwap   : BitVec 6 := 28
def lsuFnAmoadd : BitVec 6 := 29

/-- LDS 基址（parameters.scala:136） -/
def lsuLdsBase : BitVec 32 := 0x70000000#32

/-- LSUexe 实参 smax = sharemem_size = 131072（parameters.scala:93-97,
    LSU.scala:548） -/
def lsuSmaxDefault : BitVec 32 := 0x00020000#32

/-- 地址切片（:170-178；TagBits=17 SetIdxBits=8 BlockOffsetBits=5） -/
def lsuTagOf (a : BitVec 32) : BitVec 17 := a.extractLsb' 15 17
def lsuSetOf (a : BitVec 32) : BitVec 8 := a.extractLsb' 7 8
def lsuBlkOf (a : BitVec 32) : BitVec 5 := a.extractLsb' 2 5   -- D5：addr(6,2)

/- ========================================================================= -/
/- 2. ByteExtract（:95-112，本地模型，D7/D12）                                 -/
/-                                                                           -/
/-  语义：sel 为 wordOffset1H（4 位 one-hot/对）：                             -/
/-    0xF → 全字；0xC/0x3 → 高/低半字；0x8/0x4/0x2/0x1 → 字节 3/2/1/0；        -/
/-    其余（含 0）→ 原样（MuxCase 默认 in）。半字/字节按 isUInt 或符号位       -/
/-    选择零/符号扩展（!in(k) || isUInt → 零扩展）。                           -/
/- ========================================================================= -/

/-- ByteExtract.apply（:96-110；D12 用 signExtend 等价 Cat(全1,slice)） -/
def lsuByteExtract (isUInt : Bool) (x : BitVec 32) (sel : BitVec 4) : BitVec 32 :=
  if sel == 0xF#4 then x                                                       -- :100
  else if sel == 0xC#4 then                                                    -- :101
    (if (x >>> 31) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 16 16).zeroExtend 32
     else (x.extractLsb' 16 16).signExtend 32)
  else if sel == 0x3#4 then                                                    -- :102
    (if (x >>> 15) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 0 16).zeroExtend 32
     else (x.extractLsb' 0 16).signExtend 32)
  else if sel == 0x8#4 then                                                    -- :103
    (if (x >>> 31) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 24 8).zeroExtend 32
     else (x.extractLsb' 24 8).signExtend 32)
  else if sel == 0x4#4 then                                                    -- :104
    (if (x >>> 23) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 16 8).zeroExtend 32
     else (x.extractLsb' 16 8).signExtend 32)
  else if sel == 0x2#4 then                                                    -- :105
    (if (x >>> 15) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 8 8).zeroExtend 32
     else (x.extractLsb' 8 8).signExtend 32)
  else if sel == 0x1#4 then                                                    -- :106
    (if (x >>> 7) &&& 1#32 == 0#32 || isUInt then (x.extractLsb' 0 8).zeroExtend 32
     else (x.extractLsb' 0 8).signExtend 32)
  else x                                                                       -- MuxCase 默认

section LsuBexTests

-- 全字
example : lsuByteExtract true 0xDEADBEEF#32 0xF#4 = 0xDEADBEEF#32 := by decide
-- 半字：高半 0xDEAD（符号位 1）：无符号零扩展 / 有符号符号扩展
example : lsuByteExtract true 0xDEADBEEF#32 0xC#4 = 0x0000DEAD#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0xC#4 = 0xFFFFDEAD#32 := by decide
-- 低半 0xBEEF
example : lsuByteExtract true 0xDEADBEEF#32 0x3#4 = 0x0000BEEF#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x3#4 = 0xFFFFBEEF#32 := by decide
-- 字节：0xDE / 0xAD / 0xBE / 0xEF
example : lsuByteExtract true 0xDEADBEEF#32 0x8#4 = 0x000000DE#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x8#4 = 0xFFFFFFDE#32 := by decide
example : lsuByteExtract true 0xDEADBEEF#32 0x4#4 = 0x000000AD#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x4#4 = 0xFFFFFFAD#32 := by decide
example : lsuByteExtract true 0xDEADBEEF#32 0x2#4 = 0x000000BE#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x2#4 = 0xFFFFFFBE#32 := by decide
example : lsuByteExtract true 0xDEADBEEF#32 0x1#4 = 0x000000EF#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x1#4 = 0xFFFFFFEF#32 := by decide
-- 符号位为 0 时有符号也是零扩展
example : lsuByteExtract false 0x7EAD0EEF#32 0xC#4 = 0x00007EAD#32 := by decide
example : lsuByteExtract false 0xDEAD0EEF#32 0x3#4 = 0x00000EEF#32 := by decide
example : lsuByteExtract false 0xDEADBE6F#32 0x1#4 = 0x0000006F#32 := by decide
-- 默认分支（含 sel=0）
example : lsuByteExtract true 0xDEADBEEF#32 0x0#4 = 0xDEADBEEF#32 := by decide
example : lsuByteExtract false 0xDEADBEEF#32 0x5#4 = 0xDEADBEEF#32 := by decide
example : lsuByteExtract true 0xDEADBEEF#32 0x9#4 = 0xDEADBEEF#32 := by decide

end LsuBexTests

/- ---- ByteExtract 位级规约（bv_decide） ---- -/

/-- 全字恒等 -/
theorem lsuBex_word (u : Bool) (x : BitVec 32) : lsuByteExtract u x 0xF#4 = x := rfl

/-- 字节选择（RISC-V LB/LBU 语义）：sel = 1 <<< j（j ∈ 0..3）抽字节 j，
    按 u 或符号位零/符号扩展。 -/
theorem lsuBex_byte (u : Bool) (x : BitVec 32) (j : BitVec 2) :
    lsuByteExtract u x (1#4 <<< j.zeroExtend 4) =
      (if u || ((x >>> (j.zeroExtend 32 * 8 + 7)) &&& 1#32) == 0#32
       then ((x >>> (j.zeroExtend 32 * 8)).extractLsb' 0 8).zeroExtend 32
       else ((x >>> (j.zeroExtend 32 * 8)).extractLsb' 0 8).signExtend 32) := by
  simp only [lsuByteExtract]; bv_decide

/-- 半字选择（RISC-V LH/LHU 语义）：sel = 3 <<< (2h)（h=0 → 0x3 低半，
    h=1 → 0xC 高半）。 -/
theorem lsuBex_half (u : Bool) (x : BitVec 32) (h : BitVec 1) :
    lsuByteExtract u x (3#4 <<< (h.zeroExtend 4 + h.zeroExtend 4)) =
      (if u || ((x >>> (h.zeroExtend 32 * 16 + 15)) &&& 1#32) == 0#32
       then ((x >>> (h.zeroExtend 32 * 16)).extractLsb' 0 16).zeroExtend 32
       else ((x >>> (h.zeroExtend 32 * 16)).extractLsb' 0 16).signExtend 32) := by
  simp only [lsuByteExtract]; bv_decide

/-- 非表内 sel（MuxCase 默认）→ 原样返回。 -/
theorem lsuBex_default (u : Bool) (x : BitVec 32) (sel : BitVec 4)
    (h1 : sel ≠ 0xF#4) (h2 : sel ≠ 0xC#4) (h3 : sel ≠ 0x3#4) (h4 : sel ≠ 0x8#4)
    (h5 : sel ≠ 0x4#4) (h6 : sel ≠ 0x2#4) (h7 : sel ≠ 0x1#4) :
    lsuByteExtract u x sel = x := by
  simp only [lsuByteExtract]; bv_decide

/-- 无符号时恒为零扩展（截断）：结果高 24 位以上的内容只由选中 slice 决定；
    具体地，无符号字节/半字抽取恒零扩展。 -/
theorem lsuBex_unsigned_byte (x : BitVec 32) (j : BitVec 2) :
    lsuByteExtract true x (1#4 <<< j.zeroExtend 4) =
      ((x >>> (j.zeroExtend 32 * 8)).extractLsb' 0 8).zeroExtend 32 := by
  simp only [lsuByteExtract]; bv_decide

/- ========================================================================= -/
/- 3. AddrCalculate 模型（:113-489）                                          -/
/- ========================================================================= -/

/-- 32 lane 的 32 位数据行（Vec(num_thread, UInt(xLen.W))） -/
abbrev LsuRow : Type := Fin 32 → BitVec 32

/-- 逐 lane 布尔（Vec(num_thread, Bool())，D13） -/
abbrev LsuMask32 : Type := Fin 32 → Bool

/-- CtrlSigs 的 LSU 行为切片（D3） -/
structure LsuCtrl where
  wid          : BitVec 3
  reg_idxw     : BitVec 8
  mem_cmd      : BitVec 2
  mop          : BitVec 2
  mem_whb      : BitVec 2
  alu_fn       : BitVec 6
  isvec        : Bool
  disable_mask : Bool
  is_vls12     : Bool
  mem_unsigned : Bool
  atomic       : Bool
  aq           : Bool
  rl           : Bool
  fence        : Bool
  wxd          : Bool
  wvd          : Bool
deriving DecidableEq

def lsuCtrl0 : LsuCtrl :=
  ⟨0, 0, 0, 0, 0, 0, false, false, false, false, false, false, false, false,
   false, false⟩

/-- vExeData（issue.scala:17-23，D2/D3 后的切片） -/
structure LsuVExe where
  in1  : LsuRow
  in2  : LsuRow
  in3  : LsuRow
  mask : LsuMask32
  ctrl : LsuCtrl

def lsuVExe0 : LsuVExe := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => false, lsuCtrl0⟩

/-- MshrTag（:82-93；wordOffset1H 逐 lane 4 位） -/
structure LsuMshrTag where
  warp_id      : BitVec 3
  wfd          : Bool
  wxd          : Bool
  reg_idxw     : BitVec 8
  mask         : LsuMask32
  unsigned     : Bool
  isvec        : Bool
  wordOffset1H : Fin 32 → BitVec 4
  isWrite      : Bool

/-- DCacheCoreReq_np（:37-48，D2：无 asid/spike_info） -/
structure LsuDcacheReq where
  instrId    : BitVec 3
  tag        : BitVec 17
  setIdx     : BitVec 8
  blkOff     : Fin 32 → BitVec 5   -- perLaneAddr.blockOffset
  word1H     : Fin 32 → BitVec 4   -- perLaneAddr.wordOffset1H
  active     : LsuMask32           -- perLaneAddr.activeMask
  data       : LsuRow
  opcode     : BitVec 3
  param      : BitVec 4

/-- ShareMemCoreReq_np（:66-74） -/
structure LsuSharedReq where
  instrId : BitVec 3
  isWrite : Bool
  setIdx  : BitVec 8
  blkOff  : Fin 32 → BitVec 5
  word1H  : Fin 32 → BitVec 4
  active  : LsuMask32
  data    : LsuRow

/-- AddrCalculate 状态（:128-138） -/
structure LsuState where
  state   : BitVec 3      -- :130 RegInit(s_idle)
  cnt     : BitVec 5      -- :129 Counter(32)，D9
  regSave : LsuVExe       -- :132（无 RegInit，D11 建模为全 0）
  isFlush : Bool          -- :133 RegInit(false)
  entryID : BitVec 3      -- :138 RegInit(0)

def lsuInit : LsuState := ⟨lsuSIdle, 0, lsuVExe0, false, 0⟩

/-- 单拍输入 -/
structure LsuIn where
  fifoValid   : Bool        -- from_fifo.valid
  fifoBits    : LsuVExe     -- from_fifo.bits
  flushValid  : Bool        -- flush_dcache.valid（bits 未被使用）
  mshrReady   : Bool        -- to_mshr.ready
  idxEntry    : BitVec 3    -- idx_entry（:123）
  dcacheReady : Bool        -- to_dcache.ready
  sharedReady : Bool        -- to_shared.ready
  csrTid      : BitVec 32   -- csr_tid（:119）
  csrPds      : BitVec 32   -- csr_pds（:117）
  csrNumw     : BitVec 32   -- csr_numw（:118）

/- ---- 3.1 组合逻辑（:140-287） ---- -/

/-- 逐 lane 地址（:146-161，D4 模 2^32） -/
def lsuLaneAddr (v : LsuVExe) (tid pds numw : BitVec 32) (x : Fin 32) : BitVec 32 :=
  let c := v.ctrl
  let xw : BitVec 32 := BitVec.ofNat 32 x.val
  if c.isvec && c.disable_mask then                                          -- :147
    if c.is_vls12 then v.in1 x + v.in2 x                                     -- :149
    else                                                                     -- :150
      let s := v.in1 x + v.in2 x
      (s.extractLsb' 0 2).zeroExtend 32
        + ((tid + xw) <<< 2)
        + pds
        + ((((s.extractLsb' 2 30).zeroExtend 32 <<< 2) * numw) <<< 5)
  else if c.isvec then                                                       -- :152
    v.in1 x +
      (if c.mop == 0#2 then xw <<< 2                                         -- :153-154 unit stride
       else if c.mop == 3#2 then v.in2 x                                     -- :155-156 gather
       else xw * v.in2 x)                                                    -- :157 strided
  else v.in1 ⟨0, by decide⟩ + v.in2 ⟨0, by decide⟩                           -- :159 scalar

/-- is_shared(x)（:162）：掩蔽 lane 视同 shared；判界 [LDS_BASE, LDS_BASE+smax) -/
def lsuLaneIsShared (smax : BitVec 32) (v : LsuVExe) (tid pds numw : BitVec 32)
    (x : Fin 32) : Bool :=
  !(v.mask x) ||
    (decide (lsuLdsBase ≤ lsuLaneAddr v tid pds numw x) &&
     decide (lsuLaneAddr v tid pds numw x < lsuLdsBase + smax))

/-- all_shared（:164-167） -/
def lsuAllShared (smax : BitVec 32) (v : LsuVExe) (tid pds numw : BitVec 32) : Bool :=
  if v.ctrl.isvec then
    (List.finRange 32).all (fun x => lsuLaneIsShared smax v tid pds numw x)
  else lsuLaneIsShared smax v tid pds numw ⟨0, by decide⟩

/-- mask.asUInt ≠ 0（:170-171, :204 等） -/
def lsuMaskNez (m : LsuMask32) : Bool := (List.finRange 32).any (fun x => m x)

/-- PriorityEncoder(mask.asUInt)：最低置位 lane 的编号；全 0 时取 0（D13） -/
def lsuPrioEncF (m : LsuMask32) : Fin 32 :=
  ((List.finRange 32).find? (fun x => m x)).getD ⟨0, by decide⟩

/-- addr_wire（:168-169） -/
def lsuAddrWire (v : LsuVExe) (tid pds numw : BitVec 32) : BitVec 32 :=
  lsuLaneAddr v tid pds numw (lsuPrioEncF v.mask)

/-- tag（:170） -/
def lsuTagW (v : LsuVExe) (tid pds numw : BitVec 32) : BitVec 17 :=
  if lsuMaskNez v.mask then lsuTagOf (lsuAddrWire v tid pds numw) else 0#17

/-- setIdx（:171） -/
def lsuSetW (v : LsuVExe) (tid pds numw : BitVec 32) : BitVec 8 :=
  if lsuMaskNez v.mask then lsuSetOf (lsuAddrWire v tid pds numw) else 0#8

/-- wordOffset1H(x)（:180-193）：默认 15；MEM_H 按 addr(1) 选半字对；
    MEM_B 为 1 <<< addr(1,0) -/
def lsuWordOff1H (whb : BitVec 2) (a : BitVec 32) : BitVec 4 :=
  if whb == lsuMemW then 15#4
  else if whb == lsuMemH then (if (a >>> 1) &&& 1#32 == 0#32 then 3#4 else 12#4)
  else if whb == lsuMemB then 1#4 <<< (a.extractLsb' 0 2).zeroExtend 4
  else 15#4

/-- dcache 侧 activeMask(x)（:275-277）：atomic 只发优先 lane；
    否则按 (tag,setIdx) 同组 -/
def lsuDcActive (v : LsuVExe) (tid pds numw : BitVec 32) (x : Fin 32) : Bool :=
  if v.ctrl.atomic then
    v.mask x && (x == lsuPrioEncF v.mask)
  else
    v.mask x &&
      (lsuTagOf (lsuLaneAddr v tid pds numw x) == lsuTagW v tid pds numw) &&
      (lsuSetOf (lsuLaneAddr v tid pds numw x) == lsuSetW v tid pds numw)

/-- shared 侧 activeMask(x)（:220，无 atomic 特判） -/
def lsuShActive (v : LsuVExe) (tid pds numw : BitVec 32) (x : Fin 32) : Bool :=
  v.mask x &&
    (lsuTagOf (lsuLaneAddr v tid pds numw x) == lsuTagW v tid pds numw) &&
    (lsuSetOf (lsuLaneAddr v tid pds numw x) == lsuSetW v tid pds numw)

/-- mask_next(x)（:285-287）：atomic 清优先 lane；否则清同组 lane -/
def lsuMaskNext (v : LsuVExe) (tid pds numw : BitVec 32) (x : Fin 32) : Bool :=
  if v.ctrl.atomic then
    v.mask x && !(x == lsuPrioEncF v.mask)
  else
    v.mask x &&
      !((lsuTagOf (lsuLaneAddr v tid pds numw x) == lsuTagW v tid pds numw) &&
        (lsuSetOf (lsuLaneAddr v tid pds numw x) == lsuSetW v tid pds numw))

/-- param_wire_alt（:241-243，D6：FN_SWAP 的 16.U 截断为 0） -/
def lsuParamAlt (aluFn : BitVec 6) : BitVec 4 :=
  if aluFn == lsuFnSwap then 0#4        -- :241 16.U 截断（Q4）
  else if aluFn == lsuFnAmoadd then 0#4
  else if aluFn == lsuFnXor then 1#4
  else if aluFn == lsuFnAnd then 3#4
  else if aluFn == lsuFnOr then 2#4
  else if aluFn == lsuFnMin then 4#4
  else if aluFn == lsuFnMax then 5#4
  else if aluFn == lsuFnMinu then 6#4
  else if aluFn == lsuFnMaxu then 7#4
  else 1#4

/-- mem_cmd(1)（isWrite 位） -/
def lsuMemCmdWr (memCmd : BitVec 2) : Bool := ((memCmd >>> 1) &&& 1#2) == 1#2

/-- opcode_wire/param_wire（:239-270）；至多在 s_dcache/s_dcache_1/s_dcache_2
    被消费（:282） -/
def lsuOpcodeParam (c : LsuCtrl) (isFlush : Bool) (st : BitVec 3) : BitVec 3 × BitVec 4 :=
  if c.atomic then                                                          -- :245
    if c.aq && c.rl then                                                    -- :246
      (if st == lsuSD2 then 3#3 else if st == lsuSD1 then 2#3 else 3#3,     -- :247
       if st == lsuSD2 then 0#4 else if st == lsuSD1 then lsuParamAlt c.alu_fn else 0#4) -- :248
    else if c.aq then                                                       -- :249
      (if st == lsuSD1 then 2#3 else 3#3,                                   -- :250
       if st == lsuSD1 then lsuParamAlt c.alu_fn else 0#4)                  -- :251
    else if c.rl then                                                       -- :252
      (if st == lsuSD1 then 3#3 else 2#3,                                   -- :253
       if st == lsuSD1 then 0#4 else lsuParamAlt c.alu_fn)                  -- :254
    else                                                                    -- :255
      (if c.alu_fn == lsuFnAdd then (BitVec.zeroExtend 3 (c.mem_cmd.extractLsb' 1 1))
       else 2#3,                                                            -- :256
       lsuParamAlt c.alu_fn)                                                -- :257
  else if c.fence then (3#3, 0#4)                                           -- :259-261（Q7：不可达）
  else if isFlush then (3#3, 0#4)                                           -- :262-264
  else (BitVec.zeroExtend 3 (c.mem_cmd.extractLsb' 1 1), 0#4)               -- :265-268

/- ---- 3.2 握手信号与输出（:134-138, 196-282） ---- -/

def lsuFifoRdy (s : LsuState) (i : LsuIn) : Bool :=                         -- :136
  (s.state == lsuSIdle) && !i.flushValid
def lsuFifoFire (s : LsuState) (i : LsuIn) : Bool := i.fifoValid && lsuFifoRdy s i
def lsuFlushRdy (s : LsuState) : Bool := s.state == lsuSIdle                -- :137
def lsuFlushFire (s : LsuState) (i : LsuIn) : Bool := i.flushValid && lsuFlushRdy s
def lsuMshrValid (s : LsuState) : Bool :=                                   -- :204
  (s.state == lsuSSave) && (s.regSave.ctrl.mem_cmd != 0#2)
def lsuMshrFire (s : LsuState) (i : LsuIn) : Bool := lsuMshrValid s && i.mshrReady
def lsuSharedValid (s : LsuState) : Bool := s.state == lsuSShared           -- :224
def lsuSharedFire (s : LsuState) (i : LsuIn) : Bool := lsuSharedValid s && i.sharedReady
def lsuDcacheValid (s : LsuState) : Bool :=                                 -- :282
  (s.state == lsuSDcache) || (s.state == lsuSD1) || (s.state == lsuSD2)
def lsuDcacheFire (s : LsuState) (i : LsuIn) : Bool := lsuDcacheValid s && i.dcacheReady

/-- to_mshr.bits.tag（:196-205） -/
def lsuMshrTagBits (v : LsuVExe) (tid pds numw : BitVec 32) : LsuMshrTag :=
  { warp_id      := v.ctrl.wid
  , wfd          := v.ctrl.wvd                                              -- :200
  , wxd          := v.ctrl.wxd
  , reg_idxw     := v.ctrl.reg_idxw
  , mask         := v.mask
  , unsigned     := v.ctrl.mem_unsigned
  , isvec        := v.ctrl.isvec
  , wordOffset1H := fun x => lsuWordOff1H v.ctrl.mem_whb (lsuLaneAddr v tid pds numw x)
  , isWrite      := lsuMemCmdWr v.ctrl.mem_cmd }                            -- :205

/-- to_shared.bits（:213-223） -/
def lsuSharedBits (s : LsuState) (i : LsuIn) : LsuSharedReq :=
  let v := s.regSave
  { instrId := s.entryID
  , isWrite := lsuMemCmdWr v.ctrl.mem_cmd
  , setIdx  := lsuSetW v i.csrTid i.csrPds i.csrNumw
  , blkOff  := fun x => lsuBlkOf (lsuLaneAddr v i.csrTid i.csrPds i.csrNumw x)
  , word1H  := fun x => lsuWordOff1H v.ctrl.mem_whb (lsuLaneAddr v i.csrTid i.csrPds i.csrNumw x)
  , active  := fun x => lsuShActive v i.csrTid i.csrPds i.csrNumw x
  , data    := v.in3 }

/-- to_dcache.bits（:227-282） -/
def lsuDcacheBits (s : LsuState) (i : LsuIn) : LsuDcacheReq :=
  let v := s.regSave
  let op := lsuOpcodeParam v.ctrl s.isFlush s.state
  { instrId := s.entryID
  , tag     := lsuTagW v i.csrTid i.csrPds i.csrNumw
  , setIdx  := lsuSetW v i.csrTid i.csrPds i.csrNumw
  , blkOff  := fun x => lsuBlkOf (lsuLaneAddr v i.csrTid i.csrPds i.csrNumw x)
  , word1H  := fun x => lsuWordOff1H v.ctrl.mem_whb (lsuLaneAddr v i.csrTid i.csrPds i.csrNumw x)
  , active  := fun x => lsuDcActive v i.csrTid i.csrPds i.csrNumw x
  , data    := v.in3
  , opcode  := op.1
  , param   := op.2 }

/-- 全部输出（csr_wid 见 :134） -/
structure LsuOut where
  fifoRdy     : Bool
  flushRdy    : Bool
  mshrValid   : Bool
  mshrTag     : LsuMshrTag
  sharedValid : Bool
  sharedBits  : LsuSharedReq
  dcacheValid : Bool
  dcacheBits  : LsuDcacheReq
  csrWid      : BitVec 3

def lsuOutputs (s : LsuState) (i : LsuIn) : LsuOut :=
  { fifoRdy     := lsuFifoRdy s i
  , flushRdy    := lsuFlushRdy s
  , mshrValid   := lsuMshrValid s
  , mshrTag     := lsuMshrTagBits s.regSave i.csrTid i.csrPds i.csrNumw
  , sharedValid := lsuSharedValid s
  , sharedBits  := lsuSharedBits s i
  , dcacheValid := lsuDcacheValid s
  , dcacheBits  := lsuDcacheBits s i
  , csrWid      := s.regSave.ctrl.wid }

/- ---- 3.3 次态函数（:291-421，三个 switch 均读旧状态，D10） ---- -/

/-- cnt 终止条件（:314,332,349,360 的 `cnt.value >= num_thread.U`，D9） -/
def lsuCntDone (c : BitVec 5) : Bool := decide ((c.zeroExtend 6) ≥ 32#6)

/-- 掩码耗尽（:314 等的 `mask_next.asUInt === 0.U`） -/
def lsuMaskNextEmpty (s : LsuState) (i : LsuIn) : Bool :=
  !lsuMaskNez (lsuMaskNext s.regSave i.csrTid i.csrPds i.csrNumw)

/-- FSM 次态（:291-367） -/
def lsuNextState (smax : BitVec 32) (s : LsuState) (i : LsuIn) : BitVec 3 :=
  if s.state == lsuSIdle then                                               -- :292
    (if lsuFlushFire s i then lsuSDcache                                    -- :294
     else if lsuFifoFire s i then lsuSSave else lsuSIdle)                   -- :295
  else if s.state == lsuSSave then                                          -- :299
    (if s.regSave.ctrl.mem_cmd != 0#2 then
       (if lsuMshrFire s i then
          (if lsuAllShared smax s.regSave i.csrTid i.csrPds i.csrNumw && !s.isFlush
           then lsuSShared else lsuSDcache)                                 -- :301-308
        else lsuSSave)
     else lsuSIdle)                                                         -- :310
  else if s.state == lsuSShared then                                        -- :312
    (if lsuSharedFire s i then
       (if lsuCntDone s.cnt || lsuMaskNextEmpty s i then lsuSIdle else lsuSShared)
     else lsuSShared)
  else if s.state == lsuSDcache then                                        -- :321
    (if s.isFlush then (if lsuDcacheFire s i then lsuSIdle else lsuSDcache) -- :322-327
     else if lsuDcacheFire s i then                                         -- :329
       (if s.regSave.ctrl.atomic && (s.regSave.ctrl.aq || s.regSave.ctrl.rl)
        then lsuSD1                                                         -- :330-331
        else if lsuCntDone s.cnt || lsuMaskNextEmpty s i then lsuSIdle      -- :332-334
        else lsuSDcache)                                                    -- :335-337
     else lsuSDcache)
  else if s.state == lsuSD1 then                                            -- :344
    (if lsuDcacheFire s i then
       (if s.regSave.ctrl.aq && s.regSave.ctrl.rl then lsuSD2               -- :347
        else if lsuCntDone s.cnt || lsuMaskNextEmpty s i then lsuSIdle      -- :349
        else lsuSDcache)                                                    -- :352（回到 s_dcache）
     else lsuSD1)
  else if s.state == lsuSD2 then                                            -- :358
    (if lsuDcacheFire s i then
       (if lsuCntDone s.cnt || lsuMaskNextEmpty s i then lsuSIdle else lsuSDcache)
     else lsuSD2)
  else s.state                                                              -- D10 保持

/-- cnt 次态（:297,314-317,332-337,349-352,360-363；D9） -/
def lsuNextCnt (s : LsuState) (i : LsuIn) : BitVec 5 :=
  if s.state == lsuSIdle then 0#5                                           -- :297 cnt.reset()
  else if s.state == lsuSShared then                                        -- :312
    (if lsuSharedFire s i then
       (if lsuCntDone s.cnt || lsuMaskNextEmpty s i then 0#5 else s.cnt + 1)
     else s.cnt)
  else if s.state == lsuSDcache then                                        -- :321
    (if s.isFlush then s.cnt                                                -- :322-327 无 cnt 赋值
     else if lsuDcacheFire s i then
       (if s.regSave.ctrl.atomic && (s.regSave.ctrl.aq || s.regSave.ctrl.rl)
        then s.cnt                                                          -- :330-331 无 cnt 赋值
        else if lsuCntDone s.cnt || lsuMaskNextEmpty s i then 0#5
        else s.cnt + 1)
     else s.cnt)
  else if s.state == lsuSD1 then                                            -- :344
    (if lsuDcacheFire s i then
       (if s.regSave.ctrl.aq && s.regSave.ctrl.rl then s.cnt                -- :347 无 cnt 赋值
        else if lsuCntDone s.cnt || lsuMaskNextEmpty s i then 0#5
        else s.cnt + 1)
     else s.cnt)
  else if s.state == lsuSD2 then                                            -- :358
    (if lsuDcacheFire s i then
       (if lsuCntDone s.cnt || lsuMaskNextEmpty s i then 0#5 else s.cnt + 1)
     else s.cnt)
  else s.cnt                                                                -- D10 保持

/-- reg_save 次态（:369-404 的第二个 switch） -/
def lsuNextRegSave (s : LsuState) (i : LsuIn) : LsuVExe :=
  if s.state == lsuSIdle then                                               -- :370
    (if lsuFlushFire s i then                                               -- :371-373
       { lsuVExe0 with ctrl := { lsuCtrl0 with mem_cmd := 1#2 } }
     else if lsuFifoFire s i then                                           -- :374-381
       let b := i.fifoBits
       { b with
         ctrl := { b.ctrl with aq := (if b.ctrl.atomic then true else b.ctrl.aq) }
       , mask := (if b.ctrl.isvec then b.mask else fun _ => true) }
     else lsuVExe0)                                                         -- :382
  else if s.state == lsuSShared then                                        -- :389
    (if lsuSharedFire s i then
       { s.regSave with mask := lsuMaskNext s.regSave i.csrTid i.csrPds i.csrNumw }
     else s.regSave)
  else if s.state == lsuSDcache then                                        -- :397
    (if lsuDcacheFire s i then
       { s.regSave with mask := lsuMaskNext s.regSave i.csrTid i.csrPds i.csrNumw }
     else s.regSave)
  else s.regSave                                                            -- s_save/s_dcache_1/s_dcache_2 保持

/-- reg_entryID 次态（:384-388） -/
def lsuNextEntryID (s : LsuState) (i : LsuIn) : BitVec 3 :=
  if (s.state == lsuSSave) && (s.regSave.ctrl.mem_cmd != 0#2) && lsuMshrFire s i
  then i.idxEntry
  else s.entryID

/-- is_flush 次态（:406-421 的第三个 switch） -/
def lsuNextIsFlush (s : LsuState) (i : LsuIn) : Bool :=
  if s.state == lsuSIdle then lsuFlushFire s i                              -- :407-413
  else if s.state == lsuSDcache then                                        -- :414-420
    (if lsuDcacheFire s i then false else s.isFlush)
  else s.isFlush                                                            -- 其他态保持

/-- 单拍转移 -/
def lsuStep (smax : BitVec 32) (s : LsuState) (i : LsuIn) : LsuState :=
  ⟨lsuNextState smax s i, lsuNextCnt s i, lsuNextRegSave s i,
   lsuNextIsFlush s i, lsuNextEntryID s i⟩

/-- 多拍运行 -/
def lsuRun (smax : BitVec 32) (s : LsuState) (ins : List LsuIn) : LsuState :=
  ins.foldl (lsuStep smax) s

/- ========================================================================= -/
/- 4. 回归测试（先测试：组合逐 lane decide；多拍轨迹 native_decide）          -/
/- ========================================================================= -/

section LsuRegTests

/-- 空输入（无 valid/ready） -/
def lsuInNop : LsuIn := ⟨false, lsuVExe0, false, false, 0, false, false, 0, 0, 0⟩

/-- 常量行 -/
def lsuRowC (v : BitVec 32) : LsuRow := fun _ => v

/- ---- 4.1 逐 lane 地址（:146-161） ---- -/

def lsuCtrlScalarLd : LsuCtrl :=   -- LW 风格：标量、单位宽度字
  { lsuCtrl0 with mem_cmd := lsuMXrd, mem_whb := lsuMemW, wxd := true }

def lsuCtrlVecLd (mop : BitVec 2) : LsuCtrl :=
  { lsuCtrl0 with mem_cmd := lsuMXrd, mem_whb := lsuMemW, isvec := true,
                  mop := mop, wvd := true }

-- 标量：全 lane 地址 = in1(0)+in2(0)（:159）
example : lsuLaneAddr ⟨fun x => BitVec.ofNat 32 (100 + x.val), lsuRowC 7, lsuRowC 0,
    fun _ => true, lsuCtrlScalarLd⟩ 0 0 0 ⟨5, by decide⟩ = 107#32 := by decide
example : lsuLaneAddr ⟨lsuRowC 100, lsuRowC 7, lsuRowC 0, fun _ => true,
    lsuCtrlScalarLd⟩ 0 0 0 ⟨31, by decide⟩ = 107#32 := by decide

-- 单位 stride（mop=0，:154）：addr x = in1 x + 4x
example : lsuLaneAddr ⟨lsuRowC 0x1000, lsuRowC 0, lsuRowC 0, fun _ => true,
    lsuCtrlVecLd 0⟩ 0 0 0 ⟨3, by decide⟩ = 0x100C#32 := by decide
example : lsuLaneAddr ⟨lsuRowC 0x1000, lsuRowC 0, lsuRowC 0, fun _ => true,
    lsuCtrlVecLd 0⟩ 0 0 0 ⟨31, by decide⟩ = 0x107C#32 := by decide

-- 变 stride（mop=1/2，:157）：addr x = in1 x + x * in2 x
example : lsuLaneAddr ⟨lsuRowC 0x1000, lsuRowC 16, lsuRowC 0, fun _ => true,
    lsuCtrlVecLd 1⟩ 0 0 0 ⟨3, by decide⟩ = 0x1030#32 := by decide
example : lsuLaneAddr ⟨lsuRowC 0x1000, lsuRowC 16, lsuRowC 0, fun _ => true,
    lsuCtrlVecLd 2⟩ 0 0 0 ⟨3, by decide⟩ = 0x1030#32 := by decide

-- gather（mop=3，:156）：addr x = in1 x + in2 x
example : lsuLaneAddr ⟨lsuRowC 0x1000, fun x => BitVec.ofNat 32 (x.val * 64),
    lsuRowC 0, fun _ => true, lsuCtrlVecLd 3⟩ 0 0 0 ⟨3, by decide⟩ = 0x10C0#32 := by decide

-- vls12（:147-149）：disable_mask && is_vls12 → in1+in2
def lsuCtrlVls12 (v12 : Bool) : LsuCtrl :=
  { lsuCtrl0 with mem_cmd := lsuMXrd, isvec := true, disable_mask := true,
                  is_vls12 := v12 }
example : lsuLaneAddr ⟨lsuRowC 0x2000, fun x => BitVec.ofNat 32 (x.val * 4),
    lsuRowC 0, fun _ => true, lsuCtrlVls12 true⟩ 0 0 0 ⟨3, by decide⟩ = 0x200C#32 := by decide

-- vls12 形（disable_mask && !is_vls12，:150）：分段地址公式
-- s = 0x1234（lane 常量）；tid=0x10, pds=0x100, numw=2
-- addr x = (s%4) + (tid+x)*4 + pds + ((s/4*4)*numw)*32
--        = 0 + (0x10+x)*4 + 0x100 + (0x1234/4*4)*64
example : lsuLaneAddr ⟨lsuRowC 0x1234, lsuRowC 0, lsuRowC 0, fun _ => true,
    lsuCtrlVls12 false⟩ 0x10 0x100 2 ⟨0, by decide⟩ =
      (0x10 * 4 + 0x100 + (0x1234#32) * 2 * 32) := by decide
example : lsuLaneAddr ⟨lsuRowC 0x1234, lsuRowC 0, lsuRowC 0, fun _ => true,
    lsuCtrlVls12 false⟩ 0x10 0x100 2 ⟨5, by decide⟩ =
      ((0x10 + 5#32) * 4 + 0x100 + (0x1234#32) * 2 * 32) := by decide

/- ---- 4.2 is_shared 判界（:162，smax=0x20000） ---- -/

def lsuSharedV (a : BitVec 32) : LsuVExe :=
  ⟨lsuRowC a, lsuRowC 0, lsuRowC 0, fun _ => true, lsuCtrlScalarLd⟩

example : lsuLaneIsShared lsuSmaxDefault (lsuSharedV 0x6FFFFFFF) 0 0 0 ⟨0, by decide⟩ = false := by decide
example : lsuLaneIsShared lsuSmaxDefault (lsuSharedV 0x70000000) 0 0 0 ⟨0, by decide⟩ = true := by decide
example : lsuLaneIsShared lsuSmaxDefault (lsuSharedV 0x7001FFFF) 0 0 0 ⟨0, by decide⟩ = true := by decide
example : lsuLaneIsShared lsuSmaxDefault (lsuSharedV 0x70020000) 0 0 0 ⟨0, by decide⟩ = false := by decide
-- 掩蔽 lane 视同 shared（:162 的 !mask(x) 析取）
example : lsuLaneIsShared lsuSmaxDefault
    ⟨lsuRowC 0x100, lsuRowC 0, lsuRowC 0, fun _ => false, lsuCtrlScalarLd⟩ 0 0 0 ⟨0, by decide⟩ = true := by decide
-- 标量 all_shared = lane0 的 is_shared（:166）
example : lsuAllShared lsuSmaxDefault (lsuSharedV 0x70000040) 0 0 0 = true := by decide
example : lsuAllShared lsuSmaxDefault (lsuSharedV 0x80000040) 0 0 0 = false := by decide

/- ---- 4.3 wordOffset1H（:180-193） ---- -/

example : lsuWordOff1H lsuMemW 0x1234 = 15#4 := by decide
example : lsuWordOff1H lsuMemH 0x1230 = 3#4 := by decide   -- addr(1)=0
example : lsuWordOff1H lsuMemH 0x1232 = 12#4 := by decide  -- addr(1)=1
example : lsuWordOff1H lsuMemB 0x1230 = 1#4 := by decide
example : lsuWordOff1H lsuMemB 0x1231 = 2#4 := by decide
example : lsuWordOff1H lsuMemB 0x1232 = 4#4 := by decide
example : lsuWordOff1H lsuMemB 0x1233 = 8#4 := by decide
example : lsuWordOff1H lsuMemX 0x1233 = 15#4 := by decide  -- 默认（:182）

/- ---- 4.4 tag/setIdx/blockOffset 切片（:170-178） ---- -/

example : lsuTagOf 0x89ABCDEF = (0x89ABCDEF#32).extractLsb' 15 17 := by decide
example : lsuSetOf 0x89ABCDEF = (0x89ABCDEF#32).extractLsb' 7 8 := by decide
example : lsuBlkOf 0x89ABCDEF = (0x89ABCDEF#32).extractLsb' 2 5 := by decide
example : lsuSetOf 0x70000040 = 0#8 := by decide
example : lsuTagOf 0x70000040 = 0xE000#17 := by decide

/- ---- 4.5 FSM 轨迹 A：标量 shared store，单拍完成 ---- -/

def lsuCtrlStShared : LsuCtrl :=
  { lsuCtrl0 with mem_cmd := lsuMXwr, mem_whb := lsuMemW, wid := 3, reg_idxw := 9 }

def lsuReqStShared : LsuVExe :=
  ⟨lsuRowC 0x70000040, lsuRowC 0, fun x => BitVec.ofNat 32 (0xAA00 + x.val),
   fun _ => true, lsuCtrlStShared⟩

-- 拍0：接受（fifoValid）
def lsuInAccept : LsuIn := { lsuInNop with fifoValid := true, fifoBits := lsuReqStShared }
-- 拍1：mshr 分配（idxEntry=5）
def lsuInAlloc : LsuIn := { lsuInNop with mshrReady := true, idxEntry := 5 }
-- 拍2：shared 发送
def lsuInShFire : LsuIn := { lsuInNop with sharedReady := true }

def lsuAs1 := lsuStep lsuSmaxDefault lsuInit lsuInAccept
def lsuAs2 := lsuStep lsuSmaxDefault lsuAs1 lsuInAlloc
def lsuAs3 := lsuStep lsuSmaxDefault lsuAs2 lsuInShFire

-- 拍0：握手与转移
example : (lsuOutputs lsuInit lsuInAccept).fifoRdy = true := by decide
example : lsuAs1.state = lsuSSave := by native_decide
-- 标量接受：mask 强制全 true（:381）、aq 不变（atomic=false）
example : lsuAs1.regSave.mask ⟨17, by decide⟩ = true := by native_decide
example : lsuAs1.regSave.ctrl.wid = 3#3 := by native_decide
-- 拍1：to_mshr.valid 且 tag 正确（:196-205）
example : (lsuOutputs lsuAs1 lsuInAlloc).mshrValid = true := by native_decide
example : (lsuOutputs lsuAs1 lsuInAlloc).mshrTag.warp_id = 3#3 := by native_decide
example : (lsuOutputs lsuAs1 lsuInAlloc).mshrTag.reg_idxw = 9#8 := by native_decide
example : (lsuOutputs lsuAs1 lsuInAlloc).mshrTag.isWrite = true := by native_decide
example : (lsuOutputs lsuAs1 lsuInAlloc).mshrTag.wordOffset1H ⟨0, by decide⟩ = 15#4 := by native_decide
-- 拍1 fire → s_shared；entryID 捕获 5（:386）
example : lsuAs2.state = lsuSShared := by native_decide
example : lsuAs2.entryID = 5#3 := by native_decide
-- 拍2：to_shared 字段（:213-223）
example : (lsuOutputs lsuAs2 lsuInShFire).sharedValid = true := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.instrId = 5#3 := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.isWrite = true := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.setIdx = 0#8 := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.active ⟨7, by decide⟩ = true := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.data ⟨7, by decide⟩ = 0xAA07#32 := by native_decide
example : (lsuOutputs lsuAs2 lsuInShFire).sharedBits.blkOff ⟨7, by decide⟩ = 16#5 := by native_decide  -- 0x40>>2
-- 拍2 fire 后回 idle（mask_next 全 0：全 lane 同组）
example : lsuAs3.state = lsuSIdle := by native_decide

/- ---- 4.6 FSM 轨迹 B：向量 global load 跨两个 128B block ---- -/

def lsuReqVec2Blk : LsuVExe :=
  ⟨fun x => if x.val < 16 then 0x1000#32 else 0x1080#32, lsuRowC 0,
   lsuRowC 0, fun _ => true, lsuCtrlVecLd 0⟩

-- lane<16：0x1000+4x ∈ [0x1000,0x103C]（setIdx 0x20）；lane≥16：0x1080+4x ∈
-- [0x10C0,0x10FC]（setIdx 0x21）；tag 均为 0
example : lsuLaneAddr lsuReqVec2Blk 0 0 0 ⟨0, by decide⟩ = 0x1000#32 := by decide
example : lsuLaneAddr lsuReqVec2Blk 0 0 0 ⟨15, by decide⟩ = 0x103C#32 := by decide
example : lsuLaneAddr lsuReqVec2Blk 0 0 0 ⟨16, by decide⟩ = 0x10C0#32 := by decide
example : lsuLaneAddr lsuReqVec2Blk 0 0 0 ⟨31, by decide⟩ = 0x10FC#32 := by decide

def lsuInAcceptB : LsuIn := { lsuInNop with fifoValid := true, fifoBits := lsuReqVec2Blk }
def lsuInAllocB : LsuIn := { lsuInNop with mshrReady := true, idxEntry := 2 }
def lsuInDcFire : LsuIn := { lsuInNop with dcacheReady := true }

def lsuBs1 := lsuStep lsuSmaxDefault lsuInit lsuInAcceptB
def lsuBs2 := lsuStep lsuSmaxDefault lsuBs1 lsuInAllocB
def lsuBs3 := lsuStep lsuSmaxDefault lsuBs2 lsuInDcFire   -- 第一组发出
def lsuBs4 := lsuStep lsuSmaxDefault lsuBs3 lsuInDcFire   -- 第二组发出 → idle

-- 标量/向量判界：0x1000 系地址不在 LDS 区间 → 走 dcache
example : lsuBs2.state = lsuSDcache := by native_decide
example : lsuBs2.entryID = 2#3 := by native_decide
-- 第一拍请求：tag=0、setIdx=0x20、active = lane 0..15
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheValid = true := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.tag = 0#17 := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.setIdx = 0x20#8 := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.active ⟨5, by decide⟩ = true := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.active ⟨15, by decide⟩ = true := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.active ⟨16, by decide⟩ = false := by native_decide
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.opcode = 0#3 := by native_decide  -- load: mem_cmd(1)=0
example : (lsuOutputs lsuBs2 lsuInDcFire).dcacheBits.instrId = 2#3 := by native_decide
-- 第一拍 fire 后：mask 只剩 lane≥16，滞留 s_dcache
example : lsuBs3.state = lsuSDcache := by native_decide
example : lsuBs3.regSave.mask ⟨5, by decide⟩ = false := by native_decide
example : lsuBs3.regSave.mask ⟨16, by decide⟩ = true := by native_decide
-- 第二拍请求：setIdx=0x21、active = lane 16..31
example : (lsuOutputs lsuBs3 lsuInDcFire).dcacheBits.setIdx = 0x21#8 := by native_decide
example : (lsuOutputs lsuBs3 lsuInDcFire).dcacheBits.active ⟨16, by decide⟩ = true := by native_decide
example : (lsuOutputs lsuBs3 lsuInDcFire).dcacheBits.active ⟨31, by decide⟩ = true := by native_decide
example : (lsuOutputs lsuBs3 lsuInDcFire).dcacheBits.active ⟨5, by decide⟩ = false := by native_decide
-- 第二拍 fire 后回 idle
example : lsuBs4.state = lsuSIdle := by native_decide

/- ---- 4.7 FSM 轨迹 C：s_dcache 反压——valid 保持、bits 稳定（Irrevocable 测试面） ---- -/

def lsuBc1 := lsuStep lsuSmaxDefault lsuInit lsuInAcceptB
def lsuBc2 := lsuStep lsuSmaxDefault lsuBc1 lsuInAllocB
def lsuBc3 := lsuStep lsuSmaxDefault lsuBc2 lsuInNop      -- dcacheReady=0
def lsuBc4 := lsuStep lsuSmaxDefault lsuBc3 lsuInNop      -- 继续反压

example : lsuBc3.state = lsuSDcache := by native_decide
example : lsuBc4.state = lsuSDcache := by native_decide
example : (lsuOutputs lsuBc4 lsuInNop).dcacheValid = true := by native_decide
-- bits 逐点稳定（函数投影）
example : (lsuOutputs lsuBc4 lsuInNop).dcacheBits.setIdx =
    (lsuOutputs lsuBc2 lsuInNop).dcacheBits.setIdx := by native_decide
example : ∀ x, (lsuOutputs lsuBc4 lsuInNop).dcacheBits.active x =
    (lsuOutputs lsuBc2 lsuInNop).dcacheBits.active x := by native_decide
example : ∀ x, (lsuOutputs lsuBc4 lsuInNop).dcacheBits.data x =
    (lsuOutputs lsuBc2 lsuInNop).dcacheBits.data x := by native_decide

/- ---- 4.8 FSM 轨迹 D：flush_dcache（:294,322-327,262-264） ---- -/

def lsuInFlush : LsuIn := { lsuInNop with flushValid := true }
def lsuDs1 := lsuStep lsuSmaxDefault lsuInit lsuInFlush
def lsuDs2 := lsuStep lsuSmaxDefault lsuDs1 lsuInDcFire

-- flush 接受：fifo 被阻塞（:136），flushRdy=idle（:137）
example : (lsuOutputs lsuInit lsuInFlush).fifoRdy = false := by decide
example : (lsuOutputs lsuInit lsuInFlush).flushRdy = true := by decide
example : lsuDs1.state = lsuSDcache := by native_decide
example : lsuDs1.isFlush = true := by native_decide
-- flush 请求：opcode=3 param=0（:262-264），activeMask 全 0（reg_save 清零 :372）
example : (lsuOutputs lsuDs1 lsuInDcFire).dcacheBits.opcode = 3#3 := by native_decide
example : (lsuOutputs lsuDs1 lsuInDcFire).dcacheBits.param = 0#4 := by native_decide
example : ∀ x, (lsuOutputs lsuDs1 lsuInDcFire).dcacheBits.active x = false := by native_decide
-- flush 未分配 MSHR：instrId 为残留 reg_entryID（Q8，初值 0）
example : (lsuOutputs lsuDs1 lsuInDcFire).dcacheBits.instrId = 0#3 := by native_decide
-- fire 后回 idle，is_flush 清
example : lsuDs2.state = lsuSIdle := by native_decide
example : lsuDs2.isFlush = false := by native_decide

/- ---- 4.9 FSM 轨迹 E：atomic AMO（aq 被强制，:376-380），单 lane ---- -/

def lsuCtrlAmo : LsuCtrl :=
  { lsuCtrl0 with mem_cmd := lsuMXwr, mem_whb := lsuMemW, isvec := true,
                  atomic := true, alu_fn := lsuFnAmoadd, wxd := true }

def lsuReqAmo : LsuVExe :=
  ⟨lsuRowC 0x40000000, lsuRowC 0, lsuRowC 7,
   fun x => x.val == 0, lsuCtrlAmo⟩      -- 只 lane 0

def lsuInAcceptE : LsuIn := { lsuInNop with fifoValid := true, fifoBits := lsuReqAmo }
def lsuEs1 := lsuStep lsuSmaxDefault lsuInit lsuInAcceptE
def lsuEs2 := lsuStep lsuSmaxDefault lsuEs1 lsuInAllocB
def lsuEs3 := lsuStep lsuSmaxDefault lsuEs2 lsuInDcFire   -- s_dcache 发出 opcode=3
def lsuEs4 := lsuStep lsuSmaxDefault lsuEs3 lsuInDcFire   -- s_dcache_1 发出 AMO

-- 接受拍 aq 被强制 true（:376-378）
example : lsuEs1.regSave.ctrl.aq = true := by native_decide
-- s_dcache：atomic 只发优先 lane（:275），opcode=3（aq 序列化 :250）
example : (lsuOutputs lsuEs2 lsuInDcFire).dcacheBits.active ⟨0, by decide⟩ = true := by native_decide
example : ∀ x, (lsuOutputs lsuEs2 lsuInDcFire).dcacheBits.active x = (x == ⟨0, by decide⟩) := by
  native_decide
example : (lsuOutputs lsuEs2 lsuInDcFire).dcacheBits.opcode = 3#3 := by native_decide
example : (lsuOutputs lsuEs2 lsuInDcFire).dcacheBits.param = 0#4 := by native_decide
-- fire → s_dcache_1（:330-331）
example : lsuEs3.state = lsuSD1 := by native_decide
-- s_dcache_1：opcode=2、param=paramAlt(AMOADD)=0（:250-251）
example : (lsuOutputs lsuEs3 lsuInDcFire).dcacheBits.opcode = 2#3 := by native_decide
example : (lsuOutputs lsuEs3 lsuInDcFire).dcacheBits.param = 0#4 := by native_decide
-- mask 只剩空（lane0 已在 s_dcache fire 时清除）→ fire 后回 idle（:349-350）
example : lsuEs4.state = lsuSIdle := by native_decide

/- ---- 4.10 FSM 轨迹 F：s_save 反压——to_mshr valid/bits 稳定 ---- -/

def lsuFs1 := lsuStep lsuSmaxDefault lsuInit lsuInAccept
def lsuFs2 := lsuStep lsuSmaxDefault lsuFs1 lsuInNop     -- mshrReady=0

example : lsuFs2.state = lsuSSave := by native_decide
example : (lsuOutputs lsuFs2 lsuInNop).mshrValid = true := by native_decide
example : (lsuOutputs lsuFs2 lsuInNop).mshrTag.warp_id =
    (lsuOutputs lsuFs1 lsuInNop).mshrTag.warp_id := by native_decide
example : ∀ x, (lsuOutputs lsuFs2 lsuInNop).mshrTag.wordOffset1H x =
    (lsuOutputs lsuFs1 lsuInNop).mshrTag.wordOffset1H x := by native_decide

end LsuRegTests

/- ========================================================================= -/
/- 5. AddrCalculate 定理                                                      -/
/- ========================================================================= -/

/-- Q2 机证：`cnt.value >= num_thread.U`（:314,332,349,360）恒假——
    Counter(32) 值域 0..31，与 6 位字面量 32 比较永不成立；cnt 为死硬件。 -/
theorem lsuCntDone_false (c : BitVec 5) : lsuCntDone c = false := by
  simp only [lsuCntDone]; bv_decide

/-- BitVec 3 全值枚举（FSM 状态穷举用） -/
theorem lsuBv3_cases (x : BitVec 3) :
    x = 0#3 ∨ x = 1#3 ∨ x = 2#3 ∨ x = 3#3 ∨ x = 4#3 ∨ x = 5#3 ∨ x = 6#3 ∨ x = 7#3 := by
  bv_decide

/- ---- 5.1 优先编码器规格（D13） ---- -/

/-- find? 形式分解：mask 非空 ⇒ 找到最低置位 lane，且其前所有 lane 未置位 -/
theorem lsuPrioEncF_find (m : LsuMask32) (h : lsuMaskNez m = true) :
    ∃ a, (List.finRange 32).find? (fun x => m x) = some a ∧ m a = true ∧
      ∃ as bs, List.finRange 32 = as ++ a :: bs ∧ ∀ y ∈ as, !(m y) := by
  have hany : (List.finRange 32).any (fun x => m x) = true := h
  rw [List.any_eq_true] at hany
  obtain ⟨x, hxm, hx⟩ := hany
  have hne : (List.finRange 32).find? (fun x => m x) ≠ none := by
    intro hf
    rw [List.find?_eq_none] at hf
    exact absurd hx (hf x (List.mem_finRange x))
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hma, as, bs, hdecomp, hnotin⟩ := (List.find?_eq_some_iff_append).mp ha
  exact ⟨a, ha, hma, as, bs, hdecomp, hnotin⟩

/-- 选中的 lane 已置位 -/
theorem lsuPrioEncF_spec_set (m : LsuMask32) (h : lsuMaskNez m = true) :
    m (lsuPrioEncF m) = true := by
  obtain ⟨a, ha, hma, -⟩ := lsuPrioEncF_find m h
  simp [lsuPrioEncF, ha, hma]

/-- mask_next 清除优先 lane（:285-287；atomic 与非 atomic 两种形式都成立：
    atomic 直接清 pe；非 atomic 时 tag/setIdx 取自 pe 自己的地址，自反相等） -/
theorem lsuMaskNext_pe (v : LsuVExe) (tid pds numw : BitVec 32)
    (h : lsuMaskNez v.mask = true) :
    lsuMaskNext v tid pds numw (lsuPrioEncF v.mask) = false := by
  unfold lsuMaskNext
  split
  · simp   -- atomic：x == pe 自反
  · simp [lsuTagW, lsuSetW, lsuAddrWire, h]

/-- mask_next 是 mask 的子集 -/
theorem lsuMaskNext_subset (v : LsuVExe) (tid pds numw : BitVec 32) (x : Fin 32)
    (h : lsuMaskNext v tid pds numw x = true) : v.mask x = true := by
  unfold lsuMaskNext at h
  split at h <;> simp_all

/- ---- 5.2 进展：每次请求 fire 严格减少剩余 lane 数 ---- -/

/-- 剩余 lane 数（mask 的 popcount） -/
def lsuMaskCount (m : LsuMask32) : Nat := (List.finRange 32).countP (fun x => m x)

/-- 非空 mask 的一次请求（清同组/清优先 lane）使剩余 lane 数严格下降；
    这保证突发（burst）在有限拍内结束（配合 lsuCntDone_false，:314 等的
    终止条件只有 mask_next==0 在起作用）。 -/
theorem lsuT_progress (v : LsuVExe) (tid pds numw : BitVec 32)
    (h : lsuMaskNez v.mask = true) :
    lsuMaskCount (lsuMaskNext v tid pds numw) < lsuMaskCount v.mask := by
  obtain ⟨a, ha, hma, as, bs, hdecomp, hnotin⟩ := lsuPrioEncF_find v.mask h
  have hpe : lsuPrioEncF v.mask = a := by simp [lsuPrioEncF, ha]
  have hmn_a : lsuMaskNext v tid pds numw a = false := hpe ▸ lsuMaskNext_pe v tid pds numw h
  -- as 段：mask 与 mask_next 均为 0
  have h0a : as.countP (fun x => v.mask x) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    have hy' := hnotin y hy
    simp at hy'
    simp [hy']
  have h0a' : as.countP (fun x => lsuMaskNext v tid pds numw x) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    have hy' := hnotin y hy
    simp at hy'
    simp [lsuMaskNext, hy']
  -- 主等式
  have hm_count : lsuMaskCount v.mask = as.countP (fun x => v.mask x) +
      (bs.countP (fun x => v.mask x) + 1) := by
    simp only [lsuMaskCount]
    rw [hdecomp, List.countP_append, List.countP_cons]
    simp [hma]
  have hmn_count : lsuMaskCount (lsuMaskNext v tid pds numw) ≤
      bs.countP (fun x => v.mask x) := by
    simp only [lsuMaskCount]
    rw [hdecomp, List.countP_append, List.countP_cons, hmn_a]
    simp [h0a']
    exact List.countP_mono_left (fun x _ hx => lsuMaskNext_subset v tid pds numw x hx)
  omega

/-- step 级进展：s_dcache 中 fire 且 mask 非空 ⇒ 剩余 lane 数严格下降 -/
theorem lsuT_progress_dcache (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSDcache) (hf : lsuDcacheFire s i = true)
    (hm : lsuMaskNez s.regSave.mask = true) :
    lsuMaskCount (lsuStep sm s i).regSave.mask < lsuMaskCount s.regSave.mask := by
  have hsr : (lsuStep sm s i).regSave =
      { s.regSave with mask := lsuMaskNext s.regSave i.csrTid i.csrPds i.csrNumw } := by
    have b0 : (s.state == lsuSIdle) = false := by rw [hst]; decide
    have b2 : (s.state == lsuSShared) = false := by rw [hst]; decide
    have b3 : (s.state == lsuSDcache) = true := by rw [hst]; decide
    simp [lsuStep, lsuNextRegSave, b0, b2, b3, hf]
  rw [hsr]
  exact lsuT_progress s.regSave i.csrTid i.csrPds i.csrNumw hm

/-- step 级进展：s_shared 中 fire 且 mask 非空 ⇒ 严格下降 -/
theorem lsuT_progress_shared (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSShared) (hf : lsuSharedFire s i = true)
    (hm : lsuMaskNez s.regSave.mask = true) :
    lsuMaskCount (lsuStep sm s i).regSave.mask < lsuMaskCount s.regSave.mask := by
  have hsr : (lsuStep sm s i).regSave =
      { s.regSave with mask := lsuMaskNext s.regSave i.csrTid i.csrPds i.csrNumw } := by
    have b0 : (s.state == lsuSIdle) = false := by rw [hst]; decide
    have b1 : (s.state == lsuSSave) = false := by rw [hst]; decide
    have b2 : (s.state == lsuSShared) = true := by rw [hst]; decide
    simp [lsuStep, lsuNextRegSave, b0, b1, b2, hf]
  rw [hsr]
  exact lsuT_progress s.regSave i.csrTid i.csrPds i.csrNumw hm

/- ---- 5.3 握手稳定性（Irrevocable 的步级证据） ---- -/

/-- to_dcache 反压保持：valid 置位而 ready 掉落 ⇒ 整状态保持
    （valid/bits 下一拍原样，:282,:397-403,:414-420） -/
theorem lsuT_dcache_hold (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hv : lsuDcacheValid s = true) (hno : i.dcacheReady = false) :
    lsuStep sm s i = s := by
  obtain ⟨st, c, r, f, e⟩ := s
  simp only [lsuDcacheValid, Bool.or_eq_true, beq_iff_eq] at hv
  rcases hv with (h | h) | h
  · subst h
    have b0 : (lsuSDcache == lsuSIdle) = false := by decide
    have b1 : (lsuSDcache == lsuSSave) = false := by decide
    have b2 : (lsuSDcache == lsuSShared) = false := by decide
    have b4 : (lsuSDcache == lsuSD1) = false := by decide
    have b5 : (lsuSDcache == lsuSD2) = false := by decide
    simp [lsuStep, lsuNextState, lsuNextCnt, lsuNextRegSave, lsuNextEntryID,
          lsuNextIsFlush, lsuFifoFire, lsuFifoRdy, lsuFlushFire, lsuFlushRdy,
          lsuMshrFire, lsuMshrValid, lsuSharedFire, lsuSharedValid,
          lsuDcacheFire, lsuDcacheValid, hno, b0, b1, b2, b4, b5]
  · subst h
    have b0 : (lsuSD1 == lsuSIdle) = false := by decide
    have b1 : (lsuSD1 == lsuSSave) = false := by decide
    have b2 : (lsuSD1 == lsuSShared) = false := by decide
    have b3 : (lsuSD1 == lsuSDcache) = false := by decide
    have b5 : (lsuSD1 == lsuSD2) = false := by decide
    simp [lsuStep, lsuNextState, lsuNextCnt, lsuNextRegSave, lsuNextEntryID,
          lsuNextIsFlush, lsuFifoFire, lsuFifoRdy, lsuFlushFire, lsuFlushRdy,
          lsuMshrFire, lsuMshrValid, lsuSharedFire, lsuSharedValid,
          lsuDcacheFire, lsuDcacheValid, hno, b0, b1, b2, b3, b5]
  · subst h
    have b0 : (lsuSD2 == lsuSIdle) = false := by decide
    have b1 : (lsuSD2 == lsuSSave) = false := by decide
    have b2 : (lsuSD2 == lsuSShared) = false := by decide
    have b3 : (lsuSD2 == lsuSDcache) = false := by decide
    have b4 : (lsuSD2 == lsuSD1) = false := by decide
    simp [lsuStep, lsuNextState, lsuNextCnt, lsuNextRegSave, lsuNextEntryID,
          lsuNextIsFlush, lsuFifoFire, lsuFifoRdy, lsuFlushFire, lsuFlushRdy,
          lsuMshrFire, lsuMshrValid, lsuSharedFire, lsuSharedValid,
          lsuDcacheFire, lsuDcacheValid, hno, b0, b1, b2, b3, b4]

/-- 推论：反压期间 to_dcache 的 valid 与 bits 不变（Irrevocable 对偶半） -/
theorem lsuT_dcache_irrevocable (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hv : lsuDcacheValid s = true) (hno : i.dcacheReady = false) :
    (lsuOutputs (lsuStep sm s i) i).dcacheValid = true ∧
      (lsuOutputs (lsuStep sm s i) i).dcacheBits = (lsuOutputs s i).dcacheBits := by
  rw [lsuT_dcache_hold sm s i hv hno]
  exact ⟨hv, rfl⟩

/-- to_shared 反压保持 -/
theorem lsuT_shared_hold (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSShared) (hno : i.sharedReady = false) :
    lsuStep sm s i = s := by
  obtain ⟨st, c, r, f, e⟩ := s
  subst hst
  have b0 : (lsuSShared == lsuSIdle) = false := by decide
  have b1 : (lsuSShared == lsuSSave) = false := by decide
  have b3 : (lsuSShared == lsuSDcache) = false := by decide
  have b4 : (lsuSShared == lsuSD1) = false := by decide
  have b5 : (lsuSShared == lsuSD2) = false := by decide
  simp [lsuStep, lsuNextState, lsuNextCnt, lsuNextRegSave, lsuNextEntryID,
        lsuNextIsFlush, lsuFifoFire, lsuFifoRdy, lsuFlushFire, lsuFlushRdy,
        lsuMshrFire, lsuMshrValid, lsuDcacheFire, lsuDcacheValid,
        lsuSharedFire, lsuSharedValid, hno, b0, b1, b3, b4, b5]

/-- to_mshr 反压保持（:204, :302-308） -/
theorem lsuT_ssave_hold (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSSave) (hmem : s.regSave.ctrl.mem_cmd ≠ 0#2)
    (hno : i.mshrReady = false) :
    lsuStep sm s i = s := by
  obtain ⟨st, c, r, f, e⟩ := s
  subst hst
  have b0 : (lsuSSave == lsuSIdle) = false := by decide
  have b2 : (lsuSSave == lsuSShared) = false := by decide
  have b3 : (lsuSSave == lsuSDcache) = false := by decide
  have b4 : (lsuSSave == lsuSD1) = false := by decide
  have b5 : (lsuSSave == lsuSD2) = false := by decide
  simp [lsuStep, lsuNextState, lsuNextCnt, lsuNextRegSave, lsuNextEntryID,
        lsuNextIsFlush, lsuFifoFire, lsuFifoRdy, lsuFlushFire, lsuFlushRdy,
        lsuSharedFire, lsuSharedValid, lsuDcacheFire, lsuDcacheValid,
        lsuMshrFire, lsuMshrValid, hmem, hno, b0, b2, b3, b4, b5]

/-- to_mshr 单发：s_save 中 fire ⇒ 离开 s_save（进 s_shared 或 s_dcache）且
    捕获 idx_entry（:302-308, :386）；配合 lsuT_ssave_entry（s_save 只能由
    s_idle 经 from_fifo.fire 进入），每条指令恰好分配一次 MSHR 记录 -/
theorem lsuT_ssave_fire (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSSave) (hmem : s.regSave.ctrl.mem_cmd ≠ 0#2)
    (hrdy : i.mshrReady = true) :
    ((lsuStep sm s i).state = lsuSShared ∨ (lsuStep sm s i).state = lsuSDcache) ∧
      (lsuStep sm s i).entryID = i.idxEntry := by
  obtain ⟨st, c, r, f, e⟩ := s
  subst hst
  have hf : lsuMshrFire ⟨lsuSSave, c, r, f, e⟩ i = true := by
    simp [lsuMshrFire, lsuMshrValid, hmem, hrdy]
  constructor
  · have hmem' : r.ctrl.mem_cmd ≠ 0#2 := by simpa using hmem
    have hnext : lsuNextState sm ⟨lsuSSave, c, r, f, e⟩ i =
        (if (lsuAllShared sm r i.csrTid i.csrPds i.csrNumw && !f) = true then lsuSShared
         else lsuSDcache) := by
      simp only [lsuNextState]
      rw [if_neg (by decide : ¬ ((lsuSSave == lsuSIdle) = true))]
      rw [if_pos (by decide : (lsuSSave == lsuSSave) = true)]
      rw [if_pos (show (r.ctrl.mem_cmd != 0#2) = true by simpa using hmem')]
      rw [if_pos hf]
    show lsuNextState sm ⟨lsuSSave, c, r, f, e⟩ i = lsuSShared ∨
      lsuNextState sm ⟨lsuSSave, c, r, f, e⟩ i = lsuSDcache
    rw [hnext]
    by_cases hC : (lsuAllShared sm r i.csrTid i.csrPds i.csrNumw && !f) = true
    · rw [if_pos hC]; exact Or.inl rfl
    · rw [if_neg hC]; exact Or.inr rfl
  · show lsuNextEntryID ⟨lsuSSave, c, r, f, e⟩ i = i.idxEntry
    have hmem' : r.ctrl.mem_cmd ≠ 0#2 := by simpa using hmem
    simp only [lsuNextEntryID]
    rw [if_pos (by simp [hmem', hf])]

/-- s_save 的唯一入口是 s_idle 的 from_fifo.fire（否则只能滞留 s_save） -/
theorem lsuT_ssave_entry (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (h : (lsuStep sm s i).state = lsuSSave) :
    (s.state = lsuSIdle ∧ lsuFifoFire s i = true) ∨ s.state = lsuSSave := by
  have h' : lsuNextState sm s i = lsuSSave := h
  rcases lsuBv3_cases s.state with h0|h0|h0|h0|h0|h0|h0|h0
  · -- s_idle：flushFire 与空转都得不出 s_save，故必有 fifoFire
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_pos (by decide : (((0#3 : BitVec 3) == lsuSIdle) = true))] at h'
    by_cases hfl : lsuFlushFire s i = true
    · rw [if_pos hfl] at h'
      exact absurd h' (by decide)
    · rw [if_neg hfl] at h'
      by_cases hff : lsuFifoFire s i = true
      · exact Or.inl ⟨h0, hff⟩
      · rw [if_neg hff] at h'
        exact absurd h' (by decide)
  · exact Or.inr h0
  · -- s_shared：所有叶子都不是 s_save（先消字面量状态比较，再 cases 自由条件）
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((2#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((2#3 : BitVec 3) == lsuSSave) = true)),
        if_pos (by decide : (((2#3 : BitVec 3) == lsuSShared) = true))] at h'
    by_cases hf : lsuSharedFire s i = true
    · rw [if_pos hf] at h'
      by_cases hd : (lsuCntDone s.cnt || lsuMaskNextEmpty s i) = true
      · rw [if_pos hd] at h'; exact absurd h' (by decide)
      · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · rw [if_neg hf] at h'; exact absurd h' (by decide)
  · -- s_dcache
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSSave) = true)),
        if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSShared) = true)),
        if_pos (by decide : (((3#3 : BitVec 3) == lsuSDcache) = true))] at h'
    by_cases hfl : s.isFlush = true
    · rw [if_pos hfl] at h'
      by_cases hf : lsuDcacheFire s i = true
      · rw [if_pos hf] at h'; exact absurd h' (by decide)
      · rw [if_neg hf] at h'; exact absurd h' (by decide)
    · rw [if_neg hfl] at h'
      by_cases hf : lsuDcacheFire s i = true
      · rw [if_pos hf] at h'
        by_cases hat : (s.regSave.ctrl.atomic && (s.regSave.ctrl.aq || s.regSave.ctrl.rl)) = true
        · rw [if_pos hat] at h'; exact absurd h' (by decide)
        · rw [if_neg hat] at h'
          by_cases hd : (lsuCntDone s.cnt || lsuMaskNextEmpty s i) = true
          · rw [if_pos hd] at h'; exact absurd h' (by decide)
          · rw [if_neg hd] at h'; exact absurd h' (by decide)
      · rw [if_neg hf] at h'; exact absurd h' (by decide)
  · -- s_dcache_1
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSSave) = true)),
        if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSShared) = true)),
        if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSDcache) = true)),
        if_pos (by decide : (((4#3 : BitVec 3) == lsuSD1) = true))] at h'
    by_cases hf : lsuDcacheFire s i = true
    · rw [if_pos hf] at h'
      by_cases har : (s.regSave.ctrl.aq && s.regSave.ctrl.rl) = true
      · rw [if_pos har] at h'; exact absurd h' (by decide)
      · rw [if_neg har] at h'
        by_cases hd : (lsuCntDone s.cnt || lsuMaskNextEmpty s i) = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · rw [if_neg hf] at h'; exact absurd h' (by decide)
  · -- s_dcache_2
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSSave) = true)),
        if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSShared) = true)),
        if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSDcache) = true)),
        if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSD1) = true)),
        if_pos (by decide : (((5#3 : BitVec 3) == lsuSD2) = true))] at h'
    by_cases hf : lsuDcacheFire s i = true
    · rw [if_pos hf] at h'
      by_cases hd : (lsuCntDone s.cnt || lsuMaskNextEmpty s i) = true
      · rw [if_pos hd] at h'; exact absurd h' (by decide)
      · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · rw [if_neg hf] at h'; exact absurd h' (by decide)
  · -- 非法态 6：六个状态比较全否，走 D10 保持分支（叶子为 s.state 自身）
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSSave) = true)),
        if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSShared) = true)),
        if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSDcache) = true)),
        if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSD1) = true)),
        if_neg (by decide : ¬ (((6#3 : BitVec 3) == lsuSD2) = true))] at h'
    exact absurd h' (by decide)
  · -- 非法态 7
    simp only [lsuNextState] at h'
    rw [h0] at h'
    rw [if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSIdle) = true)),
        if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSSave) = true)),
        if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSShared) = true)),
        if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSDcache) = true)),
        if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSD1) = true)),
        if_neg (by decide : ¬ (((7#3 : BitVec 3) == lsuSD2) = true))] at h'
    exact absurd h' (by decide)

/- ---- 5.4 接受/冲刷语义 ---- -/

/-- fifoFire 蕴含 state = s_idle（:136）且 flushValid = false -/
theorem lsuFifoFire_facts (s : LsuState) (i : LsuIn) (hf : lsuFifoFire s i = true) :
    s.state = lsuSIdle ∧ i.flushValid = false ∧ lsuFlushFire s i = false := by
  simp only [lsuFifoFire, lsuFifoRdy, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨hv, hst, hnf⟩ := hf
  refine ⟨hst, ?_, ?_⟩
  · simp at hnf; exact hnf
  · simp [lsuFlushFire, lsuFlushRdy]
    simp at hnf; simp [hnf]

/-- 标量指令接受：mask 强制全 true（:381） -/
theorem lsuT_accept_mask_scalar (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hf : lsuFifoFire s i = true) (hvec : i.fifoBits.ctrl.isvec = false) :
    (lsuStep sm s i).regSave.mask = (fun _ => true) := by
  obtain ⟨hst, -, hnflush⟩ := lsuFifoFire_facts s i hf
  have b0 : (s.state == lsuSIdle) = true := by simp [hst]
  simp [lsuStep, lsuNextRegSave, b0, hnflush, hf, hvec]

/-- 向量指令接受：mask 透传（:381） -/
theorem lsuT_accept_mask_vec (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hf : lsuFifoFire s i = true) (hvec : i.fifoBits.ctrl.isvec = true) :
    (lsuStep sm s i).regSave.mask = i.fifoBits.mask := by
  obtain ⟨hst, -, hnflush⟩ := lsuFifoFire_facts s i hf
  have b0 : (s.state == lsuSIdle) = true := by simp [hst]
  simp [lsuStep, lsuNextRegSave, b0, hnflush, hf, hvec]

/-- atomic 接受时 aq 被强制置位（:376-379） -/
theorem lsuT_accept_aq (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hf : lsuFifoFire s i = true) (hatom : i.fifoBits.ctrl.atomic = true) :
    (lsuStep sm s i).regSave.ctrl.aq = true := by
  obtain ⟨hst, -, hnflush⟩ := lsuFifoFire_facts s i hf
  have b0 : (s.state == lsuSIdle) = true := by simp [hst]
  simp [lsuStep, lsuNextRegSave, b0, hnflush, hf, hatom]

/-- flush 接受（:294,371-373,408-410）：进 s_dcache、is_flush 置位、
    reg_save 清零且 mem_cmd=1（保证 to_mshr 不分配、走 dcache） -/
theorem lsuT_flush_accept (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (hst : s.state = lsuSIdle) (hf : i.flushValid = true) :
    (lsuStep sm s i).state = lsuSDcache ∧ (lsuStep sm s i).isFlush = true ∧
      (lsuStep sm s i).regSave = { lsuVExe0 with ctrl := { lsuCtrl0 with mem_cmd := 1#2 } } := by
  have hff : lsuFlushFire s i = true := by simp [lsuFlushFire, lsuFlushRdy, hst, hf]
  have hfifo : lsuFifoFire s i = false := by
    simp [lsuFifoFire, lsuFifoRdy, hf]
  have b0 : (s.state == lsuSIdle) = true := by simp [hst]
  refine ⟨?_, ?_, ?_⟩
  · show lsuNextState sm s i = lsuSDcache
    simp [lsuNextState, b0, hff, hfifo]
  · show lsuNextIsFlush s i = true
    simp [lsuNextIsFlush, b0, hff]
  · show lsuNextRegSave s i = _
    simp [lsuNextRegSave, b0, hff, hfifo]

/-- flush 请求的 opcode/param（:262-264，前提为 flush 接受后的可达形态：
    ctrl 已被清零，atomic/fence 分支（:245,:259）不抢先） -/
theorem lsuT_flush_opcode (s : LsuState) (i : LsuIn)
    (hf : s.isFlush = true) (ha : s.regSave.ctrl.atomic = false)
    (hfe : s.regSave.ctrl.fence = false) :
    (lsuOutputs s i).dcacheBits.opcode = 3#3 ∧ (lsuOutputs s i).dcacheBits.param = 0#4 := by
  have hop : lsuOpcodeParam s.regSave.ctrl s.isFlush s.state = (3#3, 0#4) := by
    simp [lsuOpcodeParam, ha, hfe, hf]
  simp [lsuOutputs, lsuDcacheBits, hop]

/- ---- 5.5 instrId 一致性 ---- -/

/-- 请求 instrId 恒为 reg_entryID（:213,:227，定义即如此） -/
theorem lsuT_instrId_dcache (s : LsuState) (i : LsuIn) :
    (lsuOutputs s i).dcacheBits.instrId = s.entryID := rfl

theorem lsuT_instrId_shared (s : LsuState) (i : LsuIn) :
    (lsuOutputs s i).sharedBits.instrId = s.entryID := rfl

/-- reg_entryID 只在 s_save 的 to_mshr.fire 更新（:384-388）；之后的
    s_shared/s_dcache* 拍请求携带的 instrId 恒等于分配时捕获的 idx_entry -/
theorem lsuT_entryID_hold (s : LsuState) (i : LsuIn) (hst : s.state ≠ lsuSSave) :
    lsuNextEntryID s i = s.entryID := by
  have b1 : (s.state == lsuSSave) = false := by simp [hst]
  simp [lsuNextEntryID, b1]

/- ---- 5.6 状态编码合法性 ---- -/

/-- 合法状态集（:128 的 Enum(6)） -/
abbrev lsuLegalState (st : BitVec 3) : Prop := st ≤ 5#3

theorem lsuBv3_le5_cases (x : BitVec 3) (h : x ≤ 5#3) :
    x = 0#3 ∨ x = 1#3 ∨ x = 2#3 ∨ x = 3#3 ∨ x = 4#3 ∨ x = 5#3 := by bv_decide

theorem lsuT_state_legal_step (sm : BitVec 32) (s : LsuState) (i : LsuIn)
    (h : lsuLegalState s.state) : lsuLegalState (lsuStep sm s i).state := by
  show lsuNextState sm s i ≤ 5#3
  rcases lsuBv3_le5_cases s.state h with h0|h0|h0|h0|h0|h0
  -- 每个具体状态下先用 if_pos/if_neg 消去字面量状态比较（否则死分支的自由
  -- 变量会让 decide 拒收），再对剩余自由条件 cases 后 decide
  · unfold lsuNextState; rw [h0]
    rw [if_pos (by decide : (((0#3 : BitVec 3) == lsuSIdle) = true))]
    cases lsuFlushFire s i <;> cases lsuFifoFire s i <;> decide
  · unfold lsuNextState; rw [h0]
    rw [if_neg (by decide : ¬ (((1#3 : BitVec 3) == lsuSIdle) = true))]
    rw [if_pos (by decide : (((1#3 : BitVec 3) == lsuSSave) = true))]
    cases (s.regSave.ctrl.mem_cmd != 0#2) <;> cases lsuMshrFire s i <;>
      cases (lsuAllShared sm s.regSave i.csrTid i.csrPds i.csrNumw && !s.isFlush) <;> decide
  · unfold lsuNextState; rw [h0]
    rw [if_neg (by decide : ¬ (((2#3 : BitVec 3) == lsuSIdle) = true))]
    rw [if_neg (by decide : ¬ (((2#3 : BitVec 3) == lsuSSave) = true))]
    rw [if_pos (by decide : (((2#3 : BitVec 3) == lsuSShared) = true))]
    cases lsuSharedFire s i <;> cases (lsuCntDone s.cnt || lsuMaskNextEmpty s i) <;> decide
  · unfold lsuNextState; rw [h0]
    rw [if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSIdle) = true))]
    rw [if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSSave) = true))]
    rw [if_neg (by decide : ¬ (((3#3 : BitVec 3) == lsuSShared) = true))]
    rw [if_pos (by decide : (((3#3 : BitVec 3) == lsuSDcache) = true))]
    cases s.isFlush <;> cases lsuDcacheFire s i <;>
      cases (s.regSave.ctrl.atomic && (s.regSave.ctrl.aq || s.regSave.ctrl.rl)) <;>
      cases (lsuCntDone s.cnt || lsuMaskNextEmpty s i) <;> decide
  · unfold lsuNextState; rw [h0]
    rw [if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSIdle) = true))]
    rw [if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSSave) = true))]
    rw [if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSShared) = true))]
    rw [if_neg (by decide : ¬ (((4#3 : BitVec 3) == lsuSDcache) = true))]
    rw [if_pos (by decide : (((4#3 : BitVec 3) == lsuSD1) = true))]
    cases lsuDcacheFire s i <;> cases (s.regSave.ctrl.aq && s.regSave.ctrl.rl) <;>
      cases (lsuCntDone s.cnt || lsuMaskNextEmpty s i) <;> decide
  · unfold lsuNextState; rw [h0]
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSIdle) = true))]
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSSave) = true))]
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSShared) = true))]
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSDcache) = true))]
    rw [if_neg (by decide : ¬ (((5#3 : BitVec 3) == lsuSD1) = true))]
    rw [if_pos (by decide : (((5#3 : BitVec 3) == lsuSD2) = true))]
    cases lsuDcacheFire s i <;> cases (lsuCntDone s.cnt || lsuMaskNextEmpty s i) <;> decide

theorem lsuT_state_legal_run (sm : BitVec 32) (s : LsuState) (ins : List LsuIn)
    (h : lsuLegalState s.state) : lsuLegalState (lsuRun sm s ins).state := by
  induction ins generalizing s with
  | nil => exact h
  | cons j js ih => exact ih (lsuStep sm s j) (lsuT_state_legal_step sm s j h)

theorem lsuT_init_legal : lsuLegalState lsuInit.state := by decide

/- ========================================================================= -/
/- 6. LSU2WB（:490-529）：MSHR 响应到写回级的组合桥                            -/
/- ========================================================================= -/

/-- MSHROutput（MSHR.scala:17-20：tag + data） -/
structure LsuWbRsp where
  tag  : LsuMshrTag
  data : LsuRow

/-- WriteScalarCtrl 切片（operandCollector.scala:16-22，spike_info 略） -/
structure LsuWbX where
  warp_id  : BitVec 3
  reg_idxw : BitVec 8
  wxd      : Bool
  rd       : BitVec 32
deriving DecidableEq

/-- WriteVecCtrl 切片（operandCollector.scala:8-15，spike_info 略） -/
structure LsuWbV where
  warp_id  : BitVec 3
  reg_idxw : BitVec 8
  wvd      : Bool
  mask     : LsuMask32
  data     : LsuRow

/-- LSU2WB 单拍输入观测 -/
structure LsuWbIn where
  rspValid  : Bool
  rsp       : LsuWbRsp
  outXReady : Bool
  outVReady : Bool

-- 输出 bits（:496-504：两路都从 tag/data 直连）
def lsu2wbOutXBits (rsp : LsuWbRsp) : LsuWbX :=
  ⟨rsp.tag.warp_id, rsp.tag.reg_idxw, rsp.tag.wxd, rsp.data ⟨0, by decide⟩⟩
def lsu2wbOutVBits (rsp : LsuWbRsp) : LsuWbV :=
  ⟨rsp.tag.warp_id, rsp.tag.reg_idxw, rsp.tag.wfd, rsp.tag.mask, rsp.data⟩

-- 握手路由（:509-520）：wxd 优先于 wfd
def lsu2wbOutXValid (i : LsuWbIn) : Bool := i.rspValid && i.rsp.tag.wxd
def lsu2wbOutVValid (i : LsuWbIn) : Bool := i.rspValid && !i.rsp.tag.wxd && i.rsp.tag.wfd
def lsu2wbRspReady (i : LsuWbIn) : Bool :=
  if i.rsp.tag.wxd then i.outXReady
  else if i.rsp.tag.wfd then i.outVReady
  else i.rsp.tag.isWrite

section LsuWbTests

def lsuWbTag0 : LsuMshrTag :=
  ⟨1, false, true, 7, fun _ => true, false, false, fun _ => 15#4, false⟩
def lsuWbRsp0 : LsuWbRsp := ⟨lsuWbTag0, fun x => BitVec.ofNat 32 (0x100 + x.val)⟩

-- wxd 路由（:509-512）
example : lsu2wbOutXValid ⟨true, lsuWbRsp0, true, false⟩ = true := by decide
example : lsu2wbOutVValid ⟨true, lsuWbRsp0, true, false⟩ = false := by decide
example : lsu2wbRspReady ⟨true, lsuWbRsp0, true, false⟩ = true := by decide
example : lsu2wbRspReady ⟨true, lsuWbRsp0, false, true⟩ = false := by decide
example : (lsu2wbOutXBits lsuWbRsp0).rd = 0x100#32 := by decide
example : (lsu2wbOutXBits lsuWbRsp0).warp_id = 1#3 := by decide
-- wfd 路由（:513-516）
def lsuWbTagV : LsuMshrTag := { lsuWbTag0 with wxd := false, wfd := true }
example : lsu2wbOutVValid ⟨true, ⟨lsuWbTagV, fun _ => 0⟩, false, true⟩ = true := by decide
example : lsu2wbOutXValid ⟨true, ⟨lsuWbTagV, fun _ => 0⟩, true, true⟩ = false := by decide
example : (lsu2wbOutVBits ⟨lsuWbTagV, fun _ => 9#32⟩).data ⟨3, by decide⟩ = 9#32 := by decide
-- 写穿透：¬wxd ∧ ¬wfd 时 ready = isWrite（:520）
def lsuWbTagS : LsuMshrTag := { lsuWbTag0 with wxd := false, wfd := false, isWrite := true }
example : lsu2wbRspReady ⟨true, ⟨lsuWbTagS, fun _ => 0⟩, false, false⟩ = true := by decide
-- Q6：三者皆 0 时 ready=false（响应滞留）
def lsuWbTagBad : LsuMshrTag := { lsuWbTag0 with wxd := false, wfd := false, isWrite := false }
example : lsu2wbRspReady ⟨true, ⟨lsuWbTagBad, fun _ => 0⟩, true, true⟩ = false := by decide

end LsuWbTests

/-- 保真：out_x/out_v 的 bits 是 tag/data 的逐字段直连（:496-504） -/
theorem lsu2wb_outX_fidelity (rsp : LsuWbRsp) :
    (lsu2wbOutXBits rsp).warp_id = rsp.tag.warp_id ∧
    (lsu2wbOutXBits rsp).reg_idxw = rsp.tag.reg_idxw ∧
    (lsu2wbOutXBits rsp).wxd = rsp.tag.wxd ∧
    (lsu2wbOutXBits rsp).rd = rsp.data ⟨0, by decide⟩ := ⟨rfl, rfl, rfl, rfl⟩

theorem lsu2wb_outV_fidelity (rsp : LsuWbRsp) :
    (lsu2wbOutVBits rsp).mask = rsp.tag.mask ∧ (lsu2wbOutVBits rsp).data = rsp.data :=
  ⟨rfl, rfl⟩

/-- 消费只在 fire 发生：rsp.fire 的三路分解（:509-520）。
    这是"MSHR valid 回撤无害"的 LSU 侧证据：valid 高而 ready 低时无任何消费。 -/
theorem lsu2wb_rspFire_iff (i : LsuWbIn) :
    (i.rspValid && lsu2wbRspReady i) =
      (i.rspValid && i.rsp.tag.wxd && i.outXReady) ||
      (i.rspValid && !i.rsp.tag.wxd && i.rsp.tag.wfd && i.outVReady) ||
      (i.rspValid && !i.rsp.tag.wxd && !i.rsp.tag.wfd && i.rsp.tag.isWrite) := by
  obtain ⟨rv, ⟨⟨wid, wfd, wxd, ridx, mask, uns, isv, wo, iw⟩, data⟩, oxr, ovr⟩ := i
  simp only [lsu2wbRspReady]
  cases wxd <;> cases wfd <;> cases iw <;> cases rv <;> cases oxr <;> cases ovr <;> decide

/-- valid 回撤安全（Q13）：valid=1 且 ready=0 ⇒ 两路写回均无 fire，
    MSHR 条目既不被消费也不被释放（释放只在 MSHR 侧 fire 时发生） -/
theorem lsu2wb_retract_safe (i : LsuWbIn)
    (hv : i.rspValid = true) (hr : lsu2wbRspReady i = false) :
    (lsu2wbOutXValid i && i.outXReady) = false ∧
      (lsu2wbOutVValid i && i.outVReady) = false := by
  obtain ⟨rv, ⟨⟨wid, wfd, wxd, ridx, mask, uns, isv, wo, iw⟩, data⟩, oxr, ovr⟩ := i
  simp only [lsu2wbRspReady] at hr
  simp only [lsu2wbOutXValid, lsu2wbOutVValid]
  cases wxd <;> cases wfd <;> simp_all

/- ========================================================================= -/
/- 7. ShiftBoard（:587-604）与 LSUexe 门控（:572-579）                         -/
/-                                                                           -/
/-  ShiftBoard 在 LSUexe:572 例化 num_warp=8 份（活代码），depth=              -/
/-  lsu_num_entry_each_warp=4（parameters.scala:67）。taps 打包为             -/
/-  BitVec 4（bit b = taps(b)）。:598-602 的逐位递推等价于闭式：               -/
/-    左移入（left_move）：taps' = (taps <<< 1) ||| 1                          -/
/-    右移出（right_move）：taps' = taps >>> 1                                 -/
/-    否则保持。                                                               -/
/- ========================================================================= -/

/-- ShiftBoard 单拍转移（:598-602 的闭式形式） -/
def lsuSbStep (taps : BitVec 4) (l r : Bool) : BitVec 4 :=
  if l ^^ r then (if l then (taps <<< 1) ||| 1#4 else taps >>> 1) else taps

/-- full（:603）：taps(depth-1) -/
def lsuSbFull (taps : BitVec 4) : Bool := ((taps >>> 3) &&& 1#4) == 1#4

/-- empty（:604）：当拍移动后的 taps(0) 取反——组合地包含本拍入/出 -/
def lsuSbEmpty (taps : BitVec 4) (l r : Bool) : Bool :=
  !(((lsuSbStep taps l r) &&& 1#4) == 1#4)

section LsuSbTests

-- 推入序列：0 → 1 → 3 → 7 → 15
example : lsuSbStep 0#4 true false = 0b0001#4 := by decide
example : lsuSbStep 0b0001#4 true false = 0b0011#4 := by decide
example : lsuSbStep 0b0111#4 true false = 0b1111#4 := by decide
-- 弹出序列：15 → 7 → 3 → 1 → 0
example : lsuSbStep 0b1111#4 false true = 0b0111#4 := by decide
example : lsuSbStep 0b0011#4 false true = 0b0001#4 := by decide
-- 同拍进出保持
example : lsuSbStep 0b0011#4 true true = 0b0011#4 := by decide
example : lsuSbStep 0b0011#4 false false = 0b0011#4 := by decide
-- 满时推入饱和（上游已被 :578 门控，此为兜底行为）
example : lsuSbStep 0b1111#4 true false = 0b1111#4 := by decide
-- 空时弹出不欠数
example : lsuSbStep 0#4 false true = 0#4 := by decide
-- full/empty
example : lsuSbFull 0b1111#4 = true := by decide
example : lsuSbFull 0b0111#4 = false := by decide
example : lsuSbEmpty 0#4 false false = true := by decide
example : lsuSbEmpty 0#4 true false = false := by decide   -- 本拍推入后非空
example : lsuSbEmpty 0b0001#4 false true = true := by decide  -- 本拍弹出后空

end LsuSbTests

/-- 前缀不变式：taps 形如 2^k - 1（k ≤ 4），即 taps &&& (taps+1) = 0 -/
def lsuSbInv (taps : BitVec 4) : Prop := taps &&& (taps + 1#4) = 0#4

theorem lsuSbInv_step (taps : BitVec 4) (l r : Bool) (h : lsuSbInv taps) :
    lsuSbInv (lsuSbStep taps l r) := by
  simp only [lsuSbInv, lsuSbStep] at *
  cases l <;> cases r <;> simp_all <;> bv_decide

/-- full 当且仅当 4 项全满（前缀形下 taps=15） -/
theorem lsuSbFull_iff (taps : BitVec 4) (h : lsuSbInv taps) :
    lsuSbFull taps = true ↔ taps = 0b1111#4 := by
  simp only [lsuSbFull, lsuSbInv] at *
  constructor <;> intro h' <;> bv_decide

/-- 单方向移动的闭式（助证引理） -/
theorem lsuSbStep_push (t : BitVec 4) : lsuSbStep t true false = (t <<< 1) ||| 1#4 := rfl
theorem lsuSbStep_pop (t : BitVec 4) : lsuSbStep t false true = t >>> 1 := rfl

/-- 计数语义（前缀形下 toNat = 2^k - 1；纯 BitVec 形式，mod 16 下
    t + t + 1 即 2t+1）：推入未满 ⇒ 计数加一。
    注：本工具链 bv_decide 不支持含 toNat 的不等式/乘法目标，故用纯位向量形式。 -/
theorem lsuSbStep_push_count (taps : BitVec 4) (h : lsuSbInv taps)
    (hnf : lsuSbFull taps = false) :
    lsuSbStep taps true false = taps + taps + 1#4 := by
  simp only [lsuSbInv] at h
  simp only [lsuSbFull] at hnf
  rw [lsuSbStep_push]
  bv_decide

/-- 弹出非空 ⇒ 计数减一（纯 BitVec 形式，无溢出） -/
theorem lsuSbStep_pop_count (taps : BitVec 4) (h : lsuSbInv taps)
    (hne : taps ≠ 0#4) :
    lsuSbStep taps false true + lsuSbStep taps false true + 1#4 = taps := by
  simp only [lsuSbInv] at h
  rw [lsuSbStep_pop]
  bv_decide

/-- 满时推入饱和（不溢出到错误状态；上游 :578 门控保证不触发） -/
theorem lsuSbStep_push_full (taps : BitVec 4) (h : taps = 0b1111#4) :
    lsuSbStep taps true false = 0b1111#4 := by simp [lsuSbStep, h]

/-- 空时弹出仍为 0（不欠数；MSHR 每入必有出故系统内不触发） -/
theorem lsuSbStep_pop_empty (taps : BitVec 4) (h : taps = 0#4) :
    lsuSbStep taps false true = 0#4 := by simp [lsuSbStep, h]

/-- empty 的语义：当拍移动后为空 ⇔ 次态 taps = 0（前缀形下） -/
theorem lsuSbEmpty_iff (taps : BitVec 4) (l r : Bool) (h : lsuSbInv taps) :
    lsuSbEmpty taps l r = true ↔ lsuSbStep taps l r = 0#4 := by
  simp only [lsuSbEmpty, lsuSbStep, lsuSbInv] at *
  cases l <;> cases r <;> simp_all <;> bv_decide

/- ---- LSUexe 门控（:572-579）与 fence_end（:577） ---- -/

/-- 每 warp 的左移入信号（:574）：lsu_req.fire 且 wid 匹配 -/
def lsuSbLeftOf (reqFire : Bool) (reqWid b : BitVec 3) : Bool :=
  reqFire && (reqWid == b)

/-- 每 warp 的右移出信号（:575）：lsu_rsp.fire 且 warp_id 匹配 -/
def lsuSbRightOf (rspFire : Bool) (rspWid b : BitVec 3) : Bool :=
  rspFire && (rspWid == b)

/-- 八块 ShiftBoard 阵列的单拍转移（:572-576） -/
def lsuSbStepAll (boards : BitVec 3 → BitVec 4) (reqFire : Bool) (reqWid : BitVec 3)
    (rspFire : Bool) (rspWid : BitVec 3) : BitVec 3 → BitVec 4 :=
  fun b => lsuSbStep (boards b) (lsuSbLeftOf reqFire reqWid b) (lsuSbRightOf rspFire rspWid b)

/-- lsu_req.ready 的 full 门控（:578） -/
def lsuReqReady (boards : BitVec 3 → BitVec 4) (reqWid : BitVec 3) (fifoRdy : Bool) : Bool :=
  if lsuSbFull (boards reqWid) then false else fifoRdy

/-- lsu_req 向 InputFIFO 的 valid 门控（:579） -/
def lsuReqValidGated (boards : BitVec 3 → BitVec 4) (reqWid : BitVec 3) (reqValid : Bool) : Bool :=
  if lsuSbFull (boards reqWid) then false else reqValid

/-- fence_end（:577）：所有 warp 的 ShiftBoard 当拍后为空 -/
def lsuFenceEnd (boards : BitVec 3 → BitVec 4) (reqFire : Bool) (reqWid : BitVec 3)
    (rspFire : Bool) (rspWid : BitVec 3) : Bool :=
  (List.finRange 8).all (fun b =>
    lsuSbEmpty (boards (BitVec.ofNat 3 b.val)) (lsuSbLeftOf reqFire reqWid (BitVec.ofNat 3 b.val))
      (lsuSbRightOf rspFire rspWid (BitVec.ofNat 3 b.val)))

/-- 未命中 warp 的板子不变（:574-575 的 wid 匹配） -/
theorem lsuSbStepAll_other (boards : BitVec 3 → BitVec 4) (reqFire : Bool) (reqWid : BitVec 3)
    (rspFire : Bool) (rspWid b : BitVec 3)
    (hb1 : b ≠ reqWid) (hb2 : b ≠ rspWid) :
    lsuSbStepAll boards reqFire reqWid rspFire rspWid b = boards b := by
  have e1 : lsuSbLeftOf reqFire reqWid b = false := by
    simp [lsuSbLeftOf, Ne.symm hb1]
  have e2 : lsuSbRightOf rspFire rspWid b = false := by
    simp [lsuSbRightOf, Ne.symm hb2]
  simp [lsuSbStepAll, lsuSbStep, e1, e2]

/-- 门控正确性：目标 warp 满 ⇒ 当拍 lsu_req 不可能 fire（:578-579），
    故 ShiftBoard 的满时推入（lsuSbStep_push_full）系统内不可达 -/
theorem lsuReqReady_blocked (boards : BitVec 3 → BitVec 4) (reqWid : BitVec 3)
    (fifoRdy reqValid : Bool) (h : lsuSbFull (boards reqWid) = true) :
    lsuReqReady boards reqWid fifoRdy = false ∧
      lsuReqValidGated boards reqWid reqValid = false := by
  simp [lsuReqReady, lsuReqValidGated, h]

/- ========================================================================= -/
/- 8. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms lsuBex_byte
#print axioms lsuBex_half
#print axioms lsuBex_default
#print axioms lsuCntDone_false
#print axioms lsuPrioEncF_spec_set
#print axioms lsuMaskNext_pe
#print axioms lsuT_progress
#print axioms lsuT_progress_dcache
#print axioms lsuT_progress_shared
#print axioms lsuT_dcache_hold
#print axioms lsuT_dcache_irrevocable
#print axioms lsuT_shared_hold
#print axioms lsuT_ssave_hold
#print axioms lsuT_ssave_fire
#print axioms lsuT_ssave_entry
#print axioms lsuT_accept_mask_scalar
#print axioms lsuT_accept_aq
#print axioms lsuT_flush_accept
#print axioms lsuT_flush_opcode
#print axioms lsuT_entryID_hold
#print axioms lsuT_state_legal_step
#print axioms lsuT_state_legal_run
#print axioms lsu2wb_rspFire_iff
#print axioms lsu2wb_retract_safe
#print axioms lsuSbInv_step
#print axioms lsuSbFull_iff
#print axioms lsuSbStep_push_count
#print axioms lsuSbStep_pop_count
#print axioms lsuSbEmpty_iff
#print axioms lsuSbStepAll_other
#print axioms lsuReqReady_blocked
