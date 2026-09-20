/- ========================================================================= -/
/-                        CTA/WgBuffer.lean                                   -/
/-  WG 缓冲（wg_buffer）的 Lean 4 逐拍模型 + H-WGB 契约核销                    -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/wg_buffer.scala          -/
/-    （class wg_buffer :35-177，全文；RRPriorityEncoder 见 cta/utils.scala     -/
/-    :15-36）                                                                -/
/-  例化点：cta_scheduler.scala:117（wg_buffer_inst），:123-125 host 侧 init_ok -/
/-    门控，:127 接 allocator，:128 alloc_result 回流，:129 接 cu_interface。   -/
/-  参数（top/parameters.scala）：WG_BUFFER.NUM_ENTRIES=8 (:191)、              -/
/-    WG_ID_WIDTH=32 (:142)、DEBUG=true (:196，wg_id 字段存在）。               -/
/-                                                                           -/
/-  验证目标：核销 Contracts.lean 登记册 pending 条目 H-WGB                     -/
/-    （CtaScheduler.lean:265，CtasEventOk .hostNew 分支：`pending < 8`，       -/
/-    即 wg_buffer.scala:85 `io.host_wg_new.ready := wgram_wr_next.valid`      -/
/-    的反压恰好实现「hostNew ⟹ pending < NUM_ENTRIES」）。                     -/
/-    核销链：wgb_h_wgb_discharge（主定理）+ wgb_step_count（计数演化 =          -/
/-    抽象 pending 记账）+ wgb_pending_host/alloc（逐事件对应）。               -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 逐拍建模：状态 = 全部寄存器；step = 单拍纯函数（寄存器读一律旧值）。     -/
/-  D2. NUM_ENTRIES 固定为 8（:191），wgram 地址 3 位。                         -/
/-  D3. WG 信息抽象为不透明 tag : BitVec 32。依据：host→wgram1/wgram2→          -/
/-      alloc/cuinterface 全路径为纯连线透传（:62-66 写装配、:114-117 alloc     -/
/-      读、:132-134 cuinterface 读），无任何字段变换；wgram1/wgram2 同拍       -/
/-      同址写入（:90-93 同一 when），合并建模为单个 ram；wg_id（DEBUG=true）   -/
/-      并入 tag。字段级保真因此归约为 tag 保真。                               -/
/-  D4. 幽灵字段 ghost : Fin 8 → BitVec 32：记录「使该 entry 置 valid 的那次    -/
/-      host 写入」的 tag，仅用于陈述端到端数据完整性，无硬件对应物。           -/
/-  D5. RRPriorityEncoder 内联建模（utils.scala:15-36）：last 初值 =            -/
/-      initsel−1 = 0−1 回绕 = 7；输入全 0 时 out.bits 为 Don'tCare（:31        -/
/-      Mux 的 else 分支），本模型取 prioEnc(0)+last+1，全部使用点由 valid      -/
/-      门控（:85,:107 只在 fire 时消费 bits），不影响任何已证性质。            -/
/-  D6. 环境契约 WgbEnvOk：alloc_result 只指向「在驻且已移交 allocator」的      -/
/-      entry（valid∧alloc 置位，且不指向 alloc 输出寄存器中尚未被消费的        -/
/-      entry）。依据：allocator FSM 每消费一个 wgbuffer_wg_new 请求恰好回       -/
/-      一次结果（allocator.scala:218 ready=IDLE、:296；Allocator.lean          -/
/-      alcWgbufFire :246-247），故不会提前/重复/错位响应。                     -/
/-  D7. wgram1/wgram2 为 Chisel Mem（异步读，:55-56），8 项小存储具体建模       -/
/-      （Fin 8 → BitVec 32；AGENTS.md 大存储禁令针对的是求值爆炸，8 项无       -/
/-      此问题）。同拍同址读写不发生：写只落 invalid 槽，读只取 valid 槽。       -/
/-  D8. FIFO 降级说明：wg_buffer 并非严格 FIFO——供给（rdAct）顺序在无拒绝     -/
/-      轨迹上等于写入顺序（RR 双指针，数值测试 wgbT5），但**拒绝重试会破坏     -/
/-      accept 清除序的 FIFO 性**（Q-WGB6，反例测试 wgbT7）。CtaScheduler        -/
/-      抽象模型只消费 pending 计数、不消费顺序，故 H-WGB 核销不受影响；        -/
/-      「不丢（wgb_valid_persists）、不重（wgb_no_double_clear）、不溢出        -/
/-      （wgb_h_wgb + wgb_count_bounded）、数据完整（wgb_alloc_capture /         -/
/-      wgb_cuif_capture + 稳定性 wgb_alloc_stable / wgb_cuif_stable）」均        -/
/-      为机器证明；严格 FIFO 序本身被反例否定，不再追求 QueueModel 精化。      -/
/-                                                                           -/
/- ======================== 源码审查疑点（Q 区，上报主会话） ================== -/
/-  Q-WGB1. :157 `io.alloc_result.ready := Mux(accept, ...)`：ready 依赖        -/
/-      bits.accept。Decoupled 纪律下 bits 在 valid∧!ready 期间须稳定，此时      -/
/-      无害；属风格气味，记录在案。                                            -/
/-  Q-WGB2. :175 断言只查 rstmask1∧rstmask2∧setmask 的**三重** AND，弱于注释    -/
/-      声称的「两两互斥」：rstmask2∧setmask 两位重合时断言不触发（set 覆盖       -/
/-      rst2，静默）。WgbEnvOk 下该重合不可达（rst2 目标 alloc=1、set 目标       -/
/-      alloc=0），无活 bug；但断言验证强度不足，建议改为两两断言。              -/
/-  Q-WGB3. :176 accept 清除 valid[X] 但**不清** alloc[X]（alloc 残留 1，至      -/
/-      该槽被重写时由 rstmask1 顺带清除）；rd 选择经 valid 门控，无害。模型      -/
/-      已忠实反映（wgbStep 的 alloc 更新无 accept 项），wgbT7 轨迹可见。        -/
/-  Q-WGB4. :68-69,:136-137 注释：Verilator 仿真中 wgram2 写端口第 238 bit       -/
/-      恒为 1（疑似仿真器 bug），以无用字段 useless 占位防扩散。非 RTL 逻辑     -/
/-      问题；提示仿真环境可信度风险，记录在案。                                -/
/-  Q-WGB5. alloc_result 无内部防重/防错护：若 allocator 对同一 addr 重复        -/
/-      accept，会清掉**重新驻留**的 entry 并把旧数据送 cuinterface（WG 静默     -/
/-      丢失）。依赖 allocator「每请求恰一响应」纪律，已并入 WgbEnvOk（D6）。    -/
/-  Q-WGB6. 拒绝重试使出队序 ≠ 入队序：A 先供给被拒、B 后供给先被接受 ⟹ B       -/
/-      先于 A 清除并送达 cuinterface（反例测试 wgbT7 钉死）。非 bug（协议       -/
/-      允许重试），但 wg_buffer 不能当严格 FIFO 用；CtaScheduler 抽象只用       -/
/-      pending 计数，不受影响。                                               -/
/- ========================================================================= -/

import Ventus.CTA.CtaScheduler
import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常量与位操作辅助                                                         -/
/- ========================================================================= -/

/-- WG_BUFFER.NUM_ENTRIES（parameters.scala:191） -/
def wgbNUM_ENTRIES : Nat := 8

/-- 取 v 的第 a 位（移位形式，避开变量下标 getLsbD 的 bv_decide 坑） -/
def wgbBit (v : BitVec 8) (a : BitVec 3) : Bool := ((v >>> a) &&& 1#8) != 0#8

/-- 3 位地址 → Fin 8 -/
def wgbFin (a : BitVec 3) : Fin 8 := ⟨a.toNat, a.isLt⟩

/-- valid 位图的 popcount = 缓冲中在驻 WG 数（抽象模型的 pending，D4 对照） -/
def wgbCount (v : BitVec 8) : Nat :=
  (if v.getLsbD 0 then 1 else 0) + (if v.getLsbD 1 then 1 else 0) +
  (if v.getLsbD 2 then 1 else 0) + (if v.getLsbD 3 then 1 else 0) +
  (if v.getLsbD 4 then 1 else 0) + (if v.getLsbD 5 then 1 else 0) +
  (if v.getLsbD 6 then 1 else 0) + (if v.getLsbD 7 then 1 else 0)

/-- Fin 8 函数写更新（同 cuifUpd 惯例） -/
def wgbUpd (f : Fin 8 → α) (g : Fin 8) (v : α) : Fin 8 → α :=
  fun x => if x = g then v else f x

/- ========================================================================= -/
/- 2. RRPriorityEncoder（utils.scala:15-36，n=8 内联特化）                     -/
/- ========================================================================= -/

/-- 循环右移 k 位（:28 `(in >> shift) | (in << (n - shift))`；k=0 时左移 8 = 0） -/
def wgbRotR (x : BitVec 8) (k : Nat) : BitVec 8 := (x >>> k) ||| (x <<< (8 - k))

/-- PriorityEncoder：最低置位位下标；x=0 时落入 7（Don'tCare，D5） -/
def wgbPrioEnc (x : BitVec 8) : BitVec 3 :=
  if x &&& 1#8 != 0#8 then 0 else if x &&& 2#8 != 0#8 then 1
  else if x &&& 4#8 != 0#8 then 2 else if x &&& 8#8 != 0#8 then 3
  else if x &&& 16#8 != 0#8 then 4 else if x &&& 32#8 != 0#8 then 5
  else if x &&& 64#8 != 0#8 then 6 else 7

/-- RR 选择结果（:28-31）：轮转后最低置位位映射回原下标；valid 半为 x ≠ 0（:30） -/
def wgbRrPick (last : BitVec 3) (x : BitVec 8) : BitVec 3 :=
  wgbPrioEnc (wgbRotR x ((last + 1).toNat)) + (last + 1)

/- ========================================================================= -/
/- 3. 状态、输入、组合逻辑、单拍转移                                            -/
/- ========================================================================= -/

/-- wg_buffer 全部寄存器状态（+ ghost，D4） -/
structure WgbState where
  valid       : BitVec 8            -- :57 wgram_valid
  alloc       : BitVec 8            -- :58 wgram_alloc
  wrLast      : BitVec 3            -- :72 wgram_wr_next 的 RR last（:23 初值 0-1=7）
  rdLast      : BitVec 3            -- :73 wgram1_rd_next 的 RR last
  ram         : Fin 8 → BitVec 32   -- :55-56 wgram1/wgram2 合并（D3）
  ghost       : Fin 8 → BitVec 32   -- D4 幽灵：使该 entry 置 valid 的 host tag
  allocValidR : Bool                -- :100 alloc_wg_new_valid_r
  allocDataR  : BitVec 32           -- :111 wgram1_rd_data（tag 化，D3）
  allocAddrR  : BitVec 3            -- :112 wgram1_rd_data_addr
  cuifValidR  : Bool                -- :128 cuinterface_new_wg_valid_r
  cuifDataR   : BitVec 32           -- :133 wgram2_rd_data（tag 化，D3）

/-- 复位值（:57-58 RegInit 0；:23 last 初值回绕为 7；:100,:128 RegInit false） -/
def wgbInit : WgbState where
  valid := 0#8; alloc := 0#8; wrLast := 7#3; rdLast := 7#3
  ram := fun _ => 0#32; ghost := fun _ => 0#32
  allocValidR := false; allocDataR := 0#32; allocAddrR := 0#3
  cuifValidR := false; cuifDataR := 0#32

/-- 每拍环境输入（四个 Decoupled 对端） -/
structure WgbInputs where
  hostValid  : Bool := false        -- :37 io.host_wg_new.valid（上游已含 init_ok 门控）
  hostTag    : BitVec 32 := 0#32    -- :37 io.host_wg_new.bits（tag 化，D3）
  allocReady : Bool := false        -- :38 io.alloc_wg_new.ready（allocator :218）
  resValid   : Bool := false        -- :39 io.alloc_result.valid
  resAccept  : Bool := false        -- :39 io.alloc_result.bits.accept
  resAddr    : BitVec 3 := 0#3      -- :39 io.alloc_result.bits.wgram_addr
  cuifReady  : Bool := false        -- :40 io.cuinterface_wg_new.ready

/-- :85 host ready = 存在空闲槽 -/
def wgbHostReady (s : WgbState) : Bool := (~~~s.valid) != 0#8
/-- :72 写地址选择（在 ~valid 中 RR） -/
def wgbWrAddr (s : WgbState) : BitVec 3 := wgbRrPick s.wrLast (~~~s.valid)
/-- :89 host 写入生效（wgram_wr_act = wgram_wr_next.fire） -/
def wgbHostFire (s : WgbState) (i : WgbInputs) : Bool := i.hostValid && wgbHostReady s

/-- :73 读候选 = valid ∧ ¬alloc -/
def wgbRdCand (s : WgbState) : BitVec 8 := s.valid &&& ~~~s.alloc
/-- :73 读地址选择 -/
def wgbRdAddr (s : WgbState) : BitVec 3 := wgbRrPick s.rdLast (wgbRdCand s)
/-- :107 读允许 = 输出寄存器空或本拍被消费 -/
def wgbRdAllowed (s : WgbState) (i : WgbInputs) : Bool := !s.allocValidR || i.allocReady
/-- :108 读生效（wgram1_rd_act = wgram1_rd_next.fire） -/
def wgbRdAct (s : WgbState) (i : WgbInputs) : Bool := (wgbRdCand s != 0#8) && wgbRdAllowed s i

/-- :150 cuinterface 通路不堵 = 输出寄存器空或本拍被消费 -/
def wgbClearReady (s : WgbState) (i : WgbInputs) : Bool := !s.cuifValidR || i.cuifReady
/-- :157 alloc_result.ready（accept 时看 cuif 通路，reject 恒 true；Q-WGB1） -/
def wgbResReady (s : WgbState) (i : WgbInputs) : Bool :=
  if i.resAccept = true then wgbClearReady s i else true
/-- alloc_result.fire -/
def wgbResFire (s : WgbState) (i : WgbInputs) : Bool := i.resValid && wgbResReady s i
/-- :151 accept：清 valid + 读 wgram2 送 cuinterface（wgram_rd2_clear_act） -/
def wgbClearAct (s : WgbState) (i : WgbInputs) : Bool := wgbResFire s i && i.resAccept
/-- :154 reject：只清 alloc 位，允许下轮重试（wgram_alloc_clear_act） -/
def wgbAllocClrAct (s : WgbState) (i : WgbInputs) : Bool := wgbResFire s i && !i.resAccept

/-- 对 allocator 的可观测输出 -/
def wgbAllocOutValid (s : WgbState) : Bool := s.allocValidR      -- :101
def wgbAllocOutTag (s : WgbState) : BitVec 32 := s.allocDataR    -- :114-115
def wgbAllocOutAddr (s : WgbState) : BitVec 3 := s.allocAddrR    -- :116
/-- 对 cuinterface 的可观测输出 -/
def wgbCuifOutValid (s : WgbState) : Bool := s.cuifValidR        -- :129
def wgbCuifOutTag (s : WgbState) : BitVec 32 := s.cuifDataR      -- :134

/-- :163 valid 置位掩码 -/
def wgbValidSetMask (s : WgbState) (i : WgbInputs) : BitVec 8 :=
  if wgbHostFire s i = true then (1#8 <<< wgbWrAddr s) else 0#8
/-- :164 valid 清除掩码 -/
def wgbValidRstMask (s : WgbState) (i : WgbInputs) : BitVec 8 :=
  if wgbClearAct s i = true then (1#8 <<< i.resAddr) else 0#8

/-- 单拍转移（Chisel 语义：寄存器读旧值；掩码更新 :168,:176；RegEnable :111-112,:133） -/
def wgbStep (s : WgbState) (i : WgbInputs) : WgbState where
  valid := (s.valid &&& ~~~(wgbValidRstMask s i)) ||| wgbValidSetMask s i   -- :168
  alloc := ((s.alloc &&& ~~~(if wgbHostFire s i = true then (1#8 <<< wgbWrAddr s) else 0#8)) &&&
              ~~~(if wgbAllocClrAct s i = true then (1#8 <<< i.resAddr) else 0#8)) |||
             (if wgbRdAct s i = true then (1#8 <<< wgbRdAddr s) else 0#8)   -- :176（无 accept 清除项，Q-WGB3）
  wrLast := if wgbHostFire s i = true then wgbWrAddr s else s.wrLast        -- :33-34
  rdLast := if wgbRdAct s i = true then wgbRdAddr s else s.rdLast           -- :33-34
  ram := if wgbHostFire s i = true then wgbUpd s.ram (wgbFin (wgbWrAddr s)) i.hostTag else s.ram   -- :90-93
  ghost := if wgbHostFire s i = true then wgbUpd s.ghost (wgbFin (wgbWrAddr s)) i.hostTag else s.ghost  -- D4
  allocValidR := if wgbRdAct s i = true then true                            -- :102-103
                 else (if i.allocReady = true then false else s.allocValidR)
  allocDataR := if wgbRdAct s i = true then s.ram (wgbFin (wgbRdAddr s)) else s.allocDataR  -- :111
  allocAddrR := if wgbRdAct s i = true then wgbRdAddr s else s.allocAddrR    -- :112
  cuifValidR := if wgbClearAct s i = true then true                          -- :130-131
                else (if i.cuifReady = true then false else s.cuifValidR)
  cuifDataR := if wgbClearAct s i = true then s.ram (wgbFin i.resAddr) else s.cuifDataR     -- :132-133

/-- 多拍运行 -/
def wgbRun (s : WgbState) (ins : List WgbInputs) : WgbState := ins.foldl wgbStep s

/- ========================================================================= -/
/- 4. 环境契约（D6）与数据完整性不变量（D4）                                     -/
/- ========================================================================= -/

/-- 【WgbEnvOk / D6】alloc_result 只指向在驻且已移交 allocator 的 entry -/
def WgbEnvOk (s : WgbState) (i : WgbInputs) : Prop :=
  i.resValid = true →
    wgbBit s.valid i.resAddr = true ∧ wgbBit s.alloc i.resAddr = true ∧
    (s.allocValidR = true → s.allocAddrR ≠ i.resAddr)

/-- 【数据完整性不变量】在驻 entry 的 ram 内容 = 使其驻留的那次 host 写入的 tag -/
def WgbInv (s : WgbState) : Prop :=
  ∀ a : BitVec 3, wgbBit s.valid a = true → s.ram (wgbFin a) = s.ghost (wgbFin a)

/-- 抽象 pending 的具体化：wg_buffer 在驻计数（对照 CtasState.pending） -/
def wgbPending (s : WgbState) : Nat := wgbCount s.valid

/- ========================================================================= -/
/- 5. 数值回归测试（先测试后证明；全部 `by decide`，无 native_decide 公理）      -/
/- ========================================================================= -/

section WgbRegressionTests

-- T0：RR 选择器语义（utils.scala:28-31 的数值核对：轮转 + 回绕）
theorem wgbT0_rr_fresh : wgbRrPick 7#3 0b00001100#8 = 2#3 := by decide   -- 初值 last=7 → 最低位
theorem wgbT0_rr_advance : wgbRrPick 2#3 0b00001100#8 = 3#3 := by decide -- 从 last+1 起
theorem wgbT0_rr_wrap : wgbRrPick 3#3 0b00001100#8 = 2#3 := by decide    -- 回绕
theorem wgbT0_rr_wrap2 : wgbRrPick 0#3 0b10000001#8 = 7#3 := by decide

-- T1：复位态（:57-58,:100,:128 RegInit；:23 last=7）
theorem wgbT1_init_ready : wgbHostReady wgbInit = true := by decide
theorem wgbT1_init_count : wgbCount wgbInit.valid = 0 := by decide
theorem wgbT1_init_allocValid : wgbAllocOutValid wgbInit = false := by decide
theorem wgbT1_init_cuifValid : wgbCuifOutValid wgbInit = false := by decide
theorem wgbT1_init_last : wgbInit.wrLast = 7#3 ∧ wgbInit.rdLast = 7#3 := by decide

-- T2：单写落入槽 0（:72,:85-93）
theorem wgbT2_write_slot0 :
    let s1 := wgbStep wgbInit { hostValid := true, hostTag := 0xAAAA#32 }
    wgbHostFire wgbInit { hostValid := true, hostTag := 0xAAAA#32 } = true ∧
    s1.valid = 0b00000001#8 ∧ wgbCount s1.valid = 1 ∧ s1.wrLast = 0#3 ∧
    s1.ram (wgbFin 0#3) = 0xAAAA#32 ∧ s1.ghost (wgbFin 0#3) = 0xAAAA#32 := by decide

-- T3：连写 8 个填满 → 反压（H-WGB 数值面：满时 ready=0）
def wgbT3Trace : List WgbInputs :=
  [ { hostValid := true, hostTag := 0x10#32 }, { hostValid := true, hostTag := 0x11#32 }
  , { hostValid := true, hostTag := 0x12#32 }, { hostValid := true, hostTag := 0x13#32 }
  , { hostValid := true, hostTag := 0x14#32 }, { hostValid := true, hostTag := 0x15#32 }
  , { hostValid := true, hostTag := 0x16#32 }, { hostValid := true, hostTag := 0x17#32 } ]
theorem wgbT3_full_backpressure :
    let s8 := wgbRun wgbInit wgbT3Trace
    s8.valid = 0xFF#8 ∧ wgbCount s8.valid = 8 ∧ wgbHostReady s8 = false := by decide
-- T3b：填满再写不 fire（不溢出数值面）
theorem wgbT3b_full_no_fire :
    wgbHostFire (wgbRun wgbInit wgbT3Trace) { hostValid := true, hostTag := 0x99#32 } = false := by decide

-- T4：写→供给→接受→cuinterface 端到端（tag 保真数值面）
def wgbT4Trace : List WgbInputs :=
  [ { hostValid := true, hostTag := 0xA0#32 }                                   -- c1 写
  , { allocReady := true }                                                      -- c2 供给入寄存器
  , { allocReady := true }                                                      -- c3 alloc 消费
  , { resValid := true, resAccept := true, resAddr := 0#3, cuifReady := true }  -- c4 接受
  , { cuifReady := true } ]                                                     -- c5 cuif 消费
theorem wgbT4_offer_capture :
    let s2 := wgbRun wgbInit (wgbT4Trace.take 2)
    s2.allocValidR = true ∧ s2.allocDataR = 0xA0#32 ∧ s2.allocAddrR = 0#3 := by decide
theorem wgbT4_accept_to_cuif :
    let s4 := wgbRun wgbInit (wgbT4Trace.take 4)
    s4.cuifValidR = true ∧ s4.cuifDataR = 0xA0#32 ∧ s4.valid = 0#8 ∧ wgbCount s4.valid = 0 := by decide
theorem wgbT4_drain :
    (wgbRun wgbInit wgbT4Trace).cuifValidR = false := by decide

-- T5：无拒绝时供给顺序 = 写入顺序（RR 双指针，wgbT7 的对照组）
def wgbT5Trace : List WgbInputs :=
  [ { hostValid := true, hostTag := 0xB0#32 }                        -- c1 写槽0
  , { hostValid := true, hostTag := 0xB1#32 }                        -- c2 写槽1；供给槽0入寄存器
  , { hostValid := true, hostTag := 0xB2#32 }                        -- c3 写槽2（alloc 停滞）
  , { allocReady := true }                                           -- c4 发 t0；供给槽1
  , { allocReady := true }                                           -- c5 发 t1；供给槽2
  , { allocReady := true } ]                                         -- c6 发 t2
theorem wgbT5_rr_write_order : (wgbRun wgbInit (wgbT5Trace.take 3)).wrLast = 2#3 := by decide
theorem wgbT5_rr_offer_order :
    let s3 := wgbRun wgbInit (wgbT5Trace.take 3)
    let s4 := wgbRun wgbInit (wgbT5Trace.take 4)
    let s5 := wgbRun wgbInit (wgbT5Trace.take 5)
    (s3.allocDataR = 0xB0#32 ∧ s3.allocAddrR = 0#3) ∧
    (s4.allocDataR = 0xB1#32 ∧ s4.allocAddrR = 1#3) ∧
    (s5.allocDataR = 0xB2#32 ∧ s5.allocAddrR = 2#3) := by decide

-- T6：拒绝后重试（:154 alloc 位清除 → 重新可被选择）
def wgbT6Trace : List WgbInputs :=
  [ { hostValid := true, hostTag := 0xC0#32 }                        -- c1 写
  , { allocReady := true }                                           -- c2 供给入寄存器
  , { allocReady := true }                                           -- c3 alloc 消费
  , { resValid := true, resAccept := false, resAddr := 0#3 }         -- c4 拒绝（alloc 位清）
  , { allocReady := true } ]                                         -- c5 重新供给同槽
theorem wgbT6_reject_keeps_valid :
    let s4 := wgbRun wgbInit (wgbT6Trace.take 4)
    s4.valid = 0b00000001#8 ∧ s4.alloc = 0#8 := by decide
theorem wgbT6_reoffer :
    let s5 := wgbRun wgbInit wgbT6Trace
    s5.allocValidR = true ∧ s5.allocDataR = 0xC0#32 ∧ s5.allocAddrR = 0#3 := by decide

-- T7：【Q-WGB6 反例】拒绝重试使出队序 ≠ 入队序（写入 A,B；接受 B 先于 A）
def wgbT7Trace : List WgbInputs :=
  [ { hostValid := true, hostTag := 0xAA#32 }                        -- c1 写 A（槽0）
  , { hostValid := true, hostTag := 0xBB#32, allocReady := true }    -- c2 写 B（槽1）；供给 A
  , { allocReady := true }                                           -- c3 发 A；供给 B
  , { allocReady := true }                                           -- c4 发 B
  , { resValid := true, resAccept := false, resAddr := 0#3 }         -- c5 拒绝 A
  , { allocReady := true }                                           -- c6 重新供给 A
  , { allocReady := true }                                           -- c7 再发 A
  , { resValid := true, resAccept := true, resAddr := 1#3, cuifReady := true }  -- c8 接受 B（先出队）
  , { cuifReady := true }                                            -- c9 cuif 消费 B
  , { resValid := true, resAccept := true, resAddr := 0#3, cuifReady := true } ] -- c10 接受 A
theorem wgbT7_reorder_witness :
    let s8 := wgbRun wgbInit (wgbT7Trace.take 8)
    let s10 := wgbRun wgbInit wgbT7Trace
    s8.cuifDataR = 0xBB#32 ∧ s8.valid = 0b00000001#8 ∧     -- B（后写）先出队
    s10.cuifDataR = 0xAA#32 ∧ s10.valid = 0#8 ∧ wgbCount s10.valid = 0 := by decide

-- T8：同拍写 + 接受清除不同槽：计数不变（:163-168 掩码代数）
theorem wgbT8_simul_write_accept :
    let s7 := wgbRun wgbInit (wgbT7Trace.take 7)      -- valid=0b11, alloc=0b11
    let s8 := wgbStep s7 { hostValid := true, hostTag := 0xCC#32,
                           resValid := true, resAccept := true, resAddr := 1#3, cuifReady := true }
    wgbCount s7.valid = 2 ∧ wgbCount s8.valid = 2 ∧ s8.valid = 0b00000101#8 ∧
    s8.ram (wgbFin 2#3) = 0xCC#32 ∧ s8.cuifDataR = 0xBB#32 := by decide

-- T9：反压稳定性（Irrevocable 数值面）
theorem wgbT9_alloc_stall :
    let s2 := wgbRun wgbInit [ { hostValid := true, hostTag := 0xDD#32 }, { allocReady := false } ]
    let s3 := wgbStep s2 { allocReady := false }
    s2.allocValidR = true ∧ wgbRdAct s2 { allocReady := false } = false ∧
    s3.allocValidR = true ∧ s3.allocDataR = 0xDD#32 ∧ s3.allocAddrR = 0#3 := by decide
theorem wgbT9_cuif_stall :
    let s8 := wgbRun wgbInit (wgbT7Trace.take 8)      -- cuifValidR=1 持 B
    let i : WgbInputs := { resValid := true, resAccept := true, resAddr := 0#3, cuifReady := false }
    let s9 := wgbStep s8 i
    wgbResReady s8 i = false ∧ wgbClearAct s8 i = false ∧
    s9.cuifValidR = true ∧ s9.cuifDataR = 0xBB#32 ∧ s9.valid = s8.valid := by decide

end WgbRegressionTests

/- ========================================================================= -/
/- 6. 位图桥接引理（全部 `by decide` 穷举，无 bv_decide LRAT 公理）              -/
/- ========================================================================= -/

theorem wgb_bne0 : ∀ v : BitVec 8, (v != 0#8) = true ↔ v ≠ 0#8 := by decide
theorem wgb_not_allOnes : ∀ v : BitVec 8, ~~~v ≠ 0#8 ↔ v ≠ 0xFF#8 := by decide

/-- Bool && 拆分（本工具链 Bool.and_eq_true 为 Prop 等式，此处用判定式版本） -/
theorem wgb_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- RR 选中的位必为置位位（utils.scala:30-31 的正确性半） -/
theorem wgb_rrPick_mem :
    ∀ (last : BitVec 3) (x : BitVec 8), x ≠ 0#8 → wgbBit x (wgbRrPick last x) = true := by decide

theorem wgbBit_not : ∀ (v : BitVec 8) (a : BitVec 3),
    wgbBit (~~~v) a = true ↔ wgbBit v a = false := by decide
/-- （三变量 2^19 超出内核 decide 心跳，用 bv_decide；LRAT trust 公理见末节审计） -/
theorem wgbBit_and_true : ∀ (v w : BitVec 8) (a : BitVec 3),
    wgbBit (v &&& w) a = true → wgbBit v a = true := by
  intro v w a h; unfold wgbBit at *; bv_decide
theorem wgbBit_zero : ∀ a : BitVec 3, wgbBit 0#8 a = false := by decide
theorem wgbBit_set_self : ∀ (v : BitVec 8) (x : BitVec 3),
    wgbBit (v ||| (1#8 <<< x)) x = true := by decide
theorem wgbBit_set_ne : ∀ (v : BitVec 8) (a x : BitVec 3),
    a ≠ x → wgbBit (v ||| (1#8 <<< x)) a = wgbBit v a := by decide
theorem wgbBit_clear_self : ∀ (v : BitVec 8) (x : BitVec 3),
    wgbBit (v &&& ~~~(1#8 <<< x)) x = false := by decide
theorem wgbBit_clear_ne : ∀ (v : BitVec 8) (a x : BitVec 3),
    a ≠ x → wgbBit (v &&& ~~~(1#8 <<< x)) a = wgbBit v a := by decide

theorem wgb_and_allOnes : ∀ v : BitVec 8, v &&& ~~~(0#8) = v := by decide
theorem wgb_or_zero : ∀ v : BitVec 8, v ||| 0#8 = v := by decide

/-- wgbFin 单射（3 位地址不同则 Fin 8 不同） -/
theorem wgbFin_ne : ∀ a b : BitVec 3, a ≠ b → wgbFin a ≠ wgbFin b := by decide

theorem wgbBit_ne_of {v : BitVec 8} {a b : BitVec 3}
    (h0 : wgbBit v a = false) (h1 : wgbBit v b = true) : a ≠ b := by
  intro he; subst he; simp [h0] at h1

theorem wgbCount_le : ∀ v : BitVec 8, wgbCount v ≤ 8 := by decide
theorem wgbCount_eq8_iff : ∀ v : BitVec 8, wgbCount v = 8 ↔ v = 0xFF#8 := by decide
theorem wgbCount_pos_of_bit : ∀ (v : BitVec 8) (a : BitVec 3),
    wgbBit v a = true → 1 ≤ wgbCount v := by decide
/-- 写入一个空闲位：计数 +1 -/
theorem wgbCount_set : ∀ (v : BitVec 8) (a : BitVec 3),
    wgbBit v a = false → wgbCount (v ||| (1#8 <<< a)) = wgbCount v + 1 := by decide
/-- 清除一个在驻位：计数 −1 -/
theorem wgbCount_clear : ∀ (v : BitVec 8) (a : BitVec 3),
    wgbBit v a = true → wgbCount (v &&& ~~~(1#8 <<< a)) = wgbCount v - 1 := by decide

/- ========================================================================= -/
/- 7. 投影展开引理                                                             -/
/- ========================================================================= -/

theorem wgbStep_valid (s : WgbState) (i : WgbInputs) :
    (wgbStep s i).valid =
      (s.valid &&& ~~~(wgbValidRstMask s i)) ||| wgbValidSetMask s i := rfl
theorem wgbStep_alloc (s : WgbState) (i : WgbInputs) :
    (wgbStep s i).alloc =
      ((s.alloc &&& ~~~(if wgbHostFire s i = true then (1#8 <<< wgbWrAddr s) else 0#8)) &&&
         ~~~(if wgbAllocClrAct s i = true then (1#8 <<< i.resAddr) else 0#8)) |||
        (if wgbRdAct s i = true then (1#8 <<< wgbRdAddr s) else 0#8) := rfl
theorem wgbStep_ram (s : WgbState) (i : WgbInputs) :
    (wgbStep s i).ram =
      if wgbHostFire s i = true then wgbUpd s.ram (wgbFin (wgbWrAddr s)) i.hostTag else s.ram := rfl
theorem wgbStep_ghost (s : WgbState) (i : WgbInputs) :
    (wgbStep s i).ghost =
      if wgbHostFire s i = true then wgbUpd s.ghost (wgbFin (wgbWrAddr s)) i.hostTag else s.ghost := rfl

theorem wgbSetMask_eq (s : WgbState) (i : WgbInputs) (h : wgbHostFire s i = true) :
    wgbValidSetMask s i = 1#8 <<< wgbWrAddr s := by simp [wgbValidSetMask, h]
theorem wgbSetMask_zero (s : WgbState) (i : WgbInputs) (h : ¬(wgbHostFire s i = true)) :
    wgbValidSetMask s i = 0#8 := by simp [wgbValidSetMask, h]
theorem wgbRstMask_eq (s : WgbState) (i : WgbInputs) (h : wgbClearAct s i = true) :
    wgbValidRstMask s i = 1#8 <<< i.resAddr := by simp [wgbValidRstMask, h]
theorem wgbRstMask_zero (s : WgbState) (i : WgbInputs) (h : ¬(wgbClearAct s i = true)) :
    wgbValidRstMask s i = 0#8 := by simp [wgbValidRstMask, h]

/-- host fire ⇒ host ready（&& 拆分） -/
theorem wgbHostFire_ready {s : WgbState} {i : WgbInputs} (h : wgbHostFire s i = true) :
    wgbHostReady s = true := (wgb_and_true h).2

/-- host fire ⇒ 写入槽原为空闲（RR 在 ~valid 中选择） -/
theorem wgbHostFire_bit_free {s : WgbState} {i : WgbInputs} (h : wgbHostFire s i = true) :
    wgbBit s.valid (wgbWrAddr s) = false :=
  (wgbBit_not _ _).1 (wgb_rrPick_mem _ _ ((wgb_bne0 _).1 (wgbHostFire_ready h)))

/-- clearAct ⇒ alloc_result.valid（& 拆分） -/
theorem wgbClearAct_resValid {s : WgbState} {i : WgbInputs} (h : wgbClearAct s i = true) :
    i.resValid = true :=
  (wgb_and_true (wgb_and_true h).1).1

/-- clearAct ⇒ 清除槽在驻（经 WgbEnvOk） -/
theorem wgbClearAct_bit_valid {s : WgbState} {i : WgbInputs} (henv : WgbEnvOk s i)
    (h : wgbClearAct s i = true) : wgbBit s.valid i.resAddr = true :=
  (henv (wgbClearAct_resValid h)).1

/- ========================================================================= -/
/- 8. H-WGB 核销：反压 ⟺ 计数 < 8                                              -/
/- ========================================================================= -/

/-- 【H-WGB 组合形式】host ready ⟺ 在驻计数 < NUM_ENTRIES=8（wg_buffer.scala:85） -/
theorem wgb_hostReady_iff_count (s : WgbState) :
    wgbHostReady s = true ↔ wgbCount s.valid < 8 := by
  have hle := wgbCount_le s.valid
  constructor
  · intro h
    have hff : s.valid ≠ 0xFF#8 := (wgb_not_allOnes _).1 ((wgb_bne0 _).1 h)
    have hc8 : wgbCount s.valid ≠ 8 := fun hc => hff ((wgbCount_eq8_iff _).1 hc)
    omega
  · intro h
    have hc8 : wgbCount s.valid ≠ 8 := by omega
    have hff : s.valid ≠ 0xFF#8 := fun hv => hc8 ((wgbCount_eq8_iff _).2 hv)
    exact (wgb_bne0 _).2 ((wgb_not_allOnes _).2 hff)

/-- 【H-WGB 核销主定理】host 事务生效 ⟹ 当拍在驻计数 < 8：
    即 CtasEventOk.hostNew 前提 `pending < ctasWGBUF_ENTRIES`（CtaScheduler.lean:265）
    在 wg_buffer 上的具体化——ready 由 ~valid 的 RR 编码器 valid 半直接给出（:85）。 -/
theorem wgb_h_wgb_discharge (s : WgbState) (i : WgbInputs) (h : wgbHostFire s i = true) :
    wgbPending s < ctasWGBUF_ENTRIES :=
  (wgb_hostReady_iff_count s).1 (wgbHostFire_ready h)

/-- 不溢出：8 位位图 popcount 恒 ≤ 8 -/
theorem wgb_count_bounded (s : WgbState) : wgbCount s.valid ≤ 8 := wgbCount_le _

/-- 计数演化：写 +1、accept 清除 −1（同拍不同槽则抵消），
    与抽象 ctasStep 的 hostNew(pending+1)/alloc(pending−1) 记账一致 -/
theorem wgb_step_count (s : WgbState) (i : WgbInputs) (henv : WgbEnvOk s i) :
    wgbCount (wgbStep s i).valid =
      wgbCount s.valid + (if wgbHostFire s i = true then 1 else 0) -
        (if wgbClearAct s i = true then 1 else 0) := by
  by_cases hwr : wgbHostFire s i = true
  · have hbitw := wgbHostFire_bit_free hwr
    by_cases hclr : wgbClearAct s i = true
    · have hbitr := wgbClearAct_bit_valid henv hclr
      have hne : wgbWrAddr s ≠ i.resAddr := wgbBit_ne_of hbitw hbitr
      rw [wgbStep_valid, wgbSetMask_eq _ _ hwr, wgbRstMask_eq _ _ hclr]
      have hb2 : wgbBit (s.valid &&& ~~~(1#8 <<< i.resAddr)) (wgbWrAddr s) = false := by
        rw [wgbBit_clear_ne _ _ _ hne]; exact hbitw
      rw [wgbCount_set _ _ hb2, wgbCount_clear _ _ hbitr]
      have hpos := wgbCount_pos_of_bit _ _ hbitr
      rw [if_pos hwr, if_pos hclr]; omega
    · rw [wgbStep_valid, wgbSetMask_eq _ _ hwr, wgbRstMask_zero _ _ hclr,
          wgb_and_allOnes, wgbCount_set _ _ hbitw, if_pos hwr, if_neg hclr]
      omega
  · by_cases hclr : wgbClearAct s i = true
    · have hbitr := wgbClearAct_bit_valid henv hclr
      rw [wgbStep_valid, wgbSetMask_zero _ _ hwr, wgbRstMask_eq _ _ hclr,
          wgb_or_zero, wgbCount_clear _ _ hbitr, if_neg hwr, if_pos hclr]
      omega
    · rw [wgbStep_valid, wgbSetMask_zero _ _ hwr, wgbRstMask_zero _ _ hclr,
          wgb_and_allOnes, wgb_or_zero, if_neg hwr, if_neg hclr]
      simp

/-- 对应抽象事件 .hostNew：pending +1 -/
theorem wgb_pending_host (s : WgbState) (i : WgbInputs) (henv : WgbEnvOk s i)
    (hw : wgbHostFire s i = true) (hc : ¬(wgbClearAct s i = true)) :
    wgbPending (wgbStep s i) = wgbPending s + 1 := by
  have h := wgb_step_count s i henv
  rw [if_pos hw, if_neg hc] at h
  unfold wgbPending
  omega

/-- 对应抽象事件 .alloc（accept 清除）：pending −1 -/
theorem wgb_pending_alloc (s : WgbState) (i : WgbInputs) (henv : WgbEnvOk s i)
    (hc : wgbClearAct s i = true) (hw : ¬(wgbHostFire s i = true)) :
    wgbPending (wgbStep s i) = wgbPending s - 1 := by
  have h := wgb_step_count s i henv
  rw [if_pos hc, if_neg hw] at h
  unfold wgbPending
  omega

/- ========================================================================= -/
/- 9. 数据完整性：不变量保持 + 输出捕获 + 反压稳定                               -/
/- ========================================================================= -/

/-- 不变量在复位态成立（valid 全 0，前提虚真） -/
theorem wgbInv_init : WgbInv wgbInit := by
  intro a ha
  simp [wgbInit, wgbBit_zero] at ha

/-- 不变量保持（对任意输入成立，无需环境契约：写同时更新 ram 与 ghost，
    清除只动 valid 位，二者地址错开与否都不影响其余槽） -/
theorem wgbInv_step (s : WgbState) (i : WgbInputs) (h : WgbInv s) :
    WgbInv (wgbStep s i) := by
  intro a ha
  rw [wgbStep_valid] at ha
  by_cases hwr : wgbHostFire s i = true
  · rw [wgbSetMask_eq _ _ hwr] at ha
    by_cases haw : a = wgbWrAddr s
    · subst haw
      rw [wgbStep_ram, if_pos hwr, wgbStep_ghost, if_pos hwr]
      simp [wgbUpd]
    · rw [wgbBit_set_ne _ _ _ haw] at ha
      rw [wgbStep_ram, if_pos hwr, wgbStep_ghost, if_pos hwr]
      have hne8 : wgbFin a ≠ wgbFin (wgbWrAddr s) := wgbFin_ne _ _ haw
      simp [wgbUpd, hne8]
      by_cases hclr : wgbClearAct s i = true
      · rw [wgbRstMask_eq _ _ hclr] at ha
        by_cases har : a = i.resAddr
        · subst har; rw [wgbBit_clear_self] at ha; simp at ha
        · rw [wgbBit_clear_ne _ _ _ har] at ha; exact h a ha
      · rw [wgbRstMask_zero _ _ hclr, wgb_and_allOnes] at ha; exact h a ha
  · rw [wgbSetMask_zero _ _ hwr, wgb_or_zero] at ha
    rw [wgbStep_ram, if_neg hwr, wgbStep_ghost, if_neg hwr]
    by_cases hclr : wgbClearAct s i = true
    · rw [wgbRstMask_eq _ _ hclr] at ha
      by_cases har : a = i.resAddr
      · subst har; rw [wgbBit_clear_self] at ha; simp at ha
      · rw [wgbBit_clear_ne _ _ _ har] at ha; exact h a ha
    · rw [wgbRstMask_zero _ _ hclr, wgb_and_allOnes] at ha; exact h a ha

/-- 【供给数据完整】供给生效时：载入 alloc 输出寄存器的 tag = 该槽驻留时的
    host 写入 tag（ghost），地址随之登记；valid_r 置位 -/
theorem wgb_alloc_capture (s : WgbState) (i : WgbInputs) (hinv : WgbInv s)
    (h : wgbRdAct s i = true) :
    (wgbStep s i).allocValidR = true ∧
    (wgbStep s i).allocDataR = s.ghost (wgbFin (wgbRdAddr s)) ∧
    (wgbStep s i).allocAddrR = wgbRdAddr s := by
  have hcand : wgbRdCand s ≠ 0#8 := (wgb_bne0 _).1 (wgb_and_true h).1
  have hbit : wgbBit s.valid (wgbRdAddr s) = true :=
    wgbBit_and_true _ _ _ (wgb_rrPick_mem _ _ hcand)
  have hfg := hinv _ hbit
  refine ⟨?_, ?_, ?_⟩ <;> simp [wgbStep, h]
  exact hfg

/-- 【供给即标记】供给生效后该槽 alloc 位置位（防重选，直到 allocator 回应） -/
theorem wgb_rd_sets_alloc (s : WgbState) (i : WgbInputs) (h : wgbRdAct s i = true) :
    wgbBit (wgbStep s i).alloc (wgbRdAddr s) = true := by
  rw [wgbStep_alloc]
  simp [h]
  exact wgbBit_set_self _ _

/-- 【cuinterface 数据完整】accept 清除生效时：载入 cuif 输出寄存器的 tag =
    被清除槽驻留时的 host 写入 tag（需 WgbEnvOk 保证槽在驻） -/
theorem wgb_cuif_capture (s : WgbState) (i : WgbInputs) (hinv : WgbInv s)
    (henv : WgbEnvOk s i) (h : wgbClearAct s i = true) :
    (wgbStep s i).cuifValidR = true ∧
    (wgbStep s i).cuifDataR = s.ghost (wgbFin i.resAddr) := by
  have hbit := wgbClearAct_bit_valid henv h
  have hfg := hinv _ hbit
  refine ⟨?_, ?_⟩ <;> simp [wgbStep, h]
  exact hfg

/-- 【alloc 输出反压稳定】valid_r 持起且下游不 ready：不发起新供给，
    输出寄存器保持（Irrevocable 半） -/
theorem wgb_alloc_stable (s : WgbState) (i : WgbInputs)
    (hv : s.allocValidR = true) (hr : i.allocReady = false) :
    wgbRdAct s i = false ∧
    (wgbStep s i).allocValidR = true ∧
    (wgbStep s i).allocDataR = s.allocDataR ∧
    (wgbStep s i).allocAddrR = s.allocAddrR := by
  have hallow : wgbRdAllowed s i = false := by simp [wgbRdAllowed, hv, hr]
  have hact : wgbRdAct s i = false := by simp [wgbRdAct, hallow]
  refine ⟨hact, ?_, ?_, ?_⟩ <;> simp [wgbStep, hact, hr, hv]

/-- 【cuif 输出反压稳定】valid_r 持起且下游不 ready：clear 被禁止（:150-151
    经 :157 反压 alloc_result），输出寄存器保持 -/
theorem wgb_cuif_stable (s : WgbState) (i : WgbInputs)
    (hv : s.cuifValidR = true) (hr : i.cuifReady = false) :
    wgbClearAct s i = false ∧
    (wgbStep s i).cuifValidR = true ∧
    (wgbStep s i).cuifDataR = s.cuifDataR := by
  have hcr : wgbClearReady s i = false := by simp [wgbClearReady, hv, hr]
  have hact : wgbClearAct s i = false := by
    cases hacc : i.resAccept <;> simp [wgbClearAct, wgbResFire, wgbResReady, hacc, hcr]
  refine ⟨hact, ?_, ?_⟩ <;> simp [wgbStep, hact, hr, hv]

/-- Q-WGB1 形式钉：accept 时 resReady = clearReady；reject 时恒 ready -/
theorem wgb_resReady_accept (s : WgbState) (i : WgbInputs) (h : i.resAccept = true) :
    wgbResReady s i = wgbClearReady s i := by simp [wgbResReady, h]
theorem wgb_resReady_reject (s : WgbState) (i : WgbInputs) (h : i.resAccept = false) :
    wgbResReady s i = true := by simp [wgbResReady, h]

/- ========================================================================= -/
/- 10. 不丢 / 不重                                                              -/
/- ========================================================================= -/

/-- 【不丢】在驻位保持：除「accept 清除该位」外任何操作都不清 valid 位 -/
theorem wgb_valid_persists (s : WgbState) (i : WgbInputs) (a : BitVec 3)
    (hbit : wgbBit s.valid a = true)
    (hnc : wgbClearAct s i = true → i.resAddr ≠ a) :
    wgbBit (wgbStep s i).valid a = true := by
  rw [wgbStep_valid]
  by_cases hwr : wgbHostFire s i = true
  · rw [wgbSetMask_eq _ _ hwr]
    by_cases haw : a = wgbWrAddr s
    · subst haw; exact wgbBit_set_self _ _
    · rw [wgbBit_set_ne _ _ _ haw]
      by_cases hclr : wgbClearAct s i = true
      · rw [wgbRstMask_eq _ _ hclr, wgbBit_clear_ne _ _ _ (Ne.symm (hnc hclr))]
        exact hbit
      · rw [wgbRstMask_zero _ _ hclr, wgb_and_allOnes]; exact hbit
  · rw [wgbSetMask_zero _ _ hwr, wgb_or_zero]
    by_cases hclr : wgbClearAct s i = true
    · rw [wgbRstMask_eq _ _ hclr, wgbBit_clear_ne _ _ _ (Ne.symm (hnc hclr))]
      exact hbit
    · rw [wgbRstMask_zero _ _ hclr, wgb_and_allOnes]; exact hbit

/-- 【精确回收】accept 清除后该槽 valid 位落下（写同槽同拍不可能：
    写选空闲位、清选在驻位，二者必不同槽） -/
theorem wgb_clear_exact (s : WgbState) (i : WgbInputs) (henv : WgbEnvOk s i)
    (h : wgbClearAct s i = true) :
    wgbBit (wgbStep s i).valid i.resAddr = false := by
  rw [wgbStep_valid, wgbRstMask_eq _ _ h]
  by_cases hwr : wgbHostFire s i = true
  · have hne : wgbWrAddr s ≠ i.resAddr :=
      wgbBit_ne_of (wgbHostFire_bit_free hwr) (wgbClearAct_bit_valid henv h)
    rw [wgbSetMask_eq _ _ hwr, wgbBit_set_ne _ _ _ (Ne.symm hne)]
    exact wgbBit_clear_self _ _
  · rw [wgbSetMask_zero _ _ hwr, wgb_or_zero]
    exact wgbBit_clear_self _ _

/-- 【不重】空闲槽不会被 accept 清除（WgbEnvOk 下 alloc_result 必指在驻槽）：
    结合 wgb_clear_exact，一次驻留至多被清除一次 -/
theorem wgb_no_double_clear (s : WgbState) (i : WgbInputs) (henv : WgbEnvOk s i)
    (hbit : wgbBit s.valid i.resAddr = false) : wgbClearAct s i = false := by
  cases h : wgbClearAct s i with
  | false => rfl
  | true =>
    have h1 := wgbClearAct_bit_valid henv h
    simp [hbit] at h1

/- ========================================================================= -/
/- 11. 与 CtaScheduler 抽象契约的机器可检查对照                                  -/
/- ========================================================================= -/

-- CtasEventOk 的 hostNew 分支（H-WGB 的抽象形态，CtaScheduler.lean:265）
#check @CtasEventOk
/-- hostNew 分支即 `pending < ctasWGBUF_ENTRIES`，本文件给出其具体化证明 -/
example (s : CtasState) : CtasEventOk s .hostNew ↔ s.pending < ctasWGBUF_ENTRIES := Iff.rfl

/- ========================================================================= -/
/- 12. 公理审计                                                                 -/
/- ========================================================================= -/

#print axioms wgb_h_wgb_discharge
#print axioms wgb_step_count
#print axioms wgbInv_step
#print axioms wgb_alloc_capture
#print axioms wgb_cuif_capture
#print axioms wgb_no_double_clear
#print axioms wgb_rrPick_mem
#print axioms wgbT7_reorder_witness
