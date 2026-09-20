/- ========================================================================= -/
/-                          Pipe.lean                                        -/
/-  SM 级顶层连线（class pipe）的 Lean 4 连线模型与连线契约                     -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/pipe.scala          -/
/-    （class pipe，全文 430 行，纯连线：各子模块已分别建模验证，               -/
/-      本文件只形式化"连线本身"，不重证子模块内部）                            -/
/-  参数（top/parameters.scala）：num_warp=8、depth_warp=3、num_thread=32、    -/
/-    num_lane=32、num_fetch=2、xLen=32、alu_fn 6 位、SINGLE_INST=false、      -/
/-    MMU_ENABLED=false、GVM_ENABLED=false。                                  -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 纯连线建模：每条非平凡连线 = 一个纯函数（输入为对端模块的抽象信号值）， -/
/-      输出等式 = 源码该行语义；定理多为 rfl/decide/bv_decide 级。子模块       -/
/-      内部状态不展开，只在组合契约（第 3 节）中引用其已建模的组合读出         -/
/-      （wsWarpReady / sbDelay / bjSysStep）。                                -/
/-  D2. 纯 `<>` 直通连线（pc_reset、wg_id_tag、pc_req、warpReq/warpRsp、       -/
/-      out_v/out_x↔writeVecCtrl/writeScalarCtrl、exe_data↔issue、issue 各      -/
/-      活跃通道、if_mask、pc_reconv.bits、out2br、dcache/shared/lsu_rsp、      -/
/-      wb 的 12 个 in 端口）统一抽象为 `pipeConn = id`，见 W0 与契约表。       -/
/-  D3. SINGLE_INST=false（:207-214 与 :225-226 的单指令分支不例化）；          -/
/-      :225-226 的替代门控建成 `pipeIb2iInValidSI`/`pipeIbOutReadySI` 备查。   -/
/-  D4. MMU 关闭：:188-192 的 asid 写不生成。SPIKE/GVM 调试通路（:140-145、    -/
/-      :296-307 的 printf）不建模。inst_cnt 计数（:86-113）不建模。           -/
/-  D5. alu_fn 宽 6（DecodeUnit.scala:60-100），:276-287 断言建模为 Bool        -/
/-      谓词 `pipeUndefOk`（仿真期 assertion，综合后消失——I-16 的危害前提）。   -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1.【死连线】`flush`（:52 声明、:174 赋值）与 `issue_stall`（:51 声明、    -/
/-      :429 赋值）在本模块内均无消费方（全文核查：:183/:193 直接用             -/
/-      warp_sche.io.flush 而非 `flush`）。纯死硬件（一层 wire），无功能影响。  -/
/-  Q2.【status 双视图】:155 把 warp_sche 看到的 pc_rsp.status 在 ibuffer 满    -/
/-      时强制为 1（miss→重放），但 :182/:187 的 control/ibuffer 门控读的是     -/
/-      原始 io.icache_rsp.bits.status（非强制值）。安全性不依赖强制值，而靠    -/
/-      :216 的 ready 反压（ibuffer 满 ⇒ icache_rsp.fire=false ⇒ 不入队）。     -/
/-      机证：`pipe_w2_full_blocks_enq` / `pipe_w2_status_forced`。            -/
/-  Q3.【:159-160】"not used" 注释自承：issued_warp 接 exe_dataX.enq 的         -/
/-      wid/fire，warp_sche 侧无消费。死连线，记录防误读。                     -/
/- ========================================================================= -/

import Ventus.Schedule.WarpScheduler
import Ventus.Schedule.Scoreboard
import Ventus.SIMT.BranchJoin
import Std.Tactic.BVDecide

namespace Ventus

open Ventus.Schedule Ventus.SIMT

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 常数与辅助                                                              -/
/- =========================================================================-/

/- warp 号：num_warp=8、depth_warp=3。不用 abbrev（bv_decide 看不穿）。 -/

/-- BitVec 3 只有 8 个取值（用于逐 warp 连线的穷举证明） -/
theorem pipe_bv3_cases (i : BitVec 3) :
    i = 0#3 ∨ i = 1#3 ∨ i = 2#3 ∨ i = 3#3 ∨ i = 4#3 ∨ i = 5#3 ∨ i = 6#3 ∨ i = 7#3 := by
  bv_decide

/- ========================================================================= -/
/- 2. A 类：连线事实（逐行翻译 pipe.scala，定理 = "连线函数 = 源码语义"）      -/
/- =========================================================================-/

/-- W0（:147,:150-152,:157-158,:163,:166-167,:288-294,:371-374,:376,:378,:380,
    :382,:384,:386-389,:392,:394,:396,:398,:400,:410-414,:416-427 等）：
    纯 `<>` / 直接 `:=` 直通连线的统一抽象——连线函数即恒等。 -/
def pipeConn {α : Type} (x : α) : α := x

/-- 直通连线的语义就是恒等（契约表所有 `<>` 行共用） -/
theorem pipe_conn_id {α : Type} (x : α) : pipeConn x = x := rfl

/-- W1a（:133）：externalFlushPipe.valid = flush.valid | flushCache.valid -/
def pipeExtFlushValid (flushValid flushCacheValid : Bool) : Bool := flushValid || flushCacheValid

/-- W1b（:134）：externalFlushPipe.bits = Mux(flush.valid, flush.bits, flushCache.bits) -/
def pipeExtFlushBits (flushValid : Bool) (flushBits flushCacheBits : BitVec 3) : BitVec 3 :=
  if flushValid then flushBits else flushCacheBits

theorem pipe_extFlush_valid (a b : Bool) : pipeExtFlushValid a b = (a || b) := rfl
theorem pipe_extFlush_bits_flush (a b : BitVec 3) : pipeExtFlushBits true a b = a := rfl
theorem pipe_extFlush_bits_cache (a b : BitVec 3) : pipeExtFlushBits false a b = b := rfl

/-- W2a（:153）：warp_sche.io.pc_rsp.valid = io.icache_rsp.valid（直通，无 ready 门控） -/
def pipePcRspValid (rspValid : Bool) : Bool := rspValid

/-- W2b（:155）：warp_sche 看到的 pc_rsp.status：ibuffer 可收时直通，
    不可收时强制 1（=miss，warp_schedule 侧据此重放，Q2） -/
def pipePcRspStatus (ibufRdy : Bool) (st : BitVec 2) : BitVec 2 := if ibufRdy then st else 1#2

/-- W2c（:216）：io.icache_rsp.ready = ibuffer.io.in.ready（反压直通） -/
def pipeIcacheRspReady (ibufRdy : Bool) : Bool := ibufRdy

/-- W2d（:187）：ibuffer.io.in.valid = icache_rsp.valid && !status(0)。
    注意：此处读的是**原始** status（Q2），强制值只去 warp_sche。 -/
def pipeIbInValid (rspValid : Bool) (st : BitVec 2) : Bool := rspValid && (st &&& 1#2 == 0#2)

/-- W2e（:182）：control.io.inst_mask：有效且非 miss 时直通，否则全 0 -/
def pipeInstMask (rspValid : Bool) (st : BitVec 2) (m : BitVec 2) : BitVec 2 :=
  if rspValid && (st &&& 1#2 == 0#2) then m else 0#2

/-- ibuffer 入队 fire = in.valid && in.ready（:187 + :216 组合） -/
def pipeIbEnqFire (rspValid : Bool) (st : BitVec 2) (ibufRdy : Bool) : Bool :=
  pipeIbInValid rspValid st && pipeIcacheRspReady ibufRdy

theorem pipe_pcRsp_valid (v : Bool) : pipePcRspValid v = v := rfl
theorem pipe_pcRsp_status_pass (st : BitVec 2) : pipePcRspStatus true st = st := rfl
theorem pipe_pcRsp_status_forced (st : BitVec 2) : pipePcRspStatus false st = 1#2 := rfl

/-- W2 组合（Q2 的安全性论证）：ibuffer 满时——
    (1) 无论原始 status 是什么，ibuffer 都不可能入队（ready 反压兜底）；
    (2) warp_sche 看到的 status 恒为 1（miss→重放），响应不会静默丢失。 -/
theorem pipe_w2_full_blocks_enq (rspValid : Bool) (st : BitVec 2) :
    pipeIbEnqFire rspValid st false = false ∧ pipePcRspStatus false st = 1#2 := by
  exact ⟨by simp [pipeIbEnqFire, pipeIcacheRspReady], rfl⟩

/-- ibuffer 可收时：入队与否完全由原始 status(0) 决定（非 miss 才入队） -/
theorem pipe_w2_enq_iff (rspValid : Bool) (st : BitVec 2) :
    pipeIbEnqFire rspValid st true = (rspValid && (st &&& 1#2 == 0#2)) := by
  simp [pipeIbEnqFire, pipeIbInValid, pipeIcacheRspReady]

/-- W3（:161）：scoreboard_busy = VecInit(scoreb.map(_.delay)).asUInt。
    delay 是 scoreboard.scala:142 的组合读出（读寄存器当前值，非旁路）。
    装配方式与 wsMask0 相同：bit i = 第 i 个记分板的 delay。 -/
def pipeScoreboardBusy (d : Fin 8 → Bool) : BitVec 8 :=
  (BitVec.ofBool (d (wsFin 0#3))).zeroExtend 8 |||
  ((BitVec.ofBool (d (wsFin 1#3))).zeroExtend 8 <<< 1) |||
  ((BitVec.ofBool (d (wsFin 2#3))).zeroExtend 8 <<< 2) |||
  ((BitVec.ofBool (d (wsFin 3#3))).zeroExtend 8 <<< 3) |||
  ((BitVec.ofBool (d (wsFin 4#3))).zeroExtend 8 <<< 4) |||
  ((BitVec.ofBool (d (wsFin 5#3))).zeroExtend 8 <<< 5) |||
  ((BitVec.ofBool (d (wsFin 6#3))).zeroExtend 8 <<< 6) |||
  ((BitVec.ofBool (d (wsFin 7#3))).zeroExtend 8 <<< 7)

/-- W3 取位正确性：装配后 bit i 恰好是第 i 个记分板的 delay -/
theorem pipeScoreboardBusy_bit (d : Fin 8 → Bool) (i : BitVec 3) :
    ((pipeScoreboardBusy d >>> i.zeroExtend 8) &&& 1#8 = 1#8) ↔ d (wsFin i) = true := by
  rcases pipe_bv3_cases i with h | h | h | h | h | h | h | h <;> subst h <;>
    unfold pipeScoreboardBusy <;> bv_decide

/-- W4a（:174）：flush wire = warp_sche.io.flush.valid（Q1：该 wire 无消费方） -/
def pipeFlushWire (flushValid : Bool) : Bool := flushValid

/-- W4b（:183/:193）：control.io.flush_wid 与 ibuffer.io.flush_wid 两路同源，
    都直接接 warp_sche.io.flush（不经 :174 的 flush wire）。 -/
def pipeFlushWidControl (flush : Bool × BitVec 3) : Bool × BitVec 3 := flush
def pipeFlushWidIbuffer (flush : Bool × BitVec 3) : Bool × BitVec 3 := flush

/-- 两路同源：两消费方看到的 flush 逐比特相同 -/
theorem pipe_flush_two_sinks (f : Bool × BitVec 3) :
    pipeFlushWidControl f = pipeFlushWidIbuffer f := rfl

/-- W5a（:223）：ibuffer2issue.io.in(i).valid = ibuffer.io.out(i).valid && warp_ready(i) -/
def pipeIb2iInValid (ibOutValid warpRdy : Bool) : Bool := ibOutValid && warpRdy

/-- W5b（:224）：ibuffer.io.out(i).ready = ibuffer2issue.io.in(i).ready && warp_ready(i) -/
def pipeIbOutReady (ib2iRdy warpRdy : Bool) : Bool := ib2iRdy && warpRdy

/-- W5c（:225-226，SINGLE_INST=true 替代门控，现配置不例化，D3） -/
def pipeIb2iInValidSI (ibOutValid sbDelay : Bool) : Bool := ibOutValid && !sbDelay
def pipeIbOutReadySI (ib2iRdy sbDelay : Bool) : Bool := ib2iRdy && !sbDelay

/-- 入 ibuffer2issue 的 fire（in.valid && in.ready） -/
def pipeIb2iInFire (ibOutValid ib2iRdy warpRdy : Bool) : Bool :=
  pipeIb2iInValid ibOutValid warpRdy && ib2iRdy

/-- 出 ibuffer 的 fire（out.valid && out.ready） -/
def pipeIbOutFire (ibOutValid ib2iRdy warpRdy : Bool) : Bool :=
  ibOutValid && pipeIbOutReady ib2iRdy warpRdy

/-- W5 门控：两个 fire 恒等（同一拍同一事务，两侧视图一致） -/
theorem pipe_ib2i_fire_eq (v r w : Bool) :
    pipeIb2iInFire v r w = pipeIbOutFire v r w := by
  cases v <;> cases r <;> cases w <;> rfl

/-- W5 门控：warp_ready(i)=false 时该 warp 完全不动（I-4 门控链的第一环 :223） -/
theorem pipe_ib2i_gated (v r : Bool) :
    pipeIb2iInFire v r false = false ∧ pipeIbOutFire v r false = false := by
  cases v <;> cases r <;> exact ⟨rfl, rfl⟩

/-- W6a（:242-243）：scoreb(i).if_fire =（i 是 out_x 发射的 wid 且 out_x.fire）
    或（i 是 out_v 发射的 wid 且 out_v.fire） -/
def pipeSbIfFire (i xWid vWid : BitVec 3) (xFire vFire : Bool) : Bool :=
  ((i == xWid) && xFire) || ((i == vWid) && vFire)

/-- W6b（:238）：scoreb(i).if_ctrl = Mux(i 是 out_x 发射目标且 out_x.fire,
    out_x.bits, out_v.bits)。注意：无 x 发射时直通 out_v.bits（即使 v 也未发射，
    此时 if_fire=false，bits 不被消费）。 -/
def pipeSbIfCtrl (i xWid : BitVec 3) (xFire : Bool) (xBits vBits : SbCtrl) : SbCtrl :=
  if (i == xWid) && xFire then xBits else vBits

/-- W6c（:246,:252-254）：scoreb(i).br_ctrl。默认 false（:246），三条 elsewhen
    全部赋 true.B，故结果 = 三条件之或（顺序无关）：
    branch.fire ∧ wid=i（branch_back 仲裁输出，含 simt_stack.fetch_ctl 路径）；
    warp_control.fire ∧ wid=i（endprg/barrier）；complete.valid ∧ bits=i。 -/
def pipeSbBrCtrl (i brWid wcWid cmpWid : BitVec 3) (brFire wcFire cmpValid : Bool) : Bool :=
  (brFire && (brWid == i)) || (wcFire && (wcWid == i)) || (cmpValid && (cmpWid == i))

/-- W6d（:249,:262）：scoreb 的 op_colV_in_fire——:249 先置 false，:262 对
    wid=op_colV_in_wid 的记分板覆盖为 controlV.fire（动态索引，last-connect-wins） -/
def pipeSbOpColVIn (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)
/-- W6e（:250,:263）：op_colV_out_fire 同理（:263） -/
def pipeSbOpColVOut (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)
/-- W6f（:247,:267）：op_colX_in_fire（:267） -/
def pipeSbOpColXIn (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)
/-- W6g（:248,:268）：op_colX_out_fire（:268） -/
def pipeSbOpColXOut (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)
/-- W6h（:245,:271）：wb_x_fire——:245 先置 false，:271 对 wid=wb.out_x.warp_id 覆盖 -/
def pipeSbWbXFire (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)
/-- W6i（:244,:272）：wb_v_fire 同理（:272） -/
def pipeSbWbVFire (i wid : BitVec 3) (fire : Bool) : Bool := fire && (wid == i)

/-- W6 路由正确性：fire 信号恰好送达 wid 匹配的那一个记分板 -/
theorem pipe_sb_fire_routing (i wid : BitVec 3) (f : Bool) :
    pipeSbOpColVIn i wid f = true ↔ f = true ∧ wid = i := by
  unfold pipeSbOpColVIn
  bv_decide

/-- 非目标 warp 的记分板不受影响（:249 的默认 false 保持） -/
theorem pipe_sb_fire_silent (i wid : BitVec 3) (f : Bool) (h : wid ≠ i) :
    pipeSbOpColVIn i wid f = false := by
  unfold pipeSbOpColVIn
  bv_decide

/-- W6a 规约：if_fire ⟺ 本 warp 是两条发射通道之一的当拍目标 -/
theorem pipe_sb_ifFire_spec (i xWid vWid : BitVec 3) (xFire vFire : Bool) :
    pipeSbIfFire i xWid vWid xFire vFire = true ↔
      (xFire = true ∧ xWid = i) ∨ (vFire = true ∧ vWid = i) := by
  unfold pipeSbIfFire
  bv_decide

/-- W6b 规约：x 通道命中时取 out_x.bits -/
theorem pipe_sb_ifCtrl_x (i xWid : BitVec 3) (xFire : Bool) (xb vb : SbCtrl)
    (h : ((i == xWid) && xFire) = true) : pipeSbIfCtrl i xWid xFire xb vb = xb := by
  simp [pipeSbIfCtrl, h]

/-- W6b 规约：x 通道未命中时取 out_v.bits（:238 的 Mux else 分支） -/
theorem pipe_sb_ifCtrl_v (i xWid : BitVec 3) (xFire : Bool) (xb vb : SbCtrl)
    (h : ((i == xWid) && xFire) = false) : pipeSbIfCtrl i xWid xFire xb vb = vb := by
  simp [pipeSbIfCtrl, h]

/-- W6c 规约：br_ctrl 是三个清除源之或 -/
theorem pipe_sb_brCtrl_spec (i brWid wcWid cmpWid : BitVec 3) (brFire wcFire cmpValid : Bool) :
    pipeSbBrCtrl i brWid wcWid cmpWid brFire wcFire cmpValid = true ↔
      (brFire = true ∧ brWid = i) ∨ (wcFire = true ∧ wcWid = i) ∨
      (cmpValid = true ∧ cmpWid = i) := by
  unfold pipeSbBrCtrl
  bv_decide

/-- W7（:275-287）：issue 级 undefined-instruction 断言。源码断言
    `ctrl.alu_fn =/= 63.U`，仅挂在 ibuffer2issue 的 out_x/out_v **fire** 上
    （进入 ibuffer 时不检查——:195-203 的 ibuffer 入口检查被注释移除，理由是
    未发射的预取残留不属错误）。本谓词即仿真期 assertion；综合后消失（I-16
    的危害前提：AMO 静默译码为 alu_fn=63 的 NOP 只靠本断言兜底）。 -/
def pipeUndefOk (fire : Bool) (fn : BitVec 6) : Bool := !fire || (fn != 63#6)

/-- W8a（:358）：exe_dataX（标量通路）enq.mask 强制全 1 -/
def pipeExeDataXMask : BitVec 32 := 0xFFFFFFFF#32

/-- W8b（:366）：exe_dataV（向量通路）enq.mask = 指令掩码 ∧ simt_stack.out_mask。
    这是 I-2 掩码单调链的第一环：vbranch 的 mask_init 经 :366→exe_dataV→issueV
    (:371)→out_SIMT(:382)→branch_ctl，故 mask_init ⊆ out_mask。 -/
def pipeExeDataVMask (instrMask outMask : BitVec 32) : BitVec 32 := instrMask &&& outMask

/-- W8 第一环：执行掩码是 out_mask 的子掩码（单调不增） -/
theorem pipe_vmask_sub_outMask (m om : BitVec 32) :
    pipeExeDataVMask m om &&& ~~~om = 0#32 := by
  unfold pipeExeDataVMask
  bv_decide

/-- W8 第一环：执行掩码也是指令掩码的子掩码 -/
theorem pipe_vmask_sub_instrMask (m om : BitVec 32) :
    pipeExeDataVMask m om &&& ~~~m = 0#32 := by
  unfold pipeExeDataVMask
  bv_decide

/-- W9a（:390，I-31 现场）：simt_stack.io.pc_reconv.valid = issueV.io.out_SIMT.valid
    ——valid 直通，**不过 fire 门控**（源码自带 "todo check this"）。 -/
def pipePcReconvValid (outSimtValid : Bool) : Bool := outSimtValid

/-- W9b（:389）：pc_reconv.bits = csrfile.io.simt_rpc（直通） -/
def pipePcReconvBits (rpc : BitVec 32) : BitVec 32 := rpc

/-- W10（:169-171）：flushDCache 三行手动 Decoupled 对接（替换被注释的 :168 直连）。
    valid/bits 正向直通、ready 反向直通，故两端的 fire 定义一致。 -/
def pipeFlushDCacheValidFwd (v : Bool) : Bool := v          -- :169
def pipeFlushDCacheBitsFwd (b : BitVec 3) : BitVec 3 := b     -- :170
def pipeFlushDCacheReadyBwd (r : Bool) : Bool := r          -- :171

theorem pipe_flushDCache_fire_agree (v r : Bool) :
    (pipeFlushDCacheValidFwd v && r) = (v && pipeFlushDCacheReadyBwd r) := rfl

/-- W11（:374-401）：issue 双例化的通道活性表。X（标量）只活跃 sALU/CSR/
    warpscheduler，V（向量）只活跃 vALU/LSU/SIMT/SFU/MUL/TC/vFPU；
    其余通道 ready 绑死 false.B（:375,:377,:379,:381,:383,:385,:395,:397,:399,:401）。 -/
inductive PipeIssueChan where
  | vALU | LSU | sALU | CSR | SIMT | SFU | MUL | TC | vFPU | warpSched
  deriving DecidableEq

/-- issueX 各通道是否活跃（:374-400） -/
def pipeIssueXLive : PipeIssueChan → Bool
  | .vALU => false | .LSU => false | .sALU => true | .CSR => true | .SIMT => false
  | .SFU => false | .MUL => false | .TC => false | .vFPU => false | .warpSched => true

/-- issueV 各通道是否活跃（:374-401） -/
def pipeIssueVLive : PipeIssueChan → Bool
  | .vALU => true | .LSU => true | .sALU => false | .CSR => false | .SIMT => true
  | .SFU => true | .MUL => true | .TC => true | .vFPU => true | .warpSched => false

/-- W11 通道划分：每个通道恰好在一个 issue 例化上活跃（另一例化上 ready 绑死） -/
theorem pipe_issue_partition (c : PipeIssueChan) :
    (pipeIssueXLive c && pipeIssueVLive c) = false ∧
    (pipeIssueXLive c || pipeIssueVLive c) = true := by
  cases c <;> decide

/-- W11 死通道推论：ready 绑死的通道永不 fire -/
theorem pipe_dead_channel_no_fire (v : Bool) : (v && false) = false := by cases v <;> rfl

/-- W12（:416-427）：Writeback(6,6) 端口映射。in_x(0..5) ←
    alu/fpu.out_x/lsu2wb.out_x/csrfile/sfu.out_x/mul.out_x；
    in_v(0..5) ← valu/fpu.out_v/lsu2wb.out_v/sfu.out_v/mul.out_v/tensorcore.out_v。 -/
inductive PipeWbSrc where
  | alu | fpu | lsu2wb | csr | sfu | mul | valu | tc
  deriving DecidableEq

/-- in_x 端口 i 的数据源（:416-421） -/
def pipeWbInX (i : Fin 6) : PipeWbSrc :=
  if i = 0 then .alu else if i = 1 then .fpu else if i = 2 then .lsu2wb
  else if i = 3 then .csr else if i = 4 then .sfu else .mul

/-- in_v 端口 i 的数据源（:422-427） -/
def pipeWbInV (i : Fin 6) : PipeWbSrc :=
  if i = 0 then .valu else if i = 1 then .fpu else if i = 2 then .lsu2wb
  else if i = 3 then .sfu else if i = 4 then .mul else .tc

/- ========================================================================= -/
/- 2.5 数值回归测试（先测试；全部 by decide）                                 -/
/- =========================================================================-/

section PipeRegressionTests

-- T1 W2：status 强制与反压
example : pipePcRspStatus false 2#2 = 1#2 := by decide
example : pipePcRspStatus true 2#2 = 2#2 := by decide
example : pipeIbInValid true 0#2 = true := by decide
example : pipeIbInValid true 1#2 = false := by decide      -- miss 不入队
example : pipeIbEnqFire true 0#2 false = false := by decide -- 满则反压
example : pipeInstMask true 1#2 3#2 = 0#2 := by decide     -- miss 清零 inst_mask
example : pipeInstMask true 0#2 3#2 = 3#2 := by decide

-- T2 W3：scoreboard_busy 装配（只有 warp3 的 delay 置位 → 0b00001000）
example : pipeScoreboardBusy (fun j => decide (j.val = 3)) = 8#8 := by decide
example : pipeScoreboardBusy (fun _ => false) = 0#8 := by decide
example : pipeScoreboardBusy (fun _ => true) = 0xFF#8 := by decide

-- T3 W5：warp_ready 门控
example : pipeIb2iInFire true true true = true := by decide
example : pipeIb2iInFire true true false = false := by decide
example : pipeIbOutFire true true false = false := by decide

-- T4 W6：记分板 wid 路由
example : pipeSbIfFire 3#3 3#3 5#3 true false = true := by decide
example : pipeSbIfFire 3#3 4#3 5#3 true true = false := by decide
example : pipeSbBrCtrl 2#3 2#3 0#3 0#3 true false false = true := by decide
example : pipeSbBrCtrl 2#3 1#3 0#3 2#3 false false true = true := by decide
example : pipeSbBrCtrl 2#3 1#3 0#3 3#3 false false true = false := by decide
example : pipeSbOpColVIn 5#3 5#3 true = true := by decide
example : pipeSbOpColVIn 5#3 4#3 true = false := by decide

-- T5 W7：undefined instruction 断言
example : pipeUndefOk true 63#6 = false := by decide   -- 触发 assertion
example : pipeUndefOk true 0#6 = true := by decide
example : pipeUndefOk false 63#6 = true := by decide   -- 不 fire 不检查

-- T6 W8：掩码链
example : pipeExeDataVMask 0xFF00FF00#32 0x0F0F0F0F#32 = 0x0F000F00#32 := by decide
example : pipeExeDataXMask = 0xFFFFFFFF#32 := by decide

-- T7 W11：通道划分抽查
example : pipeIssueXLive .SIMT = false ∧ pipeIssueVLive .SIMT = true := by decide
example : pipeIssueXLive .sALU = true ∧ pipeIssueVLive .sALU = false := by decide

-- T8 W12：写回端口映射抽查
example : pipeWbInX ⟨2, by decide⟩ = .lsu2wb ∧ pipeWbInV ⟨5, by decide⟩ = .tc := by decide
example : pipeWbInX ⟨5, by decide⟩ = .mul ∧ pipeWbInV ⟨0, by decide⟩ = .valu := by decide

end PipeRegressionTests

/- ========================================================================= -/
/- 3. B 类：跨模块组合契约（在连线模型上引用子模块已建模的组合读出）           -/
/- =========================================================================-/

/-- warp_ready 的第 i 位（Bool 形式），供组合契约使用 -/
def pipeWarpReadyBit (bar sb exe act : BitVec 8) (i : BitVec 3) : Bool :=
  (wsWarpReady bar sb exe act >>> i.zeroExtend 8) &&& 1#8 == 1#8

/-- B-I2a（:366 + branch_join.scala:141-142）：I-2 掩码单调链第一环。
    vbranch 的 mask_init 由 :366 给出（指令掩码 ∧ out_mask），故
    branch_join 内部的 if_mask/else_mask（= valuMask ∧ mask_init 等）都是
    out_mask 的子掩码——嵌套分化沿 taken 路径掩码单调不增的起点。 -/
theorem pipe_i2_mask_chain (instrMask outMask valuMask : BitVec 32) :
    (valuMask &&& pipeExeDataVMask instrMask outMask) &&& ~~~outMask = 0#32 ∧
    (~~~valuMask &&& pipeExeDataVMask instrMask outMask) &&& ~~~outMask = 0#32 := by
  unfold pipeExeDataVMask
  constructor <;> bv_decide

/-- B-I2b：接到 branch_join 输入结构上的同一事实（bjIfMask/bjElseMask 是
    branch_join.scala:141-142 的既有模型） -/
theorem pipe_i2_first_link (bi : BjBranchIn 32) :
    bjIfMask bi &&& ~~~bi.maskInit = 0#32 ∧ bjElseMask bi &&& ~~~bi.maskInit = 0#32 := by
  obtain ⟨vm, mi, pb, pe, pr⟩ := bi
  unfold bjIfMask bjElseMask
  constructor <;> bv_decide

/-- B-I3a（branch_join.scala:120,:145,:185-200，经 :388/:254 连线）：
    vbranch 事件的 complete 与 fetchValid 互补——至少其一成立。
    complete = takeif，fetchValid = !takeif || elseOnly，布尔互补。 -/
theorem pipe_i3_branch_complete_or_fetch (s : BjSysState 32 32) (bi : BjBranchIn 32) :
    ((bjSysStep s (.branch bi)).2.complete || (bjSysStep s (.branch bi)).2.fetchValid) = true := by
  simp only [bjSysStep]
  cases h : bjTakeif bi <;> simp

/-- B-I3b：join 事件 fetchValid 恒真（:186-200：join 总发 fetch_ctl） -/
theorem pipe_i3_join_fetch (s : BjSysState 32 32) (pc : BitVec 32) :
    (bjSysStep s (.join pc)).2.fetchValid = true := rfl

/-- B-I3c（scoreboard.scala:113-114，连线 :252-254）：br_ctrl=true 时
    beqReg 下拍必清（即使同拍有新分支发射置位，clear 后写胜，sb_clear_wins 同族）。 -/
theorem pipe_sb_beqReg_cleared (s : SbState) (inp : SbInputs) (hbr : inp.br_ctrl = true) :
    (sbStep s inp).beqReg = 0#1 := by
  rw [sbStep_beqReg, sbUtilStep_set_clear, hbr]
  unfold sbSetClear sbMask sbView
  simp

/-- B-I3d（连线级"互补契约"）：branch_join 的 complete/fetch_ctl 两路输出
    分别经 :254（complete 直连）与 :388→branch_back.in1→warp_sche.io.branch
    →:252（fetch_ctl 路径）汇入 scoreb(i).br_ctrl。只要两路输出互补（I3a/I3b），
    且连线忠实送达（本定理的前提），vbranch/join 当拍 beqReg 必被清除。
    前提即假设清单：H-BB = branch_back 仲裁终将授予 in1 且 warp_sche 接受
    （branch_ready=!flushCacheValid，WarpScheduler.lean wsOut）；H-WID =
    fetch_ctl/complete 携带的 wid 就是该 warp。 -/
theorem pipe_i3_beqReg_clear_via_wiring (s : SbState) (inp : SbInputs)
    (i brWid wcWid cmpWid : BitVec 3) (brFire wcFire cmpFire : Bool)
    (oc of_ : Bool)
    (hcomp : cmpFire = oc) (hcmpw : cmpWid = i)
    (hbr : brFire = of_) (hbrw : brWid = i)
    (hco : (oc || of_) = true)
    (hbrctrl : inp.br_ctrl = pipeSbBrCtrl i brWid wcWid cmpWid brFire wcFire cmpFire) :
    (sbStep s inp).beqReg = 0#1 := by
  have h1 : pipeSbBrCtrl i brWid wcWid cmpWid brFire wcFire cmpFire = true := by
    cases hoc : oc <;> cases hof : of_
    · rw [hoc, hof] at hco; exact absurd hco (by decide)
    · simp [pipeSbBrCtrl, hbr, hof, hbrw]
    · simp [pipeSbBrCtrl, hcomp, hoc, hcmpw]
    · simp [pipeSbBrCtrl, hcomp, hoc, hcmpw]
  exact pipe_sb_beqReg_cleared s inp (by rw [hbrctrl, h1])

/-- B-I3e：vbranch 实例化——任意 vbranch fire 事件至少走通一条 beqReg 清除路径 -/
theorem pipe_i3_vbranch_clears (s : SbState) (inp : SbInputs) (bs : BjSysState 32 32)
    (bi : BjBranchIn 32) (i brWid wcWid cmpWid : BitVec 3) (brFire wcFire cmpFire : Bool)
    (hcomp : cmpFire = (bjSysStep bs (.branch bi)).2.complete) (hcmpw : cmpWid = i)
    (hbr : brFire = (bjSysStep bs (.branch bi)).2.fetchValid) (hbrw : brWid = i)
    (hbrctrl : inp.br_ctrl = pipeSbBrCtrl i brWid wcWid cmpWid brFire wcFire cmpFire) :
    (sbStep s inp).beqReg = 0#1 :=
  pipe_i3_beqReg_clear_via_wiring s inp i brWid wcWid cmpWid brFire wcFire cmpFire _ _
    hcomp hcmpw hbr hbrw (pipe_i3_branch_complete_or_fetch bs bi) hbrctrl

/-- B-I3f：join 实例化——join 恒走 fetch_ctl 路径清除 beqReg -/
theorem pipe_i3_join_clears (s : SbState) (inp : SbInputs) (bs : BjSysState 32 32)
    (pc : BitVec 32) (i brWid wcWid cmpWid : BitVec 3) (brFire wcFire cmpFire : Bool)
    (hcomp : cmpFire = (bjSysStep bs (.join pc)).2.complete) (hcmpw : cmpWid = i)
    (hbr : brFire = (bjSysStep bs (.join pc)).2.fetchValid) (hbrw : brWid = i)
    (hbrctrl : inp.br_ctrl = pipeSbBrCtrl i brWid wcWid cmpWid brFire wcFire cmpFire) :
    (sbStep s inp).beqReg = 0#1 :=
  pipe_i3_beqReg_clear_via_wiring s inp i brWid wcWid cmpWid brFire wcFire cmpFire _ _
    hcomp hcmpw hbr hbrw (by rw [pipe_i3_join_fetch bs pc]; rfl) hbrctrl

/-- B-I4（I-4 门控链，pipe.scala:223 → warp_schedule.scala:181 → pipe.scala:161 →
    scoreboard.scala:131,142，全组合）：OpColV 占用位（寄存器当前值的组合读出）
    为 1 时，该 warp 当拍不可能从 ibuffer 向 ibuffer2issue 发射。
    链：occ(i)=1 → sbDelay ⊇ sbReadOpColV → delay(i)=1 → scoreboard_busy(i)=1
    → warp_ready(i)=0 → :223 的 valid 门控关闭 → 无 fire。
    这是 I4Fix.lean `i4f_no_two_busy_orig` 不变式依赖的门控前提在连线模型上的
    重建（格式对齐：占用 ⇒ 当拍不发射）。 -/
theorem pipe_i4_gate_chain (d : Fin 8 → Bool) (bar exe act : BitVec 8) (i : BitVec 3)
    (s : SbState) (c : SbCtrl)
    (hd : d (wsFin i) = sbDelay s c)      -- :161 scoreboard_busy(i) = 该 warp 的 delay
    (hocc : sbReadOpColV s = true)        -- opColV 占用位（组合读出寄存器当前值）
    (ibValid ib2iRdy : Bool) :
    pipeIb2iInFire ibValid ib2iRdy
      (pipeWarpReadyBit bar (pipeScoreboardBusy d) exe act i) = false := by
  have hdelay : sbDelay s c = true := by simp [sbDelay, hocc]
  have hbit : ((pipeScoreboardBusy d >>> i.zeroExtend 8) &&& 1#8) = 1#8 :=
    (pipeScoreboardBusy_bit d i).mpr (hd.trans hdelay)
  generalize pipeScoreboardBusy d = sbv at hbit ⊢
  have hnr : pipeWarpReadyBit bar sbv exe act i = false := by
    unfold pipeWarpReadyBit wsWarpReady
    bv_decide
  simp [pipeIb2iInFire, pipeIb2iInValid, hnr]

/-- B-I4 系（beqReg 同族）：分支未决位同样门控发射（sbDelay ⊇ sbReadB） -/
theorem pipe_i4_gate_chain_beq (d : Fin 8 → Bool) (bar exe act : BitVec 8) (i : BitVec 3)
    (s : SbState) (c : SbCtrl)
    (hd : d (wsFin i) = sbDelay s c)
    (hbeq : sbReadB s = true)
    (ibValid ib2iRdy : Bool) :
    pipeIb2iInFire ibValid ib2iRdy
      (pipeWarpReadyBit bar (pipeScoreboardBusy d) exe act i) = false := by
  have hdelay : sbDelay s c = true := by simp [sbDelay, hbeq]
  have hbit : ((pipeScoreboardBusy d >>> i.zeroExtend 8) &&& 1#8) = 1#8 :=
    (pipeScoreboardBusy_bit d i).mpr (hd.trans hdelay)
  generalize pipeScoreboardBusy d = sbv at hbit ⊢
  have hnr : pipeWarpReadyBit bar sbv exe act i = false := by
    unfold pipeWarpReadyBit wsWarpReady
    bv_decide
  simp [pipeIb2iInFire, pipeIb2iInValid, hnr]

/-- B-I31（:390，I-31 现场钉死）：pc_reconv.valid 只随 out_SIMT.valid，
    不看 out_SIMT.ready——反压期间 valid 持续高而通道未 fire，
    下游 Queue(_,1,flow=true) 每腾出空位即重复入队同一 simt_rpc。 -/
theorem pipe_i31_witness :
    ∃ outSimtValid outSimtReady : Bool,
      pipePcReconvValid outSimtValid = true ∧ (outSimtValid && outSimtReady) = false :=
  ⟨true, false, rfl, rfl⟩

/-- B-I31 正面刻画：valid 是 out_SIMT.valid 的恒等直通（:390 无 ready 项） -/
theorem pipe_i31_valid_passthrough (v : Bool) : pipePcReconvValid v = v := rfl

/- ========================================================================= -/
/- 4. 连线契约表（汇总；行号 = pipe.scala，定理均为本文件已证命题）            -/
/- ========================================================================= -/
/-
  | 条目 | pipe.scala | 连线内容 | 定理 |
  |------|-----------|---------|------|
  | W0  | :147,:150-152,:157-158,:163,:166-167,:288-294,:371-374 等 | 全部 `<>`/直接 := 直通 | pipe_conn_id |
  | W1  | :133-134 | externalFlushPipe valid/bits mux | pipe_extFlush_* |
  | W2  | :153-155,:182,:187,:216 | pc_rsp 路由 + status 强制 + 反压 | pipe_pcRsp_*, pipe_w2_* |
  | W3  | :161 | scoreboard_busy = delay 向量装配 | pipeScoreboardBusy_bit |
  | W4  | :174,:183,:193 | flush 两路同源（control/ibuffer） | pipe_flush_two_sinks |
  | W5  | :220-226 | ibuffer↔ibuffer2issue warp_ready 门控 | pipe_ib2i_fire_eq, pipe_ib2i_gated |
  | W6  | :237-254,:256-272 | 记分板 if/wb/br/opCol fire 的 wid 路由 | pipe_sb_* |
  | W7  | :275-287 | issue 级 undefined-instruction 断言（仿真限定） | pipeUndefOk + T5 |
  | W8  | :358,:366 | exe_data X 面罩全 1 / V 掩码 = 指令∧out_mask | pipe_vmask_sub_* |
  | W9  | :389-390 | pc_reconv bits 直通 + valid 不过 fire 门控（I-31） | pipe_i31_* |
  | W10 | :169-171 | flushDCache 三行手动 Decoupled 对接 | pipe_flushDCache_fire_agree |
  | W11 | :374-401 | issueX/issueV 通道活性划分（死通道 ready 绑死） | pipe_issue_partition |
  | W12 | :416-427 | Writeback(6,6) 12 端口映射 | pipeWbInX/pipeWbInV + T8 |

  组合契约：
  | B-I2  | :366→branch_join | 掩码单调链第一环 | pipe_i2_mask_chain, pipe_i2_first_link |
  | B-I3  | :388,:392,:148,:252-254 | fetch_ctl 与 complete 互补 ⇒ beqReg 必清 | pipe_i3_* |
  | B-I4  | :223→ws:181→:161→sb:131,142 | 占用位组合门控发射（I-4 门控链重建） | pipe_i4_gate_chain* |
  | B-I31 | :390 | pc_reconv valid 不过 fire 门控的 witness | pipe_i31_witness |

  假设清单（B 类定理的前提，非本文件义务）：
  - H-BB：branch_back（Branch_back，固定优先级 Arbiter）在 in1（fetch_ctl）
    持续 valid 时终将授予，且 warp_sche.io.branch 接受（branch_ready =
    !flushCacheValid，见 WarpScheduler.lean `wsOut`）。branch_back 自身未建模。
  - H-WID：fetch_ctl/complete 事件的 wid 与该 vbranch/join 所属 warp 一致
    （branch_join.scala:120,:179 的 wid 传递，属 branch_join 模型范畴）。
  - H-IB2I：ibuffer2issue 内部不引入额外反压扭曲——本模型只承诺 :223/:224
    的门控等式，in.ready 由 ibuffer2issue 产生（Issue/IBuffer 模型范畴）。
  - H-DELAY：pipe_i4_gate_chain 的前提 `d (wsFin i) = sbDelay s c` 即
    scoreboard.scala:142 的 delay 定义（ibuffer_if_ctrl 为 :237 所接的
    ibuffer.io.out(i).bits）——把"d 是该 warp 的 delay"留作集成侧义务。

  未覆盖范围：inst_cnt 计数（:86-113）、GVM/SPIKE 调试通路、:296-307 的
  printf 观察点、icache_req 的 addr/mask 字段级语义（pc_req 按直通处理）、
  :403-408 的 rm 舍入模式三路分发（纯直通，无逻辑）。 -/

/- 公理审计（bv_decide 定理带每定理私有的 LRAT 检查 trust 公理
   `…._native.bv_decide.ax_*`，归档注明；本文件无 native_decide） -/
#print axioms pipeScoreboardBusy_bit
#print axioms pipe_w2_full_blocks_enq
#print axioms pipe_sb_ifFire_spec
#print axioms pipe_sb_brCtrl_spec
#print axioms pipe_vmask_sub_outMask
#print axioms pipe_issue_partition
#print axioms pipe_i2_mask_chain
#print axioms pipe_i2_first_link
#print axioms pipe_i3_branch_complete_or_fetch
#print axioms pipe_i3_vbranch_clears
#print axioms pipe_i3_join_clears
#print axioms pipe_sb_beqReg_cleared
#print axioms pipe_i4_gate_chain
#print axioms pipe_i4_gate_chain_beq
#print axioms pipe_i31_witness

end Ventus

