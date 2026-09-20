/- ========================================================================= -/
/-                     Arith/ExeVALU.lean                                    -/
/-  向量 ALU 执行级（vALUexe :414-475 与 vALUv2 :476-741）的 Lean 4 模型、    -/
/-  测试与证明                                                                -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/execution.scala     -/
/-    （vALUexe :414-474；vALUv2 :476-740，:507-571 为 soft==hard 等宽分支，  -/
/-      :573-736 为 soft>hard 分时拆分分支）                                  -/
/-    每 lane ALU 复用 ScalarALU（ALU.scala:61-117，模型见 ScalarALU.lean）； -/
/-    alu_fn 为 6 位（DecodeUnit.scala:60-100），喂给 ScalarALU 的是 (4,0)。  -/
/-  例化点（活代码判定）：                                                     -/
/-    pipe.scala:77  vALUv2(num_thread, num_lane)；parameters.scala:           -/
/-    num_thread=32、num_lane=num_thread=32 ⇒ **等宽分支为现役代码**，         -/
/-    拆分分支（soft>hard）当前配置不例化（潜在代码）；vALUexe 全模块无例化    -/
/-    （仅 vALUv2 被使用），属死模块，仍按源码忠实建模。                       -/
/-    ExtMem_gen.scala:39-40 有注释掉的 vALUv2TestWrapper(12,4)（maxIter=3     -/
/-    配置，与 Q2 的断裂条件吻合）。                                          -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. vALUexe 与 vALUv2 等宽分支共享逐 lane 数据通路（:423-449 ≈            -/
/-      :508-542），唯一差别是 vALUv2 多 :530-535 的比较覆写                  -/
/-      （rd := cmp_out.asUInt）。建模为 exvLaneRdV1（无覆写，vALUexe/        -/
/-      拆分分支）与 exvLaneRdV2（有覆写，vALUv2 等宽分支）两版。             -/
/-  D2. num_thread=32、xLen=32（parameters.scala:9）；wid 3 位（num_warp=8    -/
/-      ⇒ depth_warp=3）、reg_idxw 8 位（regidx 5 + regext 3）。Vec(Bool)     -/
/-      与 asUInt/asBools 的对应：lane x ↔ bit x（Chisel Vec(0) 为 LSB）。   -/
/-  D3. writemask 在当前配置恒不可达：DecodeUnit.scala:604                    -/
/-      `c.writemask := 0.U`（s(21) 被注释）。:451-456/:544-552 的打包块仍    -/
/-      忠实建模并钉死语义（若将来接回 s(21) 即为该行为）。                   -/
/-  D4. wvd_mask 覆写链按 Chisel 末赋值生效语义建模：:448/:453/:541/:548      -/
/-      的按位赋值均被其后 :462/:559 的无条件整体赋值                         -/
/-      `wvd_mask := io.in.bits.mask` 覆盖——最终恒等于输入 mask，             -/
/-      条件赋值是死代码（见 Q1）。                                           -/
/-  D5. 拆分分支 send/recv 共享同一 fire：send.valid=sendCS≠0（:637）、        -/
/-      send.ready=recv.ready（:638）、recv.valid=send.valid（:700），        -/
/-      故 send.fire ≡ recv.fire ≡ (sendCS≠0 ∧ recvRdy)。计数器建模为         -/
/-      Nat（Chisel 为 log2Ceil(maxIter+1) 位 +% 计数器；本 FSM 中 +% 仅在    -/
/-      CS<maxIter 时使用，不绕回，无语义差）。                               -/
/-  D6. Queue(1,pipe=true) 的内部寄存与 io.out 反压不建模；outFIFOReady       -/
/-      （:580）按源码 = Mux(inReg.ctrl.simt_stack, result2simt.enq.ready,    -/
/-      result.enq.ready) 建模（注意用的是 inReg 的 ctrl，见 Q6）。           -/
/-  D7. lane 矢量在拆分 FSM 中用平坦 BitVec（lane i ↔ bits [32i+31, 32i]）；  -/
/-      :622-633 的移位 = 无符号右移 32*hard（高端补 0，与源码逐 lane         -/
/-      if/else 一致）；:674-680 的合并 = 右移后高端插入本批结果。            -/
/-  D8. :681 的 `Cat(~cmpVec, if_mask(soft-1, soft-hard))` 宽 2*hard 位，     -/
/-      赋给 soft 位信号时 Chisel 高位补零（zero-pad）；按此建模（Q2 关键）。 -/
/-  D9. 拆分分支的 hardResult（:702-729）无 :530-535 的 cmp_out 覆写、        -/
/-      无 :544-552 的 writemask 打包——源码即无，按现状建模（Q4/Q5）。        -/
/-  D10. VID 在等宽分支 = lane 常数（:443-444/:536-537）；拆分分支 =          -/
/-      Mux(sendCS=0, 0, (sendCS-1)*hard + x)（:724-725），第 k 批硬 lane x   -/
/-      恰好对应全局 lane (k-1)*hard+x，两版语义一致（本文件给（8,4）数值     -/
/-      证据）。                                                              -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类，现役】wvd_mask 死赋值链：:448/:541（VMERGE 时 wvd_mask(x):=     -/
/-      true）与 :453/:548（writemask 时 wvd_mask(0):=1）均被 :462/:559       -/
/-      的无条件 `wvd_mask := io.in.bits.mask` 覆盖（Chisel 末赋值生效）。    -/
/-      后果：VMERGE 的实际写回掩码 = 输入 mask（v0 数据），mask 位为 0 的    -/
/-      lane 不回写 vd——与 vmerge"全 lane 写"语义的关系即 I-9 消费方核查      -/
/-      的现场。本文件定理 exv_wvdMask_final 钉死"恒等于 mask"。              -/
/-  Q2【I 类，潜在，拆分分支】:681 if_mask 跨批拼接取                           -/
/-      old(soft-1, soft-hard)（应为 old(soft-1, hard) 式的整体下移）且       -/
/-      Cat 宽 2*hard 赋给 soft 位零扩展——仅当 2*hard = soft（maxIter=2）     -/
/-      时正确；maxIter≥3 时早期批次逐批丢失，最终只剩末批 ~cmp 放在          -/
/-      bits [2hard-1, hard]。符号级证据：exv_ifmask_step_maxIter3；          -/
/-      端到端证据：exvSplit_simt_ifMask_broken_trace（(6,2) 配置，           -/
/-      期望 0b000011 实际 0）。当前配置拆分分支未例化 ⇒ 不可触发；若启用     -/
/-      hardThread 切分且 maxIter≥3，分支 if_mask 全错（SIMT 栈损坏）。       -/
/-  Q3【I 类，潜在，拆分分支】:620-635 的批次移位只移 in1/in2/in3，           -/
/-      **inReg.mask 不移位**；而 VMERGE 的选择端 :728 用 inReg.mask(x)       -/
/-      （恒为第 0 批的低 hard 位）——第 k≥2 批的 VMERGE 全部错用第 0 批       -/
/-      mask。端到端证据：exvSplit_vmerge_mask_not_shifted_trace。            -/
/-      （注：:688 resultReg.wvd_mask := inReg.mask 用整体原 mask，是对的。） -/
/-  Q4【I 类，潜在，拆分分支 + 死模块 vALUexe】比较指令（FN_SEQ/SNE/SGE/      -/
/-      SGEU/SLT/SLTU）的 cmp_out 覆写（:530-535）只存在于 vALUv2 等宽        -/
/-      分支；拆分分支（:702-729 无此覆写）与 vALUexe（:423-449 无此覆写）    -/
/-      回写的是 alu.out。其中 FN_SGE/FN_SGEU 的 out 是【未取反】的 slt       -/
/-      （ScalarALU 波次已钉死，ALU.scala:96），即 ≥ 变成 <。定理             -/
/-      exv_v1_sge_out_spec 钉死该现状；等宽分支不受影响（exv_sge_cmp_spec）。 -/
/-  Q5【I 类，潜在，拆分分支】writemask 打包块（:544-552）在拆分分支整体      -/
/-      缺失（:702-730 无对应逻辑）。当前因 DecodeUnit:604 writemask≡0        -/
/-      双重不可达；若拆分分支+writemask 同时启用，掩码指令不再打包到         -/
/-      rd(0)。                                                              -/
/-  Q6【I 类，潜在，拆分分支】:580 outFIFOReady 用 inReg.ctrl.simt_stack       -/
/-      选队。排空前最后一拍 sendNS=0 会把 inReg 清零（:612-613），故          -/
/-      simt 指令的结果在排空拍（recvCS=maxIter）按【result 队】的 ready      -/
/-      放行；若 result2simt 未就绪而 result 就绪，recvNS=0 直接清            -/
/-      resultReg/simtReg.if_mask（:668-670）——simt 结果未经握手被丢弃。     -/
/-      端到端证据：exvSplit_simt_drop_witness_trace。连续流时 inReg 是        -/
/-      下一条指令的 ctrl，同样可能错配。修复建议：改用 recv_simt_stack       -/
/-      （:694 已锁存）选队。                                                -/
/-  Q7【观察】:453/:548 `wvd_mask(0):=1.U` 是 UInt→Bool 连接且为死赋值        -/
/-      （被 :462/:559 覆盖）。                                              -/
/-  Q8【观察】:681 simtReg.if_mask 的赋值位于 (0 until softThread).foreach    -/
/-      内部，同一信号被重复赋值 softThread 次（同值，无害冗余）。            -/
/-  Q9【观察】vALUexe 全模块无例化（pipe.scala 只用 vALUv2）；其与等宽        -/
/-      分支的唯一差异正是 Q4 的缺失覆写。                                    -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Arith.ScalarALU
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 6 位 alu_fn 常量（DecodeUnit.scala:60-100）                              -/
/- ========================================================================= -/

def exvFN_ADD     : BitVec 6 := 0    -- DecodeUnit.scala（FN_ADD）
def exvFN_SEQ     : BitVec 6 := 2    -- :64
def exvFN_SNE     : BitVec 6 := 3    -- :65
def exvFN_SLT     : BitVec 6 := 12   -- :72
def exvFN_SGE     : BitVec 6 := 13   -- :73
def exvFN_SLTU    : BitVec 6 := 14   -- :74
def exvFN_SGEU    : BitVec 6 := 15   -- :75
def exvFN_VMERGE  : BitVec 6 := 51   -- :100
def exvFN_VMNOR   : BitVec 6 := 54   -- :94
def exvFN_VMNAND  : BitVec 6 := 55   -- :95
def exvFN_VMXNOR  : BitVec 6 := 56   -- :96
def exvFN_VID     : BitVec 6 := 57   -- :99
def exvFN_VMORNOT : BitVec 6 := 58   -- :97
def exvFN_VMANDNOT: BitVec 6 := 59   -- :98

/-- :433/:518  五个掩码逻辑操作码判定 -/
def exvIsVmLogic (fn : BitVec 6) : Bool :=
  (fn == exvFN_VMANDNOT) || (fn == exvFN_VMORNOT) || (fn == exvFN_VMNAND)
    || (fn == exvFN_VMNOR) || (fn == exvFN_VMXNOR)

/-- :434/:519  in1 取反组（VMANDNOT/VMORNOT） -/
def exvIsVmNegIn1 (fn : BitVec 6) : Bool := (fn == exvFN_VMANDNOT) || (fn == exvFN_VMORNOT)

/-- :440/:527  输出取反组（VMNAND/VMNOR/VMXNOR） -/
def exvIsVmNegOut (fn : BitVec 6) : Bool :=
  (fn == exvFN_VMNAND) || (fn == exvFN_VMNOR) || (fn == exvFN_VMXNOR)

/-- :530-533  比较覆写组（仅 vALUv2 等宽分支） -/
def exvIsCmpFn (fn : BitVec 6) : Bool :=
  (fn == exvFN_SEQ) || (fn == exvFN_SNE) || (fn == exvFN_SGE)
    || (fn == exvFN_SGEU) || (fn == exvFN_SLT) || (fn == exvFN_SLTU)

/- ========================================================================= -/
/- 2. 逐 lane ALU 输入重接（:424-442/:509-529/:702-723）                        -/
/- ========================================================================= -/

/-- :436-439/:521-526  func 重接：
    VMANDNOT/VMORNOT/VMNAND/VMNOR → Cat(3.U(4.W), alu_fn(0))（= 7 AND / 6 OR）；
    VMXNOR → FN_XOR(4,0) = 4；其余 → alu_fn(4,0) -/
def exvAluFunc (fn : BitVec 6) : BitVec 5 :=
  if exvIsVmNegIn1 fn || (fn == exvFN_VMNAND) || (fn == exvFN_VMNOR) then
    (3#4 ++ fn.extractLsb' 0 1 : BitVec 5)
  else if fn = exvFN_VMXNOR then 4#5
  else fn.extractLsb' 0 5

/-- in1 重接。注意 :435/:520 用【原始】in1 取反，覆盖 reverse 的交换结果 -/
def exvAluIn1 (fn : BitVec 6) (rev : Bool) (in1 in2 : BitVec 32) : BitVec 32 :=
  if exvIsVmNegIn1 fn then ~~~in1
  else if rev then in2 else in1

/-- in2 重接（:429-432/:514-517，reverse 交换） -/
def exvAluIn2 (fn : BitVec 6) (rev : Bool) (in1 in2 : BitVec 32) : BitVec 32 :=
  if rev then in1 else in2

/-- 逐 lane ALU 组合结果（复用 saAlu；in3 无通路，见 ScalarALU D1） -/
def exvLaneAlu (fn : BitVec 6) (rev : Bool) (in1 in2 in3 : BitVec 32) : BitVec 32 × Bool :=
  saAlu (exvAluFunc fn) (exvAluIn1 fn rev in1 in2) (exvAluIn2 fn rev in1 in2) in3

/- ========================================================================= -/
/- 3. 逐 lane 写回数据（V1 = vALUexe :423-449 / 拆分分支 :702-729；             -/
/-    V2 = vALUv2 等宽分支 :508-542）                                          -/
/- ========================================================================= -/

/-- V1：无比较覆写。覆写优先级（Chisel 末赋值生效）：VMERGE > VID > 输出取反 > alu.out -/
def exvLaneRdV1 (fn : BitVec 6) (rev mask : Bool)
    (in1 in2 in3 laneId : BitVec 32) : BitVec 32 :=
  let out := (exvLaneAlu fn rev in1 in2 in3).1
  let r0 := if exvIsVmNegOut fn then ~~~out else out              -- :440
  let r1 := if fn = exvFN_VID then laneId else r0                 -- :443-444
  let r2 := if fn = exvFN_VMERGE then (if mask then in1 else in2) else r1  -- :447
  r2

/-- V2：在 V1 基础上于 VM 块之后插入 :530-535 的 cmp_out 覆写 -/
def exvLaneRdV2 (fn : BitVec 6) (rev mask : Bool)
    (in1 in2 in3 laneId : BitVec 32) : BitVec 32 :=
  let (out, cmp) := exvLaneAlu fn rev in1 in2 in3
  let r0 := if exvIsVmNegOut fn then ~~~out else out              -- :527
  let r1 := if exvIsCmpFn fn then (if cmp then 1#32 else 0#32) else r0  -- :530-535
  let r2 := if fn = exvFN_VID then laneId else r1                 -- :536-537
  let r3 := if fn = exvFN_VMERGE then (if mask then in1 else in2) else r2  -- :539-540
  r3

/-- :468/:563  if_mask = ~(VecInit(alu.map(_.cmp_out)).asUInt)，位 x = ~(cmp x) -/
def exvIfMask (cmpV : BitVec 32) : BitVec 32 := ~~~cmpV

/- ========================================================================= -/
/- 4. writemask 打包（:451-456/:544-552；当前配置 writemask≡0 不可达，D3）     -/
/- ========================================================================= -/

/-- :452/:545-547  打包位 x = mask(x) && alu(x).out(0)（Vec(Bool).asUInt ↔ 位与，D2） -/
def exvPackMask (maskV out0V : BitVec 32) : BitVec 32 := maskV &&& out0V

/-- :455/:550-551  取反组打包位 x = mask(x) && !alu(x).out(0) -/
def exvPackMaskN (maskV out0V : BitVec 32) : BitVec 32 := maskV &&& ~~~out0V

/-- writemask 时 rd(0)（:452-456/:545-552）。注意取反组覆写【无条件】覆盖
    readmask 分支（:454 内层 when 不看 readmask） -/
def exvWrRd0 (fn : BitVec 6) (readmask : Bool)
    (alu0out maskV out0V : BitVec 32) : BitVec 32 :=
  let base := if readmask then alu0out else exvPackMask maskV out0V
  if exvIsVmNegOut fn then exvPackMaskN maskV out0V else base

/-- wvd_mask 最终值（:462/:559 无条件赋值覆盖 :448/:453/:541/:548，D4/Q1） -/
def exvWvdMask (maskV : BitVec 32) : BitVec 32 := maskV

/- ========================================================================= -/
/- 5. vALUexe/vALUv2 等宽分支的握手组合（:463-471/:560-570）                    -/
/- ========================================================================= -/

/-- :463/:560  result.io.enq.valid -/
def exvOutEnqValid (v wvd simt : Bool) : Bool := v && wvd && !simt

/-- :469/:564  result2simt.io.enq.valid -/
def exvSimtEnqValid (v simt : Bool) : Bool := v && simt

/-- :471/:570  io.in.ready -/
def exvInReady (simt rdySimt rdyResult : Bool) : Bool :=
  if simt then rdySimt else rdyResult

/- ========================================================================= -/
/- 6. 数值回归测试（先测试：全部 by decide）                                    -/
/- ========================================================================= -/

section ExvRegressionTests

-- VM 掩码逻辑五操作码（逐 lane 语义）
example : exvLaneRdV2 exvFN_VMANDNOT false false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32) &&& 0xFF00FF00#32 := by decide
example : exvLaneRdV2 exvFN_VMORNOT false false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32) ||| 0xFF00FF00#32 := by decide
example : exvLaneRdV2 exvFN_VMNAND false false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32 &&& 0xFF00FF00#32) := by decide
example : exvLaneRdV2 exvFN_VMNOR false false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32 ||| 0xFF00FF00#32) := by decide
example : exvLaneRdV2 exvFN_VMXNOR false false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32 ^^^ 0xFF00FF00#32) := by decide

-- VMANDNOT 的 in1 取反优先于 reverse（:435 覆盖 :430 的交换）：
-- rev=true 时 in1' = ~in1（原始），in2' = in1（原始）
example : exvLaneRdV2 exvFN_VMANDNOT true false 0xF0F0F0F0#32 0xFF00FF00#32 0#32 0#32
    = ~~~(0xF0F0F0F0#32) &&& 0xF0F0F0F0#32 := by decide

-- VID：写 lane 编号
example : exvLaneRdV2 exvFN_VID false false 0#32 0#32 0#32 5#32 = 5#32 := by decide
example : exvLaneRdV1 exvFN_VID true true 0xAAAA#32 0xBBBB#32 0#32 31#32 = 31#32 := by decide

-- VMERGE：mask 选择 in1/in2（原始值，不受 reverse 影响，:447）
example : exvLaneRdV2 exvFN_VMERGE false true 0xAAAA#32 0xBBBB#32 0#32 0#32
    = 0xAAAA#32 := by decide
example : exvLaneRdV2 exvFN_VMERGE true false 0xAAAA#32 0xBBBB#32 0#32 0#32
    = 0xBBBB#32 := by decide
example : exvLaneRdV2 exvFN_VMERGE true true 0xAAAA#32 0xBBBB#32 0#32 0#32
    = 0xAAAA#32 := by decide

-- 比较指令（V2 覆写为 cmp_out）
example : exvLaneRdV2 exvFN_SEQ false false 42#32 42#32 0#32 0#32 = 1#32 := by decide
example : exvLaneRdV2 exvFN_SEQ false false 42#32 43#32 0#32 0#32 = 0#32 := by decide
example : exvLaneRdV2 exvFN_SNE false false 42#32 43#32 0#32 0#32 = 1#32 := by decide
example : exvLaneRdV2 exvFN_SLT false false 0x80000000#32 0#32 0#32 0#32 = 1#32 := by decide
-- SGE：cmp_out 语义为 ≥（与 ScalarALU 的 out 相反）
example : exvLaneRdV2 exvFN_SGE false false 5#32 3#32 0#32 0#32 = 1#32 := by decide
example : exvLaneRdV2 exvFN_SGE false false 3#32 5#32 0#32 0#32 = 0#32 := by decide
-- V1（vALUexe/拆分分支）无覆写：SGE 回写未取反 slt（Q4）
example : exvLaneRdV1 exvFN_SGE false false 5#32 3#32 0#32 0#32 = 0#32 := by decide
example : exvLaneRdV1 exvFN_SGE false false 3#32 5#32 0#32 0#32 = 1#32 := by decide
-- reverse 的比较（VMSLE 用法：交换后 SGE(vs2,vs1) ⇔ vs1 ≤ vs2）
example : exvLaneRdV2 exvFN_SGE true false 3#32 5#32 0#32 0#32 = 1#32 := by decide

-- writemask 打包
example : exvWrRd0 exvFN_ADD false 0xDEADBEEF#32 0b1010#32 0b1100#32 = 0b1000#32 := by decide
example : exvWrRd0 exvFN_ADD true 0xDEADBEEF#32 0b1010#32 0b1100#32
    = 0xDEADBEEF#32 := by decide
-- 取反组无条件覆盖 readmask（:454-456）
example : exvWrRd0 exvFN_VMNAND true 0xDEADBEEF#32 0b1010#32 0b1100#32
    = 0b1010#32 &&& ~~~(0b1100#32) := by decide
example : exvWrRd0 exvFN_VMXNOR false 0#32 0xFFFFFFFF#32 0xAAAA5555#32
    = 0x5555AAAA#32 := by decide

-- if_mask / 握手
example : exvIfMask 0b0101#32 = ~~~(0b0101#32) := by decide
example : exvOutEnqValid true true false = true := by decide
example : exvOutEnqValid true true true = false := by decide
example : exvSimtEnqValid true true = true := by decide
example : exvInReady true false true = false := by decide
example : exvInReady false false true = true := by decide

-- wvd_mask 恒等（D4/Q1）
example : exvWvdMask 0x5A5A5A5A#32 = 0x5A5A5A5A#32 := by decide

end ExvRegressionTests

/- ========================================================================= -/
/- 7. 逐操作码规约定理（后证明：自由变量，bv_decide）                            -/
/- ========================================================================= -/

/-- 展开 vALU 侧定义的标准 simp 集（bv_decide 看不穿 def，须先展开） -/
macro "exv_unfold" : tactic =>
  `(tactic| simp only [exvLaneRdV1, exvLaneRdV2, exvLaneAlu, exvAluFunc, exvAluIn1,
    exvAluIn2, exvIsVmLogic, exvIsVmNegIn1, exvIsVmNegOut, exvIsCmpFn,
    exvFN_ADD, exvFN_SEQ, exvFN_SNE, exvFN_SLT, exvFN_SGE, exvFN_SLTU, exvFN_SGEU,
    exvFN_VMERGE, exvFN_VMNOR, exvFN_VMNAND, exvFN_VMXNOR, exvFN_VID,
    exvFN_VMORNOT, exvFN_VMANDNOT])

-- VM 掩码逻辑五操作码（rev=false 形态）
theorem exv_vmandnot_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMANDNOT false m in1 in2 in3 lane = ~~~in1 &&& in2 := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_vmornot_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMORNOT false m in1 in2 in3 lane = ~~~in1 ||| in2 := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_vmnand_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMNAND false m in1 in2 in3 lane = ~~~(in1 &&& in2) := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_vmnor_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMNOR false m in1 in2 in3 lane = ~~~(in1 ||| in2) := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_vmxnor_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMXNOR false m in1 in2 in3 lane = ~~~(in1 ^^^ in2) := by
  exv_unfold; sa_unfold; bv_decide

/-- VMANDNOT 的 in1 取反优先于 reverse（rev 自由变量形态，钉死 :435 覆盖 :430） -/
theorem exv_vmandnot_rev_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMANDNOT true m in1 in2 in3 lane = ~~~in1 &&& in1 := by
  exv_unfold; sa_unfold; bv_decide

-- VID / VMERGE
theorem exv_vid_spec (rev m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VID rev m in1 in2 in3 lane = lane := by
  exv_unfold; sa_unfold; bv_decide

/-- VMERGE 用原始 in1/in2，不受 reverse 影响（:447；rev 为自由变量） -/
theorem exv_vmerge_spec (rev m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_VMERGE rev m in1 in2 in3 lane = (if m then in1 else in2) := by
  exv_unfold; sa_unfold; bv_decide

-- 比较六操作码（V2 = cmp_out 语义）
theorem exv_seq_cmp_spec (rev m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SEQ rev m in1 in2 in3 lane
      = (if exvAluIn2 exvFN_SEQ rev in1 in2 = exvAluIn1 exvFN_SEQ rev in1 in2
         then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; cases rev <;> bv_decide

theorem exv_slt_cmp_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SLT false m in1 in2 in3 lane
      = (if BitVec.slt in1 in2 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_sltu_cmp_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SLTU false m in1 in2 in3 lane
      = (if BitVec.ult in1 in2 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

/-- SGE：V2 回写 ≥ 语义（cmp_out） -/
theorem exv_sge_cmp_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SGE false m in1 in2 in3 lane
      = (if BitVec.sle in2 in1 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

theorem exv_sgeu_cmp_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SGEU false m in1 in2 in3 lane
      = (if BitVec.ule in2 in1 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

/-- 【Q4】V1（vALUexe/拆分分支）无 cmp 覆写：SGE 回写未取反的 slt -/
theorem exv_v1_sge_out_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV1 exvFN_SGE false m in1 in2 in3 lane
      = (if BitVec.slt in1 in2 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

/-- reverse（VMSLE 用法）：交换后 SGE ⇔ in1 ≤ in2 -/
theorem exv_sge_rev_cmp_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_SGE true m in1 in2 in3 lane
      = (if BitVec.sle in1 in2 then 1#32 else 0#32) := by
  exv_unfold; sa_unfold; bv_decide

/-- 普通算术（reverse 交换操作数） -/
theorem exv_add_rev_spec (m : Bool) (in1 in2 in3 lane : BitVec 32) :
    exvLaneRdV2 exvFN_ADD true m in1 in2 in3 lane = in2 + in1 := by
  exv_unfold; sa_unfold; bv_decide

/-- V1/V2 一致性：fn 不在比较组时两版相同（:530-535 是唯一差异，D1/Q9） -/
theorem exv_v2_eq_v1_of_not_cmp (fn : BitVec 6) (rev m : Bool)
    (in1 in2 in3 lane : BitVec 32) (h : exvIsCmpFn fn = false) :
    exvLaneRdV2 fn rev m in1 in2 in3 lane = exvLaneRdV1 fn rev m in1 in2 in3 lane := by
  cases hb : exvIsCmpFn fn <;> simp_all [exvLaneRdV2, exvLaneRdV1]

/-- writemask 打包：非取反组 readmask=false 时 rd(0) = mask &&& out0 -/
theorem exv_pack_spec (fn : BitVec 6) (alu0 m o : BitVec 32)
    (h : exvIsVmNegOut fn = false) :
    exvWrRd0 fn false alu0 m o = m &&& o := by
  cases hb : exvIsVmNegOut fn <;> simp_all [exvWrRd0, exvPackMask]

/-- 取反组无条件覆盖 readmask（:454-456） -/
theorem exv_pack_neg_spec (rm : Bool) (alu0 m o : BitVec 32) :
    exvWrRd0 exvFN_VMNAND rm alu0 m o = m &&& ~~~o := by
  simp [exvWrRd0, exvPackMaskN, exvIsVmNegOut, exvFN_VMNAND, exvFN_VMNOR,
    exvFN_VMXNOR]

/-- wvd_mask 恒等于输入 mask（D4/Q1：:448/:453/:541/:548 均为死赋值） -/
theorem exv_wvdMask_final (m : BitVec 32) : exvWvdMask m = m := rfl

/-- if_mask = 按位取反（:468/:563） -/
theorem exv_ifmask_spec (c : BitVec 32) : exvIfMask c = ~~~c := rfl

/- ========================================================================= -/
/- 8. vALUv2 拆分分支（soft>hard，:573-736）时序模型                            -/
/-    当前配置未例化（pipe.scala:77 传 num_lane=num_thread），属潜在代码；      -/
/-    建模目的：钉死批次调度正确性（maxIter=2）与暴露 Q2/Q3/Q6。               -/
/- ========================================================================= -/

/-- 拆分分支状态。in1/in2/in3/rd 为平坦矢量（lane i ↔ bits [32i+31, 32i]，D7）；
    sendCS/recvCS 建模为 Nat（D5） -/
structure ExvSplitState (soft : Nat) where
  sendCS : Nat
  recvCS : Nat
  in1 : BitVec (32 * soft)
  in2 : BitVec (32 * soft)
  in3 : BitVec (32 * soft)
  mask : BitVec soft
  fn : BitVec 6
  rev : Bool
  wm : Bool
  rm : Bool
  wvd : Bool
  simt : Bool
  wid : BitVec 3
  ridx : BitVec 8
  rd : BitVec (32 * soft)
  rmask : BitVec soft
  rwvd : Bool
  rwid : BitVec 3
  rridx : BitVec 8
  ifMask : BitVec soft
  simtWid : BitVec 3
  recvWvd : Bool
  recvSimt : Bool

/-- 拆分分支每拍输入（io.in 内容 + 两队列 enq.ready） -/
structure ExvSplitIn (soft : Nat) where
  fire : Bool
  in1 : BitVec (32 * soft)
  in2 : BitVec (32 * soft)
  in3 : BitVec (32 * soft)
  mask : BitVec soft
  fn : BitVec 6
  rev : Bool
  wm : Bool
  rm : Bool
  wvd : Bool
  simt : Bool
  wid : BitVec 3
  ridx : BitVec 8
  resRdy : Bool
  simtRdy : Bool

/-- 当前拍硬 lane x 的 hardResult（:702-729；无 cmp 覆写 Q4、无 writemask Q5。
    VMERGE 用 inReg.mask(x)——mask 不移位（Q3）；VID 用 :725 的全局编号公式（D10） -/
def exvSplitHardResult {soft : Nat} (hard : Nat) (st : ExvSplitState soft) (x : Nat) :
    BitVec 32 :=
  let i1 := st.in1.extractLsb' (32 * x) 32
  let i2 := st.in2.extractLsb' (32 * x) 32
  let i3 := st.in3.extractLsb' (32 * x) 32
  let out := (exvLaneAlu st.fn st.rev i1 i2 i3).1
  let r0 := if exvIsVmNegOut st.fn then ~~~out else out                     -- :721
  let r1 := if st.fn = exvFN_VID then                                       -- :724-725
      (if st.sendCS = 0 then 0#32 else BitVec.ofNat 32 ((st.sendCS - 1) * hard + x))
    else r0
  let r2 := if st.fn = exvFN_VMERGE then (if st.mask.getLsbD x then i1 else i2) else r1  -- :727-728
  r2

/-- 当前拍硬 lane 阵列结果平坦装配（:707/:721/... hardResult 全体） -/
def exvSplitHardFlat {soft : Nat} (hard : Nat) (st : ExvSplitState soft) :
    BitVec (32 * hard) :=
  (List.range hard).foldl (fun acc x =>
    acc ||| (BitVec.zeroExtend (32 * hard) (exvSplitHardResult hard st x) <<< (32 * x)))
    0

/-- 当前拍硬 lane 阵列 cmp_out 平坦装配（:681 的 VecInit(alu.map(_.cmp_out))） -/
def exvSplitCmpFlat {soft : Nat} (hard : Nat) (st : ExvSplitState soft) : BitVec hard :=
  (List.range hard).foldl (fun acc x =>
    let i1 := st.in1.extractLsb' (32 * x) 32
    let i2 := st.in2.extractLsb' (32 * x) 32
    let i3 := st.in3.extractLsb' (32 * x) 32
    if (exvLaneAlu st.fn st.rev i1 i2 i3).2 then acc ||| (1 <<< x) else acc) 0

/-- :674-680  结果跨批合并：低 soft-hard 个 lane 上移，本批结果插到顶端 -/
def exvSplitRdMerge {soft : Nat} (hard : Nat) (rd : BitVec (32 * soft))
    (hr : BitVec (32 * hard)) : BitVec (32 * soft) :=
  (rd >>> (32 * hard)) ||| (BitVec.zeroExtend (32 * soft) hr <<< (32 * (soft - hard)))

/-- :681  if_mask 跨批拼接：Cat(~cmpVec, old(soft-1, soft-hard))，
    宽 2*hard 位，零扩展到 soft（D8）——仅 maxIter=2 时正确（Q2） -/
def exvSplitIfMaskStep {soft : Nat} (hard : Nat) (cmpV : BitVec hard) (old : BitVec soft) :
    BitVec soft :=
  BitVec.zeroExtend soft ((~~~cmpV) ++ (old.extractLsb' (soft - hard) hard))

/-- 单拍转移（:582-736） -/
def exvSplitStep {soft : Nat} (hard maxIter : Nat)
    (st : ExvSplitState soft) (inp : ExvSplitIn soft) : ExvSplitState soft :=
  -- :580  outFIFOReady（注意：用 inReg.ctrl.simt_stack，不是排空指令的 recvSimt——Q6）
  let outRdy := if st.simt then inp.simtRdy else inp.resRdy
  -- :699  recv.ready
  let recvRdy := st.recvCS ≠ maxIter ∨ (st.recvCS = maxIter ∧ outRdy = true)
  -- D5：send.fire ≡ recv.fire ≡ (sendCS≠0 ∧ recvRdy)（:637-638/:700）
  let fire := st.sendCS ≠ 0 ∧ recvRdy
  -- :589-609  sendNS
  let sendNS :=
    if st.sendCS = 0 then (if inp.fire then 1 else 0)
    else if st.sendCS = maxIter then (if fire then (if inp.fire then 1 else 0) else st.sendCS)
    else (if fire then st.sendCS + 1 else st.sendCS)
  -- :646-665  recvNS
  let recvNS :=
    if st.recvCS = maxIter then (if outRdy then (if fire then 1 else 0) else st.recvCS)
    else (if fire then st.recvCS + 1 else st.recvCS)
  -- 当前拍硬 lane 组合结果（:702-730 与 :681 的 cmp）
  let hardFlat := exvSplitHardFlat hard st
  let cmpFlat := exvSplitCmpFlat hard st
  { sendCS := sendNS
    recvCS := recvNS
    -- :611-636  inReg（按 sendNS；NS≥2 移位时只移 in1/2/3，mask/ctrl 不动——Q3）
    in1 := if sendNS = 0 then 0
      else if sendNS = 1 then (if inp.fire then inp.in1 else st.in1)
      else (if st.sendCS ≠ sendNS then st.in1 >>> (32 * hard) else st.in1)
    in2 := if sendNS = 0 then 0
      else if sendNS = 1 then (if inp.fire then inp.in2 else st.in2)
      else (if st.sendCS ≠ sendNS then st.in2 >>> (32 * hard) else st.in2)
    in3 := if sendNS = 0 then 0
      else if sendNS = 1 then (if inp.fire then inp.in3 else st.in3)
      else (if st.sendCS ≠ sendNS then st.in3 >>> (32 * hard) else st.in3)
    mask := if sendNS = 0 then 0 else if sendNS = 1 then (if inp.fire then inp.mask else st.mask)
      else st.mask
    fn := if sendNS = 0 then 0 else if sendNS = 1 then (if inp.fire then inp.fn else st.fn)
      else st.fn
    rev := if sendNS = 0 then false else if sendNS = 1 then (if inp.fire then inp.rev else st.rev)
      else st.rev
    wm := if sendNS = 0 then false else if sendNS = 1 then (if inp.fire then inp.wm else st.wm)
      else st.wm
    rm := if sendNS = 0 then false else if sendNS = 1 then (if inp.fire then inp.rm else st.rm)
      else st.rm
    wvd := if sendNS = 0 then false else if sendNS = 1 then (if inp.fire then inp.wvd else st.wvd)
      else st.wvd
    simt := if sendNS = 0 then false else if sendNS = 1 then (if inp.fire then inp.simt else st.simt)
      else st.simt
    wid := if sendNS = 0 then 0 else if sendNS = 1 then (if inp.fire then inp.wid else st.wid)
      else st.wid
    ridx := if sendNS = 0 then 0 else if sendNS = 1 then (if inp.fire then inp.ridx else st.ridx)
      else st.ridx
    -- :667-698  recv 侧（按 recvNS）
    rd := if recvNS = 0 then 0
      else if fire then exvSplitRdMerge hard st.rd hardFlat
      else st.rd
    ifMask := if recvNS = 0 then 0
      else if fire then exvSplitIfMaskStep hard cmpFlat st.ifMask
      else st.ifMask
    -- :683-691  末批锁存 resultReg 头部字段
    rmask := if recvNS = 0 then 0
      else if fire ∧ recvNS = maxIter then st.mask
      else st.rmask
    rwvd := if recvNS = 0 then false
      else if fire ∧ recvNS = maxIter then st.wvd
      else st.rwvd
    rwid := if recvNS = 0 then 0
      else if fire ∧ recvNS = maxIter then st.wid
      else st.rwid
    rridx := if recvNS = 0 then 0
      else if fire ∧ recvNS = maxIter then st.ridx
      else st.rridx
    -- :692  simtReg.wid 末批锁存（:668-670 清零分支不动 wid）
    simtWid := if fire ∧ recvNS ≠ 0 ∧ recvNS = maxIter then st.wid else st.simtWid
    -- :693-694  recv_wvd / recv_simt_stack（裸 Reg，清零分支不动）
    recvWvd := if fire ∧ recvNS ≠ 0 ∧ recvNS = maxIter then st.wvd else st.recvWvd
    recvSimt := if fire ∧ recvNS ≠ 0 ∧ recvNS = maxIter then st.simt else st.recvSimt }

/-- :731  result.io.enq.valid -/
def exvSplitOutValid {soft : Nat} (maxIter : Nat) (st : ExvSplitState soft) : Bool :=
  (st.recvCS == maxIter) && st.recvWvd && !st.recvSimt

/-- :732  result2simt.io.enq.valid -/
def exvSplitSimtValid {soft : Nat} (maxIter : Nat) (st : ExvSplitState soft) : Bool :=
  (st.recvCS == maxIter) && st.recvSimt

/-- :736  io.in.ready -/
def exvSplitInReady {soft : Nat} (maxIter : Nat) (st : ExvSplitState soft)
    (outRdy : Bool) : Bool :=
  (st.sendCS == 0) || ((st.sendCS == maxIter) && outRdy)

/-- 初始状态（RegNext/Reg 上电值在 Chisel 中未指定；功能轨迹从零值开始，与
    `recvNS=0/sendNS=0` 清零分支自洽） -/
def exvSplitInit (soft : Nat) : ExvSplitState soft where
  sendCS := 0
  recvCS := 0
  in1 := 0
  in2 := 0
  in3 := 0
  mask := 0
  fn := 0
  rev := false
  wm := false
  rm := false
  wvd := false
  simt := false
  wid := 0
  ridx := 0
  rd := 0
  rmask := 0
  rwvd := false
  rwid := 0
  rridx := 0
  ifMask := 0
  simtWid := 0
  recvWvd := false
  recvSimt := false

/- ========================================================================= -/
/- 9. if_mask 拼接的组合级定理（:681；Q2 的符号级证据）                          -/
/- ========================================================================= -/

/-- maxIter=2（soft=2*hard）时单步拼接 = 精确 Cat（无零扩展损失） -/
theorem exv_ifmask_step_8_4 (c : BitVec 4) (o : BitVec 8) :
    exvSplitIfMaskStep (soft := 8) 4 c o = ((~~~c) ++ o.extractLsb' 4 4 : BitVec 8) := by
  simp only [exvSplitIfMaskStep]
  bv_decide

/-- maxIter=2 两批累积正确：先批在低 hard 位，后批在高 hard 位 -/
theorem exv_ifmask_two_batch_correct (c1 c2 : BitVec 4) :
    exvSplitIfMaskStep (soft := 8) 4 c2 (exvSplitIfMaskStep 4 c1 0#8)
      = ((~~~c2) ++ (~~~c1) : BitVec 8) := by
  simp only [exvSplitIfMaskStep]
  bv_decide

/-- 【Q2】maxIter=3（soft=3*hard）时三批累积 = 只剩末批 ~cmp 放在
    bits [2hard-1, hard]：前两批全部丢失 -/
theorem exv_ifmask_maxIter3_broken (c1 c2 c3 : BitVec 2) :
    exvSplitIfMaskStep (soft := 6) 2 c3 (exvSplitIfMaskStep 2 c2 (exvSplitIfMaskStep 2 c1 0#6))
      = (BitVec.zeroExtend 6 (~~~c3) <<< 2) := by
  simp only [exvSplitIfMaskStep]
  bv_decide

/-- 【Q2 witness】c1=0（~c1=11 应落 bit0-1）时，正确值 0b000011，实际 0 -/
theorem exv_ifmask_maxIter3_witness :
    exvSplitIfMaskStep (soft := 6) 2 0b11#2
        (exvSplitIfMaskStep 2 0b11#2 (exvSplitIfMaskStep 2 0b00#2 0#6))
      = 0#6 ∧ (0b000011#6 : BitVec 6) ≠ 0#6 := by
  decide

/- ========================================================================= -/
/- 10. 端到端轨迹测试（native_decide；AGENTS：多拍轨迹一律 native_decide，     -/
/-     公理审计会多 Lean.ofReduceBool）                                        -/
/- ========================================================================= -/

/-- 测试辅助：8 lane 平坦矢量装配 -/
def exvFlat8 (f : Nat → BitVec 32) : BitVec (32 * 8) :=
  (List.range 8).foldl (fun acc i =>
    acc ||| (BitVec.zeroExtend (32 * 8) (f i) <<< (32 * i))) 0

/-- 测试辅助：6 lane 平坦矢量装配 -/
def exvFlat6 (f : Nat → BitVec 32) : BitVec (32 * 6) :=
  (List.range 6).foldl (fun acc i =>
    acc ||| (BitVec.zeroExtend (32 * 6) (f i) <<< (32 * i))) 0

/-- 空闲拍输入（下游恒就绪） -/
def exvTestIdle8 : ExvSplitIn 8 where
  fire := false
  in1 := 0
  in2 := 0
  in3 := 0
  mask := 0
  fn := 0
  rev := false
  wm := false
  rm := false
  wvd := false
  simt := false
  wid := 0
  ridx := 0
  resRdy := true
  simtRdy := true

/-- (8,4) ADD 指令输入：lane i 的 in1 = i+1，in2 = 0x100 -/
def exvTestInpAdd : ExvSplitIn 8 where
  fire := true
  in1 := exvFlat8 (fun i => BitVec.ofNat 32 (i + 1))
  in2 := exvFlat8 (fun _ => 0x100#32)
  in3 := 0
  mask := 0xFF#8
  fn := exvFN_ADD
  rev := false
  wm := false
  rm := false
  wvd := true
  simt := false
  wid := 5#3
  ridx := 0x2A#8
  resRdy := true
  simtRdy := true

/-- 批次调度不漏不重 + 跨批合并正确（(8,4)，maxIter=2，ADD）：
    st1 捕获、st2 第一批入顶端、st3 排空可见且 lane i = (i+1)+0x100 -/
theorem exvSplit_add_trace :
    let st1 := exvSplitStep 4 2 (exvSplitInit 8) exvTestInpAdd
    let st2 := exvSplitStep 4 2 st1 exvTestIdle8
    let st3 := exvSplitStep 4 2 st2 exvTestIdle8
    st1.sendCS = 1 ∧ st1.recvCS = 0
    ∧ exvSplitInReady 2 st1 true = false                       -- 忙时不收新指令
    ∧ st2.sendCS = 2 ∧ st2.recvCS = 1
    ∧ st2.rd.extractLsb' 128 32 = 0x101#32                     -- 批1 lane0 暂存顶端
    ∧ st2.rd.extractLsb' 224 32 = 0x104#32                     -- 批1 lane3
    ∧ st3.sendCS = 0 ∧ st3.recvCS = 2
    ∧ exvSplitOutValid 2 st3 = true ∧ exvSplitSimtValid 2 st3 = false
    ∧ exvSplitInReady 2 st3 true = true
    ∧ st3.rd.extractLsb' 0 32 = 0x101#32
    ∧ st3.rd.extractLsb' 32 32 = 0x102#32
    ∧ st3.rd.extractLsb' 64 32 = 0x103#32
    ∧ st3.rd.extractLsb' 96 32 = 0x104#32
    ∧ st3.rd.extractLsb' 128 32 = 0x105#32
    ∧ st3.rd.extractLsb' 160 32 = 0x106#32
    ∧ st3.rd.extractLsb' 192 32 = 0x107#32
    ∧ st3.rd.extractLsb' 224 32 = 0x108#32
    ∧ st3.rmask = 0xFF#8 ∧ st3.rwid = 5#3 ∧ st3.rridx = 0x2A#8 ∧ st3.rwvd = true := by
  native_decide

/-- (8,4) SEQ simt 指令：偶数 lane 不等（~cmp=1），奇数 lane 相等。
    if_mask 两批拼接端到端正确（maxIter=2，对应 exv_ifmask_two_batch_correct） -/
def exvTestInpSeq : ExvSplitIn 8 where
  fire := true
  in1 := exvFlat8 (fun i => BitVec.ofNat 32 i)
  in2 := exvFlat8 (fun i => if i % 2 = 0 then 0xFF#32 else BitVec.ofNat 32 i)
  in3 := 0
  mask := 0xA5#8
  fn := exvFN_SEQ
  rev := false
  wm := false
  rm := false
  wvd := false
  simt := true
  wid := 3#3
  ridx := 0
  resRdy := true
  simtRdy := true

theorem exvSplit_seq_simt_trace :
    let st1 := exvSplitStep 4 2 (exvSplitInit 8) exvTestInpSeq
    let st2 := exvSplitStep 4 2 st1 exvTestIdle8
    let st3 := exvSplitStep 4 2 st2 exvTestIdle8
    st3.recvCS = 2
    ∧ exvSplitSimtValid 2 st3 = true ∧ exvSplitOutValid 2 st3 = false
    ∧ st3.ifMask = 0x55#8                                      -- 偶数 lane 置位
    ∧ st3.simtWid = 3#3 ∧ st3.recvSimt = true ∧ st3.recvWvd = false := by
  native_decide

/-- (8,4) VID：拆分分支 :725 的全局编号公式与等宽分支 lane 常数一致（D10） -/
theorem exvSplit_vid_trace :
    let inp : ExvSplitIn 8 := { exvTestInpAdd with fn := exvFN_VID, wvd := true }
    let st1 := exvSplitStep 4 2 (exvSplitInit 8) inp
    let st2 := exvSplitStep 4 2 st1 exvTestIdle8
    let st3 := exvSplitStep 4 2 st2 exvTestIdle8
    st3.rd.extractLsb' 0 32 = 0#32
    ∧ st3.rd.extractLsb' 32 32 = 1#32
    ∧ st3.rd.extractLsb' 96 32 = 3#32
    ∧ st3.rd.extractLsb' 128 32 = 4#32
    ∧ st3.rd.extractLsb' 224 32 = 7#32 := by
  native_decide

/-- 6-lane 空闲拍输入 -/
def exvTestIdle6 : ExvSplitIn 6 where
  fire := false
  in1 := 0
  in2 := 0
  in3 := 0
  mask := 0
  fn := 0
  rev := false
  wm := false
  rm := false
  wvd := false
  simt := false
  wid := 0
  ridx := 0
  resRdy := true
  simtRdy := true

/-- 【Q2 端到端 witness】(6,2) maxIter=3：lane 0-1 的 SEQ 为不等（~cmp 应置
    bit0-1，正确 if_mask=0b000011），实际 if_mask=0；rd 数据通路本身仍正确 -/
def exvTestInpSeq6 : ExvSplitIn 6 where
  fire := true
  in1 := exvFlat6 (fun i => BitVec.ofNat 32 (i + 1))
  in2 := exvFlat6 (fun i => if i < 2 then 99#32 else BitVec.ofNat 32 (i + 1))
  in3 := 0
  mask := 0x3F#6
  fn := exvFN_SEQ
  rev := false
  wm := false
  rm := false
  wvd := false
  simt := true
  wid := 2#3
  ridx := 0
  resRdy := true
  simtRdy := true

theorem exvSplit_simt_ifMask_broken_trace :
    let st1 := exvSplitStep 2 3 (exvSplitInit 6) exvTestInpSeq6
    let st2 := exvSplitStep 2 3 st1 exvTestIdle6
    let st3 := exvSplitStep 2 3 st2 exvTestIdle6
    let st4 := exvSplitStep 2 3 st3 exvTestIdle6
    st4.recvCS = 3 ∧ exvSplitSimtValid 3 st4 = true
    ∧ st4.ifMask = 0#6                                         -- 实际：全丢
    ∧ st4.ifMask ≠ 0b000011#6                                  -- 期望：bit0-1 置位
    ∧ st4.rd.extractLsb' 64 32 = 1#32                          -- rd 通路正常（lane2 相等→1）
    ∧ st4.rd.extractLsb' 0 32 = 0#32                           -- lane0 不等→0
    ∧ st4.simtWid = 2#3 := by
  native_decide

/-- 【Q3 端到端 witness】(8,4) VMERGE：mask=0x0F（lane 0-3 true）。
    正确语义 lane 4-7 取 in2；实际第 2 批错用第 0 批 mask（全 1）取 in1 -/
def exvTestInpVmerge : ExvSplitIn 8 where
  fire := true
  in1 := exvFlat8 (fun i => BitVec.ofNat 32 (0xA0 + i))
  in2 := exvFlat8 (fun i => BitVec.ofNat 32 (0xB0 + i))
  in3 := 0
  mask := 0x0F#8
  fn := exvFN_VMERGE
  rev := false
  wm := false
  rm := false
  wvd := true
  simt := false
  wid := 1#3
  ridx := 0
  resRdy := true
  simtRdy := true

theorem exvSplit_vmerge_mask_not_shifted_trace :
    let st1 := exvSplitStep 4 2 (exvSplitInit 8) exvTestInpVmerge
    let st2 := exvSplitStep 4 2 st1 exvTestIdle8
    let st3 := exvSplitStep 4 2 st2 exvTestIdle8
    exvSplitOutValid 2 st3 = true
    ∧ st3.rd.extractLsb' 0 32 = 0xA0#32                        -- lane0：mask=1 取 in1 ✓
    ∧ st3.rd.extractLsb' 96 32 = 0xA3#32                       -- lane3 ✓
    ∧ st3.rd.extractLsb' 128 32 = 0xA4#32                      -- lane4：应为 in2=0xB4
    ∧ st3.rd.extractLsb' 224 32 = 0xA7#32                      -- lane7：应为 in2=0xB7
    ∧ st3.rd.extractLsb' 128 32 ≠ 0xB4#32 := by
  native_decide

/-- 【Q6 端到端 witness】simt 指令排空拍：inReg 已清零（simt=false），
    outFIFOReady 错用 result 队 ready（:580）。simtRdy=false、resRdy=true 时
    FSM 照常排空并清空 simtReg——result2simt 上的表项未经握手被丢弃 -/
theorem exvSplit_simt_drop_witness_trace :
    let st1 := exvSplitStep 4 2 (exvSplitInit 8) exvTestInpSeq
    let st2 := exvSplitStep 4 2 st1 exvTestIdle8
    let st3 := exvSplitStep 4 2 st2 exvTestIdle8
    -- 排空拍：simt 结果有效，但 simt 队不就绪、result 队就绪
    let inp : ExvSplitIn 8 := { exvTestIdle8 with resRdy := true, simtRdy := false }
    let st4 := exvSplitStep 4 2 st3 inp
    exvSplitSimtValid 2 st3 = true                             -- 待排空的 simt 表项
    ∧ st3.simt = false                                         -- inReg 已清零（:612-613）
    ∧ st4.recvCS = 0                                           -- FSM 照常返回空闲
    ∧ exvSplitSimtValid 2 st4 = false
    ∧ st4.ifMask = 0#8                                         -- 表项内容被清（:668-670）
    ∧ st4.rd = 0#256 := by
  native_decide

/- ========================================================================= -/
/- 11. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms exv_vmandnot_spec
#print axioms exv_vmerge_spec
#print axioms exv_sge_cmp_spec
#print axioms exv_v1_sge_out_spec
#print axioms exv_ifmask_two_batch_correct
#print axioms exv_ifmask_maxIter3_broken
#print axioms exvSplit_add_trace
#print axioms exvSplit_simt_ifMask_broken_trace
#print axioms exvSplit_vmerge_mask_not_shifted_trace
#print axioms exvSplit_simt_drop_witness_trace

end Ventus.Arith
