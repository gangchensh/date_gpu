/- ========================================================================= -/
/-                     Arith/ExeMul.lean                                     -/
/-  乘法执行侧（execution.scala 的 ALUexe / vMULexe / vMULv2）的              -/
/-  Lean 4 模型、测试与证明                                                   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/execution.scala     -/
/-      ALUexe  :26-65    （标量 ALU 执行级，内例化 ScalarALU + 2 个          -/
/-                         Queue(_,1,pipe=true)）                             -/
/-      vMULexe :66-111   （num_thread 个 ArrayMultiplier 并行 +              -/
/-                         result_x/result_v 队列）                           -/
/-      vMULv2  :164-413  （softThread/hardThread 切分版；本文件建模其         -/
/-                         else 分支 :226-410，soft==hard 分支 :192-225        -/
/-                         与 vMULexe 逐行相同，见 D6/Q6）                    -/
/-    复用：ScalarALU → Arith/ScalarALU.lean (saAlu)；                        -/
/-          ArrayMultiplier → Arith/Multiplier.lean（mul 前缀）；             -/
/-          HasPipelineReg（mul_utils.scala:38-63）→ 本文件 exmPipe2。        -/
/-  数据类型（issue.scala:17-30、operandCollector.scala:8-22、                -/
/-    scoreboard.scala:19-  CtrlSigs、DecodeUnit.scala:23-26 分支编码）：     -/
/-      B_N=0 B_B=1 B_J=2 B_R=3；wid 宽 depth_warp=3（num_warp=8）；          -/
/-      reg_idxw 宽 regidx_width+regext_width=5+3=8。                         -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. SPIKE_OUTPUT=true 时的 spike_info 字段一律不建模：它是 Spike 对照     -/
/-      用的验证旁路，不影响 RTL 数据/握手通路。但 vMULv2 的 spike 接法本身    -/
/-      有疑点，见 Q3。                                                       -/
/-  D2. ctrl 只保留本组模块消费/透传的字段，收进 ExmCtrl：alu_fn(6b，消费     -/
/-      点取 (4,0），与 :36 和 Multiplier.scala:156-158 一致）、wid(3b)、     -/
/-      reg_idxw(8b)、branch(2b)、reverse、wxd、wvd。                         -/
/-  D3. lane 向量（in1/in2/in3/mask/wb_wvd_rd/wvd_mask）建模为                -/
/-      `Nat → BitVec 32` / `Nat → Bool`（而非 Fin n →）：下标 ≥ lane 数的    -/
/-      值是垃圾、语义上从不被读（移位只在 i+H<S 时读 i+H，pipe 只读          -/
/-      下标 < hardThread），换取移位/装配归纳证明的可行性。                  -/
/-  D4. Queue(_, 1, pipe=true) 建模为 Option α：enq.ready = !full ∨           -/
/-      deq.ready（pipe 透传），deq.valid = full，deq.bits = 寄存器值；       -/
/-      更新 full' = doEnq ∨ (full ∧ ¬doDeq)，bits 仅在 doEnq 时写入。        -/
/-  D5. ArrayMultiplier 的 2 级流水（HasPipelineReg）建模为带反压的           -/
/-      通用 2 级流水 exmPipe2，使能逐行对应 mul_utils.scala:47-60：          -/
/-      en1 = outRdy ∨ ¬(v1∧v2)（:47 i=1 且 :58 in.ready），                 -/
/-      en2 = outRdy ∨ ¬v2（:47 i=2），数据寄存器使能 = 上级 valid ∧ en       -/
/-      （:52-53 PipelineReg）。算术通路复用 Multiplier.lean 的               -/
/-      mulA33/mulB33/mulIn1/mulIn3/mulPlacedSum/mulRes/mulMacOut。           -/
/-  D6. vMULv2 的 softThread==hardThread 分支（:192-225）与 vMULexe           -/
/-      :75-108 逐行相同（:193 的 num_thread 在该分支等于 softThread），      -/
/-      由 vMULexe 模型覆盖，不重复建模。                                     -/
/-  D7. vMULv2 的 sendCS/recvCS 建模为 Nat（源码为 log2Ceil(maxIter+1) 位     -/
/-      UInt）：FSM 可达状态 ≤ maxIter，可达域内 +% 与 + 一致；具体实例       -/
/-      m=2（S=4,H=2）与 m=3（S=6,H=2）用轨迹测试钉死。                       -/
/-  D8. vMULv2 的 inReg 移位只移 in1/2/in3、不动 mask/ctrl（:290-300）——      -/
/-      忠实翻译；正确性论证见 Q4。                                           -/
/-  D9. vMULv2 建模要求 S = m*H（源码 :165 assert(softThread%hardThread==0)   -/
/-      且 else 分支 S>H，故 m≥2）。                                          -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类候选，需译码侧核实】vMULv2 内 wvd/wxd 优先级 send/recv 两侧       -/
/-      相反：send 侧 wvd 优先（:244-249、:263-268），recv 侧 wxd 优先        -/
/-      （:332-336、:353-358）。若 ctrl.wvd 与 ctrl.wxd 同时为 1，send 按     -/
/-      wvd 发 maxIter 批、recv 首批（wxd）即收尾——resultReg 只装入批次 0     -/
/-      的 H 个 lane，其余 lane 是移位垃圾并以 wvd=1 入 result_v 队列。       -/
/-      若译码保证 wvd/wxd 互斥则不可达（疑似如此，未核实）；属防御性隐患。   -/
/-  Q2【I 类候选，健壮性/现配置不可达】recvCS∈[1,maxIter) 且本拍无            -/
/-      recv.fire 时 recvNS:=0（:343-349），随之 resultReg 清零               -/
/-      （:370-372）——中途气泡会静默丢失已收批次并复位计数。现配置下不可      -/
/-      达：sendCS∈[1,m) 时 recvCS<m（recvCS=m 蕴含全部批次已发出），故       -/
/-      mul out.ready=recv.ready=1、pipe 自由流动、mul.in.ready=1，批次       -/
/-      背靠背进入、out.valid 连续，recvCS∈[1,m) 必有 fire。但若             -/
/-      ArrayMultiplier 被换成可变延迟单元即出错。对照 vALUv2 同位置是        -/
/-      保持语义（:650-652 注 "may never happen"），两模块不一致。            -/
/-  Q3【I 类候选，验证基础设施污染】vMULv2 的 spike_info（:406-409）组合      -/
/-      取自 mul(0).out.bits.ctrl 而非 resultReg：连续流时 drain 拍           -/
/-      （recvCS=maxIter、enq.valid=1）mul 输出已是【下一条】指令的首批，     -/
/-      spike_info 串指令。非连续流时恰为当前指令末批残留，偶然正确。         -/
/-      仅影响 Spike 对照（默认 SPIKE_OUTPUT=true），不影响 RTL 数据通路。    -/
/-      vALUv2 是在末批把 spike 打进 resultReg（:689-691）的正确做法。        -/
/-  Q4【观察，非 bug】inReg 移位不含 mask（:290-300），各硬件 lane 每批都     -/
/-      收到全宽 mask：ArrayMultiplier 的 mask 是纯透传（不进数据通路），     -/
/-      wvd_mask 在末批取自 mul(0).out.bits.mask（:384）= 原始全宽 mask，     -/
/-      结论正确。                                                            -/
/-  Q5【I 类，已知 I-15】vMULexe/vMULv2 路径的 MULHSU 输出 = 乘积【低】32     -/
/-      位（Multiplier.scala:204-205，Multiplier.lean Q1/mulRes_mulhsu）。    -/
/-      本文件 exmMulLaneOut_mulhsu 符号钉死 + 轨迹 witness。                 -/
/-  Q6【观察】vMULv2 的 :192-225（soft==hard 分支）与 vMULexe :75-108 逐行    -/
/-      重复；:176-181 注释掉的 ArrayMultiplier2 为死注释。                   -/
/-  Q7【观察】:400 result_x 数据取 resultReg.wb_wvd_rd(softThread-hardThread) -/
/-      ——依赖"wxd 指令只发一批（:246-247）、recv 只移一次"，此时该下标恰     -/
/-      为批次 0 的 lane 0。模型已用测试钉死。                                -/
/-  Q8【观察】ALUexe 的 B_J/B_R 走 MuxLookup 默认分支：两队列 enq.valid 互    -/
/-      以对方 ready 门控（:50、:59-61、:62-64），in.ready 求两者交集，       -/
/-      不存在部分入队；B_N 且 wxd=0 时输入被消费且无输出（无写回指令，       -/
/-      正常）。                                                              -/
/-  Q9【观察】vMULexe 的 io.in.ready 取自 mul(0).in.ready（:106），各 mul     -/
/-      完全同构（共享 ctrl/valid/ready），取 0 号无分歧。                    -/
/-  Q10【观察】vMULv2 的 :303 注释（sendCS===maxIter-1 时 io.in.ready=0）与   -/
/-      :239 一致；send/recv 中间态"保持/清零"分支在现配置下均不可达          -/
/-      （Q2 论证），模型按源码忠实保留这些分支。                             -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Arith.ScalarALU
import Ventus.Arith.Multiplier
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- ========================================================================= -/
/- 1. 公共类型与常量                                                          -/
/- ========================================================================= -/

/-- CtrlSigs 子集（D2）：本组模块消费/透传的字段 -/
structure ExmCtrl where
  aluFn : BitVec 6    -- CtrlSigs.alu_fn（消费点取 (4,0)，execution.scala:36）
  wid : BitVec 3      -- depth_warp = log2Ceil(8)
  regIdxw : BitVec 8  -- regidx_width + regext_width = 5 + 3
  branch : BitVec 2
  reverse : Bool
  wxd : Bool
  wvd : Bool
  deriving DecidableEq

def exmCtrlZero : ExmCtrl := ⟨0#6, 0#3, 0#8, 0#2, false, false, false⟩

/-- 分支编码（DecodeUnit.scala:23-26） -/
def exmB_N : BitVec 2 := 0
def exmB_B : BitVec 2 := 1
def exmB_J : BitVec 2 := 2
def exmB_R : BitVec 2 := 3

/-- sExeData（issue.scala:25-30，标量执行输入） -/
structure ExmSExeIn where
  in1 : BitVec 32
  in2 : BitVec 32
  in3 : BitVec 32
  ctrl : ExmCtrl
  deriving DecidableEq

/-- vExeData（issue.scala:17-23，向量执行输入；lane 向量见 D3） -/
structure ExmVExeIn where
  in1 : Nat → BitVec 32
  in2 : Nat → BitVec 32
  in3 : Nat → BitVec 32
  mask : Nat → Bool
  ctrl : ExmCtrl

/-- WriteScalarCtrl（operandCollector.scala:16-22，去掉 spike_info，D1） -/
structure ExmWBScalar where
  wbWxdRd : BitVec 32
  wxd : Bool
  regIdxw : BitVec 8
  warpId : BitVec 3
  deriving DecidableEq

def exmWBScalarZero : ExmWBScalar := ⟨0#32, false, 0#8, 0#3⟩

/-- WriteVecCtrl（operandCollector.scala:8-15，去掉 spike_info；lane 向量见 D3） -/
structure ExmWBVec where
  wbWvdRd : Nat → BitVec 32
  wvdMask : Nat → Bool
  wvd : Bool
  regIdxw : BitVec 8
  warpId : BitVec 3

def exmWBVecZero : ExmWBVec := ⟨fun _ => 0#32, fun _ => false, false, 0#8, 0#3⟩

/-- BranchCtrl（execution.scala:20-25，去掉 spike_info） -/
structure ExmBrCtrl where
  wid : BitVec 3
  jump : Bool
  newPc : BitVec 32
  deriving DecidableEq

def exmBrCtrlZero : ExmBrCtrl := ⟨0#3, false, 0#32⟩

/- ========================================================================= -/
/- 2. Queue(_, 1, pipe=true) 模型（D4）                                       -/
/- ========================================================================= -/

/-- enq.ready = !full || deq.ready（pipe 透传） -/
def exmQEnqRdy {α : Type} (q : Option α) (deqRdy : Bool) : Bool :=
  q.isNone || deqRdy

/-- deq.valid = full -/
def exmQDeqVld {α : Type} (q : Option α) : Bool := q.isSome

/-- 单拍更新：full' = doEnq || (full && !doDeq)；bits 仅 doEnq 时写入 -/
def exmQStep {α : Type} (q : Option α) (enqV : Bool) (bits : α) (deqRdy : Bool) : Option α :=
  let doEnq := enqV && exmQEnqRdy q deqRdy
  let doDeq := exmQDeqVld q && deqRdy
  if doEnq then some bits else if q.isSome && !doDeq then q else none

theorem exmQStep_enq_empty {α : Type} (b : α) (r : Bool) :
    exmQStep none true b r = some b := by
  simp [exmQStep, exmQEnqRdy]

theorem exmQStep_hold {α : Type} (a : α) (b : α) :
    exmQStep (some a) false b false = some a := by
  simp [exmQStep, exmQEnqRdy, exmQDeqVld]

theorem exmQStep_deq {α : Type} (a : α) (b : α) :
    exmQStep (some a) false b true = none := by
  simp [exmQStep, exmQEnqRdy, exmQDeqVld]

/-- pipe 透传：满且 deq 时同拍可 enq，新值入寄存器 -/
theorem exmQStep_pipe {α : Type} (a : α) (b : α) :
    exmQStep (some a) true b true = some b := by
  simp [exmQStep, exmQEnqRdy, exmQDeqVld]

/-- 满且 deq 不 ready 时 enq.ready=0，保持 -/
theorem exmQStep_stall {α : Type} (a : α) (b : α) :
    exmQStep (some a) true b false = some a := by
  simp [exmQStep, exmQEnqRdy, exmQDeqVld]

section ExmQTests
example : exmQStep (none : Option (BitVec 8)) true 5#8 false = some 5#8 := by decide
example : exmQStep (some 5#8 : Option (BitVec 8)) false 7#8 true = none := by decide
example : exmQStep (some 5#8 : Option (BitVec 8)) true 7#8 true = some 7#8 := by decide
example : exmQStep (some 5#8 : Option (BitVec 8)) true 7#8 false = some 5#8 := by decide
example : exmQEnqRdy (some 5#8 : Option (BitVec 8)) false = false := by decide
example : exmQEnqRdy (some 5#8 : Option (BitVec 8)) true = true := by decide
end ExmQTests

/- ========================================================================= -/
/- 3. 通用 2 级反压流水 exmPipe2（HasPipelineReg latency=2，D5）               -/
/- ========================================================================= -/

/-- 2 级流水状态：c 为随批透传的 ctrl（含 mask），d1 为第 1 级数据（乘法器
    33 位操作数），d2 为第 2 级数据（结果） -/
structure ExmPipe2 (C D1 D2 : Type) where
  v1 : Bool
  c1 : C
  d1 : D1
  v2 : Bool
  c2 : C
  d2 : D2

def exmPipe2Init {C D1 D2 : Type} (c0 : C) (d10 : D1) (d20 : D2) : ExmPipe2 C D1 D2 :=
  ⟨false, c0, d10, false, c0, d20⟩

/-- mul_utils.scala:58  io.in.ready = !(!out.ready && v1 && v2) -/
def exmPipe2InRdy {C D1 D2 : Type} (outRdy : Bool) (s : ExmPipe2 C D1 D2) : Bool :=
  outRdy || !(s.v1 && s.v2)

/-- mul_utils.scala:59  io.out.valid = valids.last = v2 -/
def exmPipe2OutVld {C D1 D2 : Type} (s : ExmPipe2 C D1 D2) : Bool := s.v2

/-- 单拍转移（mul_utils.scala:46-53）：
    en1 = outRdy || !(v1 && v2)（valids.drop(1) 归约），en2 = outRdy || !v2；
    valid 寄存器在 en 下移位；数据寄存器使能 = 上级 valid && en -/
def exmPipe2Step {C In D1 D2 : Type} (prep : C → In → D1) (f : C → D1 → D2)
    (outRdy : Bool) (inV : Bool) (inC : C) (inp : In) (s : ExmPipe2 C D1 D2) :
    ExmPipe2 C D1 D2 :=
  let en1 := exmPipe2InRdy outRdy s
  let en2 := outRdy || !s.v2
  { v1 := if en1 then inV else s.v1
  , c1 := if inV && en1 then inC else s.c1
  , d1 := if inV && en1 then prep inC inp else s.d1
  , v2 := if en2 then s.v1 else s.v2
  , c2 := if s.v1 && en2 then s.c1 else s.c2
  , d2 := if s.v1 && en2 then f s.c1 s.d1 else s.d2 }

/-- 对齐/延迟定理（自由流动）：指令 X 进入两拍后 out.valid=1、out.ctrl=X 的
    ctrl、out.data = f c (prep c i)（下一拍输入任意） -/
theorem exmPipe2_two_cycles {C In D1 D2 : Type} (prep : C → In → D1) (f : C → D1 → D2)
    (s : ExmPipe2 C D1 D2) (c yc : C) (i y : In) (yv : Bool) :
    let s2 := exmPipe2Step prep f true yv yc y (exmPipe2Step prep f true true c i s)
    s2.v2 = true ∧ s2.c2 = c ∧ s2.d2 = f c (prep c i) := by
  simp [exmPipe2Step, exmPipe2InRdy]

/-- 反压保持：out.ready=0 且第 2 级有数据（v2=1）时第 2 级冻结
    （valid/ctrl/数据均不变；v2=0 时属冒泡填充，不冻结） -/
theorem exmPipe2_stall_hold {C In D1 D2 : Type} (prep : C → In → D1) (f : C → D1 → D2)
    (s : ExmPipe2 C D1 D2) (inV : Bool) (inC : C) (inp : In) (hs2 : s.v2 = true) :
    let s' := exmPipe2Step prep f false inV inC inp s
    s'.v2 = true ∧ s'.c2 = s.c2 ∧ s'.d2 = s.d2 := by
  simp [exmPipe2Step, exmPipe2InRdy, hs2]

section ExmPipe2Tests

def exmP2TestPrep (c i : BitVec 8) : BitVec 8 := i + c
def exmP2TestF (c d : BitVec 8) : BitVec 8 := d + c

def exmP2T0 : ExmPipe2 (BitVec 8) (BitVec 8) (BitVec 8) := exmPipe2Init 0#8 0#8 0#8

-- 自由流动：t0 进 10（c=1），t2 得 v2=1 且 d2 = 10+1+1 = 12
example : let s2 := exmPipe2Step exmP2TestPrep exmP2TestF true false 0#8 0#8
              (exmPipe2Step exmP2TestPrep exmP2TestF true true 1#8 10#8 exmP2T0)
          s2.v2 = true ∧ s2.d2 = 12#8 ∧ s2.c2 = 1#8 := by decide
-- 反压：t1 起 outRdy=0，结果冻结在 v2，恢复后不变
example : let s1 := exmPipe2Step exmP2TestPrep exmP2TestF true true 1#8 10#8 exmP2T0
          let s2 := exmPipe2Step exmP2TestPrep exmP2TestF false false 0#8 0#8 s1
          let s3 := exmPipe2Step exmP2TestPrep exmP2TestF false false 0#8 0#8 s2
          s2.v2 = true ∧ s2.d2 = 12#8 ∧ s3.v2 = true ∧ s3.d2 = 12#8 := by decide
-- 反压冒泡填充：v2 阻塞但 v1=0 时仍可再收一拍（in.ready=1）
example : let s0 := exmPipe2Init 0#8 0#8 0#8
          let s1 := exmPipe2Step exmP2TestPrep exmP2TestF true true 1#8 10#8 s0
          let s2 := exmPipe2Step exmP2TestPrep exmP2TestF false true 2#8 20#8 s1
          exmPipe2InRdy false s2 = false ∧ s2.v1 = true ∧ s2.d1 = 22#8 := by decide
end ExmPipe2Tests

/- ========================================================================= -/
/- 4. ALUexe（execution.scala:26-65）                                          -/
/- ========================================================================= -/

/- ---- 组合件（MuxLookup 逐行翻译；B_B=1 先查、B_N=0 次之、默认殿后） ---- -/

/-- :50-53  io.in.ready = MuxLookup(branch, rdyBr && rdyR)(B_B→rdyBr, B_N→rdyR) -/
def exmAluInRdy (branch : BitVec 2) (rdyR rdyBr : Bool) : Bool :=
  if branch = exmB_B then rdyBr
  else if branch = exmB_N then rdyR
  else rdyBr && rdyR

/-- :59-61  result_br.enq.valid = in.valid && MuxLookup(branch, rdyR)(B_B→1, B_N→0) -/
def exmAluBrEnqOK (branch : BitVec 2) (rdyR : Bool) : Bool :=
  if branch = exmB_B then true
  else if branch = exmB_N then false
  else rdyR

/-- :62-64  result.enq.valid = in.valid && wxd && MuxLookup(branch, rdyBr)(B_B→0, B_N→1) -/
def exmAluREnqOK (branch : BitVec 2) (rdyBr : Bool) : Bool :=
  if branch = exmB_B then false
  else if branch = exmB_N then true
  else rdyBr

/-- :57  jump = MuxLookup(branch, false)(B_B→cmp_out, B_J→1, B_R→1) -/
def exmAluJump (branch : BitVec 2) (cmpOut : Bool) : Bool :=
  if branch = exmB_B then cmpOut
  else if branch = exmB_J then true
  else if branch = exmB_R then true
  else false

/- ---- 组合件逐值规约（先测试后证明的符号部分） ---- -/

theorem exmAluInRdy_bN (rR bR : Bool) : exmAluInRdy exmB_N rR bR = rR := by rfl
theorem exmAluInRdy_bB (rR bR : Bool) : exmAluInRdy exmB_B rR bR = bR := by rfl
theorem exmAluInRdy_bJ (rR bR : Bool) : exmAluInRdy exmB_J rR bR = (bR && rR) := by rfl
theorem exmAluInRdy_bR (rR bR : Bool) : exmAluInRdy exmB_R rR bR = (bR && rR) := by rfl

theorem exmAluBrEnqOK_bN (rR : Bool) : exmAluBrEnqOK exmB_N rR = false := by rfl
theorem exmAluBrEnqOK_bB (rR : Bool) : exmAluBrEnqOK exmB_B rR = true := by rfl
theorem exmAluBrEnqOK_bJ (rR : Bool) : exmAluBrEnqOK exmB_J rR = rR := by rfl
theorem exmAluBrEnqOK_bR (rR : Bool) : exmAluBrEnqOK exmB_R rR = rR := by rfl

theorem exmAluREnqOK_bN (bR : Bool) : exmAluREnqOK exmB_N bR = true := by rfl
theorem exmAluREnqOK_bB (bR : Bool) : exmAluREnqOK exmB_B bR = false := by rfl
theorem exmAluREnqOK_bJ (bR : Bool) : exmAluREnqOK exmB_J bR = bR := by rfl
theorem exmAluREnqOK_bR (bR : Bool) : exmAluREnqOK exmB_R bR = bR := by rfl

theorem exmAluJump_bN (c : Bool) : exmAluJump exmB_N c = false := by rfl
theorem exmAluJump_bB (c : Bool) : exmAluJump exmB_B c = c := by rfl
theorem exmAluJump_bJ (c : Bool) : exmAluJump exmB_J c = true := by rfl
theorem exmAluJump_bR (c : Bool) : exmAluJump exmB_R c = true := by rfl

/- ---- 执行级状态与单拍模型 ---- -/

/-- ALUexe 状态：两个 Queue(_,1,pipe=true)（:37-38） -/
structure ExmAluExeState where
  qR : Option ExmWBScalar
  qBr : Option ExmBrCtrl
  deriving DecidableEq

def exmAluExeInit : ExmAluExeState := ⟨none, none⟩

/-- ALUexe 组合输出 -/
structure ExmAluExeOut where
  inRdy : Bool
  outVld : Bool
  outBits : ExmWBScalar
  brVld : Bool
  brBits : ExmBrCtrl
  deriving DecidableEq

/-- 单拍模型（:26-65 整体）。返回（组合输出， 下一状态）。
    out/out2br 的 valid/bits 取【当前】队列状态（deq 为组合读出）。 -/
def exmAluExeStep (st : ExmAluExeState) (inV : Bool) (din : ExmSExeIn)
    (outRdy brRdy : Bool) : ExmAluExeOut × ExmAluExeState :=
  -- :32-36  ScalarALU 例化与接线（func = alu_fn(4,0)）
  let func := din.ctrl.aluFn.extractLsb' 0 5
  let aluRes := saAlu func din.in1 din.in2 din.in3
  let rdyR := exmQEnqRdy st.qR outRdy
  let rdyBr := exmQEnqRdy st.qBr brRdy
  -- :41-45  result.enq.bits（wxd/wid/reg_idxw 透传，数据 = alu.out）
  let rBits : ExmWBScalar := ⟨aluRes.1, din.ctrl.wxd, din.ctrl.regIdxw, din.ctrl.wid⟩
  -- :55-57  result_br.enq.bits（new_pc = in3，jump 见上）
  let brBits : ExmBrCtrl := ⟨din.ctrl.wid, exmAluJump din.ctrl.branch aluRes.2, din.in3⟩
  -- :50-53 / :59-64
  let inRdy := exmAluInRdy din.ctrl.branch rdyR rdyBr
  let brEnqV := inV && exmAluBrEnqOK din.ctrl.branch rdyR
  let rEnqV := inV && din.ctrl.wxd && exmAluREnqOK din.ctrl.branch rdyBr
  let out : ExmAluExeOut :=
    { inRdy := inRdy
    , outVld := exmQDeqVld st.qR
    , outBits := st.qR.getD exmWBScalarZero
    , brVld := exmQDeqVld st.qBr
    , brBits := st.qBr.getD exmBrCtrlZero }
  (out, ⟨exmQStep st.qR rEnqV rBits outRdy, exmQStep st.qBr brEnqV brBits brRdy⟩)

/-- 轨迹运行：输入序列 (inV, din, outRdy, brRdy)，返回每拍组合输出 -/
def exmAluExeRun : ExmAluExeState → List (Bool × ExmSExeIn × Bool × Bool) → List ExmAluExeOut
  | _, [] => []
  | st, (v, d, r, b) :: t =>
      let (o, st') := exmAluExeStep st v d r b
      o :: exmAluExeRun st' t

/- ---- 延迟/路由定理（执行级 = 组合 ALU ⊗ 打拍） ---- -/

/-- B_N（非分支）且 wxd：接受后下一拍 out.valid=1、数据 = saAlu 输出、
    ctrl 透传，out2br 无输出 -/
theorem exmAluExe_latency_bN (din : ExmSExeIn)
    (hbr : din.ctrl.branch = exmB_N) (hwxd : din.ctrl.wxd = true) :
    let s1 := (exmAluExeStep exmAluExeInit true din true true).2
    let o := (exmAluExeStep s1 false din true true).1
    o.outVld = true ∧
    o.outBits = ⟨ (saAlu (din.ctrl.aluFn.extractLsb' 0 5) din.in1 din.in2 din.in3).1,
                  true, din.ctrl.regIdxw, din.ctrl.wid ⟩ ∧
    o.brVld = false := by
  simp [exmAluExeStep, exmAluExeInit, exmQStep, exmQEnqRdy, exmQDeqVld, hbr, hwxd,
    exmAluInRdy_bN, exmAluBrEnqOK_bN, exmAluREnqOK_bN, exmAluJump_bN]

/-- B_B（条件分支）：接受后下一拍 out2br.valid=1、new_pc=in3、
    jump = saAlu 的 cmp_out；out（标量写回）无输出 -/
theorem exmAluExe_latency_bB (din : ExmSExeIn)
    (hbr : din.ctrl.branch = exmB_B) :
    let s1 := (exmAluExeStep exmAluExeInit true din true true).2
    let o := (exmAluExeStep s1 false din true true).1
    o.brVld = true ∧
    o.brBits = ⟨ din.ctrl.wid,
                 (saAlu (din.ctrl.aluFn.extractLsb' 0 5) din.in1 din.in2 din.in3).2,
                 din.in3 ⟩ ∧
    o.outVld = false := by
  simp [exmAluExeStep, exmAluExeInit, exmQStep, exmQEnqRdy, exmQDeqVld, hbr,
    exmAluInRdy_bB, exmAluBrEnqOK_bB, exmAluREnqOK_bB, exmAluJump_bB]

/-- B_J（跳转）：两队列都入队——out2br 得 jump=true/new_pc=in3，
    out 得 alu 结果（rd = pc+4 由 ALU 加法算出） -/
theorem exmAluExe_latency_bJ (din : ExmSExeIn)
    (hbr : din.ctrl.branch = exmB_J) (hwxd : din.ctrl.wxd = true) :
    let s1 := (exmAluExeStep exmAluExeInit true din true true).2
    let o := (exmAluExeStep s1 false din true true).1
    o.brVld = true ∧ o.brBits.jump = true ∧ o.brBits.newPc = din.in3 ∧
    o.outVld = true ∧
    o.outBits.wbWxdRd =
      (saAlu (din.ctrl.aluFn.extractLsb' 0 5) din.in1 din.in2 din.in3).1 := by
  simp [exmAluExeStep, exmAluExeInit, exmQStep, exmQEnqRdy, exmQDeqVld, hbr, hwxd,
    exmAluInRdy_bJ, exmAluBrEnqOK_bJ, exmAluREnqOK_bJ, exmAluJump_bJ]

/- ---- 数值回归测试（先测试；沿 :36 接入 saAlu 全操作码） ---- -/

section ExmAluExeTests

def exmAluMkIn (fn : BitVec 5) (br : BitVec 2) (wxd : Bool) (a b c : BitVec 32) : ExmSExeIn :=
  ⟨a, b, c, ⟨BitVec.zeroExtend 6 fn, 2#3, 5#8, br, false, wxd, false⟩⟩

-- B_N + ADD：下一拍出和，out2br 无输出；wid/reg_idxw 透传
example : exmAluExeRun exmAluExeInit
    [ (true, exmAluMkIn saFN_ADD exmB_N true 3#32 4#32 0#32, true, true)
    , (false, exmAluMkIn saFN_ADD exmB_N true 0#32 0#32 0#32, true, true) ]
    = [ { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := true, outVld := true, outBits := ⟨7#32, true, 5#8, 2#3⟩,
          brVld := false, brBits := exmBrCtrlZero } ] := by decide
-- B_B + SLT（分支不成立：0 < 0 为假）：jump=false，new_pc=in3
example : exmAluExeRun exmAluExeInit
    [ (true, exmAluMkIn saFN_SLT exmB_B false 0#32 0#32 0x1000#32, true, true)
    , (false, exmAluMkIn saFN_SLT exmB_B false 0#32 0#32 0#32, true, true) ]
    = [ { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := true, brBits := ⟨2#3, false, 0x1000#32⟩ } ] := by decide
-- B_B + SLT（-1 < 0 成立）：jump=true
example : exmAluExeRun exmAluExeInit
    [ (true, exmAluMkIn saFN_SLT exmB_B false 0xFFFFFFFF#32 0#32 0x2000#32, true, true)
    , (false, exmAluMkIn saFN_SLT exmB_B false 0#32 0#32 0#32, true, true) ]
    = [ { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := true, brBits := ⟨2#3, true, 0x2000#32⟩ } ] := by decide
-- B_J + ADD（JAL：rd=pc+4 走 out，跳转走 out2br）：两队列同拍出
example : exmAluExeRun exmAluExeInit
    [ (true, exmAluMkIn saFN_ADD exmB_J true 0x1000#32 4#32 0x8000#32, true, true)
    , (false, exmAluMkIn saFN_ADD exmB_J true 0#32 0#32 0#32, true, true) ]
    = [ { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := true, outVld := true, outBits := ⟨0x1004#32, true, 5#8, 2#3⟩,
          brVld := true, brBits := ⟨2#3, true, 0x8000#32⟩ } ] := by decide
-- 反压：outRdy=false 时 inRdy=0（B_N），输入无法进入；队列保持
example : exmAluExeRun exmAluExeInit
    [ (true, exmAluMkIn saFN_ADD exmB_N true 3#32 4#32 0#32, true, true)
    , (false, exmAluMkIn saFN_ADD exmB_N true 0#32 0#32 0#32, false, true)
    , (true, exmAluMkIn saFN_ADD exmB_N true 1#32 1#32 0#32, false, true)
    , (false, exmAluMkIn saFN_ADD exmB_N true 0#32 0#32 0#32, true, true) ]
    = [ { inRdy := true, outVld := false, outBits := exmWBScalarZero,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := false, outVld := true, outBits := ⟨7#32, true, 5#8, 2#3⟩,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := false, outVld := true, outBits := ⟨7#32, true, 5#8, 2#3⟩,
          brVld := false, brBits := exmBrCtrlZero }
      , { inRdy := true, outVld := true, outBits := ⟨7#32, true, 5#8, 2#3⟩,
          brVld := false, brBits := exmBrCtrlZero } ] := by decide

end ExmAluExeTests

/- ========================================================================= -/
/- 5. vMULexe（execution.scala:66-111）                                       -/
/- ========================================================================= -/

/-- :84-87  reverse 时交换 a/b 操作数 -/
def exmMulAB (rev : Bool) (a b : BitVec 32) : BitVec 32 × BitVec 32 :=
  if rev then (b, a) else (a, b)

/-- 单 lane 组合结果：reverse 交换后过 ArrayMultiplier wrapper
    （Multiplier.scala:149-211，经 Multiplier.lean 的 mulWrapOut） -/
def exmMulLaneOut (func : BitVec 5) (rev : Bool) (a b c : BitVec 32) : BitVec 32 :=
  mulWrapOut func (exmMulAB rev a b).1 (exmMulAB rev a b).2 c

/-- pipe 第 1 级数据准备（Multiplier.scala:156-179，:76-78/:84-87 接线） -/
def exmMulPrep (ctrl : ExmCtrl) (inp : Nat → BitVec 32 × BitVec 32 × BitVec 32) :
    Nat → BitVec 33 × BitVec 33 × BitVec 32 :=
  let f := ctrl.aluFn.extractLsb' 0 5
  fun x =>
    let (a, b, c) := inp x
    let ab := exmMulAB ctrl.reverse a b
    (mulA33 f (mulIn1 f ab.1 c), mulB33 f ab.2, mulIn3 f ab.1 c)

/-- pipe 第 2 级数据计算（Multiplier.scala:191-206，乘积→结果选择） -/
def exmMulExec (ctrl : ExmCtrl) (d1 : Nat → BitVec 33 × BitVec 33 × BitVec 32) :
    Nat → BitVec 32 :=
  let f := ctrl.aluFn.extractLsb' 0 5
  fun x =>
    let (a33, b33, c32) := d1 x
    let r := mulPlacedSum a33 b33
    mulRes f r (mulMacOut f r c32)

/-- 两级复合 = 单 lane 组合结果 -/
theorem exmMulExec_prep (ctrl : ExmCtrl)
    (inp : Nat → BitVec 32 × BitVec 32 × BitVec 32) (x : Nat) :
    exmMulExec ctrl (exmMulPrep ctrl inp) x =
      exmMulLaneOut (ctrl.aluFn.extractLsb' 0 5) ctrl.reverse
        (inp x).1 (inp x).2.1 (inp x).2.2 := by
  simp [exmMulExec, exmMulPrep, exmMulLaneOut, mulWrapOut, exmMulAB]

/-- 【Q5 / I-15】该路径的 MULHSU = (sext a)·(zext b) 的【低】32 位
    （正确语义为高 32 位；引用 Multiplier.lean 的 mul_mulhsu_diverges） -/
theorem exmMulLaneOut_mulhsu (a b c : BitVec 32) :
    exmMulLaneOut mulFN_MULHSU false a b c
      = ((BitVec.signExtend 66 a) * (BitVec.zeroExtend 66 b)).extractLsb' 0 32 := by
  simp [exmMulLaneOut, exmMulAB]
  exact mul_mulhsu_diverges a b c

/-- 【Q5 witness】a=b=0xFFFFFFFF：本路径输出 0x00000001（低 32 位），
    正确高 32 位为 0xFFFFFFFF -/
theorem exmMulLaneOut_mulhsu_witness :
    exmMulLaneOut mulFN_MULHSU false 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32
      = 1#32 ∧
    ((BitVec.signExtend 66 0xFFFFFFFF#32) * (BitVec.zeroExtend 66 0xFFFFFFFF#32)).extractLsb' 32 32
      = 0xFFFFFFFF#32 := by
  rw [exmMulLaneOut_mulhsu]
  constructor <;> native_decide

/- ---- 执行级状态与单拍模型 ---- -/

/-- vMULexe 的乘法 pipe 携带信息：ctrl + 全宽 mask -/
abbrev ExmMulPipeC := ExmCtrl × (Nat → Bool)
/-- pipe 第 1 级数据：每 lane 的 (a33, b33, c32) -/
abbrev ExmMulPipeD1 := Nat → BitVec 33 × BitVec 33 × BitVec 32
/-- pipe 第 2 级数据：每 lane 的 32 位结果 -/
abbrev ExmMulPipeD2 := Nat → BitVec 32

structure ExmVMulExeState where
  pipe : ExmPipe2 ExmMulPipeC ExmMulPipeD1 ExmMulPipeD2
  qv : Option ExmWBVec
  qx : Option ExmWBScalar

def exmVMulExeInit : ExmVMulExeState :=
  ⟨ exmPipe2Init (exmCtrlZero, fun _ => false) (fun _ => (0#33, 0#33, 0#32)) (fun _ => 0#32)
  , none, none ⟩

structure ExmVMulExeOut where
  inRdy : Bool
  outVVld : Bool
  outVBits : ExmWBVec
  outXVld : Bool
  outXBits : ExmWBScalar

/-- 单拍模型（:66-111）。out_v/out_x 的 valid/bits 取【当前】队列状态。 -/
def exmVMulExeStep (st : ExmVMulExeState) (inV : Bool) (din : ExmVExeIn)
    (outVRdy outXRdy : Bool) : ExmVMulExeOut × ExmVMulExeState :=
  let qvRdy := exmQEnqRdy st.qv outVRdy
  let qxRdy := exmQEnqRdy st.qx outXRdy
  let outCtrl := st.pipe.c2.1
  -- :83  mul(x).out.ready = Mux(ctrl.wxd, result_x.enq.ready, result_v.enq.ready)
  let pipeOutRdy := if outCtrl.wxd then qxRdy else qvRdy
  -- :106 io.in.ready = mul(0).in.ready
  let inRdy := exmPipe2InRdy pipeOutRdy st.pipe
  -- :75-88  mul(x).in 接线（valid = io.in.valid；reverse 交换 a/b）
  let pipe' := exmPipe2Step (fun c i => exmMulPrep c.1 i) (fun c d => exmMulExec c.1 d)
    pipeOutRdy inV (din.ctrl, din.mask)
    (fun x => (din.in1 x, din.in2 x, din.in3 x)) st.pipe
  -- :82, :91-94  result_v.enq：lane x ← mul(x).out.result；ctrl/mask 取 mul(0)
  let qvEnqV := st.pipe.v2 && outCtrl.wvd                              -- :104
  let qvBits : ExmWBVec :=
    ⟨st.pipe.d2, st.pipe.c2.2, outCtrl.wvd, outCtrl.regIdxw, outCtrl.wid⟩
  -- :99-105  result_x.enq：标量结果取 mul(0)（lane 0）
  let qxEnqV := st.pipe.v2 && outCtrl.wxd                              -- :105
  let qxBits : ExmWBScalar := ⟨st.pipe.d2 0, outCtrl.wxd, outCtrl.regIdxw, outCtrl.wid⟩
  let out : ExmVMulExeOut :=
    { inRdy := inRdy
    , outVVld := exmQDeqVld st.qv
    , outVBits := st.qv.getD exmWBVecZero
    , outXVld := exmQDeqVld st.qx
    , outXBits := st.qx.getD exmWBScalarZero }
  (out, ⟨pipe', exmQStep st.qv qvEnqV qvBits outVRdy,
    exmQStep st.qx qxEnqV qxBits outXRdy⟩)

def exmVMulExeRun : ExmVMulExeState → List (Bool × ExmVExeIn × Bool × Bool) →
    List ExmVMulExeOut
  | _, [] => []
  | st, (v, d, vr, xr) :: t =>
      let (o, st') := exmVMulExeStep st v d vr xr
      o :: exmVMulExeRun st' t

/- ---- 延迟定理（自由流动 + 空队列起步）：3 拍后经 result_v 出队 ---- -/

/-- 指令 X（wvd=1、wxd=0）于第 0 拍被接受：第 2 拍结果入 result_v 队列，
    第 3 拍 out_v.valid=1，每 lane = exmMulLaneOut，mask/ctrl 透传。
    （乘法器 2 拍 + 队列 1 拍；定理对任意 lane 下标 x 成立。） -/
theorem exmVMulExe_latency_wvd (din : ExmVExeIn)
    (hwvd : din.ctrl.wvd = true) (hwxd : din.ctrl.wxd = false) (x : Nat) :
    let s1 := (exmVMulExeStep exmVMulExeInit true din true true).2
    let s2 := (exmVMulExeStep s1 false din true true).2
    let s3 := (exmVMulExeStep s2 false din true true).2
    let o := (exmVMulExeStep s3 false din true true).1
    o.outVVld = true ∧
    o.outVBits.wbWvdRd x = exmMulLaneOut (din.ctrl.aluFn.extractLsb' 0 5)
        din.ctrl.reverse (din.in1 x) (din.in2 x) (din.in3 x) ∧
    o.outVBits.wvdMask = din.mask ∧
    o.outVBits.warpId = din.ctrl.wid ∧
    o.outVBits.regIdxw = din.ctrl.regIdxw ∧
    o.outXVld = false := by
  simp [exmVMulExeStep, exmVMulExeInit, exmPipe2Init, exmPipe2Step, exmPipe2InRdy,
    exmQStep, exmQEnqRdy, exmQDeqVld, hwvd, hwxd, exmMulExec_prep]

/-- 标量路径（wxd=1）：out_x 数据 = lane 0 的组合乘法结果 -/
theorem exmVMulExe_latency_wxd (din : ExmVExeIn)
    (hwvd : din.ctrl.wvd = false) (hwxd : din.ctrl.wxd = true) :
    let s1 := (exmVMulExeStep exmVMulExeInit true din true true).2
    let s2 := (exmVMulExeStep s1 false din true true).2
    let s3 := (exmVMulExeStep s2 false din true true).2
    let o := (exmVMulExeStep s3 false din true true).1
    o.outXVld = true ∧
    o.outXBits.wbWxdRd = exmMulLaneOut (din.ctrl.aluFn.extractLsb' 0 5)
        din.ctrl.reverse (din.in1 0) (din.in2 0) (din.in3 0) ∧
    o.outVVld = false := by
  simp [exmVMulExeStep, exmVMulExeInit, exmPipe2Init, exmPipe2Step, exmPipe2InRdy,
    exmQStep, exmQEnqRdy, exmQDeqVld, hwvd, hwxd, exmMulExec_prep]

/- ---- 数值回归测试（native_decide 轨迹；检查器对索引错位免疫） ---- -/

/-- lane 数据常量/下标函数构造辅助 -/
def exmLaneVals (vs : List (BitVec 32)) : Nat → BitVec 32 := fun i => vs.getD i 0#32
def exmLaneMask (vs : List Bool) : Nat → Bool := fun i => vs.getD i false

/-- 空闲（无效）输入 -/
def exmVMulIdle : ExmVExeIn :=
  ⟨fun _ => 0#32, fun _ => 0#32, fun _ => 0#32, fun _ => false, exmCtrlZero⟩

/-- 单拍 out_v 内容判据：lane 0..n-1 与期望逐点相等、mask/ctrl 透传 -/
def exmChkVBits (n : Nat) (din : ExmVExeIn) (o : ExmVMulExeOut) : Bool :=
  (List.range n).all (fun i =>
    (o.outVBits.wbWvdRd i == exmMulLaneOut (din.ctrl.aluFn.extractLsb' 0 5)
        din.ctrl.reverse (din.in1 i) (din.in2 i) (din.in3 i))
    && (o.outVBits.wvdMask i == din.mask i))
  && (o.outVBits.warpId == din.ctrl.wid) && (o.outVBits.regIdxw == din.ctrl.regIdxw)
  && (o.outVBits.wvd == din.ctrl.wvd)

/-- 单拍 out_x 内容判据（标量结果 = lane 0） -/
def exmChkXBits (din : ExmVExeIn) (o : ExmVMulExeOut) : Bool :=
  (o.outXBits.wbWxdRd == exmMulLaneOut (din.ctrl.aluFn.extractLsb' 0 5)
      din.ctrl.reverse (din.in1 0) (din.in2 0) (din.in3 0))
  && (o.outXBits.wxd == true) && (o.outXBits.warpId == din.ctrl.wid)
  && (o.outXBits.regIdxw == din.ctrl.regIdxw)

/-- 输出轨迹检查（fires 口径，反压免疫）：out_v 恰好 fire 一次（valid && 下游
    ready），且【每一拍】out_v valid 时内容都正确（stall 期间保持不变）；
    out_x 从未 fire。ins 用于提取下游 ready。 -/
def exmVMulExeChkV (n : Nat) (din : ExmVExeIn)
    (ins : List (Bool × ExmVExeIn × Bool × Bool)) (outs : List ExmVMulExeOut) : Bool :=
  let vFires := (outs.zipIdx 0).filter (fun p =>
    p.1.outVVld && (ins.getD p.2 (false, exmVMulIdle, false, false)).2.2.1)
  let xFires := (outs.zipIdx 0).filter (fun p =>
    p.1.outXVld && (ins.getD p.2 (false, exmVMulIdle, false, false)).2.2.2)
  (outs.all (fun o => !o.outVVld || exmChkVBits n din o))
    && (vFires.length == 1) && (xFires.length == 0)

/-- out_x 恰好 fire 一次且内容逐拍正确；out_v 从未 fire -/
def exmVMulExeChkX (din : ExmVExeIn)
    (ins : List (Bool × ExmVExeIn × Bool × Bool)) (outs : List ExmVMulExeOut) : Bool :=
  let vFires := (outs.zipIdx 0).filter (fun p =>
    p.1.outVVld && (ins.getD p.2 (false, exmVMulIdle, false, false)).2.2.1)
  let xFires := (outs.zipIdx 0).filter (fun p =>
    p.1.outXVld && (ins.getD p.2 (false, exmVMulIdle, false, false)).2.2.2)
  (outs.all (fun o => !o.outXVld || exmChkXBits din o))
    && (xFires.length == 1) && (vFires.length == 0)

def exmVMulMkIn (fn : BitVec 5) (rev wxd wvd : Bool) (wid : BitVec 3) (ri : BitVec 8)
    (a b c : List (BitVec 32)) (m : List Bool) : ExmVExeIn :=
  ⟨exmLaneVals a, exmLaneVals b, exmLaneVals c, exmLaneMask m,
   ⟨BitVec.zeroExtend 6 fn, wid, ri, 0#2, rev, wxd, wvd⟩⟩

section ExmVMulExeTests

-- 4 lane 向量 MUL：in1=[2,3,4,5] in2=[6,7,8,9]，全 mask
def exmT1In : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL false false true 3#3 7#8
    [2#32, 3#32, 4#32, 5#32] [6#32, 7#32, 8#32, 9#32] [0#32, 0#32, 0#32, 0#32]
    [true, true, true, true]

theorem exmVMulExe_test_vmul :
    let ins := ((true, exmT1In, true, true) :: List.replicate 8 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmT1In ins (exmVMulExeRun exmVMulExeInit ins) = true := by native_decide

-- 验证期望值本身：lane 积 = [12,21,32,45]（防止检查器双侧同错）
example : (List.range 4).map (fun i =>
    exmMulLaneOut mulFN_MUL false (exmT1In.in1 i) (exmT1In.in2 i) 0#32)
    = [12#32, 21#32, 32#32, 45#32] := by native_decide

-- 反压：outVRdy 前 5 拍为 0，结果不丢不重
theorem exmVMulExe_test_vmul_stall :
    let ins := ((true, exmT1In, false, true) :: List.replicate 4 (false, exmVMulIdle, false, true)
          ++ List.replicate 6 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmT1In ins (exmVMulExeRun exmVMulExeInit ins) = true := by native_decide

-- 标量 MULHU（wxd）：out_x = lane0 的无符号高 32 位
def exmT2In : ExmVExeIn :=
  exmVMulMkIn mulFN_MULHU false true false 1#3 2#8
    [0xFFFFFFFF#32] [0xFFFFFFFF#32] [0#32] [true]

theorem exmVMulExe_test_smulhu :
    let ins := ((true, exmT2In, true, true) :: List.replicate 8 (false, exmVMulIdle, true, true))
    exmVMulExeChkX exmT2In ins (exmVMulExeRun exmVMulExeInit ins) = true := by native_decide

-- 期望值钉死：MULHU(0xFFFFFFFF, 0xFFFFFFFF) = 0xFFFFFFFE
example : exmMulLaneOut mulFN_MULHU false 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32
    = 0xFFFFFFFE#32 := by native_decide

-- 【Q5/I-15 轨迹 witness】MULHSU 在 vMULexe 路径输出低 32 位
def exmT3In : ExmVExeIn :=
  exmVMulMkIn mulFN_MULHSU false false true 0#3 0#8
    [0xFFFFFFFF#32, 0xFFFFFFFF#32] [0xFFFFFFFF#32, 0xFFFFFFFF#32] [0#32, 0#32]
    [true, true]

theorem exmVMulExe_test_mulhsu_low32 :
    let ins := ((true, exmT3In, true, true) :: List.replicate 8 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 2 exmT3In ins (exmVMulExeRun exmVMulExeInit ins) = true := by native_decide

-- reverse：a/b 交换（MUL 可交换，改用 MACC 验证交换生效：a*b+c，swap 后 b*a+c 同值；
-- 用不可交换路径验证 swap 存在：无——MACC/MUL 均可交换，直接验证 swap 后 func 语义）
def exmT4In : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL true false true 3#3 7#8
    [2#32, 3#32] [6#32, 7#32] [0#32, 0#32] [true, true]

theorem exmVMulExe_test_reverse :
    let ins := ((true, exmT4In, true, true) :: List.replicate 8 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 2 exmT4In ins (exmVMulExeRun exmVMulExeInit ins) = true := by native_decide

end ExmVMulExeTests

/- ========================================================================= -/
/- 6. vMULv2（execution.scala:164-413，只建模 else 分支 :226-410，见 D6）      -/
/- ========================================================================= -/

/- ---- 6.1 lane 移位与结果装配（纯函数层，符号证明） ---- -/

/-- :290-300  inReg 的一批移位：in1/in2/in3 下搬 H 个 lane，顶部清零
    （mask/ctrl 不动，D8） -/
def exmShiftV (S H : Nat) (v : Nat → BitVec 32) : Nat → BitVec 32 :=
  fun i => if i + H < S then v (i + H) else 0#32

/-- 移位 k 次（批次 k 时 inReg 的状态） -/
def exmShiftN (S H : Nat) : Nat → (Nat → BitVec 32) → (Nat → BitVec 32)
  | 0, v => v
  | k + 1, v => exmShiftV S H (exmShiftN S H k v)

/-- 移位 k 次后 lane i 读到原始 lane (i + k*H)（读界内时）：
    批次 k 的硬件 lane x（x < H）拿到的正是原始 lane (k*H + x) -/
theorem exmShiftN_spec (S H : Nat) (v : Nat → BitVec 32) :
    ∀ (k i : Nat), i + k * H < S → exmShiftN S H k v i = v (i + k * H) := by
  intro k
  induction k with
  | zero =>
      intro i _
      simp [exmShiftN]
  | succ k ih =>
      intro i h
      have h1 : (k + 1) * H = k * H + H := Nat.succ_mul k H
      have hle : i + H < S := by rw [h1] at h; omega
      show exmShiftV S H (exmShiftN S H k v) i = v (i + (k + 1) * H)
      simp only [exmShiftV]
      rw [if_pos hle]
      have h' : i + H + k * H < S := by rw [h1] at h; omega
      rw [ih (i + H) h', h1]
      have : i + H + k * H = i + (k * H + H) := by omega
      rw [this]

/-- :375-382  resultReg 的一批移位装填：低 S-H 上搬，顶部 H 个装入本批结果 -/
def exmRRShift (S H : Nat) (rr batch : Nat → BitVec 32) : Nat → BitVec 32 :=
  fun i => if i + H < S then rr (i + H) else batch (i + H - S)

/-- 批次结果依次装填 k 次后的 resultReg（b t 为批次 t 的 H 个 lane 结果） -/
def exmRRAssembleN (S H : Nat) : Nat → (Nat → Nat → BitVec 32) → (Nat → BitVec 32)
  | 0, _ => fun _ => 0#32
  | k + 1, b => exmRRShift S H (exmRRAssembleN S H k b) (b k)

/-- 装配不变量：装填 k 批后，顶部 k*H 个槽位依次是批次 0..k-1 的结果
    （槽位 S - k*H + t*H + j ← 批次 t 的 lane j），即不漏不重、保序 -/
theorem exmRRAssembleN_spec (S H : Nat) (b : Nat → Nat → BitVec 32) :
    ∀ (k : Nat), k * H ≤ S → ∀ (t j : Nat), t < k → j < H →
      exmRRAssembleN S H k b (S - k * H + t * H + j) = b t j := by
  intro k
  induction k with
  | zero =>
      intro _ t j ht _
      exact absurd ht (Nat.not_lt_zero t)
  | succ k ih =>
      intro hS t j ht hj
      have hS' : (k + 1) * H ≤ S := hS
      rw [Nat.succ_mul] at hS'
      have hk : k * H ≤ S := by omega
      show exmRRShift S H (exmRRAssembleN S H k b) (b k)
        (S - (k + 1) * H + t * H + j) = b t j
      simp only [exmRRShift]
      by_cases htk : t < k
      · -- 旧批次：上搬后由原 k 批结果给出
        have htkH : (t + 1) * H ≤ k * H :=
          Nat.mul_le_mul (by omega : t + 1 ≤ k) (Nat.le_refl H)
        have htkH' : (t + 1) * H = t * H + H := Nat.succ_mul t H
        have hlt : S - (k + 1) * H + t * H + j + H < S := by rw [Nat.succ_mul]; omega
        rw [if_pos hlt]
        have hidx : S - (k + 1) * H + t * H + j + H = S - k * H + t * H + j := by
          rw [Nat.succ_mul]; omega
        rw [hidx]
        exact ih hk t j htk hj
      · -- 新批次（t = k）：落顶部槽位
        have htk2 : t = k := by omega
        rw [htk2]
        have hge : ¬(S - (k + 1) * H + k * H + j + H < S) := by rw [Nat.succ_mul] at *; omega
        rw [if_neg hge]
        have hidx : S - (k + 1) * H + k * H + j + H - S = j := by
          rw [Nat.succ_mul] at *; omega
        rw [hidx]

/-- **vMULv2 装配总定理**：S = m*H 时，m 批装填完成后 resultReg 的 lane i
    = 原始输入 lane i 的单 lane 乘法结果——每个软件 lane 恰好被服务一次。
    （批次 t 的 lane x 由 exmShiftN_spec 得原始 lane (t*H + x)，经
    exmMulExec_prep 得单 lane 结果；本定理把二者在结果层面钉合。） -/
theorem exmV2_result_spec (S H m : Nat) (hH : 0 < H) (hm : S = m * H)
    (f : BitVec 5) (r : Bool) (d1 d2 d3 : Nat → BitVec 32) (i : Nat) (hi : i < S) :
    exmRRAssembleN S H m
        (fun t x => exmMulLaneOut f r (d1 (t * H + x)) (d2 (t * H + x)) (d3 (t * H + x))) i
      = exmMulLaneOut f r (d1 i) (d2 i) (d3 i) := by
  have hmle : m * H ≤ S := by omega
  have hdecomp : (i / H) * H + i % H = i := by
    rw [Nat.mul_comm (i / H) H]
    exact Nat.div_add_mod i H
  have hmod : i % H < H := Nat.mod_lt i hH
  have hdiv : i / H < m := by
    apply Classical.byContradiction
    intro hge
    have h1 : m ≤ i / H := by omega
    have h2 : m * H ≤ (i / H) * H := Nat.mul_le_mul h1 (Nat.le_refl H)
    omega
  have hspec := exmRRAssembleN_spec S H
    (fun t x => exmMulLaneOut f r (d1 (t * H + x)) (d2 (t * H + x)) (d3 (t * H + x)))
    m hmle (i / H) (i % H) hdiv hmod
  have hidx : S - m * H + (i / H) * H + i % H = i := by omega
  simp only [hidx, hdecomp] at hspec
  exact hspec

/- ---- 6.2 时序模型（send/recv FSM + inReg/resultReg + mul pipe + 队列） ---- -/

/-- inReg（:229） -/
structure ExmV2InReg where
  in1 : Nat → BitVec 32
  in2 : Nat → BitVec 32
  in3 : Nat → BitVec 32
  mask : Nat → Bool
  ctrl : ExmCtrl

/-- resultReg（:231） -/
structure ExmV2RR where
  data : Nat → BitVec 32
  mask : Nat → Bool
  wvd : Bool
  regIdxw : BitVec 8
  wid : BitVec 3

structure ExmV2State where
  sendCS : Nat
  recvCS : Nat
  inReg : ExmV2InReg
  rr : ExmV2RR
  pipe : ExmPipe2 ExmMulPipeC ExmMulPipeD1 ExmMulPipeD2
  qv : Option ExmWBVec
  qx : Option ExmWBScalar

def exmV2Init : ExmV2State :=
  ⟨0, 0, ⟨fun _ => 0#32, fun _ => 0#32, fun _ => 0#32, fun _ => false, exmCtrlZero⟩,
   ⟨fun _ => 0#32, fun _ => false, false, 0#8, 0#3⟩,
   exmPipe2Init (exmCtrlZero, fun _ => false) (fun _ => (0#33, 0#33, 0#32)) (fun _ => 0#32),
   none, none⟩

/-- 单拍模型（:226-410 整体）。out_v/out_x 的 valid/bits 取【当前】队列状态；
    result_v/result_x 的 enq.bits 取【当前】resultReg（:398-404）。 -/
def exmV2Step (S H : Nat) (st : ExmV2State) (inV : Bool) (din : ExmVExeIn)
    (outVRdy outXRdy : Bool) : ExmVMulExeOut × ExmV2State :=
  let m := S / H                                                       -- :227
  let qvRdy := exmQEnqRdy st.qv outVRdy
  let qxRdy := exmQEnqRdy st.qx outXRdy
  -- :232  outFIFOReady（用 resultReg.wvd 的寄存器值，Q9 见 Multiplier 侧无）
  let outFIFORdy := if st.rr.wvd then qvRdy else qxRdy
  -- :392  recv.ready
  let recvRdy := (st.recvCS != m) || ((st.recvCS == m) && outFIFORdy)
  -- :309  send.ready = mul(0).in.ready；:394-395 mul(x).out.ready = recv.ready
  let sendRdy := exmPipe2InRdy recvRdy st.pipe
  -- :239  io.in.ready
  let inRdy := (st.sendCS == 0) || ((st.sendCS == m) && sendRdy)
  let inFire := inV && inRdy
  let sendVld := (st.sendCS != 0)                                      -- :308
  let sendFire := sendVld && sendRdy
  -- :241-277  sendNS（wvd 优先于 wxd，Q1）
  let sendNS :=
    if st.sendCS == 0 then
      (if inFire then (if din.ctrl.wvd then 1 else if din.ctrl.wxd then m else 0) else 0)
    else if st.sendCS == m then
      (if sendFire then
        (if inFire then (if din.ctrl.wvd then 1 else if din.ctrl.wxd then m else 0) else 0)
       else st.sendCS)
    else (if sendFire then st.sendCS + 1 else st.sendCS)
  -- :279-307  inReg 更新（keyed on sendNS；load 覆盖 shift，:303-305 在 :289 之后）
  let inReg' : ExmV2InReg :=
    if sendNS == 0 then
      ⟨fun _ => 0#32, fun _ => 0#32, fun _ => 0#32, fun _ => false, exmCtrlZero⟩
    else if sendNS == 1 then
      (if inFire then ⟨din.in1, din.in2, din.in3, din.mask, din.ctrl⟩ else st.inReg)
    else
      (if inFire then ⟨din.in1, din.in2, din.in3, din.mask, din.ctrl⟩
       else if sendFire then
        ⟨exmShiftV S H st.inReg.in1, exmShiftV S H st.inReg.in2,
         exmShiftV S H st.inReg.in3, st.inReg.mask, st.inReg.ctrl⟩
       else st.inReg)
  -- :311-322  mul 输入取【当前】inReg（reverse 用 inReg.ctrl，:318-321）
  let pipe' := exmPipe2Step (fun c i => exmMulPrep c.1 i) (fun c d => exmMulExec c.1 d)
    recvRdy sendVld (st.inReg.ctrl, st.inReg.mask)
    (fun x => (st.inReg.in1 x, st.inReg.in2 x, st.inReg.in3 x)) st.pipe
  -- :393  recv.valid = mul(0).out.valid
  let recvVld := st.pipe.v2
  let recvFire := recvVld && recvRdy
  let outCtrl := st.pipe.c2.1
  -- :329-367  recvNS（wxd 优先于 wvd，与 send 侧相反，Q1；
  --   中间态无 fire 时回 0，:343-349，Q2）
  let recvNS :=
    if st.recvCS == 0 then
      (if recvFire then (if outCtrl.wxd then m else if outCtrl.wvd then 1 else 0) else 0)
    else if st.recvCS == m then
      (if outFIFORdy then
        (if recvFire then (if outCtrl.wxd then m else if outCtrl.wvd then 1 else 0) else 0)
       else st.recvCS)
    else (if recvFire then st.recvCS + 1 else 0)
  -- :369-391  resultReg 更新（keyed on recvNS；hardResult = 当前 mul 输出，
  --   :394-397；末批捕获 mask/ctrl/wvd，:383-388）
  let rrShifted := exmRRShift S H st.rr.data st.pipe.d2
  let rr' : ExmV2RR :=
    if recvNS == 0 then ⟨fun _ => 0#32, fun _ => false, false, 0#8, 0#3⟩
    else if recvFire then
      (if recvNS == m then
        ⟨rrShifted, st.pipe.c2.2, outCtrl.wvd, outCtrl.regIdxw, outCtrl.wid⟩
       else ⟨rrShifted, st.rr.mask, st.rr.wvd, st.rr.regIdxw, st.rr.wid⟩)
    else st.rr
  -- :398-404  队列 enq（bits 取【当前】resultReg；result_x 取 lane (S-H)，Q7）
  let qvEnqV := (st.recvCS == m) && st.rr.wvd
  let qvBits : ExmWBVec := ⟨st.rr.data, st.rr.mask, st.rr.wvd, st.rr.regIdxw, st.rr.wid⟩
  let qxEnqV := (st.recvCS == m) && !st.rr.wvd
  let qxBits : ExmWBScalar := ⟨st.rr.data (S - H), !st.rr.wvd, st.rr.regIdxw, st.rr.wid⟩
  let out : ExmVMulExeOut :=
    { inRdy := inRdy
    , outVVld := exmQDeqVld st.qv
    , outVBits := st.qv.getD exmWBVecZero
    , outXVld := exmQDeqVld st.qx
    , outXBits := st.qx.getD exmWBScalarZero }
  (out, ⟨sendNS, recvNS, inReg', rr', pipe',
    exmQStep st.qv qvEnqV qvBits outVRdy, exmQStep st.qx qxEnqV qxBits outXRdy⟩)

def exmV2Run (S H : Nat) : ExmV2State → List (Bool × ExmVExeIn × Bool × Bool) →
    List ExmVMulExeOut
  | _, [] => []
  | st, (v, d, vr, xr) :: t =>
      let (o, st') := exmV2Step S H st v d vr xr
      o :: exmV2Run S H st' t

/- ---- 6.3 数值回归测试（native_decide 轨迹；S=4/H=2 与 S=6/H=2 实例） ---- -/

section ExmV2Tests

-- 向量 MUL，m=2（S=4，H=2）：每 lane 恰好服务一次、保序、mask/ctrl 透传
def exmV2T1In : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL false false true 5#3 9#8
    [2#32, 3#32, 4#32, 5#32] [6#32, 7#32, 8#32, 9#32] [0#32, 0#32, 0#32, 0#32]
    [true, false, true, false]

theorem exmV2_test_vmul_m2 :
    let ins := ((true, exmV2T1In, true, true) :: List.replicate 12 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmV2T1In ins (exmV2Run 4 2 exmV2Init ins) = true := by native_decide

-- 期望值钉死（防检查器双侧同错）：[12, 21, 32, 45]
example : (List.range 4).map (fun i =>
    exmMulLaneOut mulFN_MUL false (exmV2T1In.in1 i) (exmV2T1In.in2 i) 0#32)
    = [12#32, 21#32, 32#32, 45#32] := by native_decide

-- 向量 MUL，m=3（S=6，H=2）
def exmV2T2In : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL false false true 1#3 3#8
    [1#32, 2#32, 3#32, 4#32, 5#32, 6#32] [7#32, 8#32, 9#32, 10#32, 11#32, 12#32]
    [0#32, 0#32, 0#32, 0#32, 0#32, 0#32] [true, true, false, false, true, true]

theorem exmV2_test_vmul_m3 :
    let ins := ((true, exmV2T2In, true, true) :: List.replicate 14 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 6 exmV2T2In ins (exmV2Run 6 2 exmV2Init ins) = true := by native_decide

-- 标量 MACC（wxd，m=2）：只发一批，out_x = lane0 的 a*b+c（Q7 钉死 :400）
def exmV2T3In : ExmVExeIn :=
  exmVMulMkIn mulFN_MACC false true false 2#3 4#8
    [3#32, 0#32, 0#32, 0#32] [4#32, 0#32, 0#32, 0#32] [5#32, 0#32, 0#32, 0#32]
    [true, true, true, true]

theorem exmV2_test_smacc_m2 :
    let ins := ((true, exmV2T3In, true, true) :: List.replicate 12 (false, exmVMulIdle, true, true))
    exmVMulExeChkX exmV2T3In ins (exmV2Run 4 2 exmV2Init ins) = true := by native_decide

-- 期望值钉死：MACC(3,4,5) = 17
example : exmMulLaneOut mulFN_MACC false 3#32 4#32 5#32 = 17#32 := by native_decide

-- 连续流：A（wvd，m=2）→ B（wxd）背靠背，B 在 A 的 sendCS=maxIter 拍进入（:262-269）
def exmV2T4B : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL false true false 6#3 10#8
    [9#32, 0#32, 0#32, 0#32] [9#32, 0#32, 0#32, 0#32] [0#32, 0#32, 0#32, 0#32]
    [true, true, true, true]

/-- 连续流检查：A 的 out_v 恰好一次且先于 B 的 out_x；两侧数据/mask/ctrl 保真 -/
def exmV2ChkSeq (S : Nat) (dA dB : ExmVExeIn) (outs : List ExmVMulExeOut) : Bool :=
  let vList := (outs.zipIdx 0).filter (fun p => p.1.outVVld)
  let xList := (outs.zipIdx 0).filter (fun p => p.1.outXVld)
  match vList, xList with
  | [(v, iv)], [(x, ix)] =>
      decide (iv < ix)
      && (List.range S).all (fun i =>
          (v.outVBits.wbWvdRd i == exmMulLaneOut (dA.ctrl.aluFn.extractLsb' 0 5)
              dA.ctrl.reverse (dA.in1 i) (dA.in2 i) (dA.in3 i))
          && (v.outVBits.wvdMask i == dA.mask i))
      && (v.outVBits.warpId == dA.ctrl.wid) && (v.outVBits.regIdxw == dA.ctrl.regIdxw)
      && (x.outXBits.wbWxdRd == exmMulLaneOut (dB.ctrl.aluFn.extractLsb' 0 5)
              dB.ctrl.reverse (dB.in1 0) (dB.in2 0) (dB.in3 0))
      && (x.outXBits.wxd == true) && (x.outXBits.warpId == dB.ctrl.wid)
      && (x.outXBits.regIdxw == dB.ctrl.regIdxw)
  | _, _ => false

-- 时序推演：A 于 t0 进（sendCS 0→1），t1 发批 0，t2 发批 1 且 inRdy=1（:239），
-- B 于 t2 进
theorem exmV2_test_continuous :
    exmV2ChkSeq 4 exmV2T1In exmV2T4B
      (exmV2Run 4 2 exmV2Init
        ((true, exmV2T1In, true, true) :: (false, exmVMulIdle, true, true)
          :: (true, exmV2T4B, true, true)
          :: List.replicate 14 (false, exmVMulIdle, true, true)))
      = true := by native_decide

-- 反压：outVRdy 前 8 拍为 0，A 的结果在队列中保持，恢复后不丢不重
theorem exmV2_test_stall :
    let ins := ((true, exmV2T1In, false, true) :: List.replicate 7 (false, exmVMulIdle, false, true)
          ++ List.replicate 8 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmV2T1In ins (exmV2Run 4 2 exmV2Init ins) = true := by native_decide

-- 【Q5/I-15 轨迹 witness】vMULv2 路径 MULHSU 输出低 32 位
def exmV2T5In : ExmVExeIn :=
  exmVMulMkIn mulFN_MULHSU false false true 0#3 0#8
    [0xFFFFFFFF#32, 0xFFFFFFFF#32, 0x80000000#32, 0x80000000#32]
    [0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32]
    [0#32, 0#32, 0#32, 0#32] [true, true, true, true]

theorem exmV2_test_mulhsu_low32 :
    let ins := ((true, exmV2T5In, true, true) :: List.replicate 12 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmV2T5In ins (exmV2Run 4 2 exmV2Init ins) = true := by native_decide

-- 期望值钉死：源码现状 = 低 32 位（sext(-1)*zext(2^32-1) 低 32 = 1、
-- sext(INT_MIN)*zext(2^32-1) 低 32 = 0x80000000）
example : (List.range 4).map (fun i =>
    exmMulLaneOut mulFN_MULHSU false (exmV2T5In.in1 i) (exmV2T5In.in2 i) 0#32)
    = [1#32, 1#32, 0x80000000#32, 0x80000000#32] := by native_decide

-- reverse（m=2 路径，:318-321）
def exmV2T6In : ExmVExeIn :=
  exmVMulMkIn mulFN_MUL true false true 7#3 11#8
    [2#32, 3#32, 4#32, 5#32] [6#32, 7#32, 8#32, 9#32] [0#32, 0#32, 0#32, 0#32]
    [true, true, true, true]

theorem exmV2_test_reverse :
    let ins := ((true, exmV2T6In, true, true) :: List.replicate 12 (false, exmVMulIdle, true, true))
    exmVMulExeChkV 4 exmV2T6In ins (exmV2Run 4 2 exmV2Init ins) = true := by native_decide

end ExmV2Tests

/- ========================================================================= -/
/- 7. 公理审计（native_decide 轨迹带 Lean.ofReduceBool，归档注明）              -/
/- ========================================================================= -/

#print axioms exmQStep_pipe
#print axioms exmPipe2_two_cycles
#print axioms exmPipe2_stall_hold
#print axioms exmAluExe_latency_bN
#print axioms exmAluExe_latency_bB
#print axioms exmAluExe_latency_bJ
#print axioms exmMulExec_prep
#print axioms exmMulLaneOut_mulhsu
#print axioms exmMulLaneOut_mulhsu_witness
#print axioms exmVMulExe_latency_wvd
#print axioms exmVMulExe_latency_wxd
#print axioms exmShiftN_spec
#print axioms exmRRAssembleN_spec
#print axioms exmV2_result_spec
#print axioms exmV2_test_continuous

end Ventus.Arith
