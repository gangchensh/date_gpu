/- ========================================================================= -/
/-                     Arith/Classify.lean                                   -/
/-  IEEE 754 浮点位模式分类器（Classify）的 Lean 4 纯组合模型                  -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/Classify.scala     -/
/-    （全文 15-64 行；FloatPoint 定义见同目录 fpu_utils.scala:45-57，         -/
/-      Float32 = FloatPoint(8, 23) 见 fpu_utils.scala:74）                   -/
/-  例化点（全仓库仅两处，已 grep 核实）：                                      -/
/-    pipeline/FloatDivSqrt.scala:129,132，均为 Float32（expWidth=8,         -/
/-    fracWidth=23），且只消费 io.isSubnormalOrZero（:131,:134）。             -/
/-                                                                           -/
/- ======================== 建模假设 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 位段排布（Classify.scala:37-38）：io.in.asTypeOf(new FloatPoint)      -/
/-      按 Bundle 字段声明顺序 sign/exp/frac 从 MSB 到 LSB 拼接               -/
/-      （fpu_utils.scala:46-48），故 BitVec (1+e+f) 中 sign = 最高位、       -/
/-      exp = 位 [f+e-1 : f]、frac = 位 [f-1 : 0]。定理 cls_t4_sign/exp/     -/
/-      frac 将该排布钉死。                                                   -/
/-  D2. frac.head(1)（:54-55）= frac 的最高位（chisel3 API 文档：head(n)      -/
/-      返回 n 个最高有效位；tail(n) 返回 n 个最低位）。:54 的                 -/
/-      `!frac.head(1)` 未写 .asBool 而 :55 写了——两者均合法且语义一致：      -/
/-      UInt 的 unary_! 是"是否为零"的逻辑非（chisel3.UInt API 确认），       -/
/-      对 1 位 UInt 等价于按位取反。建模为 frac.msb。                        -/
/-  D3. (~exp).asUInt === 0.U（:42）：.asUInt 是恒等（exp 本为 UInt），       -/
/-      建模为 (~~~exp) == 0，即 exp 全 1。                                   -/
/-  D4. 输出前向引用：:44-52 读取 :58-62 才赋值的 io.isInf/isSubnormal/       -/
/-      isZero。Chisel 组合逻辑按最后连接语义，读到的是最终驱动值，            -/
/-      建模为同名局部 let 值，与赋值顺序无关。                                -/
/-  D5. 泛型假设 expWidth ≥ 1 且 fracWidth ≥ 1（Float32 实例 8/23 满足）；    -/
/-      零宽参数 Chisel 本身无法例化，不予建模。                              -/
/-  D6. 无状态纯组合：无寄存器、无握手，建模为单个纯函数。                     -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 输出信号集合（Classify.scala:16-36）                                    -/
/- ========================================================================= -/

/-- Classify 的 16 个输出信号（字段顺序与 Classify.scala:18-35 一致） -/
structure ClsOut where
  isNegInf : Bool          -- Classify.scala:18
  isNegNormal : Bool       -- Classify.scala:19
  isNegSubnormal : Bool    -- Classify.scala:20
  isNegZero : Bool         -- Classify.scala:21
  isPosZero : Bool         -- Classify.scala:22
  isPosSubnormal : Bool    -- Classify.scala:23
  isPosNormal : Bool       -- Classify.scala:24
  isPosInf : Bool          -- Classify.scala:25
  isSNaN : Bool            -- Classify.scala:26
  isQNaN : Bool            -- Classify.scala:27
  isNaN : Bool             -- Classify.scala:29
  isInf : Bool             -- Classify.scala:30
  isInfOrNaN : Bool        -- Classify.scala:31
  isSubnormal : Bool       -- Classify.scala:33
  isZero : Bool            -- Classify.scala:34
  isSubnormalOrZero : Bool -- Classify.scala:35
  deriving DecidableEq

/- ========================================================================= -/
/- 2. 位段切分（Classify.scala:37-38；FloatPoint 见 fpu_utils.scala:45-48）   -/
/- ========================================================================= -/

/-- sign 段（Classify.scala:38 flpt.sign）：输入最高位（见 D1） -/
def clsSign {e f : Nat} (x : BitVec (1+e+f)) : Bool := x.msb

/-- exp 段（Classify.scala:38 flpt.exp）：输入位 [f+e-1 : f] -/
def clsExp {e f : Nat} (x : BitVec (1+e+f)) : BitVec e := x.extractLsb' f e

/-- frac 段（Classify.scala:38 flpt.frac）：输入位 [f-1 : 0] -/
def clsFrac {e f : Nat} (x : BitVec (1+e+f)) : BitVec f := x.extractLsb' 0 f

/- ========================================================================= -/
/- 3. 组合逻辑（Classify.scala:40-63，逐行对应）                              -/
/- ========================================================================= -/

/-- Classify 纯组合模型，泛型于 (expWidth, fracWidth)。 -/
def clsClassify {e f : Nat} (x : BitVec (1+e+f)) : ClsOut :=
  let sign := clsSign x                               -- :38
  let exp := clsExp x                                 -- :38
  let frac := clsFrac x                               -- :38
  let isSubnormalOrZero := (exp == 0)                 -- :40  exp === 0.U
  let fracIsZero := (frac == 0)                       -- :41  frac === 0.U
  let isInfOrNaN := ((~~~exp) == 0)                   -- :42  (~exp).asUInt === 0.U（见 D3）
  let isNaN := isInfOrNaN && !fracIsZero              -- :57
  let isInf := isInfOrNaN && fracIsZero               -- :58
  let isSubnormal := isSubnormalOrZero && !fracIsZero -- :61
  let isZero := isSubnormalOrZero && fracIsZero       -- :62
  let fracHead := frac.msb                            -- :54-55 frac.head(1)（见 D2）
  { isNegInf       := sign && isInf                   -- :44（读 io.isInf，见 D4）
    isNegNormal    := sign && !isSubnormalOrZero && !isInfOrNaN   -- :45
    isNegSubnormal := sign && isSubnormal             -- :46
    isNegZero      := sign && isZero                  -- :47
    isPosZero      := !sign && isZero                 -- :52
    isPosSubnormal := !sign && isSubnormal            -- :51
    isPosNormal    := !sign && !isSubnormalOrZero && !isInfOrNaN  -- :50
    isPosInf       := !sign && isInf                  -- :49
    isSNaN         := isNaN && !fracHead              -- :54
    isQNaN         := isNaN && fracHead               -- :55
    isNaN          := isNaN                           -- :57
    isInf          := isInf                           -- :58
    isInfOrNaN     := isInfOrNaN                      -- :59
    isSubnormal    := isSubnormal                     -- :61
    isZero         := isZero                          -- :62
    isSubnormalOrZero := isSubnormalOrZero            -- :63
  }

/-- Float32 实例（expWidth=8, fracWidth=23；fpu_utils.scala:74，
    对应 FloatDivSqrt.scala:129,132 的实际例化） -/
def clsClassify32 (x : BitVec 32) : ClsOut := clsClassify (e := 8) (f := 23) x

/- ========================================================================= -/
/- 4. 数值回归测试（先测试：Float32 代表位模式，全部 `by decide`，            -/
/-    期望值逐字段独立写出，不借用模型的派生等式）                             -/
/- ========================================================================= -/

section ClsRegressionTests

-- +0（0x00000000）：isPosZero / isZero / isSubnormalOrZero
example : clsClassify32 0x00000000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := true, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := true, isSubnormalOrZero := true } := by decide

-- −0（0x80000000）：isNegZero / isZero / isSubnormalOrZero
example : clsClassify32 0x80000000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := true, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := true, isSubnormalOrZero := true } := by decide

-- +Inf（0x7F800000）：isPosInf / isInf / isInfOrNaN
example : clsClassify32 0x7F800000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := true, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := true, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- −Inf（0xFF800000）：isNegInf / isInf / isInfOrNaN
example : clsClassify32 0xFF800000#32 =
    { isNegInf := true, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := true, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- 正非规格化（0x007FFFF0）：isPosSubnormal / isSubnormal / isSubnormalOrZero
example : clsClassify32 0x007FFFF0#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := true,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := true, isZero := false, isSubnormalOrZero := true } := by decide

-- 负非规格化（0x80000001）：isNegSubnormal / isSubnormal / isSubnormalOrZero
example : clsClassify32 0x80000001#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := true,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := true, isZero := false, isSubnormalOrZero := true } := by decide

-- 最大非规格化（0x007FFFFF）：仍是非规格化而非 Normal
example : clsClassify32 0x007FFFFF#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := true,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := true, isZero := false, isSubnormalOrZero := true } := by decide

-- +1.0（0x3F800000）：isPosNormal，其余全假
example : clsClassify32 0x3F800000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := true, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- −1.0（0xBF800000）：isNegNormal，其余全假
example : clsClassify32 0xBF800000#32 =
    { isNegInf := false, isNegNormal := true, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- 最小正规格化（0x00800000）：isPosNormal（exp=0x01 边界）
example : clsClassify32 0x00800000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := true, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- 最大规格化（0x7F7FFFFF）：isPosNormal（exp=0xFE 边界）
example : clsClassify32 0x7F7FFFFF#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := true, isPosInf := false, isSNaN := false, isQNaN := false,
      isNaN := false, isInf := false, isInfOrNaN := false,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- SNaN（0x7F800001，exp 全 1、frac≠0、frac 最高位=0）：isSNaN / isNaN / isInfOrNaN
example : clsClassify32 0x7F800001#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := true, isQNaN := false,
      isNaN := true, isInf := false, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- 负号 SNaN（0xFF800001）：SNaN/QNaN 不分符号（Classify.scala:54-55 无 sign 项）
example : clsClassify32 0xFF800001#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := true, isQNaN := false,
      isNaN := true, isInf := false, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- QNaN（0x7FC00000，frac 最高位=1）：isQNaN / isNaN / isInfOrNaN
example : clsClassify32 0x7FC00000#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := true,
      isNaN := true, isInf := false, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

-- 全 1（0xFFFFFFFF）：负号 QNaN，isNegInf 必须为假
example : clsClassify32 0xFFFFFFFF#32 =
    { isNegInf := false, isNegNormal := false, isNegSubnormal := false,
      isNegZero := false, isPosZero := false, isPosSubnormal := false,
      isPosNormal := false, isPosInf := false, isSNaN := false, isQNaN := true,
      isNaN := true, isInf := false, isInfOrNaN := true,
      isSubnormal := false, isZero := false, isSubnormalOrZero := false } := by decide

end ClsRegressionTests

/- ========================================================================= -/
/- 5. 规约定理（后证明：自由 32 位变量，bv_decide）                            -/
/- ========================================================================= -/

/-- 展开 clsClassify32 及其位段/常量的标准 simp 集（bv_decide 看不穿 def） -/
macro "cls_unfold" : tactic =>
  `(tactic| simp only [clsClassify32, clsClassify, clsSign, clsExp, clsFrac])

/-- T1：十个带符号类别两两互斥（45 对，按首元素分 9 组）。 -/
theorem cls_t1_negInf_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isNegInf ∧ o.isNegNormal) ∧ ¬(o.isNegInf ∧ o.isNegSubnormal) ∧
    ¬(o.isNegInf ∧ o.isNegZero) ∧ ¬(o.isNegInf ∧ o.isPosZero) ∧
    ¬(o.isNegInf ∧ o.isPosSubnormal) ∧ ¬(o.isNegInf ∧ o.isPosNormal) ∧
    ¬(o.isNegInf ∧ o.isPosInf) ∧ ¬(o.isNegInf ∧ o.isSNaN) ∧
    ¬(o.isNegInf ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_negNormal_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isNegNormal ∧ o.isNegSubnormal) ∧ ¬(o.isNegNormal ∧ o.isNegZero) ∧
    ¬(o.isNegNormal ∧ o.isPosZero) ∧ ¬(o.isNegNormal ∧ o.isPosSubnormal) ∧
    ¬(o.isNegNormal ∧ o.isPosNormal) ∧ ¬(o.isNegNormal ∧ o.isPosInf) ∧
    ¬(o.isNegNormal ∧ o.isSNaN) ∧ ¬(o.isNegNormal ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_negSubnormal_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isNegSubnormal ∧ o.isNegZero) ∧ ¬(o.isNegSubnormal ∧ o.isPosZero) ∧
    ¬(o.isNegSubnormal ∧ o.isPosSubnormal) ∧ ¬(o.isNegSubnormal ∧ o.isPosNormal) ∧
    ¬(o.isNegSubnormal ∧ o.isPosInf) ∧ ¬(o.isNegSubnormal ∧ o.isSNaN) ∧
    ¬(o.isNegSubnormal ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_negZero_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isNegZero ∧ o.isPosZero) ∧ ¬(o.isNegZero ∧ o.isPosSubnormal) ∧
    ¬(o.isNegZero ∧ o.isPosNormal) ∧ ¬(o.isNegZero ∧ o.isPosInf) ∧
    ¬(o.isNegZero ∧ o.isSNaN) ∧ ¬(o.isNegZero ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_posZero_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isPosZero ∧ o.isPosSubnormal) ∧ ¬(o.isPosZero ∧ o.isPosNormal) ∧
    ¬(o.isPosZero ∧ o.isPosInf) ∧ ¬(o.isPosZero ∧ o.isSNaN) ∧
    ¬(o.isPosZero ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_posSubnormal_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isPosSubnormal ∧ o.isPosNormal) ∧ ¬(o.isPosSubnormal ∧ o.isPosInf) ∧
    ¬(o.isPosSubnormal ∧ o.isSNaN) ∧ ¬(o.isPosSubnormal ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_posNormal_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isPosNormal ∧ o.isPosInf) ∧ ¬(o.isPosNormal ∧ o.isSNaN) ∧
    ¬(o.isPosNormal ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_posInf_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isPosInf ∧ o.isSNaN) ∧ ¬(o.isPosInf ∧ o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t1_sNaN_pairwise (x : BitVec 32) :
    let o := clsClassify32 x
    ¬(o.isSNaN ∧ o.isQNaN) := by
  cls_unfold; bv_decide

/-- T2：穷尽性——任一输入恰落入十类之一（至少一类；结合 T1 即恰好一类）。
    SNaN/QNaN 不分符号，故十类已覆盖全部 2³² 种输入。 -/
theorem cls_t2_exhaustive (x : BitVec 32) :
    let o := clsClassify32 x
    o.isNegInf ∨ o.isNegNormal ∨ o.isNegSubnormal ∨ o.isNegZero ∨
    o.isPosZero ∨ o.isPosSubnormal ∨ o.isPosNormal ∨ o.isPosInf ∨
    o.isSNaN ∨ o.isQNaN := by
  cls_unfold; bv_decide

/-- T3：派生信号一致性（布尔等式） -/
theorem cls_t3_isNaN (x : BitVec 32) :
    let o := clsClassify32 x
    o.isNaN = (o.isSNaN || o.isQNaN) := by
  cls_unfold; bv_decide

theorem cls_t3_isInf (x : BitVec 32) :
    let o := clsClassify32 x
    o.isInf = (o.isPosInf || o.isNegInf) := by
  cls_unfold; bv_decide

theorem cls_t3_isInfOrNaN (x : BitVec 32) :
    let o := clsClassify32 x
    o.isInfOrNaN = (o.isInf || o.isNaN) := by
  cls_unfold; bv_decide

theorem cls_t3_isZero (x : BitVec 32) :
    let o := clsClassify32 x
    o.isZero = (o.isPosZero || o.isNegZero) := by
  cls_unfold; bv_decide

theorem cls_t3_isSubnormal (x : BitVec 32) :
    let o := clsClassify32 x
    o.isSubnormal = (o.isPosSubnormal || o.isNegSubnormal) := by
  cls_unfold; bv_decide

theorem cls_t3_isSubnormalOrZero (x : BitVec 32) :
    let o := clsClassify32 x
    o.isSubnormalOrZero = (o.isSubnormal || o.isZero) := by
  cls_unfold; bv_decide

/-- T4：位段切分钉死（FloatPoint Bundle 排布，见 D1） -/
theorem cls_t4_sign (x : BitVec 32) :
    clsSign (e := 8) (f := 23) x = x.msb := rfl

theorem cls_t4_exp (x : BitVec 32) :
    clsExp (e := 8) (f := 23) x = x.extractLsb' 23 8 := rfl

theorem cls_t4_frac (x : BitVec 32) :
    clsFrac (e := 8) (f := 23) x = x.extractLsb' 0 23 := rfl

/-- T4：十类与位条件的数学规约对应 -/
theorem cls_t4_isPosInf (x : BitVec 32) :
    (clsClassify32 x).isPosInf =
      (!x.msb && (x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isNegInf (x : BitVec 32) :
    (clsClassify32 x).isNegInf =
      (x.msb && (x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isPosNormal (x : BitVec 32) :
    (clsClassify32 x).isPosNormal =
      (!x.msb && (x.extractLsb' 23 8 != 0#8) && (x.extractLsb' 23 8 != 0xFF#8)) := by
  cls_unfold; bv_decide

theorem cls_t4_isNegNormal (x : BitVec 32) :
    (clsClassify32 x).isNegNormal =
      (x.msb && (x.extractLsb' 23 8 != 0#8) && (x.extractLsb' 23 8 != 0xFF#8)) := by
  cls_unfold; bv_decide

theorem cls_t4_isPosSubnormal (x : BitVec 32) :
    (clsClassify32 x).isPosSubnormal =
      (!x.msb && (x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 != 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isNegSubnormal (x : BitVec 32) :
    (clsClassify32 x).isNegSubnormal =
      (x.msb && (x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 != 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isPosZero (x : BitVec 32) :
    (clsClassify32 x).isPosZero =
      (!x.msb && (x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isNegZero (x : BitVec 32) :
    (clsClassify32 x).isNegZero =
      (x.msb && (x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

/-- SNaN/QNaN 由 frac 最高位（= 输入位 22）区分，与符号位无关 -/
theorem cls_t4_isSNaN (x : BitVec 32) :
    (clsClassify32 x).isSNaN =
      ((x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 != 0#23) &&
        !x.getLsbD 22) := by
  cls_unfold; bv_decide

theorem cls_t4_isQNaN (x : BitVec 32) :
    (clsClassify32 x).isQNaN =
      ((x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 != 0#23) &&
        x.getLsbD 22) := by
  cls_unfold; bv_decide

/-- T4：派生信号的位条件规约 -/
theorem cls_t4_isNaN (x : BitVec 32) :
    (clsClassify32 x).isNaN =
      ((x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 != 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isInf (x : BitVec 32) :
    (clsClassify32 x).isInf =
      ((x.extractLsb' 23 8 == 0xFF#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isInfOrNaN (x : BitVec 32) :
    (clsClassify32 x).isInfOrNaN = (x.extractLsb' 23 8 == 0xFF#8) := by
  cls_unfold; bv_decide

theorem cls_t4_isSubnormal (x : BitVec 32) :
    (clsClassify32 x).isSubnormal =
      ((x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 != 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isZero (x : BitVec 32) :
    (clsClassify32 x).isZero =
      ((x.extractLsb' 23 8 == 0#8) && (x.extractLsb' 0 23 == 0#23)) := by
  cls_unfold; bv_decide

theorem cls_t4_isSubnormalOrZero (x : BitVec 32) :
    (clsClassify32 x).isSubnormalOrZero = (x.extractLsb' 23 8 == 0#8) := by
  cls_unfold; bv_decide

/- ========================================================================= -/
/- 6. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms cls_t1_negInf_pairwise
#print axioms cls_t1_sNaN_pairwise
#print axioms cls_t2_exhaustive
#print axioms cls_t3_isInfOrNaN
#print axioms cls_t3_isSubnormalOrZero
#print axioms cls_t4_isPosNormal
#print axioms cls_t4_isSNaN
#print axioms cls_t4_isQNaN

end Ventus.Arith
