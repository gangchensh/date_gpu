/- ========================================================================= -/
/-                     Arith/ScalarALU.lean                                  -/
/-  标量 ALU（ScalarALU）的 Lean 4 纯组合模型（M0 试点二）                    -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/ALU.scala          -/
/-    （ScalarALU 在 61-117 行；ALUOps 操作码表在 17-57 行；                 -/
/-      rocket-chip ALU 血统，SiFive 版权头；xLen = 32）                      -/
/-                                                                           -/
/- ======================== 建模假设 / 对 Chisel 的偏离点 ==================== -/
/-  D1. in3 无数据通路：ScalarALU 内 in3 输入（ALU.scala:66）不接任何逻辑，   -/
/-      MUL/MAC 族操作码（20-27，ALU.scala:40-47）在本模块输出恒 0            -/
/-      （isMIN/isMUL/isMAC 均不匹配 out 的 minmax 通路，shift_logic_cmp       -/
/-      三项全 0）。这是源码现状而非建模简化；正确性依赖 issue 阶段不将        -/
/-      MUL/MAC 路由到 ScalarALU 的约定（由主会话另行核实）。定理              -/
/-      sa_mul_family_out_zero 将"输出恒 0"钉死。                            -/
/-  D2. 移位器的 Reverse 技巧（ALU.scala:84-89）直接建模为 BitVec 移位：      -/
/-      SLL: Reverse 后逻辑右移再 Reverse ⇔ 左移；                           -/
/-      SRL: Cat(0, shin) >>> shamt 取低 32 位 ⇔ 逻辑右移；                  -/
/-      SRA: isSub(11)=true，Cat(符号位, shin) 算术右移取低 32 位 ⇔          -/
/-      sshiftRight（shamt ≤ 31 < 33 时逐位可验，33 位结果低 32 位与          -/
/-      32 位算术右移一致：bit i = i+shamt ≤ 31 ? x[i+shamt] : x[31]）。     -/
/-      shamt = in2 低 5 位（:84），建模为 in2 &&& 0x1F（高 27 位为 0，      -/
/-      与 5 位 shamt 的 toNat 相同）。                                      -/
/-  D3. Bool→UInt 的 1 位零扩展提升（:81, :96, :97 中 Bool 与 UInt 相或/      -/
/-      赋值）建模为 if-then-else 1#32/0#32。                                -/
/-  D4. in1_xor_in2 = in1 ^ in2_inv（:75，注意是 in2_inv 而非 in2），         -/
/-      按原样建模。由于 cmpEq=!func(3) 为真的 func（0-7）均不满足            -/
/-      isSub（10-15），eq 通路实际比较的就是 in1 == in2，与审查结论一致。    -/
/-  D5. adder_out 为 32 位回绕加（Chisel UInt(32.W)+UInt(32.W)+UInt(1.W)      -/
/-      结果按 xLen=32 截断，:74），对应 BitVec 32 的 +。                    -/
/-  D6. 无状态纯组合：无寄存器、无握手，建模为单个纯函数。                    -/
/-  D7. FN_SGE/FN_SGEU 的 out 语义：out 的比较通路（ALU.scala:96）用原始     -/
/-      slt 信号，cmpInverted 只作用于 cmp_out（ALU.scala:81），故这两个      -/
/-      func 的 out = (in1 < in2) 的 0/1，与 cmp_out 的 ≥ 语义相反。         -/
/-      与 rocket-chip 原版一致；定理 sa_sge_out_spec / sa_sgeu_out_spec       -/
/-      按源码现状钉死，是否构成 I 类 bug 取决于流水线是否消费此 out。         -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 操作码常量（ALU.scala:17-57 ALUOps）                                    -/
/- ========================================================================= -/

def saFN_ADD    : BitVec 5 := 0    -- ALU.scala:20
def saFN_SL     : BitVec 5 := 1    -- ALU.scala:21
def saFN_SEQ    : BitVec 5 := 2    -- ALU.scala:22
def saFN_SNE    : BitVec 5 := 3    -- ALU.scala:23
def saFN_XOR    : BitVec 5 := 4    -- ALU.scala:24
def saFN_SR     : BitVec 5 := 5    -- ALU.scala:25
def saFN_OR     : BitVec 5 := 6    -- ALU.scala:26
def saFN_AND    : BitVec 5 := 7    -- ALU.scala:27
def saFN_A1ZERO : BitVec 5 := 8    -- ALU.scala:38
def saFN_A2ZERO : BitVec 5 := 9    -- ALU.scala:39
def saFN_SUB    : BitVec 5 := 10   -- ALU.scala:28
def saFN_SRA    : BitVec 5 := 11   -- ALU.scala:29
def saFN_SLT    : BitVec 5 := 12   -- ALU.scala:30
def saFN_SGE    : BitVec 5 := 13   -- ALU.scala:31
def saFN_SLTU   : BitVec 5 := 14   -- ALU.scala:32
def saFN_SGEU   : BitVec 5 := 15   -- ALU.scala:33
def saFN_MAX    : BitVec 5 := 16   -- ALU.scala:34
def saFN_MIN    : BitVec 5 := 17   -- ALU.scala:35
def saFN_MAXU   : BitVec 5 := 18   -- ALU.scala:36
def saFN_MINU   : BitVec 5 := 19   -- ALU.scala:37
def saFN_MUL    : BitVec 5 := 20   -- ALU.scala:40
def saFN_MULH   : BitVec 5 := 21   -- ALU.scala:41
def saFN_MULHU  : BitVec 5 := 22   -- ALU.scala:42
def saFN_MULHSU : BitVec 5 := 23   -- ALU.scala:43
def saFN_MACC   : BitVec 5 := 24   -- ALU.scala:44
def saFN_NMSAC  : BitVec 5 := 25   -- ALU.scala:45
def saFN_MADD   : BitVec 5 := 26   -- ALU.scala:46
def saFN_NMSUB  : BitVec 5 := 27   -- ALU.scala:47

/- ========================================================================= -/
/- 2. func 译码谓词（ALU.scala:49-56）                                        -/
/-    全部写成 BitVec Bool 运算，保证 bv_decide 可穿透                         -/
/- ========================================================================= -/

/-- ALU.scala:49  isSub = (cmd >= FN_SUB) & (cmd <= FN_SGEU)，无符号区间比较 -/
def saIsSub (func : BitVec 5) : Bool :=
  BitVec.ule saFN_SUB func && BitVec.ule func saFN_SGEU

/-- ALU.scala:50  isCmp = (cmd >= FN_SLT) & (cmd <= FN_SGEU) -/
def saIsCmp (func : BitVec 5) : Bool :=
  BitVec.ule saFN_SLT func && BitVec.ule func saFN_SGEU

/-- ALU.scala:51  cmpUnsigned = cmd(1) -/
def saCmpUnsigned (func : BitVec 5) : Bool := func.getLsbD 1

/-- ALU.scala:52  cmpInverted = cmd(0) -/
def saCmpInverted (func : BitVec 5) : Bool := func.getLsbD 0

/-- ALU.scala:53  cmpEq = !cmd(3) -/
def saCmpEq (func : BitVec 5) : Bool := !func.getLsbD 3

/-- ALU.scala:54  isMIN = (cmd(4,2) == b100)，覆盖 func ∈ {16,17,18,19} -/
def saIsMIN (func : BitVec 5) : Bool := func.extractLsb' 2 3 == 0b100#3

/- ========================================================================= -/
/- 3. 组合数据通路（ALU.scala:61-117）                                        -/
/- ========================================================================= -/

/-- ScalarALU 纯组合模型。返回 (out, cmp_out)。in3 无通路（见 D1）。 -/
def saAlu (func : BitVec 5) (in1 in2 in3 : BitVec 32) : BitVec 32 × Bool :=
  -- ADD, SUB（ALU.scala:73-74）
  let in2_inv := if saIsSub func then ~~~in2 else in2
  let adder_out := in1 + in2_inv + (if saIsSub func then 1#32 else 0#32)
  -- ALU.scala:75（注意：与 in2_inv 异或，见 D4）
  let in1_xor_in2 := in1 ^^^ in2_inv
  -- SLT, SLTU（ALU.scala:78-80）：符号位相同取差的符号位，
  -- 否则无符号比较取 in2 符号位、有符号比较取 in1 符号位（rocket 标准做法）
  let sltRes :=
    if in1.msb == in2.msb then adder_out.msb
    else if saCmpUnsigned func then in2.msb else in1.msb
  -- cmp_out（ALU.scala:81）
  let cmp_out :=
    Bool.xor (saCmpInverted func)
      (if saCmpEq func then in1_xor_in2 == 0#32 else sltRes)
  -- SLL, SRL, SRA（ALU.scala:84-89）：Reverse 技巧 ⇔ 直接移位（见 D2）
  let shamt := in2 &&& 0x1F#32
  let shout :=
    if func == saFN_SRA then BitVec.sshiftRight' in1 shamt
    else if func == saFN_SR then in1 >>> shamt
    else if func == saFN_SL then in1 <<< shamt
    else 0#32
  -- AND, OR, XOR（ALU.scala:92-94）
  let logic :=
    if func == saFN_XOR then in1 ^^^ in2
    else if func == saFN_OR then in1 ||| in2
    else if func == saFN_AND then in1 &&& in2
    else 0#32
  -- ALU.scala:96（Bool 提升为 1#32/0#32，见 D3；三类通路 func 两两不相交，
  -- 故 OR 不会串扰：isCmp ⊂ {12..15}，logic 仅 {4,6,7}，shout 仅 {1,5,11}）
  let shift_logic_cmp :=
    (if saIsCmp func && sltRes then 1#32 else 0#32) ||| logic ||| shout
  -- ALU.scala:97
  let out_inner :=
    if func == saFN_ADD || func == saFN_SUB then adder_out
    else if func == saFN_SEQ then (if in1 == in2 then 1#32 else 0#32)
    else if func == saFN_SNE then (if in1 != in2 then 1#32 else 0#32)
    else shift_logic_cmp
  -- MIN, MAX（ALU.scala:101-106）：minu/maxu 无符号，mins/maxs 有符号
  let minu := if BitVec.ult in2 in1 then in2 else in1
  let maxu := if BitVec.ult in2 in1 then in1 else in2
  let mins := if BitVec.slt in2 in1 then in2 else in1
  let maxs := if BitVec.slt in2 in1 then in1 else in2
  -- ALU.scala:107-109（默认分支 maxu，仅 func=18 (MAXU) 落入）
  let minmaxout :=
    if func == saFN_MIN then mins
    else if func == saFN_MAX then maxs
    else if func == saFN_MINU then minu
    else maxu
  -- ALU.scala:111-113（注意 A1ZERO 输出 in2、A2ZERO 输出 in1，与名字相反）
  let out :=
    if func == saFN_A1ZERO then in2
    else if func == saFN_A2ZERO then in1
    else if saIsMIN func then minmaxout
    else out_inner
  (out, cmp_out)

/- ========================================================================= -/
/- 4. 数值回归测试（先测试：全部 `by decide`，覆盖边角）                       -/
/- ========================================================================= -/

section SaRegressionTests

-- ADD / SUB：回绕
example : (saAlu saFN_ADD 0xFFFFFFFF#32 1#32 0#32).1 = 0#32 := by decide
example : (saAlu saFN_ADD 3#32 4#32 0#32).1 = 7#32 := by decide
example : (saAlu saFN_SUB 0#32 1#32 0#32).1 = 0xFFFFFFFF#32 := by decide
example : (saAlu saFN_SUB 10#32 3#32 0#32).1 = 7#32 := by decide
example : (saAlu saFN_SUB 0x80000000#32 1#32 0#32).1 = 0x7FFFFFFF#32 := by decide

-- SLL：shamt = 0（且验证 in2 高位被掩蔽）、31、常规
example : (saAlu saFN_SL 1#32 31#32 0#32).1 = 0x80000000#32 := by decide
example : (saAlu saFN_SL 0xABCD#32 0x20#32 0#32).1 = 0xABCD#32 := by decide
example : (saAlu saFN_SL 1#32 0xFFFFFFE1#32 0#32).1 = 2#32 := by decide
example : (saAlu saFN_SL 0xFFFFFFFF#32 16#32 0#32).1 = 0xFFFF0000#32 := by decide

-- SRL：逻辑右移，高位补 0
example : (saAlu saFN_SR 0x80000000#32 31#32 0#32).1 = 1#32 := by decide
example : (saAlu saFN_SR 0xFFFF0000#32 8#32 0#32).1 = 0x00FFFF00#32 := by decide
example : (saAlu saFN_SR 0xDEADBEEF#32 0x40#32 0#32).1 = 0xDEADBEEF#32 := by decide

-- SRA：负数符号扩展（核心边角）
example : (saAlu saFN_SRA 0x80000000#32 31#32 0#32).1 = 0xFFFFFFFF#32 := by decide
example : (saAlu saFN_SRA 0xFFFF0000#32 8#32 0#32).1 = 0xFFFFFF00#32 := by decide
example : (saAlu saFN_SRA 0x7FFF0000#32 8#32 0#32).1 = 0x007FFF00#32 := by decide
example : (saAlu saFN_SRA 0x80000000#32 0#32 0#32).1 = 0x80000000#32 := by decide
example : (saAlu saFN_SRA 0xFFFFFFFF#32 20#32 0#32).1 = 0xFFFFFFFF#32 := by decide

-- SLT / SLTU：0x80000000 符号边界
example : (saAlu saFN_SLT 0x80000000#32 0#32 0#32) = (1#32, true) := by decide
example : (saAlu saFN_SLT 0#32 0x80000000#32 0#32) = (0#32, false) := by decide
example : (saAlu saFN_SLT 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32) = (0#32, false) := by decide
example : (saAlu saFN_SLTU 0x80000000#32 0x7FFFFFFF#32 0#32) = (0#32, false) := by decide
example : (saAlu saFN_SLTU 0x7FFFFFFF#32 0x80000000#32 0#32) = (1#32, true) := by decide
example : (saAlu saFN_SLTU 0xFFFFFFFF#32 0#32 0#32) = (0#32, false) := by decide

-- SGE / SGEU：注意 out 取的是原始 slt 信号（in1<in2，未按 cmpInverted 取反，
-- ALU.scala:96），正确的 ≥ 语义只在 cmp_out 上（ALU.scala:81）
example : (saAlu saFN_SGE 0#32 0xFFFFFFFF#32 0#32) = (0#32, true) := by decide
example : (saAlu saFN_SGE 0x80000000#32 0#32 0#32) = (1#32, false) := by decide
example : (saAlu saFN_SGEU 0xFFFFFFFF#32 0x80000000#32 0#32) = (0#32, true) := by decide
example : (saAlu saFN_SGEU 0#32 1#32 0#32) = (1#32, false) := by decide

-- SEQ / SNE
example : (saAlu saFN_SEQ 42#32 42#32 0#32) = (1#32, true) := by decide
example : (saAlu saFN_SEQ 42#32 43#32 0#32) = (0#32, false) := by decide
example : (saAlu saFN_SNE 42#32 43#32 0#32) = (1#32, true) := by decide
example : (saAlu saFN_SNE 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32) = (0#32, false) := by decide

-- XOR / OR / AND
example : (saAlu saFN_XOR 0xFF00FF00#32 0x0F0F0F0F#32 0#32).1 = 0xF00FF00F#32 := by decide
example : (saAlu saFN_OR  0xFF000000#32 0x00FF00FF#32 0#32).1 = 0xFFFF00FF#32 := by decide
example : (saAlu saFN_AND 0xFF00FF00#32 0x0FF00FF0#32 0#32).1 = 0x0F000F00#32 := by decide

-- A1ZERO / A2ZERO：输出与名字相反（A1ZERO→in2，A2ZERO→in1）
example : (saAlu saFN_A1ZERO 0xAAAA#32 0xBBBB#32 0#32).1 = 0xBBBB#32 := by decide
example : (saAlu saFN_A2ZERO 0xAAAA#32 0xBBBB#32 0#32).1 = 0xAAAA#32 := by decide

-- MIN / MAX：有符号负值
example : (saAlu saFN_MIN 0xFFFFFFFF#32 1#32 0#32).1 = 0xFFFFFFFF#32 := by decide
example : (saAlu saFN_MIN 0x80000000#32 0x7FFFFFFF#32 0#32).1 = 0x80000000#32 := by decide
example : (saAlu saFN_MAX 0xFFFFFFFF#32 1#32 0#32).1 = 1#32 := by decide
example : (saAlu saFN_MAX 0x80000000#32 0x7FFFFFFF#32 0#32).1 = 0x7FFFFFFF#32 := by decide
example : (saAlu saFN_MIN 5#32 5#32 0#32).1 = 5#32 := by decide

-- MINU / MAXU：无符号
example : (saAlu saFN_MINU 0xFFFFFFFF#32 1#32 0#32).1 = 1#32 := by decide
example : (saAlu saFN_MAXU 0xFFFFFFFF#32 1#32 0#32).1 = 0xFFFFFFFF#32 := by decide
example : (saAlu saFN_MINU 0x80000000#32 0x7FFFFFFF#32 0#32).1 = 0x7FFFFFFF#32 := by decide

-- MUL/MAC 族（20-27）：无数据通路，输出恒 0（钉死现状，见 D1）
example : (saAlu saFN_MUL 6#32 7#32 0#32).1 = 0#32 := by decide
example : (saAlu saFN_MULH 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32).1 = 0#32 := by decide
example : (saAlu saFN_MACC 1#32 2#32 3#32).1 = 0#32 := by decide
example : (saAlu saFN_NMSUB 0xDEADBEEF#32 0x12345678#32 0#32).1 = 0#32 := by decide

end SaRegressionTests

/- ========================================================================= -/
/- 5. 逐操作码规约定理（后证明：自由变量 in1 in2 in3，bv_decide）              -/
/- ========================================================================= -/

/-- 展开 saAlu 及其译码/常量的标准 simp 集（bv_decide 看不穿 def，须先展开） -/
macro "sa_unfold" : tactic =>
  `(tactic| simp only [saAlu, saIsSub, saIsCmp, saCmpUnsigned, saCmpInverted, saCmpEq,
    saIsMIN, saFN_ADD, saFN_SL, saFN_SEQ, saFN_SNE, saFN_XOR, saFN_SR, saFN_OR,
    saFN_AND, saFN_A1ZERO, saFN_A2ZERO, saFN_SUB, saFN_SRA, saFN_SLT, saFN_SGE,
    saFN_SLTU, saFN_SGEU, saFN_MAX, saFN_MIN, saFN_MAXU, saFN_MINU, saFN_MUL,
    saFN_MULH, saFN_MULHU, saFN_MULHSU, saFN_MACC, saFN_NMSAC, saFN_MADD, saFN_NMSUB])

-- ADD / SUB：32 位回绕加减
theorem sa_add_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_ADD in1 in2 in3).1 = in1 + in2 := by
  sa_unfold; bv_decide

theorem sa_sub_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SUB in1 in2 in3).1 = in1 - in2 := by
  sa_unfold; bv_decide

-- XOR / OR / AND
theorem sa_xor_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_XOR in1 in2 in3).1 = in1 ^^^ in2 := by
  sa_unfold; bv_decide

theorem sa_or_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_OR in1 in2 in3).1 = in1 ||| in2 := by
  sa_unfold; bv_decide

theorem sa_and_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_AND in1 in2 in3).1 = in1 &&& in2 := by
  sa_unfold; bv_decide

-- SLL / SRL / SRA：shamt = in2 低 5 位
theorem sa_sll_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SL in1 in2 in3).1 = in1 <<< (in2 &&& 0x1F#32) := by
  sa_unfold; bv_decide

theorem sa_srl_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SR in1 in2 in3).1 = in1 >>> (in2 &&& 0x1F#32) := by
  sa_unfold; bv_decide

theorem sa_sra_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SRA in1 in2 in3).1 = BitVec.sshiftRight' in1 (in2 &&& 0x1F#32) := by
  sa_unfold; bv_decide

-- SEQ / SNE：out 与 cmp_out 均为相等/不等谓词
theorem sa_seq_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SEQ in1 in2 in3).1 = (if in1 == in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_seq_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SEQ in1 in2 in3).2 = (in1 == in2) := by
  sa_unfold; bv_decide

theorem sa_sne_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SNE in1 in2 in3).1 = (if in1 != in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_sne_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SNE in1 in2 in3).2 = (in1 != in2) := by
  sa_unfold; bv_decide

-- SLT / SGE / SLTU / SGEU：out 与 cmp_out 等于对应有/无符号谓词的 0/1
theorem sa_slt_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SLT in1 in2 in3).1 = (if BitVec.slt in1 in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_slt_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SLT in1 in2 in3).2 = BitVec.slt in1 in2 := by
  sa_unfold; bv_decide

-- 注意（与任务审查结论不符之处，按源码现状建模并钉死）：
-- out 的比较通路是 isCmp(func) && slt（ALU.scala:96），用的是未按
-- cmpInverted(func) 取反的原始 slt 信号；cmpInverted 只作用于 cmp_out
-- （ALU.scala:81）。因此 FN_SGE/FN_SGEU 的 out = (in1 < in2) 的 0/1，
-- 与 cmp_out 的 ≥ 语义相反。这与 rocket-chip 原版一致（SGE/SGEU 在
-- RISC-V 中无寄存器写回形式，仅作分支条件走 cmp_out），是否构成
-- I 类 bug 取决于 Ventus 流水线是否消费这两个 func 的 out（待主会话核实）。
theorem sa_sge_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SGE in1 in2 in3).1 = (if BitVec.slt in1 in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_sge_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SGE in1 in2 in3).2 = BitVec.sle in2 in1 := by
  sa_unfold; bv_decide

theorem sa_sltu_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SLTU in1 in2 in3).1 = (if BitVec.ult in1 in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_sltu_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SLTU in1 in2 in3).2 = BitVec.ult in1 in2 := by
  sa_unfold; bv_decide

theorem sa_sgeu_out_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SGEU in1 in2 in3).1 = (if BitVec.ult in1 in2 then 1#32 else 0#32) := by
  sa_unfold; bv_decide

theorem sa_sgeu_cmp_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_SGEU in1 in2 in3).2 = BitVec.ule in2 in1 := by
  sa_unfold; bv_decide

-- MIN / MAX / MINU / MAXU
theorem sa_min_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_MIN in1 in2 in3).1 = (if BitVec.slt in1 in2 then in1 else in2) := by
  sa_unfold; bv_decide

theorem sa_max_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_MAX in1 in2 in3).1 = (if BitVec.slt in1 in2 then in2 else in1) := by
  sa_unfold; bv_decide

theorem sa_minu_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_MINU in1 in2 in3).1 = (if BitVec.ult in1 in2 then in1 else in2) := by
  sa_unfold; bv_decide

theorem sa_maxu_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_MAXU in1 in2 in3).1 = (if BitVec.ult in1 in2 then in2 else in1) := by
  sa_unfold; bv_decide

-- A1ZERO / A2ZERO：注意输出与操作码名字相反（ALU.scala:111-112）
theorem sa_a1zero_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_A1ZERO in1 in2 in3).1 = in2 := by
  sa_unfold; bv_decide

theorem sa_a2zero_spec (in1 in2 in3 : BitVec 32) :
    (saAlu saFN_A2ZERO in1 in2 in3).1 = in1 := by
  sa_unfold; bv_decide

-- MUL/MAC 族（func ∈ [20,27]）：无数据通路，out 恒 0（钉死源码现状，见 D1）
theorem sa_mul_family_out_zero (func : BitVec 5) (in1 in2 in3 : BitVec 32)
    (hlo : 20#5 ≤ func) (hhi : func ≤ 27#5) :
    (saAlu func in1 in2 in3).1 = 0#32 := by
  sa_unfold; bv_decide

/- ========================================================================= -/
/- 6. 公理审计（关键定理）                                                    -/
/- ========================================================================= -/

#print axioms sa_add_spec
#print axioms sa_sra_spec
#print axioms sa_slt_cmp_spec
#print axioms sa_sgeu_cmp_spec
#print axioms sa_min_spec
#print axioms sa_mul_family_out_zero

end Ventus.Arith
