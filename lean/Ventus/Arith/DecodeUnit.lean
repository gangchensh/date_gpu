/- ========================================================================= -/
/-                     Arith/DecodeUnit.lean                                 -/
/-  译码单元（InstrDecodeV2）译码表与字段抽取的 Lean 4 模型                    -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/DecodeUnit.scala   -/
/-    （IDecode/IDecodeLUT_* 译码表 :18-493；InstrDecodeV2 :498-630）        -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/Instructions.scala -/
/-    （BitPat 指令编码表 :17-636）                                          -/
/-                                                                           -/
/-  本文件由脚本从上述两个 Scala 文件机械生成（BitPat→(mask,value)，         -/
/-  表行→27 元组），生成前已用独立的 Python 仿真核对每个回归测试编码          -/
/-  命中预期表行，并计算全部两两 BitPat 相交对。                              -/
/-                                                                           -/
/- ======================== 建模假设 / 对 Chisel 的偏离点 ==================== -/
/-  D1. ListLookup 语义：Chisel 7.0.0-RC1 的 ListLookup 实现为逐元素          -/
/-      MuxCase（首匹配优先，非 espresso 最小化；已从本机 coursier 缓存的      -/
/-      chisel_2.13-7.0.0-RC1.jar 字节码核实：ListLookup$ 对 default 与       -/
/-      mapping 逐列折叠 Mux）。因此 BitPat 两两相交时结果仍确定——表中        -/
/-      靠前的行遮蔽靠后的行；不相交性定理（A 区）是对"无遮蔽"的审计，        -/
/-      发现相交即发现潜在死行/误遮蔽。                                       -/
/-  D2. 单发射通道建模：num_fetch 通道共享同一译码逻辑（仅 pc/通道不同），    -/
/-      本模型只建模单条指令的 decDecode；regext 前缀按任务简报简化为          -/
/-      regPrefix=0（无扩展前缀），regext 流水线（:516-550）不在本文件。      -/
/-  D3. 外层 ListLookup（inst(6,0) 选表）的元素级 MuxCase 等价于整行选择      -/
/-      （各字段选择子相同），建模为整行 if-else 链，优先级与源码一致。       -/
/-  D4. c.csr 字段宽 2 位（scoreboard.scala:27），表行中的 CSR.N/W/S/C        -/
/-      为 chisel3.util.CSR 的 3 位常量（0-3），赋值时被截断为 2 位；          -/
/-      0-3 均可表示，截断无害，模型直接用 BitVec 2。                          -/
/-  D5. 默认行/表行中的 X = false.B（DecodeUnit.scala:22），各列取 0。        -/
/-      默认行 FN_X=63（6 位全 1），alu_fn=63 在 pipe.scala:277/283 有        -/
/-      issue 期 assertion（仿真期报 UNDEFINED INSTRUCTION）。                -/
/-  D6. c.writemask := 0.U（:604，s(21) 被弃用）——模型保留 s(21) 列数据       -/
/-      （与表一致），但"有效控制信号"中 writemask 恒 false。               -/
/-  D7. IDecodeLUT_A（AMO/LR/SC 表，:453-468）在源码中从未被例化              -/
/-      （:558 只用了 IMF/V/VL/VC）——AMO 指令经外层 ListLookup 落入 IMF       -/
/-      表查无此行，译码为默认行。模型忠实复现（AMO → decDefaultRow），        -/
/-      详见报告 I 类发现。                                                   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. BitPat 与匹配（Instructions.scala → (mask, value)）                     -/
/- ========================================================================= -/

/-- BitPat 编译后的形式：mask 中为 1 的位要求与 value 一致（? 位 mask=0）。 -/
structure DecBitPat where
  mask  : BitVec 32
  value : BitVec 32
  deriving Inhabited, DecidableEq

/-- BitPat 匹配（Chisel `pat === x`）：(x &&& mask) == value -/
def decMatch (p : DecBitPat) (x : BitVec 32) : Bool := (x &&& p.mask) == p.value

/-- 7 位 opcode 子模式匹配（外层 ListLookup，DecodeUnit.scala:561-569） -/
def decMatch7 (m v : BitVec 7) (x : BitVec 32) : Bool :=
  (x.extractLsb' 0 7 &&& m) == v

/- ========================================================================= -/
/- 2. 控制信号行（CtrlSigs 译码表部分，s(0)..s(26)，DecodeUnit.scala:579-625）-/
/-    列序 = 表行列序 = 赋值清单序：                                          -/
/-    s0 isvec, s1 fp, s2 barrier, s3 branch, s4 simtStack, s5 simtStackOp,   -/
/-    s6 csr, s7 reverse, s8 selAlu3, s9 selAlu2, s10 selAlu1, s11 selImm,    -/
/-    s12 memWhb, s13 aluFn, s14 mul, s15 memCmd, s16 memUnsigned, s17 fence, -/
/-    s18 sfu, s19 wvd, s20 readmask, s21 writemask(弃用), s22 wxd, s23 tc,   -/
/-    s24 disableMask, s25 custom0, s26 atomic                                -/
/- ========================================================================= -/

structure DecCtrlRow where
  isvec       : Bool      -- s0
  fp          : Bool      -- s1
  barrier     : Bool      -- s2
  branch      : BitVec 2  -- s3
  simtStack   : Bool      -- s4
  simtStackOp : Bool      -- s5
  csr         : BitVec 2  -- s6（CtrlSigs 为 2 位，见 D4）
  reverse     : Bool      -- s7
  selAlu3     : BitVec 2  -- s8
  selAlu2     : BitVec 2  -- s9
  selAlu1     : BitVec 2  -- s10
  selImm      : BitVec 4  -- s11
  memWhb      : BitVec 2  -- s12
  aluFn       : BitVec 6  -- s13
  mul         : Bool      -- s14
  memCmd      : BitVec 2  -- s15
  memUnsigned : Bool      -- s16
  fence       : Bool      -- s17
  sfu         : Bool      -- s18
  wvd         : Bool      -- s19
  readmask    : Bool      -- s20
  writemask   : Bool      -- s21（表中数据保留；c.writemask 恒 0，见 D6）
  wxd         : Bool      -- s22
  tc          : Bool      -- s23
  disableMask : Bool      -- s24
  custom0     : Bool      -- s25
  atomic      : Bool      -- s26
  deriving Inhabited, DecidableEq

/-- 带名字的表项（名字仅用于审计与报错定位，不参与译码） -/
structure DecEntry where
  name : String
  pat  : DecBitPat
  row  : DecCtrlRow
  deriving Inhabited, DecidableEq

/-- 默认行（DecodeUnit.scala:151）：全部副作用字段无效，aluFn=FN_X=63 -/
def decDefaultRow : DecCtrlRow := ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 0#2, 0#4, 0#2, 63#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩

/- ========================================================================= -/
/- 3. 四张译码表（DecodeUnit.scala:168-493；逐行机械移植，注释为源行号）      -/
/- ========================================================================= -/

/-- IDecodeLUT_IMF（:170-252）：RV32IMF + CSR/FENCE -/
def decTableIMF : List DecEntry := [
  ⟨"BNE", ⟨0x0000707F#32, 0x00001063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 3#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :171
  ⟨"BEQ", ⟨0x0000707F#32, 0x00000063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 2#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :172
  ⟨"BLT", ⟨0x0000707F#32, 0x00004063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 12#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :173
  ⟨"BLTU", ⟨0x0000707F#32, 0x00006063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 14#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :174
  ⟨"BGE", ⟨0x0000707F#32, 0x00005063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 13#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :175
  ⟨"BGEU", ⟨0x0000707F#32, 0x00007063#32⟩, ⟨false, false, false, 1#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 2#4, 0#2, 15#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :176
  ⟨"JAL", ⟨0x0000007F#32, 0x0000006F#32⟩, ⟨false, false, false, 2#2, false, false, 0#2, false, 0#2, 0#2, 0#2, 5#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :177
  ⟨"JALR", ⟨0x0000707F#32, 0x00000067#32⟩, ⟨false, false, false, 3#2, false, false, 0#2, false, 0#2, 0#2, 0#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :178
  ⟨"AUIPC", ⟨0x0000007F#32, 0x00000017#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 0#2, 3#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :179
  ⟨"CSRRW", ⟨0x0000707F#32, 0x00001073#32⟩, ⟨false, false, false, 0#2, false, false, 1#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :183
  ⟨"CSRRS", ⟨0x0000707F#32, 0x00002073#32⟩, ⟨false, false, false, 0#2, false, false, 2#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :184
  ⟨"CSRRC", ⟨0x0000707F#32, 0x00003073#32⟩, ⟨false, false, false, 0#2, false, false, 3#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :185
  ⟨"CSRRWI", ⟨0x0000707F#32, 0x00005073#32⟩, ⟨false, false, false, 0#2, false, false, 1#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :186
  ⟨"CSRRSI", ⟨0x0000707F#32, 0x00006073#32⟩, ⟨false, false, false, 0#2, false, false, 2#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :187
  ⟨"CSRRCI", ⟨0x0000707F#32, 0x00007073#32⟩, ⟨false, false, false, 0#2, false, false, 3#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :188
  ⟨"FENCE", ⟨0x0000707F#32, 0x0000000F#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 0#2, 0#4, 0#2, 0#6, false, 0#2, false, true, false, false, false, false, true, false, false, false, false⟩⟩, -- :190
  ⟨"LW", ⟨0x0000707F#32, 0x00002003#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 3#2, 0#6, false, 1#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :191
  ⟨"LH", ⟨0x0000707F#32, 0x00001003#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 1#2, 0#6, false, 1#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :192
  ⟨"LB", ⟨0x0000707F#32, 0x00000003#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 2#2, 0#6, false, 1#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :193
  ⟨"LHU", ⟨0x0000707F#32, 0x00005003#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 1#2, 0#6, false, 1#2, true, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :194
  ⟨"LBU", ⟨0x0000707F#32, 0x00004003#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 2#2, 0#6, false, 1#2, true, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :195
  ⟨"SW", ⟨0x0000707F#32, 0x00002023#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 1#2, 1#4, 3#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :196
  ⟨"SH", ⟨0x0000707F#32, 0x00001023#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 1#2, 1#4, 1#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :197
  ⟨"SB", ⟨0x0000707F#32, 0x00000023#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 1#2, 1#4, 2#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :198
  ⟨"LUI", ⟨0x0000007F#32, 0x00000037#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 0#2, 3#4, 0#2, 8#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :199
  ⟨"ADDI", ⟨0x0000707F#32, 0x00000013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :200
  ⟨"SLTI", ⟨0x0000707F#32, 0x00002013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :201
  ⟨"SLTIU", ⟨0x0000707F#32, 0x00003013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :202
  ⟨"ANDI", ⟨0x0000707F#32, 0x00007013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :203
  ⟨"ORI", ⟨0x0000707F#32, 0x00006013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :204
  ⟨"XORI", ⟨0x0000707F#32, 0x00004013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :205
  ⟨"ADD", ⟨0xFE00707F#32, 0x00000033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :206
  ⟨"SUB", ⟨0xFE00707F#32, 0x40000033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :207
  ⟨"SLT", ⟨0xFE00707F#32, 0x00002033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :208
  ⟨"SLTU", ⟨0xFE00707F#32, 0x00003033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :209
  ⟨"AND", ⟨0xFE00707F#32, 0x00007033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :210
  ⟨"OR", ⟨0xFE00707F#32, 0x00006033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :211
  ⟨"XOR", ⟨0xFE00707F#32, 0x00004033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :212
  ⟨"SLL", ⟨0xFE00707F#32, 0x00001033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :213
  ⟨"SRL", ⟨0xFE00707F#32, 0x00005033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :214
  ⟨"SRA", ⟨0xFE00707F#32, 0x40005033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :215
  ⟨"SLLI", ⟨0xFE00707F#32, 0x00001013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 4#4, 0#2, 1#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :216
  ⟨"SRLI", ⟨0xFE00707F#32, 0x00005013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 4#4, 0#2, 5#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :217
  ⟨"SRAI", ⟨0xFE00707F#32, 0x40005013#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 1#2, 4#4, 0#2, 11#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :218
  ⟨"MUL", ⟨0xFE00707F#32, 0x02000033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 20#6, true, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :221
  ⟨"MULH", ⟨0xFE00707F#32, 0x02001033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 21#6, true, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :222
  ⟨"MULHSU", ⟨0xFE00707F#32, 0x02002033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 23#6, true, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :223
  ⟨"MULHU", ⟨0xFE00707F#32, 0x02003033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 22#6, true, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :224
  ⟨"DIV", ⟨0xFE00707F#32, 0x02004033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :225
  ⟨"DIVU", ⟨0xFE00707F#32, 0x02005033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 2#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :226
  ⟨"REM", ⟨0xFE00707F#32, 0x02006033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :227
  ⟨"REMU", ⟨0xFE00707F#32, 0x02007033#32⟩, ⟨false, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 3#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :228
  ⟨"FMADD_S", ⟨0x0600007F#32, 0x00000043#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 2#2, 1#2, 1#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :230
  ⟨"FMSUB_S", ⟨0x0600007F#32, 0x00000047#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 2#2, 1#2, 1#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :231
  ⟨"FNMSUB_S", ⟨0x0600007F#32, 0x0000004B#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 2#2, 1#2, 1#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :232
  ⟨"FNMADD_S", ⟨0x0600007F#32, 0x0000004F#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 2#2, 1#2, 1#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :233
  ⟨"FADD_S", ⟨0xFE00007F#32, 0x00000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :234
  ⟨"FSUB_S", ⟨0xFE00007F#32, 0x08000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :235
  ⟨"FMUL_S", ⟨0xFE00007F#32, 0x10000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 2#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :236
  ⟨"FDIV_S", ⟨0xFE00007F#32, 0x18000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :237
  ⟨"FSQRT_S", ⟨0xFFF0007F#32, 0x58000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, true, false, false, false, true, false, false, false, false⟩⟩, -- :238
  ⟨"FSGNJ_S", ⟨0xFE00707F#32, 0x20000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 22#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :239
  ⟨"FSGNJN_S", ⟨0xFE00707F#32, 0x20001053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 21#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :240
  ⟨"FSGNJX_S", ⟨0xFE00707F#32, 0x20002053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 20#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :241
  ⟨"FMIN_S", ⟨0xFE00707F#32, 0x28000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 8#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :242
  ⟨"FMAX_S", ⟨0xFE00707F#32, 0x28001053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :243
  ⟨"FCVT_W_S", ⟨0xFFF0007F#32, 0xC0000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 25#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :244
  ⟨"FCVT_WU_S", ⟨0xFFF0007F#32, 0xC0100053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 24#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :245
  ⟨"FEQ_S", ⟨0xFE00707F#32, 0xA0002053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :246
  ⟨"FLT_S", ⟨0xFE00707F#32, 0xA0001053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :247
  ⟨"FLE_S", ⟨0xFE00707F#32, 0xA0000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :248
  ⟨"FCLASS_S", ⟨0xFFF0707F#32, 0xE0001053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 18#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :249
  ⟨"FCVT_S_W", ⟨0xFFF0007F#32, 0xD0000053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 33#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :250
  ⟨"FCVT_S_WU", ⟨0xFFF0007F#32, 0xD0100053#32⟩, ⟨false, true, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 32#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩ -- :251
  ]

/-- IDecodeLUT_V（:258-420）：RVV 算术（opcode 1010111） -/
def decTableV : List DecEntry := [
  ⟨"VFMUL_VV", ⟨0xFC00707F#32, 0x90001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 2#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :259
  ⟨"VFMUL_VF", ⟨0xFC00707F#32, 0x90005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 2#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :260
  ⟨"VFMADD_VV", ⟨0xFC00707F#32, 0xA0001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 2#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :261
  ⟨"VFMADD_VF", ⟨0xFC00707F#32, 0xA0005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 1#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :262
  ⟨"VFNMADD_VV", ⟨0xFC00707F#32, 0xA4001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 2#2, 0#4, 0#2, 17#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :263
  ⟨"VFNMADD_VF", ⟨0xFC00707F#32, 0xA4005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 1#2, 0#4, 0#2, 17#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :264
  ⟨"VFMSUB_VV", ⟨0xFC00707F#32, 0xA8001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 2#2, 0#4, 0#2, 15#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :265
  ⟨"VFMSUB_VF", ⟨0xFC00707F#32, 0xA8005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 1#2, 0#4, 0#2, 15#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :266
  ⟨"VFNMSUB_VV", ⟨0xFC00707F#32, 0xAC001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 2#2, 0#4, 0#2, 16#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :267
  ⟨"VFNMSUB_VF", ⟨0xFC00707F#32, 0xAC005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 1#2, 0#4, 0#2, 16#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :268
  ⟨"VFMACC_VV", ⟨0xFC00707F#32, 0xB0001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :270
  ⟨"VFMACC_VF", ⟨0xFC00707F#32, 0xB0005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :271
  ⟨"VFNMACC_VV", ⟨0xFC00707F#32, 0xB4001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :272
  ⟨"VFNMACC_VF", ⟨0xFC00707F#32, 0xB4005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :273
  ⟨"VFMSAC_VV", ⟨0xFC00707F#32, 0xB8001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :274
  ⟨"VFMSAC_VF", ⟨0xFC00707F#32, 0xB8005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :275
  ⟨"VFNMSAC_VV", ⟨0xFC00707F#32, 0xBC001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :276
  ⟨"VFNMSAC_VF", ⟨0xFC00707F#32, 0xBC005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :277
  ⟨"VADD_VV", ⟨0xFC00707F#32, 0x00000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :278
  ⟨"VADD_VX", ⟨0xFC00707F#32, 0x00004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :279
  ⟨"VADD_VI", ⟨0xFC00707F#32, 0x00003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 3#2, 6#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :280
  ⟨"VFADD_VV", ⟨0xFC00707F#32, 0x00001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :281
  ⟨"VFADD_VF", ⟨0xFC00707F#32, 0x00005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :282
  ⟨"VFSUB_VV", ⟨0xFC00707F#32, 0x08001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :283
  ⟨"VFSUB_VF", ⟨0xFC00707F#32, 0x08005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :284
  ⟨"VFRSUB_VF", ⟨0xFC00707F#32, 0x9C005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :285
  ⟨"VSUB_VV", ⟨0xFC00707F#32, 0x08000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :286
  ⟨"VSUB_VX", ⟨0xFC00707F#32, 0x08004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :287
  ⟨"VRSUB_VX", ⟨0xFC00707F#32, 0x0C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :288
  ⟨"VRSUB_VI", ⟨0xFC00707F#32, 0x0C003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :289
  ⟨"VFMIN_VV", ⟨0xFC00707F#32, 0x10001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 8#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :290
  ⟨"VFMIN_VF", ⟨0xFC00707F#32, 0x10005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 8#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :291
  ⟨"VFMAX_VV", ⟨0xFC00707F#32, 0x18001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :292
  ⟨"VFMAX_VF", ⟨0xFC00707F#32, 0x18005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :293
  ⟨"VAND_VV", ⟨0xFC00707F#32, 0x24000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :294
  ⟨"VAND_VX", ⟨0xFC00707F#32, 0x24004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :295
  ⟨"VAND_VI", ⟨0xFC00707F#32, 0x24003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 7#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :296
  ⟨"VOR_VV", ⟨0xFC00707F#32, 0x28000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :297
  ⟨"VOR_VX", ⟨0xFC00707F#32, 0x28004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :298
  ⟨"VOR_VI", ⟨0xFC00707F#32, 0x28003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 6#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :299
  ⟨"VXOR_VV", ⟨0xFC00707F#32, 0x2C000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :300
  ⟨"VXOR_VX", ⟨0xFC00707F#32, 0x2C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :301
  ⟨"VXOR_VI", ⟨0xFC00707F#32, 0x2C003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 4#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :302
  ⟨"VMSEQ_VV", ⟨0xFC00707F#32, 0x60000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 2#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :303
  ⟨"VMSEQ_VX", ⟨0xFC00707F#32, 0x60004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 2#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :304
  ⟨"VMSEQ_VI", ⟨0xFC00707F#32, 0x60003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 2#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :305
  ⟨"VMSNE_VV", ⟨0xFC00707F#32, 0x64000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 3#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :306
  ⟨"VMSNE_VX", ⟨0xFC00707F#32, 0x64004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 3#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :307
  ⟨"VMSNE_VI", ⟨0xFC00707F#32, 0x64003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 3#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :308
  ⟨"VMFEQ_VV", ⟨0xFC00707F#32, 0x60001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :309
  ⟨"VMFEQ_VF", ⟨0xFC00707F#32, 0x60005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :310
  ⟨"VMFNE_VV", ⟨0xFC00707F#32, 0x70001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 13#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :311
  ⟨"VMFNE_VF", ⟨0xFC00707F#32, 0x70005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 13#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :312
  ⟨"VMFLE_VV", ⟨0xFC00707F#32, 0x64001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :313
  ⟨"VMFLE_VF", ⟨0xFC00707F#32, 0x64005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :314
  ⟨"VMSLTU_VV", ⟨0xFC00707F#32, 0x68000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :315
  ⟨"VMSLTU_VX", ⟨0xFC00707F#32, 0x68004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :316
  ⟨"VMSLT_VV", ⟨0xFC00707F#32, 0x6C000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :317
  ⟨"VMSLT_VX", ⟨0xFC00707F#32, 0x6C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :318
  ⟨"VMFLT_VV", ⟨0xFC00707F#32, 0x6C001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :319
  ⟨"VMFLT_VF", ⟨0xFC00707F#32, 0x6C005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :320
  ⟨"VMFGT_VF", ⟨0xFC00707F#32, 0x74005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :321
  ⟨"VMFGE_VF", ⟨0xFC00707F#32, 0x7C005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :322
  ⟨"VSLL_VV", ⟨0xFC00707F#32, 0x94000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :323
  ⟨"VSLL_VX", ⟨0xFC00707F#32, 0x94004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :324
  ⟨"VSLL_VI", ⟨0xFC00707F#32, 0x94003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 3#2, 6#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :325
  ⟨"VSRL_VV", ⟨0xFC00707F#32, 0xA0000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :326
  ⟨"VSRL_VX", ⟨0xFC00707F#32, 0xA0004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 5#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :327
  ⟨"VSRL_VI", ⟨0xFC00707F#32, 0xA0003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 3#2, 6#4, 0#2, 5#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :328
  ⟨"VSRA_VV", ⟨0xFC00707F#32, 0xA4000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :329
  ⟨"VSRA_VX", ⟨0xFC00707F#32, 0xA4004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :330
  ⟨"VSRA_VI", ⟨0xFC00707F#32, 0xA4003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 3#2, 6#4, 0#2, 11#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :331
  ⟨"VMSLEU_VV", ⟨0xFC00707F#32, 0x70000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 15#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :333
  ⟨"VMSLEU_VI", ⟨0xFC00707F#32, 0x70003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 7#4, 0#2, 15#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :334
  ⟨"VMSLEU_VX", ⟨0xFC00707F#32, 0x70004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 15#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :335
  ⟨"VMSLE_VV", ⟨0xFC00707F#32, 0x74000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 13#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :336
  ⟨"VMSLE_VI", ⟨0xFC00707F#32, 0x74003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 13#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :337
  ⟨"VMSLE_VX", ⟨0xFC00707F#32, 0x74004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 13#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :338
  ⟨"VMSGTU_VI", ⟨0xFC00707F#32, 0x78003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 7#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :339
  ⟨"VMSGTU_VX", ⟨0xFC00707F#32, 0x78004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 14#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :340
  ⟨"VMSGT_VI", ⟨0xFC00707F#32, 0x7C003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :341
  ⟨"VMSGT_VX", ⟨0xFC00707F#32, 0x7C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 12#6, false, 0#2, false, false, false, true, false, true, false, false, false, false, false⟩⟩, -- :342
  ⟨"VREM_VV", ⟨0xFC00707F#32, 0x8C002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 1#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :344
  ⟨"VREM_VX", ⟨0xFC00707F#32, 0x8C006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 1#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :345
  ⟨"VREMU_VV", ⟨0xFC00707F#32, 0x88002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 3#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :346
  ⟨"VREMU_VX", ⟨0xFC00707F#32, 0x88006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 3#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :347
  ⟨"VDIV_VV", ⟨0xFC00707F#32, 0x84002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :348
  ⟨"VDIV_VX", ⟨0xFC00707F#32, 0x84006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :349
  ⟨"VDIVU_VV", ⟨0xFC00707F#32, 0x80002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 2#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :350
  ⟨"VDIVU_VX", ⟨0xFC00707F#32, 0x80006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 2#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :351
  ⟨"VFDIV_VV", ⟨0xFC00707F#32, 0x80001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :352
  ⟨"VFDIV_VF", ⟨0xFC00707F#32, 0x80005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :353
  ⟨"VFRDIV_VF", ⟨0xFC00707F#32, 0x84005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :354
  ⟨"VFSQRT_V", ⟨0xFC0FF07F#32, 0x4C001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 1#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩, -- :355
  ⟨"VMAND_MM", ⟨0xFC00707F#32, 0x64002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 7#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :357
  ⟨"VMOR_MM", ⟨0xFC00707F#32, 0x68002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 6#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :358
  ⟨"VMXOR_MM", ⟨0xFC00707F#32, 0x6C002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 4#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :359
  ⟨"VMANDN_MM", ⟨0xFC00707F#32, 0x60002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 59#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :360
  ⟨"VMORN_MM", ⟨0xFC00707F#32, 0x70002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 58#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :361
  ⟨"VMNAND_MM", ⟨0xFC00707F#32, 0x74002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 55#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :362
  ⟨"VMNOR_MM", ⟨0xFC00707F#32, 0x78002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 54#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :363
  ⟨"VMXNOR_MM", ⟨0xFC00707F#32, 0x7C002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 56#6, false, 0#2, false, false, false, true, true, true, false, false, false, false, false⟩⟩, -- :364
  ⟨"VID_V", ⟨0xFDFFF07F#32, 0x5008A057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 0#2, 0#4, 0#2, 57#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :366
  ⟨"VMERGE_VVM", ⟨0xFE00707F#32, 0x5C000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 51#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :367
  ⟨"VMERGE_VXM", ⟨0xFE00707F#32, 0x5C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 51#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :368
  ⟨"VMERGE_VIM", ⟨0xFE00707F#32, 0x5C003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 3#2, 6#4, 0#2, 51#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :369
  ⟨"VMUL_VV", ⟨0xFC00707F#32, 0x94002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 20#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :371
  ⟨"VMUL_VX", ⟨0xFC00707F#32, 0x94006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 20#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :372
  ⟨"VMULH_VV", ⟨0xFC00707F#32, 0x9C002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 21#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :373
  ⟨"VMULH_VX", ⟨0xFC00707F#32, 0x9C006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 21#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :374
  ⟨"VMULHU_VV", ⟨0xFC00707F#32, 0x90002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 22#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :375
  ⟨"VMULHU_VX", ⟨0xFC00707F#32, 0x90006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 22#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :376
  ⟨"VMULHSU_VV", ⟨0xFC00707F#32, 0x98002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 23#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :377
  ⟨"VMULHSU_VX", ⟨0xFC00707F#32, 0x98006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 23#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :378
  ⟨"VMACC_VV", ⟨0xFC00707F#32, 0xB4002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 24#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :379
  ⟨"VMACC_VX", ⟨0xFC00707F#32, 0xB4006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 24#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :380
  ⟨"VNMSAC_VV", ⟨0xFC00707F#32, 0xBC002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 25#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :381
  ⟨"VNMSAC_VX", ⟨0xFC00707F#32, 0xBC006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 25#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :382
  ⟨"VMADD_VV", ⟨0xFC00707F#32, 0xA4002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 26#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :383
  ⟨"VMADD_VX", ⟨0xFC00707F#32, 0xA4006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 26#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :384
  ⟨"VNMSUB_VV", ⟨0xFC00707F#32, 0xAC002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 2#2, 0#4, 0#2, 27#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :385
  ⟨"VNMSUB_VX", ⟨0xFC00707F#32, 0xAC006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 1#2, 2#2, 1#2, 0#4, 0#2, 27#6, true, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :386
  ⟨"VMINU_VV", ⟨0xFC00707F#32, 0x10000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 19#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :388
  ⟨"VMAXU_VV", ⟨0xFC00707F#32, 0x18000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 18#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :389
  ⟨"VMIN_VV", ⟨0xFC00707F#32, 0x14000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 17#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :390
  ⟨"VMAX_VV", ⟨0xFC00707F#32, 0x1C000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 2#2, 0#4, 0#2, 16#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :391
  ⟨"VMINU_VX", ⟨0xFC00707F#32, 0x10004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 19#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :392
  ⟨"VMAXU_VX", ⟨0xFC00707F#32, 0x18004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 18#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :393
  ⟨"VMIN_VX", ⟨0xFC00707F#32, 0x14004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 17#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :394
  ⟨"VMAX_VX", ⟨0xFC00707F#32, 0x1C004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 0#2, 16#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :395
  ⟨"VFSGNJ_VV", ⟨0xFC00707F#32, 0x20001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 22#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :396
  ⟨"VFSGNJ_VF", ⟨0xFC00707F#32, 0x20005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 22#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :397
  ⟨"VFSGNJN_VV", ⟨0xFC00707F#32, 0x24001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 21#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :398
  ⟨"VFSGNJN_VF", ⟨0xFC00707F#32, 0x24005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 21#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :399
  ⟨"VFSGNJX_VV", ⟨0xFC00707F#32, 0x28001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 2#2, 0#4, 0#2, 20#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :400
  ⟨"VFSGNJX_VF", ⟨0xFC00707F#32, 0x28005057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 1#2, 0#4, 0#2, 20#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :401
  ⟨"VFCVT_XU_F_V", ⟨0xFC0FF07F#32, 0x48001057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 24#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :402
  ⟨"VFCVT_X_F_V", ⟨0xFC0FF07F#32, 0x48009057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 25#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :403
  ⟨"VFCVT_RTZ_XU_F_V", ⟨0xFC0FF07F#32, 0x48031057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 24#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :404
  ⟨"VFCVT_RTZ_X_F_V", ⟨0xFC0FF07F#32, 0x48039057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 25#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :405
  ⟨"VFCVT_F_XU_V", ⟨0xFC0FF07F#32, 0x48011057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 32#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :406
  ⟨"VFCVT_F_X_V", ⟨0xFC0FF07F#32, 0x48019057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 33#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :407
  ⟨"VFCLASS_V", ⟨0xFC0FF07F#32, 0x4C081057#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, true, 0#2, 2#2, 0#2, 0#4, 0#2, 18#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :408
  ⟨"VMV_V_V", ⟨0xFFF0707F#32, 0x5E000057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 2#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :409
  ⟨"VFMV_V_F", ⟨0xFFF0707F#32, 0x5E005057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :410
  ⟨"VMV_V_I", ⟨0xFFF0707F#32, 0x5E003057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 0#2, 6#4, 0#2, 8#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :411
  ⟨"VMV_V_X", ⟨0xFFF0707F#32, 0x5E004057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :412
  ⟨"VMV_X_S", ⟨0xFE0FF07F#32, 0x42002057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 0#2, 0#4, 0#2, 8#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :413
  ⟨"VMV_S_X", ⟨0xFFF0707F#32, 0x42006057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :414
  ⟨"VFMV_F_S", ⟨0xFE0FF07F#32, 0x42001057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 0#2, 0#4, 0#2, 8#6, false, 0#2, false, false, false, false, false, false, true, false, false, false, false⟩⟩, -- :415
  ⟨"VFMV_S_F", ⟨0xFFF0707F#32, 0x42005057#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 9#6, false, 0#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :416
  ⟨"VSETVLI", ⟨0x8000707F#32, 0x00007057#32⟩, ⟨true, false, false, 0#2, false, false, 2#2, false, 0#2, 0#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, true, false, false⟩⟩, -- :417
  ⟨"VSETIVLI", ⟨0xC000707F#32, 0xC0007057#32⟩, ⟨true, false, false, 0#2, false, false, 2#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, true, false, false⟩⟩, -- :418
  ⟨"VSETVL", ⟨0xFE00707F#32, 0x80007057#32⟩, ⟨true, false, false, 0#2, false, false, 2#2, false, 0#2, 1#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, true, false, false⟩⟩ -- :419
  ]

/-- IDecodeLUT_VL（:426-451）：RVV 访存（0?00111/0101011/1111011） -/
def decTableVL : List DecEntry := [
  ⟨"VLE32_V", ⟨0x1DF0707F#32, 0x00006007#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 0#2, 1#2, 0#4, 3#2, 0#6, false, 1#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :428
  ⟨"VLSE32_V", ⟨0x1C00707F#32, 0x08006007#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 1#2, 1#2, 0#4, 3#2, 0#6, false, 1#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :429
  ⟨"VLOXEI32_V", ⟨0x1C00707F#32, 0x0C006007#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 1#2, 0#4, 3#2, 0#6, false, 1#2, false, false, false, true, false, false, false, false, false, false, false⟩⟩, -- :430
  ⟨"VSE32_V", ⟨0x1DF0707F#32, 0x00006027#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 0#2, 1#2, 0#4, 3#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :431
  ⟨"VSSE32_V", ⟨0x1C00707F#32, 0x08006027#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 1#2, 1#2, 0#4, 3#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :432
  ⟨"VSOXEI32_V", ⟨0x1C00707F#32, 0x0C006027#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 2#2, 1#2, 0#4, 3#2, 0#6, false, 2#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :433
  ⟨"VLW_V", ⟨0x8000707F#32, 0x0000202B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 9#4, 3#2, 0#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :435
  ⟨"VLH_V", ⟨0x8000707F#32, 0x0000102B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 9#4, 1#2, 0#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :436
  ⟨"VLB_V", ⟨0x8000707F#32, 0x0000002B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 9#4, 2#2, 0#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :437
  ⟨"VLHU_V", ⟨0x8000707F#32, 0x0000502B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 9#4, 1#2, 0#6, false, 1#2, true, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :438
  ⟨"VLBU_V", ⟨0x8000707F#32, 0x0000402B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 9#4, 2#2, 0#6, false, 1#2, true, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :439
  ⟨"VSW_V", ⟨0x8000707F#32, 0x8000202B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 8#4, 3#2, 0#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩, -- :440
  ⟨"VSH_V", ⟨0x8000707F#32, 0x8000102B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 8#4, 1#2, 0#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩, -- :441
  ⟨"VSB_V", ⟨0x8000707F#32, 0x8000002B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 8#4, 2#2, 0#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩, -- :442
  ⟨"VLW12_V", ⟨0x0000707F#32, 0x0000207B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 3#2, 30#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :443
  ⟨"VLH12_V", ⟨0x0000707F#32, 0x0000107B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 1#2, 30#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :444
  ⟨"VLB12_V", ⟨0x0000707F#32, 0x0000007B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 2#2, 30#6, false, 1#2, false, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :445
  ⟨"VLHU12_V", ⟨0x0000707F#32, 0x0000507B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 1#2, 30#6, false, 1#2, true, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :446
  ⟨"VLBU12_V", ⟨0x0000707F#32, 0x0000407B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 2#2, 30#6, false, 1#2, true, false, false, true, true, false, false, false, true, false, false⟩⟩, -- :447
  ⟨"VSW12_V", ⟨0x0000707F#32, 0x0000607B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 1#4, 3#2, 30#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩, -- :448
  ⟨"VSH12_V", ⟨0x0000707F#32, 0x0000307B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 1#4, 1#2, 30#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩, -- :449
  ⟨"VSB12_V", ⟨0x0000707F#32, 0x0000707B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 3#2, 3#2, 2#2, 1#4, 2#2, 30#6, false, 2#2, false, false, false, false, true, false, false, false, true, false, false⟩⟩ -- :450
  ]

/-- IDecodeLUT_VC（:472-492）：SIMT 自定义（1011011/0001011） -/
def decTableVC : List DecEntry := [
  ⟨"VBNE", ⟨0x0000707F#32, 0x0000105B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 3#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :473
  ⟨"VBEQ", ⟨0x0000707F#32, 0x0000005B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 2#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :474
  ⟨"VBLT", ⟨0x0000707F#32, 0x0000405B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 12#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :475
  ⟨"VBLTU", ⟨0x0000707F#32, 0x0000605B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 14#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :476
  ⟨"VBGE", ⟨0x0000707F#32, 0x0000505B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 13#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :477
  ⟨"VBGEU", ⟨0x0000707F#32, 0x0000705B#32⟩, ⟨true, false, false, 1#2, true, false, 0#2, true, 0#2, 2#2, 2#2, 2#4, 0#2, 15#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :478
  ⟨"JOIN", ⟨0x0000707F#32, 0x0000205B#32⟩, ⟨true, false, false, 1#2, true, true, 0#2, false, 0#2, 0#2, 0#2, 2#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, false, false, true, false, false⟩⟩, -- :479
  ⟨"SETRPC", ⟨0x0000707F#32, 0x0000305B#32⟩, ⟨false, false, false, 0#2, false, false, 1#2, false, 0#2, 3#2, 1#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, true, false, false, true, false⟩⟩, -- :480
  ⟨"BARRIER", ⟨0xFE00707F#32, 0x0400400B#32⟩, ⟨false, false, true, 0#2, false, false, 0#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :481
  ⟨"BARRIERSUB", ⟨0xFE00707F#32, 0x0600400B#32⟩, ⟨false, false, true, 0#2, false, false, 0#2, false, 0#2, 0#2, 3#2, 7#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :482
  ⟨"ENDPRG", ⟨0xFE00707F#32, 0x0000400B#32⟩, ⟨false, false, true, 0#2, false, true, 0#2, false, 0#2, 0#2, 0#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, false, false, false, false, false, false, false, false⟩⟩, -- :483
  ⟨"VADD12_VI", ⟨0x0000707F#32, 0x0000000B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, true, 0#2, 3#2, 2#2, 0#4, 0#2, 0#6, false, 0#2, false, false, false, true, false, false, false, false, true, false, false⟩⟩, -- :485
  ⟨"VSUB12_VI", ⟨0x0000707F#32, 0x0000100B#32⟩, ⟨true, false, false, 0#2, false, false, 0#2, false, 0#2, 3#2, 2#2, 0#4, 0#2, 10#6, false, 0#2, false, false, false, true, false, false, false, false, true, false, false⟩⟩, -- :486
  ⟨"VFTTA_VV", ⟨0xFC00707F#32, 0x0C00400B#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 1#2, 2#2, 2#2, 0#4, 0#2, 1#6, false, 0#2, false, false, false, true, false, false, false, true, false, false, false⟩⟩, -- :487
  ⟨"VFEXP_V", ⟨0xFC0FF07F#32, 0x0800600B#32⟩, ⟨true, true, false, 0#2, false, false, 0#2, false, 0#2, 2#2, 0#2, 0#4, 0#2, 4#6, false, 0#2, false, false, true, true, false, false, false, false, false, false, false⟩⟩ -- :488
  ]

/-- 全表拼接（审计用；IDecodeLUT_A 不在其中——它从未被例化，见 D7） -/
def decAllTables : List DecEntry :=
  decTableIMF ++ decTableV ++ decTableVL ++ decTableVC

/- ========================================================================= -/
/- 4. 译码器（ListLookup = 首匹配优先，见 D1/D3；DecodeUnit.scala:557-569）   -/
/- ========================================================================= -/

/-- 单表 ListLookup：首匹配优先，无匹配回落默认行 -/
def decLookupEntry (x : BitVec 32) : List DecEntry → DecCtrlRow
  | [] => decDefaultRow
  | e :: es => if decMatch e.pat x then e.row else decLookupEntry x es

/-- 完整译码：外层 ListLookup 按 inst(6,0) 选表（优先级序与 :562-568 一致） -/
def decDecode (inst : BitVec 32) : DecCtrlRow :=
  if decMatch7 0x7F#7 0x57#7 inst then decLookupEntry inst decTableV        -- 1010111
  else if decMatch7 0x7F#7 0x7B#7 inst then decLookupEntry inst decTableVL  -- 1111011
  else if decMatch7 0x5F#7 0x07#7 inst then decLookupEntry inst decTableVL  -- 0?00111
  else if decMatch7 0x7F#7 0x2B#7 inst then decLookupEntry inst decTableVL  -- 0101011
  else if decMatch7 0x7F#7 0x5B#7 inst then decLookupEntry inst decTableVC  -- 1011011
  else if decMatch7 0x7F#7 0x0B#7 inst then decLookupEntry inst decTableVC  -- 0001011
  else decLookupEntry inst decTableIMF

/-- 按名字取表行（回归测试用） -/
def decRowOf (t : List DecEntry) (name : String) : DecCtrlRow :=
  match t.find? (·.name == name) with
  | some e => e.row
  | none => decDefaultRow

/- ========================================================================= -/
/- 5. 字段抽取（DecodeUnit.scala:578-627；regext 关闭，regPrefix=0，见 D2）   -/
/- ========================================================================= -/

def decFN_VMERGE : BitVec 6 := 51  -- DecodeUnit.scala:100
def decFN_VLS12  : BitVec 6 := 30  -- DecodeUnit.scala:92
def decFN_X      : BitVec 6 := 63  -- DecodeUnit.scala:61

/-- :578  c.mop := Mux(c.readmask, 3.U, inst(27,26)) -/
def decMop (readmask : Bool) (inst : BitVec 32) : BitVec 2 :=
  if readmask then 3#2 else inst.extractLsb' 26 2

/-- :588  c.mask := (~inst(25) | alu_fn === FN_VMERGE) & isvec & !disable_mask -/
def decMaskEn (inst : BitVec 32) (aluFn : BitVec 6) (isvec disableMask : Bool) : Bool :=
  ((!(inst.extractLsb' 25 1 == 1#1)) || (aluFn == decFN_VMERGE)) && isvec && !disableMask

/-- :594  c.force_rm_rtz：对两条 VFCVT_RTZ 做 BitPat 相等比较
    （注意：是带 don't-care 的 BitPat ===，不是全 32 位精确相等，inst(25,20) 不参与比较） -/
def decForceRmRtz (inst : BitVec 32) : Bool :=
  decMatch ⟨0xFC0FF07F#32, 0x48039057#32⟩ inst ||
  decMatch ⟨0xFC0FF07F#32, 0x48031057#32⟩ inst

/-- :595  c.is_vls12 := s(13) === FN_VLS12 -/
def decIsVls12 (aluFn : BitVec 6) : Bool := aluFn == decFN_VLS12

/-- :609-612  reg_idx 拼接（regext 关闭时 regPrefix=0） -/
def decRegIdx1 (pfx : BitVec 3) (inst : BitVec 32) : BitVec 8 :=
  pfx ++ inst.extractLsb' 15 5
def decRegIdx2 (pfx : BitVec 3) (inst : BitVec 32) : BitVec 8 :=
  pfx ++ inst.extractLsb' 20 5
def decRegIdx3 (fp isvec : Bool) (pfx : BitVec 3) (inst : BitVec 32) : BitVec 8 :=
  if fp && !isvec then 0#3 ++ inst.extractLsb' 27 5 else pfx ++ inst.extractLsb' 7 5
def decRegIdxw (pfx : BitVec 3) (inst : BitVec 32) : BitVec 8 :=
  pfx ++ inst.extractLsb' 7 5

/-- :626-627  c.aq := s(26) & inst(26)；c.rl := s(26) & inst(25) -/
def decAq (atomic : Bool) (inst : BitVec 32) : Bool :=
  atomic && (inst.extractLsb' 26 1 == 1#1)
def decRl (atomic : Bool) (inst : BitVec 32) : Bool :=
  atomic && (inst.extractLsb' 25 1 == 1#1)

/- ========================================================================= -/
/- 6. A 区：BitPat 两两不相交审计                                             -/
/-    Chisel ListLookup 为首匹配优先（D1），相交不导致不确定，但意味着         -/
/-    靠后的行被遮蔽（死行）或意外的优先级覆盖——两类都应当为零。              -/
/- ========================================================================= -/

/-- 两 BitPat 可同时匹配同一输入 ⇔ 两 mask 共同约束的位上 value 无冲突 -/
def decOverlap (a b : DecBitPat) : Bool :=
  (a.mask &&& b.mask &&& (a.value ^^^ b.value)) == 0#32

/-- 表中所有两两相交的行对（按名字报告） -/
def decOverlapPairs (t : List DecEntry) : List (String × String) :=
  t.zipIdx.flatMap fun (a, i) =>
    (t.drop (i + 1)).filterMap fun b =>
      if decOverlap a.pat b.pat then some (a.name, b.name) else none

theorem dec_overlap_imf : decOverlapPairs decTableIMF = [] := by native_decide
theorem dec_overlap_v   : decOverlapPairs decTableV = [] := by native_decide
theorem dec_overlap_vl  : decOverlapPairs decTableVL = [] := by native_decide
theorem dec_overlap_vc  : decOverlapPairs decTableVC = [] := by native_decide

/- ========================================================================= -/
/- 7. B 区：默认行安全性与译码完备性                                          -/
/- ========================================================================= -/

/-- 默认行无任何架构状态副作用（不写寄存器、不访存、不分支、无 CSR/屏障/原子） -/
theorem dec_default_safe :
    decDefaultRow.wxd = false ∧ decDefaultRow.wvd = false ∧
    decDefaultRow.memCmd = 0#2 ∧ decDefaultRow.branch = 0#2 ∧
    decDefaultRow.simtStack = false ∧ decDefaultRow.csr = 0#2 ∧
    decDefaultRow.barrier = false ∧ decDefaultRow.atomic = false ∧
    decDefaultRow.mul = false ∧ decDefaultRow.sfu = false ∧
    decDefaultRow.fence = false ∧ decDefaultRow.tc = false ∧
    decDefaultRow.custom0 = false ∧ decDefaultRow.isvec = false ∧
    decDefaultRow.fp = false ∧ decDefaultRow.readmask = false ∧
    decDefaultRow.disableMask = false ∧ decDefaultRow.memUnsigned = false ∧
    decDefaultRow.aluFn = decFN_X := by decide

/-- 单表查找的值域：默认行或表中某行 -/
theorem decLookupEntry_mem (x : BitVec 32) (t : List DecEntry) :
    decLookupEntry x t = decDefaultRow ∨ decLookupEntry x t ∈ t.map DecEntry.row := by
  induction t with
  | nil => exact Or.inl rfl
  | cons e es ih =>
    unfold decLookupEntry
    by_cases h : decMatch e.pat x = true
    · rw [if_pos h]
      exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
    · rw [if_neg h]
      rcases ih with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons.mpr (Or.inr h2))

/-- 整机译码的值域：默认行或四张表中的某一行（副作用字段因此必与某表行一致） -/
theorem decDecode_mem (inst : BitVec 32) :
    decDecode inst = decDefaultRow ∨
    decDecode inst ∈ decTableIMF.map DecEntry.row ∨
    decDecode inst ∈ decTableV.map DecEntry.row ∨
    decDecode inst ∈ decTableVL.map DecEntry.row ∨
    decDecode inst ∈ decTableVC.map DecEntry.row := by
  unfold decDecode
  (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    rcases decLookupEntry_mem inst _ with h | h
    <;> first
      | exact Or.inl h
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inr (Or.inl h))
      | exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/- ========================================================================= -/
/- 8. C 区：编码→译码往返回归（27 字段全行钉死，编码由脚本生成并经独立仿真核对）-/
/- ========================================================================= -/

-- ADD x3,x4,x5
example : decDecode 0x005201B3#32 = (decRowOf decAllTables "ADD") := by decide
-- SUB x6,x7,x8
example : decDecode 0x40838333#32 = (decRowOf decAllTables "SUB") := by decide
-- MULH x1,x2,x3
example : decDecode 0x023110B3#32 = (decRowOf decAllTables "MULH") := by decide
-- MUL x9,x10,x11
example : decDecode 0x02B504B3#32 = (decRowOf decAllTables "MUL") := by decide
-- DIV x1,x2,x3
example : decDecode 0x023140B3#32 = (decRowOf decAllTables "DIV") := by decide
-- ADDI x1,x2,0x7FF
example : decDecode 0xFE010093#32 = (decRowOf decAllTables "ADDI") := by decide
-- SLLI x3,x4,5
example : decDecode 0x00521193#32 = (decRowOf decAllTables "SLLI") := by decide
-- SRAI x5,x6,7
example : decDecode 0x40735293#32 = (decRowOf decAllTables "SRAI") := by decide
-- LUI x8,hi
example : decDecode 0x56000437#32 = (decRowOf decAllTables "LUI") := by decide
-- AUIPC x9,hi
example : decDecode 0x24000497#32 = (decRowOf decAllTables "AUIPC") := by decide
-- LW x5,16(x6)
example : decDecode 0x02032283#32 = (decRowOf decAllTables "LW") := by decide
-- SW x7,20(x8)
example : decDecode 0x02742023#32 = (decRowOf decAllTables "SW") := by decide
-- BNE x1,x2,off
example : decDecode 0x3E209063#32 = (decRowOf decAllTables "BNE") := by decide
-- JAL x1,off
example : decDecode 0xAA0000EF#32 = (decRowOf decAllTables "JAL") := by decide
-- JALR x3,x4,0
example : decDecode 0x000201E7#32 = (decRowOf decAllTables "JALR") := by decide
-- CSRRW x1,csr,x2
example : decDecode 0x600110F3#32 = (decRowOf decAllTables "CSRRW") := by decide
-- CSRRSI x5,csr,uimm
example : decDecode 0x6001E2F3#32 = (decRowOf decAllTables "CSRRSI") := by decide
-- FENCE
example : decDecode 0x1E00000F#32 = (decRowOf decAllTables "FENCE") := by decide
-- FADD_S f1,f2,f3
example : decDecode 0x003100D3#32 = (decRowOf decAllTables "FADD_S") := by decide
-- FMADD_S f1,f2,f3,f4
example : decDecode 0x203100C3#32 = (decRowOf decAllTables "FMADD_S") := by decide
-- FSQRT_S f5,f6
example : decDecode 0x580302D3#32 = (decRowOf decAllTables "FSQRT_S") := by decide
-- FCVT_S_W f7,f8
example : decDecode 0xD00403D3#32 = (decRowOf decAllTables "FCVT_S_W") := by decide
-- FCVT_S_WU f9,f10
example : decDecode 0xD01504D3#32 = (decRowOf decAllTables "FCVT_S_WU") := by decide
-- VADD_VV v1,v2,v3
example : decDecode 0x003100D7#32 = (decRowOf decAllTables "VADD_VV") := by decide
-- VMERGE_VVM v4,v5,v6
example : decDecode 0x5C628257#32 = (decRowOf decAllTables "VMERGE_VVM") := by decide
-- VMAND_MM v7,v8,v9
example : decDecode 0x649423D7#32 = (decRowOf decAllTables "VMAND_MM") := by decide
-- VID_V v10
example : decDecode 0x5008A557#32 = (decRowOf decAllTables "VID_V") := by decide
-- VMSLE_VI v11,v12,imm
example : decDecode 0x740635D7#32 = (decRowOf decAllTables "VMSLE_VI") := by decide
-- VMSGTU_VI v13,v14,u
example : decDecode 0x780736D7#32 = (decRowOf decAllTables "VMSGTU_VI") := by decide
-- VBNE v1,v2,off
example : decDecode 0x2020905B#32 = (decRowOf decAllTables "VBNE") := by decide
-- JOIN off
example : decDecode 0x4000205B#32 = (decRowOf decAllTables "JOIN") := by decide
-- SETRPC x1,x2,imm
example : decDecode 0x060130DB#32 = (decRowOf decAllTables "SETRPC") := by decide
-- BARRIER
example : decDecode 0x0400400B#32 = (decRowOf decAllTables "BARRIER") := by decide
-- BARRIERSUB
example : decDecode 0x0600400B#32 = (decRowOf decAllTables "BARRIERSUB") := by decide
-- ENDPRG
example : decDecode 0x0000400B#32 = (decRowOf decAllTables "ENDPRG") := by decide
-- VADD12_VI v1,v2,imm
example : decDecode 0x0801008B#32 = (decRowOf decAllTables "VADD12_VI") := by decide
-- VFTTA_VV v1,v2,v3,v4
example : decDecode 0x0C31408B#32 = (decRowOf decAllTables "VFTTA_VV") := by decide
-- VFEXP_V v5,v6
example : decDecode 0x0860628B#32 = (decRowOf decAllTables "VFEXP_V") := by decide
-- VLW_V v1,(x2)
example : decDecode 0x040120AB#32 = (decRowOf decAllTables "VLW_V") := by decide
-- VSW12_V v3,(x4)
example : decDecode 0x0A0261FB#32 = (decRowOf decAllTables "VSW12_V") := by decide
-- VLE32_V v5,(x6)
example : decDecode 0x80036287#32 = (decRowOf decAllTables "VLE32_V") := by decide
-- VSOXEI32_V v7,(x8),v9
example : decDecode 0xCC9463A7#32 = (decRowOf decAllTables "VSOXEI32_V") := by decide
-- VSETVLI x1,x2,cfg
example : decDecode 0x300170D7#32 = (decRowOf decAllTables "VSETVLI") := by decide
-- VSETIVLI x3,uimm,cfg
example : decDecode 0xF00271D7#32 = (decRowOf decAllTables "VSETIVLI") := by decide
-- VSETVL x5,x6,x7
example : decDecode 0x807372D7#32 = (decRowOf decAllTables "VSETVL") := by decide
-- VMV_X_S x1,v2
example : decDecode 0x420020D7#32 = (decRowOf decAllTables "VMV_X_S") := by decide
-- VFMV_S_F v3,f4
example : decDecode 0x420251D7#32 = (decRowOf decAllTables "VFMV_S_F") := by decide
-- AMOADD_W x4,x5,x6 ->default
example : decDecode 0x0062A22F#32 = decDefaultRow := by decide
-- LR_W x7,(x8) ->default
example : decDecode 0x100423AF#32 = decDefaultRow := by decide
-- SC_W x9,x10,x11 ->default
example : decDecode 0x18B524AF#32 = decDefaultRow := by decide
-- FLW f1,0(x2) ->default
example : decDecode 0x00012087#32 = decDefaultRow := by decide
-- FSD f3,0(x4) ->default
example : decDecode 0x00323027#32 = decDefaultRow := by decide
-- ECALL ->default
example : decDecode 0x00000073#32 = decDefaultRow := by decide
-- C_ADDI ->default
example : decDecode 0x00000001#32 = decDefaultRow := by decide

/- ========================================================================= -/
/- 9. D 区：alu_fn 位宽截断碰撞分析                                           -/
/-    消费方位宽：ScalarALU ← alu_fn(4,0)（execution.scala:36）；              -/
/-    Multiplier ← alu_fn(4,0)（Multiplier.scala:156-200）；vALU ← alu_fn(4,0)-/
/-    但对 FN≥50 的行先做全 6 位比较覆写（execution.scala:433-449,518-549,    -/
/-    712-728）；FPU ← 全 6 位 alu_fn（execution.scala:768）；intDiv ←         -/
/-    alu_fn(2,0)（:870,889,891）。                                           -/
/-    结论：FN≥32 的行全部走 isvec 或 fp 路径（下一定理），不消费 ScalarALU    -/
/-    的 5 位截断输出；Multiplier 路径（mul=true）全部 FN≤27；vALU 路径的     -/
/-    FN≥50 均被全 6 位覆写逻辑拦截。故低 5 位碰撞全部无害。                  -/
/- ========================================================================= -/

/-- FN ≥ 32 的表行必走向量或浮点路径（不经过 ScalarALU/Multiplier 的 5 位截断） -/
theorem dec_fn_ge32_implies_vec_or_fp :
    decAllTables.all (fun e => e.row.aluFn < 32#6 || e.row.isvec || e.row.fp) = true :=
  by native_decide

/-- mul=true 的表行 FN 全部 ≤ 27（Multiplier 的 (4,0) 截断无碰撞） -/
theorem dec_mul_fn_lt32 :
    decAllTables.all (fun e => !e.row.mul || e.row.aluFn ≤ 27#6) = true :=
  by native_decide

/-- FN≥32 值与低 5 位碰撞清单（钉死数值；消费方分析见本节头注释） -/
example : (32#6 : BitVec 6).extractLsb' 0 5 = 0#5  := by decide  -- FN_IU2F→FN_ADD
example : (33#6 : BitVec 6).extractLsb' 0 5 = 1#5  := by decide  -- FN_I2F→FN_SL
example : (51#6 : BitVec 6).extractLsb' 0 5 = 19#5 := by decide  -- FN_VMERGE→FN_MINU
example : (54#6 : BitVec 6).extractLsb' 0 5 = 22#5 := by decide  -- FN_VMNOR→FN_MULHU
example : (55#6 : BitVec 6).extractLsb' 0 5 = 23#5 := by decide  -- FN_VMNAND→FN_MULHSU
example : (56#6 : BitVec 6).extractLsb' 0 5 = 24#5 := by decide  -- FN_VMXNOR→FN_MACC
example : (57#6 : BitVec 6).extractLsb' 0 5 = 25#5 := by decide  -- FN_VID→FN_NMSAC
example : (58#6 : BitVec 6).extractLsb' 0 5 = 26#5 := by decide  -- FN_VMORNOT→FN_MADD
example : (59#6 : BitVec 6).extractLsb' 0 5 = 27#5 := by decide  -- FN_VMANDNOT→FN_NMSUB
example : (63#6 : BitVec 6).extractLsb' 0 5 = 31#5 := by decide  -- FN_X→31（无此 ALU 操作码）

/- ========================================================================= -/
/- 10. D 区：字段抽取定理                                                     -/
/- ========================================================================= -/

/-- 展开字段抽取定义的标准 simp 集（bv_decide 看不穿 def，须先展开） -/
macro "dec_unfold" : tactic =>
  `(tactic| simp only [decMatch, decMatch7, decMop, decMaskEn, decForceRmRtz,
    decIsVls12, decRegIdx1, decRegIdx2, decRegIdx3, decRegIdxw, decAq, decRl,
    decFN_VMERGE, decFN_VLS12, decFN_X])

/-- regext 关闭时 reg_idx = 原 inst 字段的零扩展（:609-612） -/
theorem dec_regidx1_noext (inst : BitVec 32) :
    decRegIdx1 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 15 5) := by
  dec_unfold; bv_decide
theorem dec_regidx2_noext (inst : BitVec 32) :
    decRegIdx2 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 20 5) := by
  dec_unfold; bv_decide
theorem dec_regidxw_noext (inst : BitVec 32) :
    decRegIdxw 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 7 5) := by
  dec_unfold; bv_decide

/-- reg_idx3：标量浮点取 rs3 字段（inst(31,27)，前缀恒 0），其余取 rd 字段 -/
theorem dec_regidx3_scalar_fp (inst : BitVec 32) :
    decRegIdx3 true false 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 27 5) := by
  dec_unfold; bv_decide
theorem dec_regidx3_noext (inst : BitVec 32) :
    decRegIdx3 false false 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 7 5) := by
  dec_unfold; bv_decide
theorem dec_regidx3_vec (inst : BitVec 32) :
    decRegIdx3 false true 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 7 5) := by
  dec_unfold; bv_decide
theorem dec_regidx3_vec_fp (inst : BitVec 32) :
    decRegIdx3 true true 0#3 inst = BitVec.zeroExtend 8 (inst.extractLsb' 7 5) := by
  dec_unfold; bv_decide

/-- mop：readmask=1 时强制 3，否则透传 inst(27,26)（:578） -/
theorem dec_mop_readmask (inst : BitVec 32) : decMop true inst = 3#2 := by
  dec_unfold; bv_decide
theorem dec_mop_passthru (inst : BitVec 32) :
    decMop false inst = inst.extractLsb' 26 2 := by
  dec_unfold; bv_decide

/-- mask 使能（:588）：vm=1（inst(25)=0）或 FN_VMERGE 时向量指令读 v0 掩码 -/
theorem dec_mask_vm0 (inst : BitVec 32) (aluFn : BitVec 6)
    (h : inst.extractLsb' 25 1 = 0#1) :
    decMaskEn inst aluFn true false = true := by
  dec_unfold; bv_decide
theorem dec_mask_vmerge (inst : BitVec 32)
    (h : inst.extractLsb' 25 1 = 1#1) :
    decMaskEn inst decFN_VMERGE true false = true := by
  dec_unfold; bv_decide
theorem dec_mask_scalar_off (inst : BitVec 32) (aluFn : BitVec 6) :
    decMaskEn inst aluFn false false = false := by
  dec_unfold; bv_decide
theorem dec_mask_disable (inst : BitVec 32) (aluFn : BitVec 6) :
    decMaskEn inst aluFn true true = false := by
  dec_unfold; bv_decide

/-- force_rm_rtz（:594）：BitPat 比较，inst(25,20) 不影响结果 -/
theorem dec_force_rm_rtz_spec (inst : BitVec 32) :
    decForceRmRtz inst = true ↔
      (inst &&& 0xFC0FF07F#32) == 0x48039057#32 ∨
      (inst &&& 0xFC0FF07F#32) == 0x48031057#32 := by
  dec_unfold; bv_decide

/-- aq/rl：仅 atomic 行为 1 时透传 inst(26)/inst(25)（:626-627） -/
theorem dec_aq_spec (inst : BitVec 32) :
    decAq true inst = (inst.extractLsb' 26 1 == 1#1) := by
  dec_unfold; bv_decide
theorem dec_rl_spec (inst : BitVec 32) :
    decRl true inst = (inst.extractLsb' 25 1 == 1#1) := by
  dec_unfold; bv_decide
theorem dec_aq_nonatomic (inst : BitVec 32) : decAq false inst = false := by
  dec_unfold; bv_decide
theorem dec_rl_nonatomic (inst : BitVec 32) : decRl false inst = false := by
  dec_unfold; bv_decide

/-- is_vls12 等价于 aluFn = 30（:595） -/
theorem dec_isvls12_spec (aluFn : BitVec 6) :
    decIsVls12 aluFn = (aluFn == 30#6) := by
  dec_unfold; bv_decide

/- ========================================================================= -/
/- 11. 公理审计（native_decide 定理含 Lean.ofReduceBool，归档注明）            -/
/- ========================================================================= -/

#print axioms dec_overlap_imf
#print axioms dec_overlap_v
#print axioms dec_overlap_vl
#print axioms dec_overlap_vc
#print axioms dec_default_safe
#print axioms decDecode_mem
#print axioms dec_fn_ge32_implies_vec_or_fp
#print axioms dec_mul_fn_lt32
#print axioms dec_regidx1_noext
#print axioms dec_force_rm_rtz_spec

end Ventus.Arith
