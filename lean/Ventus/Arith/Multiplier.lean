/- ========================================================================= -/
/-                     Arith/Multiplier.lean                                 -/
/-  阵列乘法器（Multiplier.scala + mul_utils.scala）的 Lean 4 模型、测试与证明 -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/Multiplier.scala    -/
/-    （ArrayMulDataModule :28-147，Booth-2 部分积 + CSA 列压缩，             -/
/-      XiangShan 血统；ArrayMultiplier :149-211，latency=2 wrapper）          -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/mul_utils.scala     -/
/-    （CSA2_2/3_2/5_3 :72-105，SignExt/ZeroExt :107-119，                    -/
/-      LookupTree :16-18，HasPipelineReg :38-63）                            -/
/-  例化点（活代码判定）：                                                     -/
/-    ArrayMultiplier(num_thread, xLen) ← execution.scala:72（xLen=32）       -/
/-      与 execution.scala:188（hardThread 版，同 xLen=32）；                  -/
/-      其内部 ArrayMulDataModule(len+1)=ArrayMulDataModule(33)。              -/
/-  ALUOps（ALU.scala:40-47，5 位；DecodeUnit.scala:82-85 为 6 位版，          -/
/-    数值相同）：FN_MUL=20 FN_MULH=21 FN_MULHU=22 FN_MULHSU=23               -/
/-    FN_MACC=24 FN_NMSAC=25 FN_MADD=26 FN_NMSUB=27                          -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 电路层（mulColumns/mulAddOneColumn/mulAddRound/mulCompress/           -/
/-      mulDataModule）对 len 泛型，与 Chisel 逐行对应（len=8 用于穷举         -/
/-      测试）；算术/证明层（mulPlacedRow/mulPlacedSum 及全部定理）特化         -/
/-      len=33、宽度 66（实际例化）。                                        -/
/-  D2. 流水寄存器建模为恒等（组合语义不变）：columns_reg（:143）与           -/
/-      depth==4 的 RegEnable（:134-136）。关键事实：len=33 时 CSA 树         -/
/-      4 轮收敛（深度 0..3），base case 在 depth=4 入口命中，:133-136         -/
/-      的寄存器根本不会被例化（Python 位精确复本逐轮验证：len=8→2 轮，       -/
/-      16→3，32→4，33→4，64→5）。数据通路仅 columns_reg 一级寄存器。         -/
/-  D3. HasPipelineReg（mul_utils.scala:38-63）：建模自由流动                 -/
/-      （io.out.ready=true）语义——valids 逐级移位、RegEnable 使能=上级        -/
/-      valid 且数据保持；反压/停顿行为不建模（本文件目标是功能正确性）。      -/
/-  D4. SignExt/ZeroExt（mul_utils.scala:107-119）用 BitVec.signExtend/       -/
/-      zeroExtend；Chisel 版在 aLen ≥ len 时截断，本文件全部用法均为扩宽，   -/
/-      无语义差。                                                           -/
/-  D5. 算术层：每行的"列放置加权和"定义为组件和（pp_temp 零扩展 + 符号位     -/
/-      模式 + t 修正），三个保真引理（mulFidRow0/mulFidMid/mulFidLast，      -/
/-      纯 rw 手工证明，见 Q6/Q7）把组件和钉死到 :62-69 的 Cat 位模式。        -/
/-      末行 ~s 位于第                                                        -/
/-      2len=66 列、被 :70-74 的列界限丢弃，恰好实现 mod 2^66 截断            -/
/-      （mulPlacedRow_last 证明中该常量消失）。                              -/
/-  D6. mac_out（:201）的 67 位符号加减取低 32 位，建模为 32 位回绕加减       -/
/-      （低 32 位逐位等价）。                                               -/
/-  D7. addAll 收尾（:117-122）的 sum/carry 拼接建模为按位权直接求和：        -/
/-      sum = 各列 bit0 的位权和、carry = 各列 bit1 的位权和，与               -/
/-      Cat(_(0))/Cat(_(1))/0.U(k.W) 拼接语义相同（位的列位置不变）。         -/
/-  D8. ctrl 只建模 alu_fn(4,0)（:200 的 func 消费点）；mask 与 ctrl 其余     -/
/-      位共用同一两级寄存器结构，打拍对齐结论相同。                          -/
/-  D9. LookupTree（mul_utils.scala:16-18）在 Multiplier 中仅出现在           -/
/-      注释掉的死代码（:163-177），不建模。                                 -/
/-  D10. 空列（size 0）在 Chisel addOneColumn 中会落入 case n 并对            -/
/-      take4/drop4 无限递归（展开期挂起）——len=33/8 实例在所有轮次均无       -/
/-      空列（Python 复本逐轮验证），不会触发。Lean 模型给空列 case-1          -/
/-      同构语义（直接传递），仅为保证函数全域性。                            -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类，已确认】MULHSU 高低位选择缺失（Multiplier.scala:204-205）。     -/
/-      res 的高位条件为 func===FN_MULH | func===FN_MULHU，不含               -/
/-      FN_MULHSU——MULHSU 返回乘积【低】32 位而非高 32 位。操作数形成         -/
/-      正确（:178-179 对 MULHSU 恰当选了 sext(a)/zext(b)，:161-177 注释      -/
/-      掉的 mulInputFuncTable 也证明设计意图是 sext×zext），仅结果选择错。   -/
/-      活跃译码：DecodeUnit.scala:223（标量 MULHSU）与 :377-378              -/
/-      （VMULHSU_VV/VX）→ mul=Y → issue.scala:110 out_MUL →                 -/
/-      execution.scala:72。无下游补偿（主会话已查）。witness 定理             -/
/-      mul_mulhsu_witness：a=b=0xFFFFFFFF 时按源码返回 0x00000001（低 32      -/
/-      位），正确高 32 位为 0xFFFFFFFF。修复建议：高位条件加入              -/
/-      func===FN_MULHSU。                                                  -/
/-  Q2【I 类候选，潜在陷阱】流水线对齐依赖"CSA ≤ 4 轮"这一 len 相关事实：     -/
/-      len=33 时数据通路 1 级（columns_reg），func 取自 ctrlVec(1)（:200     -/
/-      打 1 拍）、cVec 打 1 拍、res 再打 1 拍成第 2 级（:206）、              -/
/-      ctrl/mask/valid 共 2 级——全部对齐（定理 mulPipe_two_cycles 钉死）。   -/
/-      但 len ≥ 64 时 CSA 需 5 轮、:133 的 depth==4 寄存器被例化（数据       -/
/-      通路变 2 级），func/cVec/out.valid 将比乘积早一拍，全链路差拍。       -/
/-      wrapper 正确性隐式依赖 len+1=33 的轮数，模块接口却声称泛型 len。      -/
/-      现状（Ventus 仅例化 len=32→33）非 bug，但属脆弱设计；                 -/
/-      regEnables(1) 在 len=33 下为死信号。                                 -/
/-  Q3【I 类，潜在/现配置不可达】Booth 末行取反修正丢失。算术层恒等式          -/
/-      （mulPlacedSum_eq）给出 placedSum = sext(a)*sext(b) - corr(x_last)    -/
/-      ·2^32（mod 2^66）：末行 Booth 窗 x=6（即 a 的 bit32=1 且 bit31=0）    -/
/-      时结果少 corr·2^32（取反 +1/+2 修正由"下一行 t"提供，末行没有下一     -/
/-      行）。len=33 下该 a 不可达——a 必为 32 位符号/零扩展（bit32=bit31      -/
/-      或 bit32=0，mul_sext33_corr0/mul_zext33_corr0 钉死），故实际           -/
/-      产品正确（Python 复本 3000 组随机可达输入全对）。但 len=8 穷举        -/
/-      （mul_dataModule8_exhaustive）证实：末行窗 ∈ {4,5,6} 的 a（占 3/8）   -/
/-      全部出错——模块仅在"len 为奇数且输入为 (len-1) 位扩展值"的隐性契约     -/
/-      下正确。上游 XiangShan 同代码（len=65 例化）同样依赖该契约。          -/
/-  Q4【观察】:163-177 注释掉的 LookupTree 版本与 :178-179 活代码语义         -/
/-      一致（mulInputFuncTable 四行 = 两个 Mux 的四种组合），无分歧。         -/
/-  Q5【观察】:184-185、:209-210 注释代码为死注释。                          -/
/-                                                                           -/
/-  ===== 公理清洁度记档（2026-08-30，agent-MULAX）=====                        -/
/-  Q6【已换成手工证明】mulFidRow0/mulFidMid/mulFidLast：bv_decide → 纯 rw      -/
/-      路线（apply BitVec.eq_of_toNat_eq 后逐条 rw 推 toNat——mulToNat_append   -/
/-      把 append 化为乘加、decide 出移位常量 toNat、按 msb 分情形 omega         -/
/-      闭合），公理收敛到 [propext, Quot.sound]。                              -/
/-  Q7【新坑，重要】simp only 把 toNat 类引理（toNat_add/toNat_shiftLeft/      -/
/-      toNat_ofNat 等）推进【含大常量（2^36 级移位、twoPow、大字面量）的         -/
/-      BitVec 项】时，kernel 复核报 "(kernel) deep recursion detected"         -/
/-      （maxRecDepth 调大无效；1#66<<<3 小移位不触发、1#66<<<36 触发；         -/
/-      同一目标改用 rw 逐条改写则完全正常）。对策：含 66 位大常量的 toNat       -/
/-      归一一律走 rw 链，不用 simp。                                         -/
/-  Q8【已全部换成手工证明】mulBaseRow0/mulBaseMid/mulBaseLast（并行会话，      -/
/-      8 路分情形 + 逐形式辅助引理 rw 推 toNat + b.msb 分情形 omega；           -/
/-      mulBaseLast 的 <<< 32 经 Nat.mul_mod_mul_right 化为 mod 2^34 同余）；    -/
/-      mulWindow32_eq6/mulCorr_window32_eq0/mul_sext33_corr0/mul_zext33_corr0   -/
/-      （并行会话，mulB2cases 4 路穷举）；mulTelescope（本会话，见 Q10）。      -/
/-      另顺手消掉 mulSextSext/mulA33_mac/mulMacOut_nmsac/mulMacOut_nmsub        -/
/-      的 bv_decide（前两者 toNat/分情形，后两者 if_neg + decide）。            -/
/-  Q9【新坑，重要】omega 目标含【变量 x 的 div/mod 链】与【% 2^66 取模】并存    -/
/-      时直接挂死（实测 2 窗规模也 4 分钟无响应）；generalize 2^66 又使         -/
/-      x % M 的商消元变成非线性（M·q 双变量）报 spurious counterexample。       -/
/-      对策：% 2^66 一律先用重写引理剥掉再进 omega——Nat.add_mod_right/          -/
/-      Nat.add_mod_mod/Nat.mod_add_mod（吸收单个 %）、Nat.add_mul_mod_self_     -/
/-      left（吸收 2^66·y 倍项）、Nat.mod_eq_of_lt（值域 < 2^66 时消模）；       -/
/-      omega 只面对"大常量作为纯加项/字面系数"的形式（mulBase* 已验证可行）。   -/
/-      另：同一证明里累积的含 % 2^66 的 have 假设会被后续每个 omega 拖进        -/
/-      原子集导致慢性爆炸——长链步进证明拆成独立顶层定理（mulTelePart*）。     -/
/-      还有：omega 不知道 2^i > 0（i 变量），需显式给 Nat.one_le_pow。         -/
/-  Q10【mulTelescope 换证路线】eq_of_toNat_eq 后：mulDigitVec_toNat 把 digit    -/
/-      写成 w 的闭式（8 路 decide）；mulWinNat* 把窗值桥接成 a.toNat 的         -/
/-      div/mod；mulTermNat* 用 mulTermMod 把每项剥成 lo·2^i + mid·2^i +         -/
/-      hi·(2^66 - 2^{i+1})（mod 2^66）；mulTelePart1..15 逐窗步进部分和         -/
/-      （不变式：前 k 窗和 = a.toNat % 2^{2k+1} + bit_{2k+1}·(2^66 - 2^{2k+1})， -/
/-      每步 hi·(2^66 - 2^e) 与下一窗 lo·2^{e+1} 合并出 2^66·bit 由              -/
/-      add_mul_mod_self_left 吸收）；末窗 msb 分情形 omega 收尾。全程公理       -/
/-      [propext, Classical.choice, Quot.sound]。                               -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- ========================================================================= -/
/- 1. 操作码常量与译码谓词（ALU.scala:40-47, 54-56）                           -/
/- ========================================================================= -/

def mulFN_MUL    : BitVec 5 := 20   -- ALU.scala:40
def mulFN_MULH   : BitVec 5 := 21   -- ALU.scala:41
def mulFN_MULHU  : BitVec 5 := 22   -- ALU.scala:42
def mulFN_MULHSU : BitVec 5 := 23   -- ALU.scala:43
def mulFN_MACC   : BitVec 5 := 24   -- ALU.scala:44
def mulFN_NMSAC  : BitVec 5 := 25   -- ALU.scala:45
def mulFN_MADD   : BitVec 5 := 26   -- ALU.scala:46
def mulFN_NMSUB  : BitVec 5 := 27   -- ALU.scala:47

/-- ALU.scala:56  isMAC = (cmd(4,2) == b110)，覆盖 func ∈ {24,25,26,27} -/
def mulIsMAC (func : BitVec 5) : Bool := func.extractLsb' 2 3 == 0b110#3

/-- ALU.scala:55  isMUL = (cmd(4,2) == b101)，覆盖 func ∈ {20,21,22,23} -/
def mulIsMUL (func : BitVec 5) : Bool := func.extractLsb' 2 3 == 0b101#3

/- ========================================================================= -/
/- 2. CSA 压缩器（mul_utils.scala:72-105）                                    -/
/- ========================================================================= -/

/-- CSA2_2 单位宽（mul_utils.scala:74-79）：sum = a^b，cout = a&b -/
def mulC22 (a b : Bool) : Bool × Bool := (xor a b, a && b)

/-- CSA3_2 单位宽（mul_utils.scala:85-92）：全加器 -/
def mulC32 (a b cin : Bool) : Bool × Bool :=
  let axb := xor a b
  (xor axb cin, (a && b) || (axb && cin))

/-- CSA5_3 单位宽（mul_utils.scala:97-100）：两个 CSA3_2 级联。
    输出 (out0, out1, out2)，out0 权 1，out1/out2 权 2 -/
def mulC53 (i0 i1 i2 i3 i4 : Bool) : Bool × Bool × Bool :=
  let (s1, c1) := mulC32 i0 i1 i2
  let (s2, c2) := mulC32 s1 i3 i4
  (s2, c1, c2)

/-- C22 位级真值表：out0 + 2·out1 = a + b -/
theorem mulC22_spec (a b : Bool) :
    (mulC22 a b).1.toNat + 2 * (mulC22 a b).2.toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide

/-- C32 位级真值表：out0 + 2·out1 = a + b + cin -/
theorem mulC32_spec (a b cin : Bool) :
    (mulC32 a b cin).1.toNat + 2 * (mulC32 a b cin).2.toNat
      = a.toNat + b.toNat + cin.toNat := by
  cases a <;> cases b <;> cases cin <;> decide

/-- C53 位级真值表：out0 + 2·(out1 + out2) = Σ 输入 -/
theorem mulC53_spec (i0 i1 i2 i3 i4 : Bool) :
    (mulC53 i0 i1 i2 i3 i4).1.toNat
      + 2 * ((mulC53 i0 i1 i2 i3 i4).2.1.toNat + (mulC53 i0 i1 i2 i3 i4).2.2.toNat)
      = i0.toNat + i1.toNat + i2.toNat + i3.toNat + i4.toNat := by
  cases i0 <;> cases i1 <;> cases i2 <;> cases i3 <;> cases i4 <;> decide

/- ========================================================================= -/
/- 3. Booth-2 部分积生成（Multiplier.scala:36-74）                            -/
/- ========================================================================= -/

/-- :37  b_sext := SignExt(b, len+1) -/
def mulB_sext {len : Nat} (b : BitVec len) : BitVec (len + 1) := b.signExtend (len + 1)

/-- :38  bx2 := b_sext << 1（赋回 len+1 位线网，截断；BitVec 移位天然截断） -/
def mulBx2 {len : Nat} (b : BitVec len) : BitVec (len + 1) := mulB_sext b <<< 1

/-- :39  neg_b := (~b_sext).asUInt -/
def mulNegB {len : Nat} (b : BitVec len) : BitVec (len + 1) := ~~~(mulB_sext b)

/-- :40  neg_bx2 := neg_b << 1（同截断） -/
def mulNegBx2 {len : Nat} (b : BitVec len) : BitVec (len + 1) := mulNegB b <<< 1

/-- :47-54  pp_temp := MuxLookup(x, 0)(1→b_sext, 2→b_sext, 3→bx2,
    4→neg_bx2, 5→neg_b, 6→neg_b)，默认 0 -/
def mulPpTemp {len : Nat} (x : BitVec 3) (b : BitVec len) : BitVec (len + 1) :=
  if x = 1#3 ∨ x = 2#3 then mulB_sext b
  else if x = 3#3 then mulBx2 b
  else if x = 4#3 then mulNegBx2 b
  else if x = 5#3 ∨ x = 6#3 then mulNegB b
  else 0#(len + 1)

/-- :56-60  t := MuxLookup(last_x, 0)(4→2, 5→1, 6→1)：上一行取反的 +1/+2 修正 -/
def mulT (lastX : BitVec 3) : BitVec 2 :=
  if lastX = 4#3 then 2#2
  else if lastX = 5#3 ∨ lastX = 6#3 then 1#2
  else 0#2

/-- :46  Booth 3 位窗：i=0 时 Cat(a(1,0), 0)；i+1==len 时 SignExt(a(i,i-1), 3)；
    否则 a(i+1, i-1) -/
def mulWindow {len : Nat} (a : BitVec len) (i : Nat) : BitVec 3 :=
  if i = 0 then (a.extractLsb' 0 2) ++ 0#1
  else if i + 1 = len then BitVec.signExtend 3 (a.extractLsb' (i - 1) 2)
  else a.extractLsb' (i - 1) 3

/-- :64  首行 pp = Cat(~s, s, s, pp_temp)（宽 len+4） -/
def mulPpRow0 {len : Nat} (ppt : BitVec (len + 1)) : BitVec (len + 4) :=
  BitVec.cast (by omega)
    (BitVec.ofBool (!ppt.msb) ++ BitVec.ofBool ppt.msb ++ BitVec.ofBool ppt.msb ++ ppt)

/-- :68  中间行 pp = Cat(1, ~s, pp_temp, t)（宽 len+5） -/
def mulPpRowMid {len : Nat} (ppt : BitVec (len + 1)) (t : BitVec 2) : BitVec (len + 5) :=
  BitVec.cast (by omega) (1#1 ++ BitVec.ofBool (!ppt.msb) ++ ppt ++ t)

/-- :66  末行 pp = Cat(~s, pp_temp, t)（宽 len+4）；~s 位于第 2len 列，被丢弃 -/
def mulPpRowLast {len : Nat} (ppt : BitVec (len + 1)) (t : BitVec 2) : BitVec (len + 4) :=
  BitVec.cast (by omega) (BitVec.ofBool (!ppt.msb) ++ ppt ++ t)

/- ========================================================================= -/
/- 4. 电路层（可执行模型）：列阵列 + CSA 压缩（Multiplier.scala:42-146）       -/
/- ========================================================================= -/

/-- BitVec 转 Bool 列表（LSB 在前） -/
def mulBvBits {w : Nat} (v : BitVec w) : List Bool := (List.range w).map v.getLsbD

/-- :45  Range(0, len, 2) -/
def mulRowIndices (len : Nat) : List Nat := List.range' 0 ((len + 1) / 2) 2

/-- :44-69  一行的（pp 位列表, weight） -/
def mulRowBits {len : Nat} (a b : BitVec len) (i : Nat) : List Bool × Nat :=
  let x := mulWindow a i
  let px := if i = 0 then 0#3 else mulWindow a (i - 2)   -- :61 last_x
  let ppt := mulPpTemp x b
  let t := mulT px                                        -- :56-60
  if i = 0 then (mulBvBits (mulPpRow0 ppt), 0)
  else if i = len - 1 ∨ i = len - 2 then (mulBvBits (mulPpRowLast ppt t), i - 2)
  else (mulBvBits (mulPpRowMid ppt t), i - 2)

/-- :42, :70-74  部分积按 weight 放入列阵列 -/
def mulColumns {len : Nat} (a b : BitVec len) : Array (List Bool) :=
  Id.run do
    let mut cols : Array (List Bool) := Array.replicate (2 * len) []
    for i in mulRowIndices len do
      let (bits, weight) := mulRowBits a b i
      for j in List.range (2 * len) do
        if weight ≤ j ∧ j < weight + bits.length then
          cols := cols.modify j (fun c => c ++ [bits.getD (j - weight) false])
    return cols

/-- :77-113  addOneColumn：单列压缩（C22/C32/C53 + 超 4 位递归二分）。
    返回 (sum, cout1, cout2)：sum 权 1，cout1/cout2 权 2 -/
def mulAddOneColumn (col cin : List Bool) : List Bool × List Bool × List Bool :=
  if h : col.length ≤ 4 then
    match col, cin with
    | [], cin => (cin, [], [])                            -- 见 D10（Chisel 不可达）
    | [a], cin => ([a] ++ cin, [], [])                    -- :82-83
    | [a, b], cin =>
        let (s, c) := mulC22 a b                          -- :84-88
        ([s] ++ cin, [], [c])
    | [a, b, c], cin =>
        let (s, co) := mulC32 a b c                       -- :89-93
        ([s] ++ cin, [], [co])
    | [a, b, c, d], cin =>
        let (o0, o1, o2) := mulC53 a b c d (cin.headD false)  -- :94-102
        ([o0] ++ cin.drop 1, [o1], [o2])
    | col, cin => (col ++ cin, [], [])                    -- 不可达分支（length ≤ 4 兜底）
  else
    let (s1, c11, c12) := mulAddOneColumn (col.take 4) (cin.take 1)   -- :103-110
    let (s2, c21, c22) := mulAddOneColumn (col.drop 4) (cin.drop 1)
    (s1 ++ s2, c11 ++ c21, c12 ++ c22)
termination_by col.length
decreasing_by
  · simp_wf; omega
  · simp_wf; omega

/-- :124-131  addAll 的一轮：逐列压缩，cout1 作下一列 cin，cout2 并入下一列 -/
def mulAddRound (cols : List (List Bool)) : List (List Bool) :=
  let step := fun (acc : List (List Bool) × List Bool × List Bool) (col : List Bool) =>
    match acc with
    | (built, cout1, cout2) =>
        let (s, c1, c2) := mulAddOneColumn col cout1
        (built ++ [s ++ cout2], c1, c2)
  (cols.foldl step ([], [], [])).1

/-- :116-141  addAll：迭代压缩至每列 ≤ 2 位（fuel 12 足够 len ≤ 512） -/
def mulCompress : Nat → List (List Bool) → List (List Bool)
  | 0, cols => cols
  | fuel + 1, cols =>
    if cols.all (fun c => decide (c.length ≤ 2)) then cols
    else mulCompress fuel (mulAddRound cols)

/-- Bool 列表按位权装配为 BitVec（bit i 权 2^i） -/
def mulBitsToBv {w : Nat} (bits : List Bool) : BitVec w :=
  (bits.zipIdx 0).foldl (fun acc p => if p.1 then acc ||| (1#w <<< p.2) else acc) 0#w

/-- :116-146  ArrayMulDataModule 组合语义：列阵列 → 压缩 → sum + carry（D7） -/
def mulDataModule {len : Nat} (a b : BitVec len) : BitVec (2 * len) :=
  let cols := (mulColumns a b).toList
  let fin := mulCompress 12 cols
  let sum := mulBitsToBv (fin.map (fun c => c.getD 0 false))
  let carry := mulBitsToBv (fin.map (fun c => c.getD 1 false))
  sum + carry

/- ========================================================================= -/
/- 5. 算术层：Booth 系数、组件行值与保真引理（len=33，宽度 66）                -/
/-                                                                           -/
/-  记 B := BitVec.signExtend 66 b。第 i 行的放置值分解为：                    -/
/-    数字项  d(x_i)·B·2^i  （d ∈ {0,±1,±2}，用移位/取负实现，无乘法）         -/
/-    修正项  -e(x_i)·2^i   （取反行的 +1/+2，由下一行 t 归还，见 Q3）         -/
/-    常数项  符号位编码常数（首行 2^36，中间行 3·2^(34+i)，末行 0——           -/
/-      末行 ~s 落第 66 列被丢弃，常量恰好≡0 mod 2^66）                       -/
/-    t 项    e(x_{i-2})·2^(i-2)                                             -/
/- ========================================================================= -/

/-- Booth 窗系数（数字向量）：x ↦ 0,1,1,2,-2,-1,-1,0 -/
def mulDigitVec (x : BitVec 3) : BitVec 66 :=
  if x = 1#3 ∨ x = 2#3 then 1#66
  else if x = 3#3 then 2#66
  else if x = 4#3 then -2#66
  else if x = 5#3 ∨ x = 6#3 then -1#66
  else 0#66

/-- d(x)·B 的移位实现：x=1,2→B；3→B<<<1；4→-(B<<<1)；5,6→-B；0,7→0 -/
def mulBoothB (x : BitVec 3) (B : BitVec 66) : BitVec 66 :=
  if x = 1#3 ∨ x = 2#3 then B
  else if x = 3#3 then B <<< 1
  else if x = 4#3 then -(B <<< 1)
  else if x = 5#3 ∨ x = 6#3 then -B
  else 0#66

/-- 取反修正 e(x) = (mulT x) 的 66 位零扩展（x=4→2；x=5,6→1；否则 0） -/
def mulCorrBV (x : BitVec 3) : BitVec 66 := BitVec.zeroExtend 66 (mulT x)

/-- 移位对加法的分配（经 twoPow 乘法） -/
theorem mulShiftAdd (X Y : BitVec 66) (i : Nat) :
    (X + Y) <<< i = X <<< i + Y <<< i := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
    BitVec.shiftLeft_eq_mul_twoPow, BitVec.add_mul]

/-- 移位对减法的分配 -/
theorem mulShiftSub (X Y : BitVec 66) (i : Nat) :
    (X - Y) <<< i = X <<< i - Y <<< i := by
  have h : (-Y) <<< i = -(Y <<< i) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, BitVec.neg_mul]
  rw [BitVec.sub_eq_add_neg, mulShiftAdd, h, ← BitVec.sub_eq_add_neg]

/-- 移位与乘法交换： (v <<< i) * B = (v * B) <<< i -/
theorem mulShiftComm (v B : BitVec 66) (i : Nat) :
    (v <<< i) * B = (v * B) <<< i := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
    BitVec.mul_assoc, BitVec.mul_comm (BitVec.twoPow 66 i) B, ← BitVec.mul_assoc]

/-- 8 路穷举（无 mathlib 的 fin_cases 替代） -/
theorem mulB3cases (x : BitVec 3) : x = 0#3 ∨ x = 1#3 ∨ x = 2#3 ∨ x = 3#3 ∨
    x = 4#3 ∨ x = 5#3 ∨ x = 6#3 ∨ x = 7#3 := by
  have hlt := x.isLt
  have e : x = BitVec.ofNat 3 x.toNat := by simp [BitVec.ofNat_toNat]
  have : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨
      x.toNat = 4 ∨ x.toNat = 5 ∨ x.toNat = 6 ∨ x.toNat = 7 := by omega
  rcases this with h|h|h|h|h|h|h|h <;> rw [e, h] <;> simp

/-- 4 路穷举（BitVec 2，同 mulB3cases；末行窗消 bv_decide 用） -/
theorem mulB2cases (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by
  have hlt := x.isLt
  have e : x = BitVec.ofNat 2 x.toNat := by simp [BitVec.ofNat_toNat]
  have : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
  rcases this with h|h|h|h <;> rw [e, h] <;> simp

/-- 数字向量乘 B 等于移位实现（核心代数事实；8 路分情形避开符号乘法） -/
theorem mulBoothA0 (x : BitVec 3) (B : BitVec 66) :
    mulDigitVec x * B = mulBoothB x B := by
  have h2 : BitVec.twoPow 66 1 = 2#66 := by decide
  rcases mulB3cases x with h | h | h | h | h | h | h | h <;> subst h
  · show (0#66 : BitVec 66) * B = 0#66
    exact BitVec.zero_mul
  · show (1#66 : BitVec 66) * B = B
    exact BitVec.one_mul B
  · show (1#66 : BitVec 66) * B = B
    exact BitVec.one_mul B
  · show (2#66 : BitVec 66) * B = B <<< 1
    rw [← BitVec.mul_twoPow_eq_shiftLeft, h2, BitVec.mul_comm]
  · show (-2#66 : BitVec 66) * B = -(B <<< 1)
    rw [show (-2#66 : BitVec 66) = -(2#66) from rfl, BitVec.neg_mul,
      ← BitVec.mul_twoPow_eq_shiftLeft, h2, BitVec.mul_comm B (2#66)]
  · show (-1#66 : BitVec 66) * B = -B
    rw [show (-1#66 : BitVec 66) = -(1#66) from rfl, BitVec.neg_mul, BitVec.one_mul]
  · show (-1#66 : BitVec 66) * B = -B
    rw [show (-1#66 : BitVec 66) = -(1#66) from rfl, BitVec.neg_mul, BitVec.one_mul]
  · show (0#66 : BitVec 66) * B = 0#66
    exact BitVec.zero_mul

/-- 数字向量移位后乘 B： (d(x) <<< i) * B = mulBoothB x B <<< i -/
theorem mulBoothA0Shift (x : BitVec 3) (B : BitVec 66) (i : Nat) :
    (mulDigitVec x <<< i) * B = mulBoothB x B <<< i := by
  rw [mulShiftComm, mulBoothA0]

/-- append 的 toNat 线性形式：核心库 `BitVec.toNat_append` 是 `<<< |||` 位运算
    形式，借 `Nat.shiftLeft_add_eq_or_of_lt` 化为乘加形式供 omega 使用
    （保真引理的手工证明用，替代 bv_decide） -/
theorem mulToNat_append {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- 保真引理（:64）：Cat(~s, s, s, pp_temp) 的位权值 = pp_temp + 符号位模式。
    手工证明：全程 rw（不用 simp——simp 推 toNat 进含大常量项触发 kernel
    deep recursion，见文件头 Q6 记档），toNat 归一后按 msb 分情形 omega 闭合 -/
theorem mulFidRow0 (ppt : BitVec 34) :
    BitVec.zeroExtend 66 (mulPpRow0 (len := 33) ppt)
      = BitVec.zeroExtend 66 ppt
        + (if ppt.msb then (1#66 <<< 34) + (1#66 <<< 35) else (1#66 <<< 36)) := by
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [mulPpRow0]
  rw [BitVec.toNat_setWidth, BitVec.toNat_cast, mulToNat_append, mulToNat_append,
    mulToNat_append, BitVec.toNat_ofBool, BitVec.toNat_ofBool,
    BitVec.toNat_add, apply_ite BitVec.toNat, BitVec.toNat_setWidth]
  cases hs : ppt.msb
  · rw [if_neg (by decide : ¬ (false = true)), ht36, Bool.not_false,
      Bool.toNat_true, Bool.toNat_false]
    omega
  · rw [if_pos rfl, BitVec.toNat_add, ht34, ht35, Bool.not_true,
      Bool.toNat_true, Bool.toNat_false]
    omega

/-- 保真引理（:68）：Cat(1, ~s, pp_temp, t) 的位权值（纯 rw 手工证明，同 mulFidRow0） -/
theorem mulFidMid (ppt : BitVec 34) (t : BitVec 2) :
    BitVec.zeroExtend 66 (mulPpRowMid (len := 33) ppt t)
      = (BitVec.zeroExtend 66 ppt) <<< 2
        + (if ppt.msb then 0#66 else (1#66 <<< 36)) + (1#66 <<< 37)
        + BitVec.zeroExtend 66 t := by
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  have ht37 : ((1#66 : BitVec 66) <<< 37).toNat = 137438953472 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [mulPpRowMid]
  rw [BitVec.toNat_setWidth, BitVec.toNat_cast, mulToNat_append, mulToNat_append,
    mulToNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofBool,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_setWidth, ht37]
  cases hs : ppt.msb
  · rw [if_neg (by decide : ¬ (false = true)), ht36, Bool.not_false,
      Bool.toNat_true]
    omega
  · rw [if_pos rfl, BitVec.toNat_zero, Bool.not_true, Bool.toNat_false]
    omega

/-- 保真引理（:66）：Cat(~s, pp_temp, t) 的位权值（纯 rw 手工证明，同 mulFidRow0） -/
theorem mulFidLast (ppt : BitVec 34) (t : BitVec 2) :
    BitVec.zeroExtend 66 (mulPpRowLast (len := 33) ppt t)
      = (BitVec.zeroExtend 66 ppt) <<< 2
        + (if ppt.msb then 0#66 else (1#66 <<< 36)) + BitVec.zeroExtend 66 t := by
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [mulPpRowLast]
  rw [BitVec.toNat_setWidth, BitVec.toNat_cast, mulToNat_append, mulToNat_append,
    BitVec.toNat_ofBool, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_setWidth]
  cases hs : ppt.msb
  · rw [if_neg (by decide : ¬ (false = true)), ht36, Bool.not_false,
      Bool.toNat_true]
    omega
  · rw [if_pos rfl, BitVec.toNat_zero, Bool.not_true, Bool.toNat_false]
    omega

/- ---- mulBase* 手工换证（消 bv_decide）的辅助引理：按 pp_temp 四种形式 ----
    路线（Q8）：8 路分情形（mulB3cases）+ 逐形式 show/rfl 归约 +
    apply BitVec.eq_of_toNat_eq 后逐条 rw 推 toNat（严禁 simp 推大常量项，Q7）
    + b.msb 分情形 + omega。msb 辅助事实走 msb_eq_true/false_iff_two_mul_* -/

/-- Row0 辅助：pp_temp = sext34 b（x ∈ {1,2}） -/
theorem mulRow0Sext (b : BitVec 33) :
    BitVec.zeroExtend 66 (BitVec.signExtend 34 b)
      + (if (BitVec.signExtend 34 b).msb then (1#66 <<< 34) + (1#66 <<< 35)
         else (1#66 <<< 36))
    = BitVec.signExtend 66 b - 0#66 + (1#66 <<< 36) := by
  have hb_lt := b.isLt
  have hmsb : (BitVec.signExtend 34 b).msb = b.msb := by
    rw [BitVec.msb_signExtend]; rfl
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, apply_ite BitVec.toNat,
    BitVec.toNat_add, ht34, ht35, ht36, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_zero, BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633, hmsb]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    omega

/-- Row0 辅助：pp_temp = sext34 b <<< 1（x = 3） -/
theorem mulRow0Bx2 (b : BitVec 33) :
    BitVec.zeroExtend 66 (BitVec.signExtend 34 b <<< 1)
      + (if (BitVec.signExtend 34 b <<< 1).msb then (1#66 <<< 34) + (1#66 <<< 35)
         else (1#66 <<< 36))
    = (BitVec.signExtend 66 b <<< 1) - 0#66 + (1#66 <<< 36) := by
  have hb_lt := b.isLt
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, apply_ite BitVec.toNat,
    BitVec.toNat_add, ht34, ht35, ht36, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_zero, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : (BitVec.signExtend 34 b <<< 1).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : (BitVec.signExtend 34 b <<< 1).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_pos rfl, if_pos rfl, if_pos rfl]
    omega

/-- Row0 辅助：pp_temp = (~~~sext34 b) <<< 1（x = 4） -/
theorem mulRow0NegBx2 (b : BitVec 33) :
    BitVec.zeroExtend 66 ((~~~(BitVec.signExtend 34 b)) <<< 1)
      + (if ((~~~(BitVec.signExtend 34 b)) <<< 1).msb then (1#66 <<< 34) + (1#66 <<< 35)
         else (1#66 <<< 36))
    = -((BitVec.signExtend 66 b) <<< 1) - 2#66 + (1#66 <<< 36) := by
  have hb_lt := b.isLt
  have ht2 : ((2#66 : BitVec 66)).toNat = 2 := by decide
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, apply_ite BitVec.toNat,
    BitVec.toNat_add, ht34, ht35, ht36, BitVec.toNat_add, BitVec.toNat_sub, ht2,
    BitVec.toNat_neg, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : ((~~~(BitVec.signExtend 34 b)) <<< 1).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_not, BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_pos rfl, if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : ((~~~(BitVec.signExtend 34 b)) <<< 1).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_not, BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_pos rfl, if_pos rfl]
    omega

/-- Row0 辅助：pp_temp = ~~~sext34 b（x ∈ {5,6}） -/
theorem mulRow0NegB (b : BitVec 33) :
    BitVec.zeroExtend 66 (~~~(BitVec.signExtend 34 b))
      + (if (~~~(BitVec.signExtend 34 b)).msb then (1#66 <<< 34) + (1#66 <<< 35)
         else (1#66 <<< 36))
    = -(BitVec.signExtend 66 b) - 1#66 + (1#66 <<< 36) := by
  have hb_lt := b.isLt
  have ht1 : ((1#66 : BitVec 66)).toNat = 1 := by decide
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht36 : ((1#66 : BitVec 66) <<< 36).toNat = 68719476736 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, apply_ite BitVec.toNat,
    BitVec.toNat_add, ht34, ht35, ht36, BitVec.toNat_add, BitVec.toNat_sub, ht1,
    BitVec.toNat_neg, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : (~~~(BitVec.signExtend 34 b)).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_not,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_pos rfl, if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : (~~~(BitVec.signExtend 34 b)).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_not,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_pos rfl, if_pos rfl]
    omega

/-- 首行基准恒等式（i=0）：pp_temp 零扩展 + 符号位模式 = d·B - e + 2^36。
    手工证明（消 bv_decide）：8 路分情形 + 四形式辅助引理 -/
theorem mulBaseRow0 (x : BitVec 3) (b : BitVec 33) :
    BitVec.zeroExtend 66 (mulPpTemp x b)
      + (if (mulPpTemp x b).msb then (1#66 <<< 34) + (1#66 <<< 35) else (1#66 <<< 36))
    = mulBoothB x (BitVec.signExtend 66 b) - mulCorrBV x + (1#66 <<< 36) := by
  rcases mulB3cases x with h|h|h|h|h|h|h|h <;> subst h
  · rw [show mulPpTemp 0#3 b = 0#34 from rfl,
      show mulBoothB 0#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 0#3 = (0#66) from rfl,
      show (0#34 : BitVec 34).msb = false from by decide,
      if_neg (by decide : ¬ (false = true))]
    decide
  · rw [show mulPpTemp 1#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 1#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 1#3 = (0#66) from rfl]
    exact mulRow0Sext b
  · rw [show mulPpTemp 2#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 2#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 2#3 = (0#66) from rfl]
    exact mulRow0Sext b
  · rw [show mulPpTemp 3#3 b = BitVec.signExtend 34 b <<< 1 from rfl,
      show mulBoothB 3#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b <<< 1 from rfl,
      show mulCorrBV 3#3 = (0#66) from rfl]
    exact mulRow0Bx2 b
  · rw [show mulPpTemp 4#3 b = (~~~(BitVec.signExtend 34 b)) <<< 1 from rfl,
      show mulBoothB 4#3 (BitVec.signExtend 66 b) = -((BitVec.signExtend 66 b) <<< 1)
        from rfl,
      show mulCorrBV 4#3 = (2#66) from rfl]
    exact mulRow0NegBx2 b
  · rw [show mulPpTemp 5#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 5#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 5#3 = (1#66) from rfl]
    exact mulRow0NegB b
  · rw [show mulPpTemp 6#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 6#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 6#3 = (1#66) from rfl]
    exact mulRow0NegB b
  · rw [show mulPpTemp 7#3 b = 0#34 from rfl,
      show mulBoothB 7#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 7#3 = (0#66) from rfl,
      show (0#34 : BitVec 34).msb = false from by decide,
      if_neg (by decide : ¬ (false = true))]
    decide

/-- Mid 辅助：pp_temp = sext34 b（x ∈ {1,2}） -/
theorem mulMidSext (b : BitVec 33) :
    BitVec.zeroExtend 66 (BitVec.signExtend 34 b)
      + (if (BitVec.signExtend 34 b).msb then 0#66 else (1#66 <<< 34)) + (1#66 <<< 35)
    = BitVec.signExtend 66 b - 0#66 + 3#66 * (1#66 <<< 34) := by
  rw [show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
  have hb_lt := b.isLt
  have hmsb : (BitVec.signExtend 34 b).msb = b.msb := by
    rw [BitVec.msb_signExtend]; rfl
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht3m : ((3#66 : BitVec 66) <<< 34).toNat = 51539607552 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_zero, ht34, ht35,
    BitVec.toNat_add, ht3m, BitVec.toNat_sub, BitVec.toNat_zero,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633, hmsb]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    omega

/-- Mid 辅助：pp_temp = sext34 b <<< 1（x = 3） -/
theorem mulMidBx2 (b : BitVec 33) :
    BitVec.zeroExtend 66 (BitVec.signExtend 34 b <<< 1)
      + (if (BitVec.signExtend 34 b <<< 1).msb then 0#66 else (1#66 <<< 34))
      + (1#66 <<< 35)
    = (BitVec.signExtend 66 b <<< 1) - 0#66 + 3#66 * (1#66 <<< 34) := by
  rw [show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
  have hb_lt := b.isLt
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht3m : ((3#66 : BitVec 66) <<< 34).toNat = 51539607552 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_zero, ht34, ht35,
    BitVec.toNat_add, ht3m, BitVec.toNat_sub, BitVec.toNat_zero,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : (BitVec.signExtend 34 b <<< 1).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : (BitVec.signExtend 34 b <<< 1).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_pos rfl, if_pos rfl, if_pos rfl]
    omega

/-- Mid 辅助：pp_temp = (~~~sext34 b) <<< 1（x = 4） -/
theorem mulMidNegBx2 (b : BitVec 33) :
    BitVec.zeroExtend 66 ((~~~(BitVec.signExtend 34 b)) <<< 1)
      + (if ((~~~(BitVec.signExtend 34 b)) <<< 1).msb then 0#66 else (1#66 <<< 34))
      + (1#66 <<< 35)
    = -((BitVec.signExtend 66 b) <<< 1) - 2#66 + 3#66 * (1#66 <<< 34) := by
  rw [show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
  have hb_lt := b.isLt
  have ht2 : ((2#66 : BitVec 66)).toNat = 2 := by decide
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht3m : ((3#66 : BitVec 66) <<< 34).toNat = 51539607552 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_zero, ht34, ht35,
    BitVec.toNat_add, ht3m, BitVec.toNat_sub, ht2,
    BitVec.toNat_neg, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : ((~~~(BitVec.signExtend 34 b)) <<< 1).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_not, BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_pos rfl, if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : ((~~~(BitVec.signExtend 34 b)) <<< 1).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        BitVec.toNat_not, BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_pos rfl, if_pos rfl]
    omega

/-- Mid 辅助：pp_temp = ~~~sext34 b（x ∈ {5,6}） -/
theorem mulMidNegB (b : BitVec 33) :
    BitVec.zeroExtend 66 (~~~(BitVec.signExtend 34 b))
      + (if (~~~(BitVec.signExtend 34 b)).msb then 0#66 else (1#66 <<< 34))
      + (1#66 <<< 35)
    = -(BitVec.signExtend 66 b) - 1#66 + 3#66 * (1#66 <<< 34) := by
  rw [show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
  have hb_lt := b.isLt
  have ht1 : ((1#66 : BitVec 66)).toNat = 1 := by decide
  have ht34 : ((1#66 : BitVec 66) <<< 34).toNat = 17179869184 := by decide
  have ht35 : ((1#66 : BitVec 66) <<< 35).toNat = 34359738368 := by decide
  have ht3m : ((3#66 : BitVec 66) <<< 34).toNat = 51539607552 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth,
    apply_ite BitVec.toNat, BitVec.toNat_zero, ht34, ht35,
    BitVec.toNat_add, ht3m, BitVec.toNat_sub, ht1,
    BitVec.toNat_neg, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  cases hb : b.msb
  · have hbn : 2 * b.toNat < 2^33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hb
    have hm : (~~~(BitVec.signExtend 34 b)).msb = true := by
      rw [BitVec.msb_eq_true_iff_two_mul_ge, BitVec.toNat_not,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb,
        if_neg (by decide : ¬ (false = true))]
      omega
    rw [hm, if_pos rfl, if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · have hbn : 2 * b.toNat ≥ 2^33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    have hm : (~~~(BitVec.signExtend 34 b)).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_not,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, hb, if_pos rfl]
      omega
    rw [hm, if_neg (by decide : ¬ (false = true)), if_pos rfl, if_pos rfl]
    omega

/-- 中间行基准恒等式（相对行基 i）：pp_temp 零扩展 + 符号位模式
    = d·B - e + 3·2^34（符号位 s 恰好消去）。手工证明（消 bv_decide） -/
theorem mulBaseMid (x : BitVec 3) (b : BitVec 33) :
    BitVec.zeroExtend 66 (mulPpTemp x b)
      + (if (mulPpTemp x b).msb then 0#66 else (1#66 <<< 34)) + (1#66 <<< 35)
    = mulBoothB x (BitVec.signExtend 66 b) - mulCorrBV x + 3#66 * (1#66 <<< 34) := by
  rcases mulB3cases x with h|h|h|h|h|h|h|h <;> subst h
  · rw [show mulPpTemp 0#3 b = 0#34 from rfl,
      show mulBoothB 0#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 0#3 = (0#66) from rfl,
      show (0#34 : BitVec 34).msb = false from by decide,
      if_neg (by decide : ¬ (false = true)),
      show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
    decide
  · rw [show mulPpTemp 1#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 1#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 1#3 = (0#66) from rfl]
    exact mulMidSext b
  · rw [show mulPpTemp 2#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 2#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 2#3 = (0#66) from rfl]
    exact mulMidSext b
  · rw [show mulPpTemp 3#3 b = BitVec.signExtend 34 b <<< 1 from rfl,
      show mulBoothB 3#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b <<< 1 from rfl,
      show mulCorrBV 3#3 = (0#66) from rfl]
    exact mulMidBx2 b
  · rw [show mulPpTemp 4#3 b = (~~~(BitVec.signExtend 34 b)) <<< 1 from rfl,
      show mulBoothB 4#3 (BitVec.signExtend 66 b) = -((BitVec.signExtend 66 b) <<< 1)
        from rfl,
      show mulCorrBV 4#3 = (2#66) from rfl]
    exact mulMidNegBx2 b
  · rw [show mulPpTemp 5#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 5#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 5#3 = (1#66) from rfl]
    exact mulMidNegB b
  · rw [show mulPpTemp 6#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 6#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 6#3 = (1#66) from rfl]
    exact mulMidNegB b
  · rw [show mulPpTemp 7#3 b = 0#34 from rfl,
      show mulBoothB 7#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 7#3 = (0#66) from rfl,
      show (0#34 : BitVec 34).msb = false from by decide,
      if_neg (by decide : ¬ (false = true)),
      show (3#66 : BitVec 66) * (1#66 <<< 34) = 3#66 <<< 34 from by decide]
    decide

/-- Last 辅助：pp_temp = sext34 b（x ∈ {1,2}） -/
theorem mulLastSext (b : BitVec 33) :
    (BitVec.zeroExtend 66 (BitVec.signExtend 34 b)) <<< 32
    = (BitVec.signExtend 66 b - 0#66) <<< 32 := by
  have hb_lt := b.isLt
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_zero,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  rw [show (2:Nat)^66 = 2^34 * 2^32 from by decide, Nat.mul_mod_mul_right,
    Nat.mul_mod_mul_right]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
    omega
  · rw [if_pos rfl, if_pos rfl]
    omega

/-- Last 辅助：pp_temp = sext34 b <<< 1（x = 3） -/
theorem mulLastBx2 (b : BitVec 33) :
    (BitVec.zeroExtend 66 (BitVec.signExtend 34 b <<< 1)) <<< 32
    = ((BitVec.signExtend 66 b <<< 1) - 0#66) <<< 32 := by
  have hb_lt := b.isLt
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_zero,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  rw [show (2:Nat)^66 = 2^34 * 2^32 from by decide, Nat.mul_mod_mul_right,
    Nat.mul_mod_mul_right]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
    omega
  · rw [if_pos rfl, if_pos rfl]
    omega

/-- Last 辅助：pp_temp = (~~~sext34 b) <<< 1（x = 4） -/
theorem mulLastNegBx2 (b : BitVec 33) :
    (BitVec.zeroExtend 66 ((~~~(BitVec.signExtend 34 b)) <<< 1)) <<< 32
    = (-((BitVec.signExtend 66 b) <<< 1) - 2#66) <<< 32 := by
  have hb_lt := b.isLt
  have ht2 : ((2#66 : BitVec 66)).toNat = 2 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_sub, ht2,
    BitVec.toNat_neg, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  rw [show (2:Nat)^66 = 2^34 * 2^32 from by decide, Nat.mul_mod_mul_right,
    Nat.mul_mod_mul_right]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
    omega
  · rw [if_pos rfl, if_pos rfl]
    omega

/-- Last 辅助：pp_temp = ~~~sext34 b（x ∈ {5,6}） -/
theorem mulLastNegB (b : BitVec 33) :
    (BitVec.zeroExtend 66 (~~~(BitVec.signExtend 34 b))) <<< 32
    = (-(BitVec.signExtend 66 b) - 1#66) <<< 32 := by
  have hb_lt := b.isLt
  have ht1 : ((1#66 : BitVec 66)).toNat = 1 := by decide
  have h3433 : (2:Nat) ^ 34 - 2 ^ 33 = 8589934592 := by decide
  have h6633 : (2:Nat) ^ 66 - 2 ^ 33 = 73786976286248271872 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_sub, ht1,
    BitVec.toNat_neg, BitVec.toNat_not,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h3433,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, h6633]
  rw [show (2:Nat)^66 = 2^34 * 2^32 from by decide, Nat.mul_mod_mul_right,
    Nat.mul_mod_mul_right]
  cases hb : b.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
    omega
  · rw [if_pos rfl, if_pos rfl]
    omega

/-- 末行基准恒等式（<<< 32）：~s 丢弃恰好实现 mod 2^66。手工证明（消
    bv_decide）：8 路分情形 + 四形式辅助引理（<<< 32 经 Nat.mul_mod_mul_right
    化为 mod 2^34 同余） -/
theorem mulBaseLast (x : BitVec 3) (b : BitVec 33) :
    (BitVec.zeroExtend 66 (mulPpTemp x b)) <<< 32
    = (mulBoothB x (BitVec.signExtend 66 b) - mulCorrBV x) <<< 32 := by
  rcases mulB3cases x with h|h|h|h|h|h|h|h <;> subst h
  · rw [show mulPpTemp 0#3 b = 0#34 from rfl,
      show mulBoothB 0#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 0#3 = (0#66) from rfl]
    decide
  · rw [show mulPpTemp 1#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 1#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 1#3 = (0#66) from rfl]
    exact mulLastSext b
  · rw [show mulPpTemp 2#3 b = BitVec.signExtend 34 b from rfl,
      show mulBoothB 2#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b from rfl,
      show mulCorrBV 2#3 = (0#66) from rfl]
    exact mulLastSext b
  · rw [show mulPpTemp 3#3 b = BitVec.signExtend 34 b <<< 1 from rfl,
      show mulBoothB 3#3 (BitVec.signExtend 66 b) = BitVec.signExtend 66 b <<< 1 from rfl,
      show mulCorrBV 3#3 = (0#66) from rfl]
    exact mulLastBx2 b
  · rw [show mulPpTemp 4#3 b = (~~~(BitVec.signExtend 34 b)) <<< 1 from rfl,
      show mulBoothB 4#3 (BitVec.signExtend 66 b) = -((BitVec.signExtend 66 b) <<< 1)
        from rfl,
      show mulCorrBV 4#3 = (2#66) from rfl]
    exact mulLastNegBx2 b
  · rw [show mulPpTemp 5#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 5#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 5#3 = (1#66) from rfl]
    exact mulLastNegB b
  · rw [show mulPpTemp 6#3 b = ~~~(BitVec.signExtend 34 b) from rfl,
      show mulBoothB 6#3 (BitVec.signExtend 66 b) = -(BitVec.signExtend 66 b) from rfl,
      show mulCorrBV 6#3 = (1#66) from rfl]
    exact mulLastNegB b
  · rw [show mulPpTemp 7#3 b = 0#34 from rfl,
      show mulBoothB 7#3 (BitVec.signExtend 66 b) = 0#66 from rfl,
      show mulCorrBV 7#3 = (0#66) from rfl]
    decide


/-- 单行放置值（算术层，len=33；与电路层 mulRowBits 同行同位） -/
def mulPlacedRow (a b : BitVec 33) (i : Nat) : BitVec 66 :=
  let x := mulWindow a i
  let ppt := mulPpTemp x b
  let t := mulT (mulWindow a (i - 2))
  if i = 0 then BitVec.zeroExtend 66 (mulPpRow0 ppt)
  else if i = 32 ∨ i = 31 then (BitVec.zeroExtend 66 (mulPpRowLast ppt t)) <<< (i - 2)
  else (BitVec.zeroExtend 66 (mulPpRowMid ppt t)) <<< (i - 2)

/-- 移位 0 化简 -/
theorem mulShiftZero (v : BitVec 66) : v <<< 0 = v := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have h : BitVec.twoPow 66 0 = 1#66 := by decide
  rw [h, BitVec.mul_one]

/-- 首行值引理 -/
theorem mulPlacedRow_zero (a b : BitVec 33) :
    mulPlacedRow a b 0 =
      (mulDigitVec (mulWindow a 0) <<< 0) * BitVec.signExtend 66 b
        - (mulCorrBV (mulWindow a 0) <<< 0) + (1#66 <<< 36) := by
  show BitVec.zeroExtend 66 (mulPpRow0 (mulPpTemp (mulWindow a 0) b)) = _
  rw [mulFidRow0, mulShiftZero (mulDigitVec (mulWindow a 0)),
    mulShiftZero (mulCorrBV (mulWindow a 0)), mulBoothA0]
  exact mulBaseRow0 (mulWindow a 0) b

/-- 中间行值引理 -/
theorem mulPlacedRow_mid (a b : BitVec 33) (i : Nat)
    (h2 : 2 ≤ i) (h31 : i ≠ 31) (h32 : i ≠ 32) :
    mulPlacedRow a b i =
      (mulDigitVec (mulWindow a i) <<< i) * BitVec.signExtend 66 b
        - (mulCorrBV (mulWindow a i) <<< i) + ((3#66 <<< 34) <<< i)
        + (mulCorrBV (mulWindow a (i - 2)) <<< (i - 2)) := by
  have h0 : i ≠ 0 := by omega
  have hnot : ¬(i = 32 ∨ i = 31) := not_or.mpr ⟨h32, h31⟩
  have hsh2 : 2 + (i - 2) = i := by omega
  have hsh36 : 36 + (i - 2) = i + 34 := by omega
  have hsh37 : 37 + (i - 2) = i + 35 := by omega
  simp only [mulPlacedRow]
  rw [if_neg h0, if_neg hnot]
  rw [mulFidMid, mulShiftAdd, mulShiftAdd, mulShiftAdd]
  rw [← BitVec.shiftLeft_add, hsh2]
  rw [apply_ite (fun v : BitVec 66 => v <<< (i - 2))]
  have hz : (0#66 : BitVec 66) <<< (i - 2) = 0#66 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.zero_mul]
  rw [hz, ← BitVec.shiftLeft_add, hsh36, ← BitVec.shiftLeft_add, hsh37]
  have hbase := congrArg (fun v : BitVec 66 => v <<< i) (mulBaseMid (mulWindow a i) b)
  rw [mulShiftAdd, mulShiftAdd] at hbase
  rw [apply_ite (fun v : BitVec 66 => v <<< i)] at hbase
  have hz2 : (0#66 : BitVec 66) <<< i = 0#66 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.zero_mul]
  rw [hz2] at hbase
  rw [mulShiftAdd, mulShiftSub] at hbase
  rw [← BitVec.shiftLeft_add, ← BitVec.shiftLeft_add] at hbase
  rw [← mulBoothA0Shift] at hbase
  have h3 : 3#66 * (1#66 <<< 34) = (3#66 <<< 34) := by decide
  rw [h3] at hbase
  have hc1 : 34 + i = i + 34 := by omega
  have hc2 : 35 + i = i + 35 := by omega
  rw [hc1, hc2] at hbase
  show _ = (mulDigitVec (mulWindow a i) <<< i) * BitVec.signExtend 66 b
    - (mulCorrBV (mulWindow a i) <<< i) + ((3#66 <<< 34) <<< i)
    + (BitVec.zeroExtend 66 (mulT (mulWindow a (i - 2)))) <<< (i - 2)
  rw [← hbase]

/-- 末行值引理 -/
theorem mulPlacedRow_last (a b : BitVec 33) :
    mulPlacedRow a b 32 =
      (mulDigitVec (mulWindow a 32) <<< 32) * BitVec.signExtend 66 b
        - (mulCorrBV (mulWindow a 32) <<< 32)
        + (mulCorrBV (mulWindow a 30) <<< 30) := by
  show (BitVec.zeroExtend 66 (mulPpRowLast (mulPpTemp (mulWindow a 32) b)
      (mulT (mulWindow a (32 - 2))))) <<< (32 - 2) = _
  rw [mulFidLast, mulShiftAdd, mulShiftAdd]
  rw [← BitVec.shiftLeft_add]
  have h32 : 2 + (32 - 2) = 32 := by decide
  rw [h32]
  rw [apply_ite (fun v : BitVec 66 => v <<< (32 - 2))]
  have hz : (0#66 : BitVec 66) <<< (32 - 2) = 0#66 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.zero_mul]
  rw [hz]
  rw [← BitVec.shiftLeft_add]
  have h66 : (1#66 : BitVec 66) <<< (36 + (32 - 2)) = 0#66 := by decide
  rw [h66]
  rw [show (if (mulPpTemp (mulWindow a 32) b).msb then (0#66 : BitVec 66) else 0#66)
      = 0#66 from by split <;> rfl]
  rw [BitVec.add_zero]
  rw [mulBaseLast, mulShiftSub, ← mulBoothA0Shift]
  rfl

/-- 数字和（望远镜形式，17 项左结合） -/
def mulDigitSumVec (a : BitVec 33) : BitVec 66 :=
  (mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2) +
  (mulDigitVec (mulWindow a 4) <<< 4) + (mulDigitVec (mulWindow a 6) <<< 6) +
  (mulDigitVec (mulWindow a 8) <<< 8) + (mulDigitVec (mulWindow a 10) <<< 10) +
  (mulDigitVec (mulWindow a 12) <<< 12) + (mulDigitVec (mulWindow a 14) <<< 14) +
  (mulDigitVec (mulWindow a 16) <<< 16) + (mulDigitVec (mulWindow a 18) <<< 18) +
  (mulDigitVec (mulWindow a 20) <<< 20) + (mulDigitVec (mulWindow a 22) <<< 22) +
  (mulDigitVec (mulWindow a 24) <<< 24) + (mulDigitVec (mulWindow a 26) <<< 26) +
  (mulDigitVec (mulWindow a 28) <<< 28) + (mulDigitVec (mulWindow a 30) <<< 30) +
  (mulDigitVec (mulWindow a 32) <<< 32)

/-- 数字向量的 toNat 闭式：d(w) = w%2 + (w/2)%2 - 2·(w/4)（mod 2^66）。
    8 路穷举 + decide（mulTelescope 手工证明用，见文件头 Q9/Q10） -/
theorem mulDigitVec_toNat (w : BitVec 3) :
    (mulDigitVec w).toNat
      = (w.toNat % 2 + (w.toNat / 2) % 2 + 2 ^ 66 - 2 * (w.toNat / 4)) % 2 ^ 66 := by
  rcases mulB3cases w with h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- 单窗项的模剥离（mulTelescope 手工证明用）：lo/mid/hi ∈ {0,1}、i ≤ 32 时
    ((lo + mid + 2^66 - 2·hi) % 2^66 · 2^i) % 2^66
      = (lo·2^i + mid·2^i + hi·(2^66 - 2^(i+1))) % 2^66。
    纯 rw（add_mod_right/mod_eq_of_lt/add_mul_mod_self_left）+ 线性 omega——
    全程不让 omega 直接面对 % 2^66（见文件头 Q9）；lo=mid=hi=1 角点值恰为
    2^66 需单列（此时 digit = 0） -/
theorem mulTermMod (lo mid hi : Nat) (hlo : lo ≤ 1) (hmid : mid ≤ 1) (hhi : hi ≤ 1)
    (i : Nat) (hi32 : i ≤ 32) :
    ((lo + mid + 2 ^ 66 - 2 * hi) % 2 ^ 66 * 2 ^ i) % 2 ^ 66
      = (lo * 2 ^ i + mid * 2 ^ i + hi * (2 ^ 66 - 2 ^ (i + 1))) % 2 ^ 66 := by
  have hib : 2 ^ i ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hi32
  have hpi : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
  have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases h : hi = 0
  · subst h
    rw [Nat.mul_zero, Nat.sub_zero, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : lo + mid < 2 ^ 66), Nat.add_mul,
      Nat.zero_mul, Nat.add_zero]
  · have h1 : hi = 1 := by omega
    subst h1
    rw [Nat.mul_one, Nat.one_mul]
    by_cases hlm : lo + mid = 2
    · have hlo1 : lo = 1 := by omega
      have hmid1 : mid = 1 := by omega
      subst hlo1; subst hmid1
      rw [show 1 + 1 + 2 ^ 66 - 2 = 2 ^ 66 from by decide, Nat.mod_self, Nat.zero_mul,
        Nat.zero_mod,
        show 1 * 2 ^ i + 1 * 2 ^ i + (2 ^ 66 - 2 ^ (i + 1)) = 2 ^ 66 from by omega,
        Nat.mod_self]
    · have hlm1 : lo + mid ≤ 1 := by omega
      rw [Nat.mod_eq_of_lt (by omega : lo + mid + 2 ^ 66 - 2 < 2 ^ 66)]
      have hkey : (lo + mid + 2 ^ 66 - 2) * 2 ^ i
          = lo * 2 ^ i + mid * 2 ^ i + (2 ^ 66 - 2 ^ (i + 1)) + 2 ^ 66 * (2 ^ i - 1) := by
        rw [show lo + mid + 2 ^ 66 - 2 = (lo + mid) + (2 ^ 66 - 2) from by omega,
          Nat.add_mul, Nat.add_mul, Nat.sub_mul, Nat.mul_sub_one, hpow]
        omega
      rw [hkey, Nat.add_mul_mod_self_left]

/-- 窗 0 的 toNat 桥接（mulTelescope 手工证明用） -/
theorem mulWinNat0 (a : BitVec 33) : (mulWindow a 0).toNat = 2 * (a.toNat % 4) := by
  show ((a.extractLsb' 0 2) ++ (0#1)).toNat = 2 * (a.toNat % 4)
  rw [mulToNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  omega
/-- 窗 2 的 toNat 桥接 -/
theorem mulWinNat2 (a : BitVec 33) :
    (mulWindow a 2).toNat = a.toNat / 2 ^ 1 % 8 := by
  show (a.extractLsb' 1 3).toNat = a.toNat / 2 ^ 1 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 4 的 toNat 桥接 -/
theorem mulWinNat4 (a : BitVec 33) :
    (mulWindow a 4).toNat = a.toNat / 2 ^ 3 % 8 := by
  show (a.extractLsb' 3 3).toNat = a.toNat / 2 ^ 3 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 6 的 toNat 桥接 -/
theorem mulWinNat6 (a : BitVec 33) :
    (mulWindow a 6).toNat = a.toNat / 2 ^ 5 % 8 := by
  show (a.extractLsb' 5 3).toNat = a.toNat / 2 ^ 5 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 8 的 toNat 桥接 -/
theorem mulWinNat8 (a : BitVec 33) :
    (mulWindow a 8).toNat = a.toNat / 2 ^ 7 % 8 := by
  show (a.extractLsb' 7 3).toNat = a.toNat / 2 ^ 7 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 10 的 toNat 桥接 -/
theorem mulWinNat10 (a : BitVec 33) :
    (mulWindow a 10).toNat = a.toNat / 2 ^ 9 % 8 := by
  show (a.extractLsb' 9 3).toNat = a.toNat / 2 ^ 9 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 12 的 toNat 桥接 -/
theorem mulWinNat12 (a : BitVec 33) :
    (mulWindow a 12).toNat = a.toNat / 2 ^ 11 % 8 := by
  show (a.extractLsb' 11 3).toNat = a.toNat / 2 ^ 11 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 14 的 toNat 桥接 -/
theorem mulWinNat14 (a : BitVec 33) :
    (mulWindow a 14).toNat = a.toNat / 2 ^ 13 % 8 := by
  show (a.extractLsb' 13 3).toNat = a.toNat / 2 ^ 13 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 16 的 toNat 桥接 -/
theorem mulWinNat16 (a : BitVec 33) :
    (mulWindow a 16).toNat = a.toNat / 2 ^ 15 % 8 := by
  show (a.extractLsb' 15 3).toNat = a.toNat / 2 ^ 15 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 18 的 toNat 桥接 -/
theorem mulWinNat18 (a : BitVec 33) :
    (mulWindow a 18).toNat = a.toNat / 2 ^ 17 % 8 := by
  show (a.extractLsb' 17 3).toNat = a.toNat / 2 ^ 17 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 20 的 toNat 桥接 -/
theorem mulWinNat20 (a : BitVec 33) :
    (mulWindow a 20).toNat = a.toNat / 2 ^ 19 % 8 := by
  show (a.extractLsb' 19 3).toNat = a.toNat / 2 ^ 19 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 22 的 toNat 桥接 -/
theorem mulWinNat22 (a : BitVec 33) :
    (mulWindow a 22).toNat = a.toNat / 2 ^ 21 % 8 := by
  show (a.extractLsb' 21 3).toNat = a.toNat / 2 ^ 21 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 24 的 toNat 桥接 -/
theorem mulWinNat24 (a : BitVec 33) :
    (mulWindow a 24).toNat = a.toNat / 2 ^ 23 % 8 := by
  show (a.extractLsb' 23 3).toNat = a.toNat / 2 ^ 23 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 26 的 toNat 桥接 -/
theorem mulWinNat26 (a : BitVec 33) :
    (mulWindow a 26).toNat = a.toNat / 2 ^ 25 % 8 := by
  show (a.extractLsb' 25 3).toNat = a.toNat / 2 ^ 25 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 28 的 toNat 桥接 -/
theorem mulWinNat28 (a : BitVec 33) :
    (mulWindow a 28).toNat = a.toNat / 2 ^ 27 % 8 := by
  show (a.extractLsb' 27 3).toNat = a.toNat / 2 ^ 27 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 30 的 toNat 桥接 -/
theorem mulWinNat30 (a : BitVec 33) :
    (mulWindow a 30).toNat = a.toNat / 2 ^ 29 % 8 := by
  show (a.extractLsb' 29 3).toNat = a.toNat / 2 ^ 29 % 8
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- 窗 32 的 toNat 桥接（符号扩展窗） -/
theorem mulWinNat32 (a : BitVec 33) :
    (mulWindow a 32).toNat
      = a.toNat / 2 ^ 31 % 4 + (if a.getLsbD 32 then 4 else 0) := by
  have hu : mulWindow a 32 = BitVec.signExtend 3 (a.extractLsb' 31 2) := rfl
  rw [hu, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hmsb : (a.extractLsb' 31 2).msb = a.getLsbD 32 := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb']; rfl
  rw [hmsb]
  by_cases hb : a.getLsbD 32 = true
  · rw [if_pos hb]; omega
  · rw [if_neg hb]; omega

/-- 窗 0 项的 toNat（mulTelescope 手工证明用；模剥离走 mulTermMod） -/
theorem mulTermNat0 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 0) <<< 0).toNat
      = (0 * 2 ^ 0 + (a.toNat % 2) * 2 ^ 0
        + (a.toNat / 2 % 2) * (2 ^ 66 - 2 ^ 1)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 0),
    mulWinNat0]
  have c1 : (2 * (a.toNat % 4)) % 2 = 0 := by omega
  have c2 : (2 * (a.toNat % 4)) / 2 % 2 = a.toNat % 2 := by omega
  have c3 : (2 * (a.toNat % 4)) / 4 = a.toNat / 2 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 0 (by omega)
/-- 窗 2 项的 toNat -/
theorem mulTermNat2 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 2) <<< 2).toNat
      = ((a.toNat / 2 ^ 1 % 2) * 2 ^ 2 + (a.toNat / 2 ^ 2 % 2) * 2 ^ 2 + (a.toNat / 2 ^ 3 % 2) * (2 ^ 66 - 2 ^ 3)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 2),
    mulWinNat2]
  have c1 : (a.toNat / 2 ^ 1 % 8) % 2 = a.toNat / 2 ^ 1 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 1 % 8) / 2 % 2 = a.toNat / 2 ^ 2 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 1 % 8) / 4 = a.toNat / 2 ^ 3 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 2 (by omega)
/-- 窗 4 项的 toNat -/
theorem mulTermNat4 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 4) <<< 4).toNat
      = ((a.toNat / 2 ^ 3 % 2) * 2 ^ 4 + (a.toNat / 2 ^ 4 % 2) * 2 ^ 4 + (a.toNat / 2 ^ 5 % 2) * (2 ^ 66 - 2 ^ 5)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 4),
    mulWinNat4]
  have c1 : (a.toNat / 2 ^ 3 % 8) % 2 = a.toNat / 2 ^ 3 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 3 % 8) / 2 % 2 = a.toNat / 2 ^ 4 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 3 % 8) / 4 = a.toNat / 2 ^ 5 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 4 (by omega)
/-- 窗 6 项的 toNat -/
theorem mulTermNat6 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 6) <<< 6).toNat
      = ((a.toNat / 2 ^ 5 % 2) * 2 ^ 6 + (a.toNat / 2 ^ 6 % 2) * 2 ^ 6 + (a.toNat / 2 ^ 7 % 2) * (2 ^ 66 - 2 ^ 7)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 6),
    mulWinNat6]
  have c1 : (a.toNat / 2 ^ 5 % 8) % 2 = a.toNat / 2 ^ 5 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 5 % 8) / 2 % 2 = a.toNat / 2 ^ 6 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 5 % 8) / 4 = a.toNat / 2 ^ 7 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 6 (by omega)
/-- 窗 8 项的 toNat -/
theorem mulTermNat8 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 8) <<< 8).toNat
      = ((a.toNat / 2 ^ 7 % 2) * 2 ^ 8 + (a.toNat / 2 ^ 8 % 2) * 2 ^ 8 + (a.toNat / 2 ^ 9 % 2) * (2 ^ 66 - 2 ^ 9)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 8),
    mulWinNat8]
  have c1 : (a.toNat / 2 ^ 7 % 8) % 2 = a.toNat / 2 ^ 7 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 7 % 8) / 2 % 2 = a.toNat / 2 ^ 8 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 7 % 8) / 4 = a.toNat / 2 ^ 9 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 8 (by omega)
/-- 窗 10 项的 toNat -/
theorem mulTermNat10 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 10) <<< 10).toNat
      = ((a.toNat / 2 ^ 9 % 2) * 2 ^ 10 + (a.toNat / 2 ^ 10 % 2) * 2 ^ 10 + (a.toNat / 2 ^ 11 % 2) * (2 ^ 66 - 2 ^ 11)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 10),
    mulWinNat10]
  have c1 : (a.toNat / 2 ^ 9 % 8) % 2 = a.toNat / 2 ^ 9 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 9 % 8) / 2 % 2 = a.toNat / 2 ^ 10 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 9 % 8) / 4 = a.toNat / 2 ^ 11 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 10 (by omega)
/-- 窗 12 项的 toNat -/
theorem mulTermNat12 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 12) <<< 12).toNat
      = ((a.toNat / 2 ^ 11 % 2) * 2 ^ 12 + (a.toNat / 2 ^ 12 % 2) * 2 ^ 12 + (a.toNat / 2 ^ 13 % 2) * (2 ^ 66 - 2 ^ 13)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 12),
    mulWinNat12]
  have c1 : (a.toNat / 2 ^ 11 % 8) % 2 = a.toNat / 2 ^ 11 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 11 % 8) / 2 % 2 = a.toNat / 2 ^ 12 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 11 % 8) / 4 = a.toNat / 2 ^ 13 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 12 (by omega)
/-- 窗 14 项的 toNat -/
theorem mulTermNat14 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 14) <<< 14).toNat
      = ((a.toNat / 2 ^ 13 % 2) * 2 ^ 14 + (a.toNat / 2 ^ 14 % 2) * 2 ^ 14 + (a.toNat / 2 ^ 15 % 2) * (2 ^ 66 - 2 ^ 15)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 14),
    mulWinNat14]
  have c1 : (a.toNat / 2 ^ 13 % 8) % 2 = a.toNat / 2 ^ 13 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 13 % 8) / 2 % 2 = a.toNat / 2 ^ 14 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 13 % 8) / 4 = a.toNat / 2 ^ 15 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 14 (by omega)
/-- 窗 16 项的 toNat -/
theorem mulTermNat16 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 16) <<< 16).toNat
      = ((a.toNat / 2 ^ 15 % 2) * 2 ^ 16 + (a.toNat / 2 ^ 16 % 2) * 2 ^ 16 + (a.toNat / 2 ^ 17 % 2) * (2 ^ 66 - 2 ^ 17)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 16),
    mulWinNat16]
  have c1 : (a.toNat / 2 ^ 15 % 8) % 2 = a.toNat / 2 ^ 15 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 15 % 8) / 2 % 2 = a.toNat / 2 ^ 16 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 15 % 8) / 4 = a.toNat / 2 ^ 17 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 16 (by omega)
/-- 窗 18 项的 toNat -/
theorem mulTermNat18 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 18) <<< 18).toNat
      = ((a.toNat / 2 ^ 17 % 2) * 2 ^ 18 + (a.toNat / 2 ^ 18 % 2) * 2 ^ 18 + (a.toNat / 2 ^ 19 % 2) * (2 ^ 66 - 2 ^ 19)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 18),
    mulWinNat18]
  have c1 : (a.toNat / 2 ^ 17 % 8) % 2 = a.toNat / 2 ^ 17 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 17 % 8) / 2 % 2 = a.toNat / 2 ^ 18 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 17 % 8) / 4 = a.toNat / 2 ^ 19 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 18 (by omega)
/-- 窗 20 项的 toNat -/
theorem mulTermNat20 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 20) <<< 20).toNat
      = ((a.toNat / 2 ^ 19 % 2) * 2 ^ 20 + (a.toNat / 2 ^ 20 % 2) * 2 ^ 20 + (a.toNat / 2 ^ 21 % 2) * (2 ^ 66 - 2 ^ 21)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 20),
    mulWinNat20]
  have c1 : (a.toNat / 2 ^ 19 % 8) % 2 = a.toNat / 2 ^ 19 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 19 % 8) / 2 % 2 = a.toNat / 2 ^ 20 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 19 % 8) / 4 = a.toNat / 2 ^ 21 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 20 (by omega)
/-- 窗 22 项的 toNat -/
theorem mulTermNat22 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 22) <<< 22).toNat
      = ((a.toNat / 2 ^ 21 % 2) * 2 ^ 22 + (a.toNat / 2 ^ 22 % 2) * 2 ^ 22 + (a.toNat / 2 ^ 23 % 2) * (2 ^ 66 - 2 ^ 23)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 22),
    mulWinNat22]
  have c1 : (a.toNat / 2 ^ 21 % 8) % 2 = a.toNat / 2 ^ 21 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 21 % 8) / 2 % 2 = a.toNat / 2 ^ 22 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 21 % 8) / 4 = a.toNat / 2 ^ 23 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 22 (by omega)
/-- 窗 24 项的 toNat -/
theorem mulTermNat24 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 24) <<< 24).toNat
      = ((a.toNat / 2 ^ 23 % 2) * 2 ^ 24 + (a.toNat / 2 ^ 24 % 2) * 2 ^ 24 + (a.toNat / 2 ^ 25 % 2) * (2 ^ 66 - 2 ^ 25)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 24),
    mulWinNat24]
  have c1 : (a.toNat / 2 ^ 23 % 8) % 2 = a.toNat / 2 ^ 23 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 23 % 8) / 2 % 2 = a.toNat / 2 ^ 24 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 23 % 8) / 4 = a.toNat / 2 ^ 25 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 24 (by omega)
/-- 窗 26 项的 toNat -/
theorem mulTermNat26 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 26) <<< 26).toNat
      = ((a.toNat / 2 ^ 25 % 2) * 2 ^ 26 + (a.toNat / 2 ^ 26 % 2) * 2 ^ 26 + (a.toNat / 2 ^ 27 % 2) * (2 ^ 66 - 2 ^ 27)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 26),
    mulWinNat26]
  have c1 : (a.toNat / 2 ^ 25 % 8) % 2 = a.toNat / 2 ^ 25 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 25 % 8) / 2 % 2 = a.toNat / 2 ^ 26 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 25 % 8) / 4 = a.toNat / 2 ^ 27 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 26 (by omega)
/-- 窗 28 项的 toNat -/
theorem mulTermNat28 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 28) <<< 28).toNat
      = ((a.toNat / 2 ^ 27 % 2) * 2 ^ 28 + (a.toNat / 2 ^ 28 % 2) * 2 ^ 28 + (a.toNat / 2 ^ 29 % 2) * (2 ^ 66 - 2 ^ 29)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 28),
    mulWinNat28]
  have c1 : (a.toNat / 2 ^ 27 % 8) % 2 = a.toNat / 2 ^ 27 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 27 % 8) / 2 % 2 = a.toNat / 2 ^ 28 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 27 % 8) / 4 = a.toNat / 2 ^ 29 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 28 (by omega)
/-- 窗 30 项的 toNat -/
theorem mulTermNat30 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 30) <<< 30).toNat
      = ((a.toNat / 2 ^ 29 % 2) * 2 ^ 30 + (a.toNat / 2 ^ 30 % 2) * 2 ^ 30 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 30),
    mulWinNat30]
  have c1 : (a.toNat / 2 ^ 29 % 8) % 2 = a.toNat / 2 ^ 29 % 2 := by omega
  have c2 : (a.toNat / 2 ^ 29 % 8) / 2 % 2 = a.toNat / 2 ^ 30 % 2 := by omega
  have c3 : (a.toNat / 2 ^ 29 % 8) / 4 = a.toNat / 2 ^ 31 % 2 := by omega
  rw [c1, c2, c3]
  exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 30 (by omega)
/-- 窗 32 项的 toNat -/
theorem mulTermNat32 (a : BitVec 33) :
    (mulDigitVec (mulWindow a 32) <<< 32).toNat
      = ((a.toNat / 2 ^ 31 % 2) * 2 ^ 32 + (a.toNat / 2 ^ 32 % 2) * 2 ^ 32
        + (a.toNat / 2 ^ 32 % 2) * (2 ^ 66 - 2 ^ 33)) % 2 ^ 66 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, mulDigitVec_toNat (mulWindow a 32),
    mulWinNat32]
  cases hmsb : a.msb
  · have hb : a.getLsbD 32 = false := BitVec.msb_eq_getLsbD_last a ▸ hmsb
    have hbn : 2 * a.toNat < 2 ^ 33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hmsb
    rw [hb, if_neg (by decide : ¬ (false = true))]
    have c1 : (a.toNat / 2 ^ 31 % 4 + 0) % 2 = a.toNat / 2 ^ 31 % 2 := by omega
    have c2 : (a.toNat / 2 ^ 31 % 4 + 0) / 2 % 2 = a.toNat / 2 ^ 32 % 2 := by omega
    have c3 : (a.toNat / 2 ^ 31 % 4 + 0) / 4 = a.toNat / 2 ^ 32 % 2 := by omega
    rw [c1, c2, c3]
    exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 32 (by omega)
  · have hb : a.getLsbD 32 = true := BitVec.msb_eq_getLsbD_last a ▸ hmsb
    have hbn : 2 * a.toNat ≥ 2 ^ 33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hmsb
    rw [hb, if_pos rfl]
    have c1 : (a.toNat / 2 ^ 31 % 4 + 4) % 2 = a.toNat / 2 ^ 31 % 2 := by omega
    have c2 : (a.toNat / 2 ^ 31 % 4 + 4) / 2 % 2 = a.toNat / 2 ^ 32 % 2 := by omega
    have c3 : (a.toNat / 2 ^ 31 % 4 + 4) / 4 = a.toNat / 2 ^ 32 % 2 := by omega
    rw [c1, c2, c3]
    exact mulTermMod _ _ _ (by omega) (by omega) (by omega) 32 (by omega)

/-- 部分和（窗 0,2） -/
theorem mulTelePart1 (a : BitVec 33) :
    (((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2))).toNat = a.toNat % 2 ^ 3 + (a.toNat / 2 ^ 3 % 2) * (2 ^ 66 - 2 ^ 3) := by
  rw [BitVec.toNat_add, mulTermNat0, mulTermNat2, ← Nat.add_mod]
  have hkey : 0 * 2 ^ 0 + (a.toNat % 2) * 2 ^ 0 + (a.toNat / 2 % 2) * (2 ^ 66 - 2 ^ 1)
      + ((a.toNat / 2 ^ 1 % 2) * 2 ^ 2 + (a.toNat / 2 ^ 2 % 2) * 2 ^ 2
        + (a.toNat / 2 ^ 3 % 2) * (2 ^ 66 - 2 ^ 3))
      = (a.toNat % 2 ^ 3 + (a.toNat / 2 ^ 3 % 2) * (2 ^ 66 - 2 ^ 3)) + 2 ^ 66 * (a.toNat / 2 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..4） -/
theorem mulTelePart2 (a : BitVec 33) :
    ((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4))).toNat = a.toNat % 2 ^ 5 + (a.toNat / 2 ^ 5 % 2) * (2 ^ 66 - 2 ^ 5) := by
  rw [BitVec.toNat_add, mulTelePart1, mulTermNat4, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 3 + (a.toNat / 2 ^ 3 % 2) * (2 ^ 66 - 2 ^ 3)
      + ((a.toNat / 2 ^ 3 % 2) * 2 ^ 4 + (a.toNat / 2 ^ 4 % 2) * 2 ^ 4 + (a.toNat / 2 ^ 5 % 2) * (2 ^ 66 - 2 ^ 5))
      = (a.toNat % 2 ^ 5 + (a.toNat / 2 ^ 5 % 2) * (2 ^ 66 - 2 ^ 5)) + 2 ^ 66 * (a.toNat / 2 ^ 3 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..6） -/
theorem mulTelePart3 (a : BitVec 33) :
    (((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6))).toNat = a.toNat % 2 ^ 7 + (a.toNat / 2 ^ 7 % 2) * (2 ^ 66 - 2 ^ 7) := by
  rw [BitVec.toNat_add, mulTelePart2, mulTermNat6, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 5 + (a.toNat / 2 ^ 5 % 2) * (2 ^ 66 - 2 ^ 5)
      + ((a.toNat / 2 ^ 5 % 2) * 2 ^ 6 + (a.toNat / 2 ^ 6 % 2) * 2 ^ 6 + (a.toNat / 2 ^ 7 % 2) * (2 ^ 66 - 2 ^ 7))
      = (a.toNat % 2 ^ 7 + (a.toNat / 2 ^ 7 % 2) * (2 ^ 66 - 2 ^ 7)) + 2 ^ 66 * (a.toNat / 2 ^ 5 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..8） -/
theorem mulTelePart4 (a : BitVec 33) :
    ((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8))).toNat = a.toNat % 2 ^ 9 + (a.toNat / 2 ^ 9 % 2) * (2 ^ 66 - 2 ^ 9) := by
  rw [BitVec.toNat_add, mulTelePart3, mulTermNat8, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 7 + (a.toNat / 2 ^ 7 % 2) * (2 ^ 66 - 2 ^ 7)
      + ((a.toNat / 2 ^ 7 % 2) * 2 ^ 8 + (a.toNat / 2 ^ 8 % 2) * 2 ^ 8 + (a.toNat / 2 ^ 9 % 2) * (2 ^ 66 - 2 ^ 9))
      = (a.toNat % 2 ^ 9 + (a.toNat / 2 ^ 9 % 2) * (2 ^ 66 - 2 ^ 9)) + 2 ^ 66 * (a.toNat / 2 ^ 7 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..10） -/
theorem mulTelePart5 (a : BitVec 33) :
    (((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10))).toNat = a.toNat % 2 ^ 11 + (a.toNat / 2 ^ 11 % 2) * (2 ^ 66 - 2 ^ 11) := by
  rw [BitVec.toNat_add, mulTelePart4, mulTermNat10, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 9 + (a.toNat / 2 ^ 9 % 2) * (2 ^ 66 - 2 ^ 9)
      + ((a.toNat / 2 ^ 9 % 2) * 2 ^ 10 + (a.toNat / 2 ^ 10 % 2) * 2 ^ 10 + (a.toNat / 2 ^ 11 % 2) * (2 ^ 66 - 2 ^ 11))
      = (a.toNat % 2 ^ 11 + (a.toNat / 2 ^ 11 % 2) * (2 ^ 66 - 2 ^ 11)) + 2 ^ 66 * (a.toNat / 2 ^ 9 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..12） -/
theorem mulTelePart6 (a : BitVec 33) :
    ((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12))).toNat = a.toNat % 2 ^ 13 + (a.toNat / 2 ^ 13 % 2) * (2 ^ 66 - 2 ^ 13) := by
  rw [BitVec.toNat_add, mulTelePart5, mulTermNat12, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 11 + (a.toNat / 2 ^ 11 % 2) * (2 ^ 66 - 2 ^ 11)
      + ((a.toNat / 2 ^ 11 % 2) * 2 ^ 12 + (a.toNat / 2 ^ 12 % 2) * 2 ^ 12 + (a.toNat / 2 ^ 13 % 2) * (2 ^ 66 - 2 ^ 13))
      = (a.toNat % 2 ^ 13 + (a.toNat / 2 ^ 13 % 2) * (2 ^ 66 - 2 ^ 13)) + 2 ^ 66 * (a.toNat / 2 ^ 11 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..14） -/
theorem mulTelePart7 (a : BitVec 33) :
    (((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14))).toNat = a.toNat % 2 ^ 15 + (a.toNat / 2 ^ 15 % 2) * (2 ^ 66 - 2 ^ 15) := by
  rw [BitVec.toNat_add, mulTelePart6, mulTermNat14, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 13 + (a.toNat / 2 ^ 13 % 2) * (2 ^ 66 - 2 ^ 13)
      + ((a.toNat / 2 ^ 13 % 2) * 2 ^ 14 + (a.toNat / 2 ^ 14 % 2) * 2 ^ 14 + (a.toNat / 2 ^ 15 % 2) * (2 ^ 66 - 2 ^ 15))
      = (a.toNat % 2 ^ 15 + (a.toNat / 2 ^ 15 % 2) * (2 ^ 66 - 2 ^ 15)) + 2 ^ 66 * (a.toNat / 2 ^ 13 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..16） -/
theorem mulTelePart8 (a : BitVec 33) :
    ((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16))).toNat = a.toNat % 2 ^ 17 + (a.toNat / 2 ^ 17 % 2) * (2 ^ 66 - 2 ^ 17) := by
  rw [BitVec.toNat_add, mulTelePart7, mulTermNat16, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 15 + (a.toNat / 2 ^ 15 % 2) * (2 ^ 66 - 2 ^ 15)
      + ((a.toNat / 2 ^ 15 % 2) * 2 ^ 16 + (a.toNat / 2 ^ 16 % 2) * 2 ^ 16 + (a.toNat / 2 ^ 17 % 2) * (2 ^ 66 - 2 ^ 17))
      = (a.toNat % 2 ^ 17 + (a.toNat / 2 ^ 17 % 2) * (2 ^ 66 - 2 ^ 17)) + 2 ^ 66 * (a.toNat / 2 ^ 15 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..18） -/
theorem mulTelePart9 (a : BitVec 33) :
    (((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18))).toNat = a.toNat % 2 ^ 19 + (a.toNat / 2 ^ 19 % 2) * (2 ^ 66 - 2 ^ 19) := by
  rw [BitVec.toNat_add, mulTelePart8, mulTermNat18, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 17 + (a.toNat / 2 ^ 17 % 2) * (2 ^ 66 - 2 ^ 17)
      + ((a.toNat / 2 ^ 17 % 2) * 2 ^ 18 + (a.toNat / 2 ^ 18 % 2) * 2 ^ 18 + (a.toNat / 2 ^ 19 % 2) * (2 ^ 66 - 2 ^ 19))
      = (a.toNat % 2 ^ 19 + (a.toNat / 2 ^ 19 % 2) * (2 ^ 66 - 2 ^ 19)) + 2 ^ 66 * (a.toNat / 2 ^ 17 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..20） -/
theorem mulTelePart10 (a : BitVec 33) :
    ((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20))).toNat = a.toNat % 2 ^ 21 + (a.toNat / 2 ^ 21 % 2) * (2 ^ 66 - 2 ^ 21) := by
  rw [BitVec.toNat_add, mulTelePart9, mulTermNat20, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 19 + (a.toNat / 2 ^ 19 % 2) * (2 ^ 66 - 2 ^ 19)
      + ((a.toNat / 2 ^ 19 % 2) * 2 ^ 20 + (a.toNat / 2 ^ 20 % 2) * 2 ^ 20 + (a.toNat / 2 ^ 21 % 2) * (2 ^ 66 - 2 ^ 21))
      = (a.toNat % 2 ^ 21 + (a.toNat / 2 ^ 21 % 2) * (2 ^ 66 - 2 ^ 21)) + 2 ^ 66 * (a.toNat / 2 ^ 19 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..22） -/
theorem mulTelePart11 (a : BitVec 33) :
    (((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22))).toNat = a.toNat % 2 ^ 23 + (a.toNat / 2 ^ 23 % 2) * (2 ^ 66 - 2 ^ 23) := by
  rw [BitVec.toNat_add, mulTelePart10, mulTermNat22, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 21 + (a.toNat / 2 ^ 21 % 2) * (2 ^ 66 - 2 ^ 21)
      + ((a.toNat / 2 ^ 21 % 2) * 2 ^ 22 + (a.toNat / 2 ^ 22 % 2) * 2 ^ 22 + (a.toNat / 2 ^ 23 % 2) * (2 ^ 66 - 2 ^ 23))
      = (a.toNat % 2 ^ 23 + (a.toNat / 2 ^ 23 % 2) * (2 ^ 66 - 2 ^ 23)) + 2 ^ 66 * (a.toNat / 2 ^ 21 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..24） -/
theorem mulTelePart12 (a : BitVec 33) :
    ((((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22)) + (mulDigitVec (mulWindow a 24) <<< 24))).toNat = a.toNat % 2 ^ 25 + (a.toNat / 2 ^ 25 % 2) * (2 ^ 66 - 2 ^ 25) := by
  rw [BitVec.toNat_add, mulTelePart11, mulTermNat24, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 23 + (a.toNat / 2 ^ 23 % 2) * (2 ^ 66 - 2 ^ 23)
      + ((a.toNat / 2 ^ 23 % 2) * 2 ^ 24 + (a.toNat / 2 ^ 24 % 2) * 2 ^ 24 + (a.toNat / 2 ^ 25 % 2) * (2 ^ 66 - 2 ^ 25))
      = (a.toNat % 2 ^ 25 + (a.toNat / 2 ^ 25 % 2) * (2 ^ 66 - 2 ^ 25)) + 2 ^ 66 * (a.toNat / 2 ^ 23 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..26） -/
theorem mulTelePart13 (a : BitVec 33) :
    (((((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22)) + (mulDigitVec (mulWindow a 24) <<< 24)) + (mulDigitVec (mulWindow a 26) <<< 26))).toNat = a.toNat % 2 ^ 27 + (a.toNat / 2 ^ 27 % 2) * (2 ^ 66 - 2 ^ 27) := by
  rw [BitVec.toNat_add, mulTelePart12, mulTermNat26, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 25 + (a.toNat / 2 ^ 25 % 2) * (2 ^ 66 - 2 ^ 25)
      + ((a.toNat / 2 ^ 25 % 2) * 2 ^ 26 + (a.toNat / 2 ^ 26 % 2) * 2 ^ 26 + (a.toNat / 2 ^ 27 % 2) * (2 ^ 66 - 2 ^ 27))
      = (a.toNat % 2 ^ 27 + (a.toNat / 2 ^ 27 % 2) * (2 ^ 66 - 2 ^ 27)) + 2 ^ 66 * (a.toNat / 2 ^ 25 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..28） -/
theorem mulTelePart14 (a : BitVec 33) :
    ((((((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22)) + (mulDigitVec (mulWindow a 24) <<< 24)) + (mulDigitVec (mulWindow a 26) <<< 26)) + (mulDigitVec (mulWindow a 28) <<< 28))).toNat = a.toNat % 2 ^ 29 + (a.toNat / 2 ^ 29 % 2) * (2 ^ 66 - 2 ^ 29) := by
  rw [BitVec.toNat_add, mulTelePart13, mulTermNat28, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 27 + (a.toNat / 2 ^ 27 % 2) * (2 ^ 66 - 2 ^ 27)
      + ((a.toNat / 2 ^ 27 % 2) * 2 ^ 28 + (a.toNat / 2 ^ 28 % 2) * 2 ^ 28 + (a.toNat / 2 ^ 29 % 2) * (2 ^ 66 - 2 ^ 29))
      = (a.toNat % 2 ^ 29 + (a.toNat / 2 ^ 29 % 2) * (2 ^ 66 - 2 ^ 29)) + 2 ^ 66 * (a.toNat / 2 ^ 27 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- 部分和（窗 0..30） -/
theorem mulTelePart15 (a : BitVec 33) :
    (((((((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22)) + (mulDigitVec (mulWindow a 24) <<< 24)) + (mulDigitVec (mulWindow a 26) <<< 26)) + (mulDigitVec (mulWindow a 28) <<< 28)) + (mulDigitVec (mulWindow a 30) <<< 30))).toNat = a.toNat % 2 ^ 31 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31) := by
  rw [BitVec.toNat_add, mulTelePart14, mulTermNat30, Nat.add_mod_mod]
  have hkey : a.toNat % 2 ^ 29 + (a.toNat / 2 ^ 29 % 2) * (2 ^ 66 - 2 ^ 29)
      + ((a.toNat / 2 ^ 29 % 2) * 2 ^ 30 + (a.toNat / 2 ^ 30 % 2) * 2 ^ 30 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31))
      = (a.toNat % 2 ^ 31 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31)) + 2 ^ 66 * (a.toNat / 2 ^ 29 % 2) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- Booth 望远镜恒等式：Σ d(x_i)·2^i = a 的符号扩展（33 位变量，无乘法）。
    手工证明（消 bv_decide，文件头 Q10）：eq_of_toNat_eq + 逐窗项模剥离
    （mulTermNat*，经 mulTermMod）+ 15 步部分和步进（mulTelePart*，每步把上一窗
    的 hi·(2^66 - 2^e) 与本窗 lo·2^{e+1} 合并出 2^66·bit 供 add_mul_mod_self_left
    吸收）+ msb 分情形 omega——全程不让 omega 直接面对 % 2^66（Q9 的坑） -/
theorem mulTelescope (a : BitVec 33) :
    mulDigitSumVec a = BitVec.signExtend 66 a := by
  apply BitVec.eq_of_toNat_eq
  show ((((((((((((((((((mulDigitVec (mulWindow a 0) <<< 0) + (mulDigitVec (mulWindow a 2) <<< 2)) + (mulDigitVec (mulWindow a 4) <<< 4)) + (mulDigitVec (mulWindow a 6) <<< 6)) + (mulDigitVec (mulWindow a 8) <<< 8)) + (mulDigitVec (mulWindow a 10) <<< 10)) + (mulDigitVec (mulWindow a 12) <<< 12)) + (mulDigitVec (mulWindow a 14) <<< 14)) + (mulDigitVec (mulWindow a 16) <<< 16)) + (mulDigitVec (mulWindow a 18) <<< 18)) + (mulDigitVec (mulWindow a 20) <<< 20)) + (mulDigitVec (mulWindow a 22) <<< 22)) + (mulDigitVec (mulWindow a 24) <<< 24)) + (mulDigitVec (mulWindow a 26) <<< 26)) + (mulDigitVec (mulWindow a 28) <<< 28)) + (mulDigitVec (mulWindow a 30) <<< 30)) + (mulDigitVec (mulWindow a 32) <<< 32))).toNat = (BitVec.signExtend 66 a).toNat
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have h := a.isLt; omega : a.toNat < 2 ^ 66)]
  have hlt := a.isLt
  rw [BitVec.toNat_add, mulTelePart15, mulTermNat32, Nat.add_mod_mod]
  cases hmsb : a.msb
  · have hbn : 2 * a.toNat < 2 ^ 33 := BitVec.msb_eq_false_iff_two_mul_lt.mp hmsb
    rw [if_neg (by decide : ¬ (false = true))]
    have hkey : a.toNat % 2 ^ 31 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31)
        + ((a.toNat / 2 ^ 31 % 2) * 2 ^ 32 + (a.toNat / 2 ^ 32 % 2) * 2 ^ 32 + (a.toNat / 2 ^ 32 % 2) * (2 ^ 66 - 2 ^ 33))
        = (a.toNat + 0) + 2 ^ 66 * (a.toNat / 2 ^ 31 % 2) := by
      omega
    rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hbn : 2 * a.toNat ≥ 2 ^ 33 := BitVec.msb_eq_true_iff_two_mul_ge.mp hmsb
    rw [if_pos rfl]
    have hkey : a.toNat % 2 ^ 31 + (a.toNat / 2 ^ 31 % 2) * (2 ^ 66 - 2 ^ 31)
        + ((a.toNat / 2 ^ 31 % 2) * 2 ^ 32 + (a.toNat / 2 ^ 32 % 2) * 2 ^ 32 + (a.toNat / 2 ^ 32 % 2) * (2 ^ 66 - 2 ^ 33))
        = (a.toNat + (2 ^ 66 - 2 ^ 33)) + 2 ^ 66 * (a.toNat / 2 ^ 31 % 2) := by
      omega
    rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Σ (d(x_i)·2^i)·B = (Σ d(x_i)·2^i)·B = sext(a)·B：乘法对数字和的分配 -/
theorem mulDigitTermSum_eq (a b : BitVec 33) :
    (mulDigitVec (mulWindow a 0) <<< 0) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 2) <<< 2) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 4) <<< 4) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 6) <<< 6) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 8) <<< 8) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 10) <<< 10) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 12) <<< 12) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 14) <<< 14) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 16) <<< 16) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 18) <<< 18) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 20) <<< 20) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 22) <<< 22) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 24) <<< 24) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 26) <<< 26) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 28) <<< 28) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 30) <<< 30) * BitVec.signExtend 66 b +
    (mulDigitVec (mulWindow a 32) <<< 32) * BitVec.signExtend 66 b
    = (BitVec.signExtend 66 a) * (BitVec.signExtend 66 b) := by
  simp only [← BitVec.add_mul]
  show mulDigitSumVec a * BitVec.signExtend 66 b = _
  rw [mulTelescope]

/-- 消去引理：(x - y) + (z + y) = x + z（66 位加法链使 SAT 求解器病态超时，
    线性装配一律改用手工 AC 重写，不用 bv_decide） -/
theorem mulSubAddAdd (x y z : BitVec 66) : (x - y) + (z + y) = x + z := by
  rw [BitVec.add_comm z y, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- 加-减结合：x + (y - z) = (x + y) - z -/
theorem mulAddSubAssoc (x y z : BitVec 66) : x + (y - z) = (x + y) - z := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, ← BitVec.add_assoc]

/-- 加-减交换：(x + y) - z = (x - z) + y -/
theorem mulAddSubSwap (x y z : BitVec 66) : (x + y) - z = (x - z) + y := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc,
    BitVec.add_comm y (-z), ← BitVec.add_assoc]

/-- 装配步进引理：相邻两组项合并（E 相消、K 累积） -/
theorem mulLinStep (S KK D F L E : BitVec 66) :
    (S - E + KK) + (D - F + L + E) = (S + D) - F + (KK + L) := by
  rw [BitVec.add_assoc (S - E) KK (D - F + L + E),
    ← BitVec.add_assoc KK ((D - F) + L) E, mulSubAddAdd,
    ← BitVec.add_assoc S KK (D - F + L), BitVec.add_comm (D - F) L,
    ← BitVec.add_assoc (S + KK) L (D - F), BitVec.add_assoc S KK L,
    mulAddSubAssoc, BitVec.add_assoc S (KK + L) D, BitVec.add_comm (KK + L) D,
    ← BitVec.add_assoc S D (KK + L), mulAddSubSwap]

/-- 装配收尾步（末行无 K 项） -/
theorem mulLinStepLast (S KK D F E : BitVec 66) :
    (S - F + KK) + (D - E + F) = (S + D) - E + KK := by
  rw [BitVec.add_assoc (S - F) KK (D - E + F),
    ← BitVec.add_assoc KK (D - E) F, mulSubAddAdd,
    ← BitVec.add_assoc S KK (D - E), mulAddSubAssoc,
    BitVec.add_assoc S KK D, BitVec.add_comm KK D,
    ← BitVec.add_assoc S D KK, mulAddSubSwap]

/-- 常数项总和：2^36 + Σ_{i=2..30} 3·2^(34+i) = 2^66 ≡ 0（mod 2^66） -/
theorem mulLinConst :
    ((1#66 <<< 36) + ((3#66 <<< 34) <<< 2) + ((3#66 <<< 34) <<< 4) +
    ((3#66 <<< 34) <<< 6) + ((3#66 <<< 34) <<< 8) + ((3#66 <<< 34) <<< 10) +
    ((3#66 <<< 34) <<< 12) + ((3#66 <<< 34) <<< 14) + ((3#66 <<< 34) <<< 16) +
    ((3#66 <<< 34) <<< 18) + ((3#66 <<< 34) <<< 20) + ((3#66 <<< 34) <<< 22) +
    ((3#66 <<< 34) <<< 24) + ((3#66 <<< 34) <<< 26) + ((3#66 <<< 34) <<< 28) +
    ((3#66 <<< 34) <<< 30)) = 0#66 := by
  decide

/-- 线性组合装配：34 个自由分量 + 数字和假设 → 总和 = P - E32。
    修正项/t 项两两相消，仅剩末行修正 -E32（见 Q3）。 -/
theorem mulLinearComb
    {D0 D2 D4 D6 D8 D10 D12 D14 D16 D18 D20 D22 D24 D26 D28 D30 D32 : BitVec 66}
    {E0 E2 E4 E6 E8 E10 E12 E14 E16 E18 E20 E22 E24 E26 E28 E30 E32 : BitVec 66}
    {P : BitVec 66}
    (hdig : D0 + D2 + D4 + D6 + D8 + D10 + D12 + D14 + D16 + D18 + D20 + D22 +
      D24 + D26 + D28 + D30 + D32 = P) :
    (D0 - E0 + (1#66 <<< 36))
    + (D2 - E2 + ((3#66 <<< 34) <<< 2) + E0)
    + (D4 - E4 + ((3#66 <<< 34) <<< 4) + E2)
    + (D6 - E6 + ((3#66 <<< 34) <<< 6) + E4)
    + (D8 - E8 + ((3#66 <<< 34) <<< 8) + E6)
    + (D10 - E10 + ((3#66 <<< 34) <<< 10) + E8)
    + (D12 - E12 + ((3#66 <<< 34) <<< 12) + E10)
    + (D14 - E14 + ((3#66 <<< 34) <<< 14) + E12)
    + (D16 - E16 + ((3#66 <<< 34) <<< 16) + E14)
    + (D18 - E18 + ((3#66 <<< 34) <<< 18) + E16)
    + (D20 - E20 + ((3#66 <<< 34) <<< 20) + E18)
    + (D22 - E22 + ((3#66 <<< 34) <<< 22) + E20)
    + (D24 - E24 + ((3#66 <<< 34) <<< 24) + E22)
    + (D26 - E26 + ((3#66 <<< 34) <<< 26) + E24)
    + (D28 - E28 + ((3#66 <<< 34) <<< 28) + E26)
    + (D30 - E30 + ((3#66 <<< 34) <<< 30) + E28)
    + (D32 - E32 + E30)
    = P - E32 := by
  rw [mulLinStep, mulLinStep, mulLinStep, mulLinStep, mulLinStep, mulLinStep,
    mulLinStep, mulLinStep, mulLinStep, mulLinStep, mulLinStep, mulLinStep,
    mulLinStep, mulLinStep, mulLinStep, mulLinStepLast, mulLinConst,
    BitVec.add_zero, hdig]

/-- 部分积加权和（算术层总和，17 行左结合） -/
def mulPlacedSum (a b : BitVec 33) : BitVec 66 :=
  mulPlacedRow a b 0 + mulPlacedRow a b 2 + mulPlacedRow a b 4 +
  mulPlacedRow a b 6 + mulPlacedRow a b 8 + mulPlacedRow a b 10 +
  mulPlacedRow a b 12 + mulPlacedRow a b 14 + mulPlacedRow a b 16 +
  mulPlacedRow a b 18 + mulPlacedRow a b 20 + mulPlacedRow a b 22 +
  mulPlacedRow a b 24 + mulPlacedRow a b 26 + mulPlacedRow a b 28 +
  mulPlacedRow a b 30 + mulPlacedRow a b 32

/-- **核心正确性定理**：部分积加权和 = sext(a)·sext(b) - 末行修正（mod 2^66）。
    末行修正项仅在 x_last ∈ {4,5,6} 时非零（见 Q3）。 -/
theorem mulPlacedSum_eq (a b : BitVec 33) :
    mulPlacedSum a b =
      (BitVec.signExtend 66 a) * (BitVec.signExtend 66 b)
        - (mulCorrBV (mulWindow a 32) <<< 32) := by
  rw [mulPlacedSum, mulPlacedRow_zero, mulPlacedRow_last,
    mulPlacedRow_mid a b 2 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 4 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 6 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 8 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 10 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 12 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 14 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 16 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 18 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 20 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 22 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 24 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 26 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 28 (by omega) (by omega) (by omega),
    mulPlacedRow_mid a b 30 (by omega) (by omega) (by omega)]
  exact mulLinearComb (mulDigitTermSum_eq a b)

/-- 末行窗为 6 ⟺ a 的 bit32=1 且 bit31=0（Q3 的触发条件）。
    手工证明（消 bv_decide）：窗归约为 signExtend 3 的 2 位截取 + 4 路穷举 -/
theorem mulWindow32_eq6 (a : BitVec 33) :
    (mulWindow a 32 = 6#3) ↔ (a.getLsbD 32 = true ∧ a.getLsbD 31 = false) := by
  have hw : mulWindow a 32 = BitVec.signExtend 3 (a.extractLsb' 31 2) := rfl
  have h1 : (a.extractLsb' 31 2).getLsbD 0 = a.getLsbD 31 := by
    rw [BitVec.getLsbD_extractLsb']; rfl
  have h2 : (a.extractLsb' 31 2).getLsbD 1 = a.getLsbD 32 := by
    rw [BitVec.getLsbD_extractLsb']; rfl
  rw [hw, ← h1, ← h2]
  rcases mulB2cases (a.extractLsb' 31 2) with h|h|h|h <;> rw [h] <;> decide

/-- 可达性：bit32=0 或 bit31=1 时末行修正为零。手工证明（消 bv_decide） -/
theorem mulCorr_window32_eq0 (a : BitVec 33)
    (h : a.getLsbD 32 = false ∨ a.getLsbD 31 = true) :
    mulCorrBV (mulWindow a 32) = 0#66 := by
  have hw : mulWindow a 32 = BitVec.signExtend 3 (a.extractLsb' 31 2) := rfl
  have h1 : (a.extractLsb' 31 2).getLsbD 0 = a.getLsbD 31 := by
    rw [BitVec.getLsbD_extractLsb']; rfl
  have h2 : (a.extractLsb' 31 2).getLsbD 1 = a.getLsbD 32 := by
    rw [BitVec.getLsbD_extractLsb']; rfl
  rw [hw]
  rw [← h1, ← h2] at h
  rcases mulB2cases (a.extractLsb' 31 2) with hv|hv|hv|hv <;> rw [hv] at h ⊢ <;>
    rcases h with h | h <;> first | decide | exact absurd h (by decide)

/-- 可达性（符号扩展 32→33）：末行修正为零。手工证明（消 bv_decide） -/
theorem mul_sext33_corr0 (x : BitVec 32) :
    mulCorrBV (mulWindow (BitVec.signExtend 33 x) 32) = 0#66 := by
  have h32 : (BitVec.signExtend 33 x).getLsbD 32 = x.msb := by
    rw [BitVec.getLsbD_signExtend]; rfl
  have h31 : (BitVec.signExtend 33 x).getLsbD 31 = x.msb := by
    rw [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]; rfl
  apply mulCorr_window32_eq0
  cases hm : x.msb
  · exact Or.inl (by rw [h32]; exact hm)
  · exact Or.inr (by rw [h31]; exact hm)

/-- 可达性（零扩展 32→33）：末行修正为零。手工证明（消 bv_decide） -/
theorem mul_zext33_corr0 (x : BitVec 32) :
    mulCorrBV (mulWindow (BitVec.zeroExtend 33 x) 32) = 0#66 := by
  have h32 : (BitVec.zeroExtend 33 x).getLsbD 32 = false := by
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge x 32 (Nat.le_refl 32)]; rfl
  exact mulCorr_window32_eq0 _ (Or.inl h32)

/-- 修正项为零时的乘积形式 -/
theorem mulPlacedSum_eq_of_corr0 (a b : BitVec 33)
    (h : mulCorrBV (mulWindow a 32) = 0#66) :
    mulPlacedSum a b = (BitVec.signExtend 66 a) * (BitVec.signExtend 66 b) := by
  rw [mulPlacedSum_eq, h]
  have hz : (0#66 : BitVec 66) <<< 32 = 0#66 := by decide
  rw [hz]
  simp

/-- 可达输入乘积形式（bit32=0 或 bit31=1） -/
theorem mulPlacedSum_eq_reachable (a b : BitVec 33)
    (h : a.getLsbD 32 = false ∨ a.getLsbD 31 = true) :
    mulPlacedSum a b = (BitVec.signExtend 66 a) * (BitVec.signExtend 66 b) :=
  mulPlacedSum_eq_of_corr0 a b (mulCorr_window32_eq0 a h)

/-- Q3 witness：存在（不可达的）a 使放置和 ≠ 乘积：a 的 bit32=1、bit31=0 时
    少 corr·2^32。 -/
theorem mulPlacedSum_quirk :
    ∃ a b : BitVec 33, mulPlacedSum a b
      ≠ (BitVec.signExtend 66 a) * (BitVec.signExtend 66 b) :=
  ⟨0x100000000#33, 5#33, by native_decide⟩


/- ========================================================================= -/
/- 6. ArrayMultiplier wrapper（Multiplier.scala:149-211，len=32，latency=2）   -/
/- ========================================================================= -/

/-- :156  mul_in1 = Mux(func===FN_MADD|func===FN_NMSUB, c, a) -/
def mulIn1 (func : BitVec 5) (a c : BitVec 32) : BitVec 32 :=
  if func = mulFN_MADD ∨ func = mulFN_NMSUB then c else a

/-- :158  mul_in3 = Mux(func===FN_MADD|func===FN_NMSUB, a, c) -/
def mulIn3 (func : BitVec 5) (a c : BitVec 32) : BitVec 32 :=
  if func = mulFN_MADD ∨ func = mulFN_NMSUB then a else c

/-- :178  io.a = Mux(func===FN_MULH|func===FN_MULHSU, signext(mul_in1), zeroext(mul_in1)) -/
def mulA33 (func : BitVec 5) (in1 : BitVec 32) : BitVec 33 :=
  if func = mulFN_MULH ∨ func = mulFN_MULHSU
  then BitVec.signExtend 33 in1 else BitVec.zeroExtend 33 in1

/-- :179  io.b = Mux(func===FN_MULH, signext(mul_in2), zeroext(mul_in2)) -/
def mulB33 (func : BitVec 5) (in2 : BitVec 32) : BitVec 33 :=
  if func = mulFN_MULH then BitVec.signExtend 33 in2 else BitVec.zeroExtend 33 in2

/-- :201  mac_out 低 32 位（67 位符号加减取低 32 = 32 位回绕加减，D6）：
    MACC|MADD → result+c，其余（NMSAC|NMSUB）→ c-result -/
def mulMacOut (func : BitVec 5) (result : BitVec 66) (c : BitVec 32) : BitVec 32 :=
  if func = mulFN_MACC ∨ func = mulFN_MADD
  then result.extractLsb' 0 32 + c
  else c - result.extractLsb' 0 32

/-- :204-205  res = Mux(isMAC(func), mac_out,
    Mux(func===FN_MULH | func===FN_MULHU, result(63,32), result(31,0)))
    【Q1：FN_MULHSU 不在高位条件中，落入低 32 位分支】 -/
def mulRes (func : BitVec 5) (result : BitVec 66) (macOut : BitVec 32) : BitVec 32 :=
  if mulIsMAC func then macOut
  else if func = mulFN_MULH ∨ func = mulFN_MULHU then result.extractLsb' 32 32
  else result.extractLsb' 0 32

/-- wrapper 组合输出（算术层 product 由 mulPlacedSum 给出；:206 的打拍见流水线模型） -/
def mulWrapOut (func : BitVec 5) (a b c : BitVec 32) : BitVec 32 :=
  let in1 := mulIn1 func a c
  let in3 := mulIn3 func a c
  let r := mulPlacedSum (mulA33 func in1) (mulB33 func b)
  mulRes func r (mulMacOut func r in3)

/-- 展开 wrapper 定义的标准 simp 集 -/
macro "mul_wrap_unfold" : tactic =>
  `(tactic| simp only [mulRes, mulMacOut, mulIn1, mulIn3, mulA33, mulB33, mulIsMAC,
    mulIsMUL, mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC,
    mulFN_NMSAC, mulFN_MADD, mulFN_NMSUB])

/- ---- 逐 func 选择规约（result/macOut 抽象，bv_decide 钉死源码现状） ---- -/

theorem mulRes_mul (r : BitVec 66) (m : BitVec 32) :
    mulRes mulFN_MUL r m = r.extractLsb' 0 32 := by
  mul_wrap_unfold; bv_decide

theorem mulRes_mulh (r : BitVec 66) (m : BitVec 32) :
    mulRes mulFN_MULH r m = r.extractLsb' 32 32 := by
  mul_wrap_unfold; bv_decide

theorem mulRes_mulhu (r : BitVec 66) (m : BitVec 32) :
    mulRes mulFN_MULHU r m = r.extractLsb' 32 32 := by
  mul_wrap_unfold; bv_decide

/-- 【Q1】MULHSU 返回【低】32 位（源码现状；正确语义应为高 32 位） -/
theorem mulRes_mulhsu (r : BitVec 66) (m : BitVec 32) :
    mulRes mulFN_MULHSU r m = r.extractLsb' 0 32 := by
  mul_wrap_unfold; bv_decide

theorem mulRes_mac (func : BitVec 5) (r : BitVec 66) (m : BitVec 32)
    (h : mulIsMAC func = true) :
    mulRes func r m = m := by
  simp only [mulIsMAC] at h
  mul_wrap_unfold
  bv_decide

theorem mulMacOut_macc (r : BitVec 66) (c : BitVec 32) :
    mulMacOut mulFN_MACC r c = r.extractLsb' 0 32 + c := by
  mul_wrap_unfold; bv_decide

theorem mulMacOut_nmsac (r : BitVec 66) (c : BitVec 32) :
    mulMacOut mulFN_NMSAC r c = c - r.extractLsb' 0 32 := by
  show (if mulFN_NMSAC = mulFN_MACC ∨ mulFN_NMSAC = mulFN_MADD
      then r.extractLsb' 0 32 + c else c - r.extractLsb' 0 32) = _
  rw [if_neg (by decide)]

theorem mulMacOut_madd (r : BitVec 66) (c : BitVec 32) :
    mulMacOut mulFN_MADD r c = r.extractLsb' 0 32 + c := by
  mul_wrap_unfold; bv_decide

theorem mulMacOut_nmsub (r : BitVec 66) (c : BitVec 32) :
    mulMacOut mulFN_NMSUB r c = c - r.extractLsb' 0 32 := by
  show (if mulFN_NMSUB = mulFN_MACC ∨ mulFN_NMSUB = mulFN_MADD
      then r.extractLsb' 0 32 + c else c - r.extractLsb' 0 32) = _
  rw [if_neg (by decide)]

/- ---- 操作数选择/扩展规约 ---- -/

theorem mulIn1_madd (a c : BitVec 32) : mulIn1 mulFN_MADD a c = c := by
  mul_wrap_unfold; bv_decide

theorem mulIn3_madd (a c : BitVec 32) : mulIn3 mulFN_MADD a c = a := by
  mul_wrap_unfold; bv_decide

theorem mulIn1_nmsub (a c : BitVec 32) : mulIn1 mulFN_NMSUB a c = c := by
  mul_wrap_unfold; bv_decide

theorem mulIn3_nmsub (a c : BitVec 32) : mulIn3 mulFN_NMSUB a c = a := by
  mul_wrap_unfold; bv_decide

theorem mulA33_mulh (x : BitVec 32) :
    mulA33 mulFN_MULH x = BitVec.signExtend 33 x := by
  mul_wrap_unfold; bv_decide

theorem mulA33_mulhsu (x : BitVec 32) :
    mulA33 mulFN_MULHSU x = BitVec.signExtend 33 x := by
  mul_wrap_unfold; bv_decide

theorem mulB33_mulhsu (x : BitVec 32) :
    mulB33 mulFN_MULHSU x = BitVec.zeroExtend 33 x := by
  mul_wrap_unfold; bv_decide

/-- MAC 操作数零扩展（:178-179 条件不含 MAC 操作码；低 32 位与符号无关，见下）。
    手工证明（消 bv_decide）：mulIsMAC 展开后 func=21/23 均矛盾，if_neg 收尾 -/
theorem mulA33_mac (func : BitVec 5) (x : BitVec 32) (h : mulIsMAC func = true) :
    mulA33 func x = BitVec.zeroExtend 33 x := by
  simp only [mulIsMAC] at h
  have h21 : func ≠ mulFN_MULH := fun he => absurd (he ▸ h) (by decide)
  have h23 : func ≠ mulFN_MULHSU := fun he => absurd (he ▸ h) (by decide)
  simp only [mulA33]
  rw [if_neg (not_or.mpr ⟨h21, h23⟩)]

/- ---- 扩展复合与低位乘法 ---- -/

theorem mulSextZext (x : BitVec 32) :
    BitVec.signExtend 66 (BitVec.zeroExtend 33 x) = BitVec.zeroExtend 66 x := by
  bv_decide

theorem mulSextSext (x : BitVec 32) :
    BitVec.signExtend 66 (BitVec.signExtend 33 x) = BitVec.signExtend 66 x := by
  have hmsb : (BitVec.signExtend 33 x).msb = x.msb := by
    rw [BitVec.msb_signExtend]; rfl
  have hlt := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_signExtend, BitVec.toNat_setWidth, hmsb]
  cases hm : x.msb
  · rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true)),
      if_neg (by decide : ¬ (false = true))]
    omega
  · rw [if_pos rfl, if_pos rfl, if_pos rfl]
    omega

/-- 零扩展乘积的低 32 位 = 32 位乘积（toNat 路线，避免对符号乘法用 bv_decide） -/
theorem mul_zext66_low32 (a b : BitVec 32) :
    ((BitVec.zeroExtend 66 a) * (BitVec.zeroExtend 66 b)).extractLsb' 0 32 = a * b := by
  have hz : ∀ x : BitVec 32, (BitVec.zeroExtend 66 x).toNat = x.toNat := by
    intro x
    rw [show BitVec.zeroExtend 66 x = BitVec.setWidth 66 x from rfl, BitVec.toNat_setWidth]
    have := x.isLt
    omega
  apply BitVec.eq_of_toNat_eq
  rw [← BitVec.setWidth_eq_extractLsb' (show 32 ≤ 66 by omega), BitVec.toNat_setWidth,
    BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (show (2 : Nat) ^ 32 ∣ 2 ^ 66 by decide),
    hz, hz, BitVec.toNat_mul]

/- ---- 整型 wrapper 规约（mulPlacedSum 核心定理 + 选择规约复合） ---- -/

/-- MUL：低 32 位乘积（零扩展×零扩展，低位与符号无关） -/
theorem mul_wrap_mul (a b c : BitVec 32) :
    mulWrapOut mulFN_MUL a b c = a * b := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 a),
    mulSextZext, mulSextZext, mul_zext66_low32]

/-- MULH：64 位有符号乘积的高 32 位（bit 63:32） -/
theorem mul_wrap_mulh (a b c : BitVec 32) :
    mulWrapOut mulFN_MULH a b c
      = ((BitVec.signExtend 66 a) * (BitVec.signExtend 66 b)).extractLsb' 32 32 := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_sext33_corr0 a), mulSextSext, mulSextSext]

/-- MULHU：64 位无符号乘积的高 32 位 -/
theorem mul_wrap_mulhu (a b c : BitVec 32) :
    mulWrapOut mulFN_MULHU a b c
      = ((BitVec.zeroExtend 66 a) * (BitVec.zeroExtend 66 b)).extractLsb' 32 32 := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 a), mulSextZext, mulSextZext]

/-- 【Q1 主定理】MULHSU 按源码返回乘积【低】32 位（正确语义为高 32 位，
    即 ((sext a)·(zext b))(63,32)） -/
theorem mul_mulhsu_diverges (a b c : BitVec 32) :
    mulWrapOut mulFN_MULHSU a b c
      = ((BitVec.signExtend 66 a) * (BitVec.zeroExtend 66 b)).extractLsb' 0 32 := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_sext33_corr0 a), mulSextSext, mulSextZext]

/-- 【Q1 witness】存在 a,b 使源码输出 ≠ 正确高 32 位：a=b=0xFFFFFFFF 时
    源码输出 0x00000001（低 32 位），正确高 32 位为 0xFFFFFFFF -/
theorem mul_mulhsu_witness :
    ∃ a b : BitVec 32, mulWrapOut mulFN_MULHSU a b 0#32
      ≠ ((BitVec.signExtend 66 a) * (BitVec.zeroExtend 66 b)).extractLsb' 32 32 := by
  refine ⟨0xFFFFFFFF#32, 0xFFFFFFFF#32, ?_⟩
  rw [mul_mulhsu_diverges]
  native_decide

/-- MACC：vd = (vs1·vs2 + vd) 低 32 位（a·b + c；:201 加分支，:156-158 不换） -/
theorem mul_wrap_macc (a b c : BitVec 32) :
    mulWrapOut mulFN_MACC a b c = a * b + c := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 a),
    mulSextZext, mulSextZext, mul_zext66_low32]

/-- NMSAC：vd = (-(vs1·vs2) + vd) 低 32 位（c - a·b；:201 减分支，不换） -/
theorem mul_wrap_nmsac (a b c : BitVec 32) :
    mulWrapOut mulFN_NMSAC a b c = c - a * b := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 a),
    mulSextZext, mulSextZext, mul_zext66_low32]

/-- MADD：vd = (vd·vs2 + vs1) 低 32 位（c·b + a；:156-158 换 c/a，:201 加分支） -/
theorem mul_wrap_madd (a b c : BitVec 32) :
    mulWrapOut mulFN_MADD a b c = c * b + a := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 c),
    mulSextZext, mulSextZext, mul_zext66_low32]

/-- NMSUB：vd = (-(vd·vs2) + vs1) 低 32 位（a - c·b；:156-158 换 c/a，:201 减分支） -/
theorem mul_wrap_nmsub (a b c : BitVec 32) :
    mulWrapOut mulFN_NMSUB a b c = a - c * b := by
  simp [mulWrapOut, mulIn1, mulIn3, mulA33, mulB33, mulRes, mulMacOut, mulIsMAC,
    mulFN_MUL, mulFN_MULH, mulFN_MULHU, mulFN_MULHSU, mulFN_MACC, mulFN_NMSAC,
    mulFN_MADD, mulFN_NMSUB]
  rw [mulPlacedSum_eq_of_corr0 _ _ (mul_zext33_corr0 c),
    mulSextZext, mulSextZext, mul_zext66_low32]

/- ========================================================================= -/
/- 7. 流水线对齐模型（latency=2；HasPipelineReg mul_utils.scala:38-63）        -/
/-    自由流动（D3）。len=33 时数据通路仅 columns_reg 一级寄存器（D2）：       -/
/-    func=ctrlVec(1)（:200，打 1 拍）与 cVec(1)、result 同属第 1 级；        -/
/-    res 经 PipelineReg(2)（:206）与 ctrlVec(2)/maskVec(2)/valids(2) 同属    -/
/-    第 2 级——ctrl 与数据同一指令，对齐正确（:200 疑点否定，见 Q2 的         -/
/-    len ≥ 64 反例条件）。                                                  -/
/- ========================================================================= -/

/-- 输入（每拍；ctrl 只保留 alu_fn(4,0)，D8） -/
structure MulPipeIn where
  func : BitVec 5
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  valid : Bool

/-- 流水线状态：第 1 级（columns_reg/ctrlVec(1)/cVec(1)，使能 = in.valid）
    与第 2 级（ctrlVec(2)/outReg/valids(2)，使能 = 第 1 级 valid） -/
structure MulPipeState where
  v1 : Bool
  f1 : BitVec 5
  a1 : BitVec 33
  b1 : BitVec 33
  c1 : BitVec 32
  v2 : Bool
  f2 : BitVec 5
  r2 : BitVec 32

/-- 单拍转移（RegEnable 保持语义：使能关断时保持） -/
def mulPipeStep (prod : BitVec 33 → BitVec 33 → BitVec 66)
    (st : MulPipeState) (inp : MulPipeIn) : MulPipeState :=
  { v1 := inp.valid
  , f1 := if inp.valid then inp.func else st.f1
  , a1 := if inp.valid then mulA33 inp.func (mulIn1 inp.func inp.a inp.c) else st.a1
  , b1 := if inp.valid then mulB33 inp.func inp.b else st.b1
  , c1 := if inp.valid then mulIn3 inp.func inp.a inp.c else st.c1
  , v2 := st.v1
  , f2 := if st.v1 then st.f1 else st.f2
  , r2 := if st.v1
      then mulRes st.f1 (prod st.a1 st.b1) (mulMacOut st.f1 (prod st.a1 st.b1) st.c1)
      else st.r2 }

/-- 对齐定理：指令 X 进入两拍后，out.valid=1、out.ctrl=X 的 func、
    out.result = X 自己的 func/操作数/乘积的选择结果（prod 为抽象乘积函数，
    实际为 mulPlacedSum）。即 :200 的 func 打拍与数据通路同指令对齐。 -/
theorem mulPipe_two_cycles (prod : BitVec 33 → BitVec 33 → BitVec 66)
    (st : MulPipeState) (x y : MulPipeIn) (hx : x.valid = true) :
    let st2 := mulPipeStep prod (mulPipeStep prod st x) y
    st2.v2 = true ∧ st2.f2 = x.func ∧
      st2.r2 = mulRes x.func
        (prod (mulA33 x.func (mulIn1 x.func x.a x.c)) (mulB33 x.func x.b))
        (mulMacOut x.func
          (prod (mulA33 x.func (mulIn1 x.func x.a x.c)) (mulB33 x.func x.b))
          (mulIn3 x.func x.a x.c)) := by
  simp [mulPipeStep, hx]

/- ========================================================================= -/
/- 8. 数值回归测试                                                           -/
/- ========================================================================= -/

/-- len=8 穷举（全 2^16 输入对，native_decide）：电路层 = 乘积 - 末行修正
    （修正项仅在末行窗 ∈ {4,5,6} 时非零，Q3；len=8 下该窗可达故必须保留） -/
theorem mul_dataModule8_exhaustive :
    ∀ a b : BitVec 8, mulDataModule a b
      = (BitVec.signExtend 16 a) * (BitVec.signExtend 16 b)
        - ((BitVec.zeroExtend 16 (mulT (mulWindow a 6))) <<< 6) := by
  native_decide

/-- len=8 穷举（修正为零的情形即真乘积；与上一式联立读） -/
theorem mul_dataModule8_exhaustive_corr0 :
    ∀ a b : BitVec 8, mulT (mulWindow a 6) = 0#2 →
      mulDataModule a b = (BitVec.signExtend 16 a) * (BitVec.signExtend 16 b) := by
  intro a b h
  rw [mul_dataModule8_exhaustive a b, h]
  bv_decide

-- len=33 定向向量（可达输入形态 = 32 位符号/零扩展，修正项恒零）
theorem mul_dm33_sext_intmin_intmax :
    mulDataModule (BitVec.signExtend 33 0x80000000#32) (BitVec.signExtend 33 0x7FFFFFFF#32)
      = (BitVec.signExtend 66 (BitVec.signExtend 33 0x80000000#32))
        * (BitVec.signExtend 66 (BitVec.signExtend 33 0x7FFFFFFF#32)) := by
  native_decide

theorem mul_dm33_sext_neg1_neg1 :
    mulDataModule (BitVec.signExtend 33 0xFFFFFFFF#32) (BitVec.signExtend 33 0xFFFFFFFF#32)
      = (BitVec.signExtend 66 (BitVec.signExtend 33 0xFFFFFFFF#32))
        * (BitVec.signExtend 66 (BitVec.signExtend 33 0xFFFFFFFF#32)) := by
  native_decide

theorem mul_dm33_sext_rand1 :
    mulDataModule (BitVec.signExtend 33 0x12345678#32) (BitVec.signExtend 33 0x7ABCDEF1#32)
      = (BitVec.signExtend 66 (BitVec.signExtend 33 0x12345678#32))
        * (BitVec.signExtend 66 (BitVec.signExtend 33 0x7ABCDEF1#32)) := by
  native_decide

theorem mul_dm33_sext_zext_witness :
    mulDataModule (BitVec.signExtend 33 0xFFFFFFFF#32) (BitVec.zeroExtend 33 0xFFFFFFFF#32)
      = (BitVec.signExtend 66 (BitVec.signExtend 33 0xFFFFFFFF#32))
        * (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xFFFFFFFF#32)) := by
  native_decide

theorem mul_dm33_sext_zext_intmin :
    mulDataModule (BitVec.signExtend 33 0x80000000#32) (BitVec.zeroExtend 33 0xFFFFFFFF#32)
      = (BitVec.signExtend 66 (BitVec.signExtend 33 0x80000000#32))
        * (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xFFFFFFFF#32)) := by
  native_decide

theorem mul_dm33_zext_max_max :
    mulDataModule (BitVec.zeroExtend 33 0xFFFFFFFF#32) (BitVec.zeroExtend 33 0xFFFFFFFF#32)
      = (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xFFFFFFFF#32))
        * (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xFFFFFFFF#32)) := by
  native_decide

theorem mul_dm33_zext_intmin_intmin :
    mulDataModule (BitVec.zeroExtend 33 0x80000000#32) (BitVec.zeroExtend 33 0x80000000#32)
      = (BitVec.signExtend 66 (BitVec.zeroExtend 33 0x80000000#32))
        * (BitVec.signExtend 66 (BitVec.zeroExtend 33 0x80000000#32)) := by
  native_decide

theorem mul_dm33_zext_one_sext_intmin :
    mulDataModule (BitVec.zeroExtend 33 1#32) (BitVec.signExtend 33 0x80000000#32)
      = (BitVec.signExtend 66 (BitVec.zeroExtend 33 1#32))
        * (BitVec.signExtend 66 (BitVec.signExtend 33 0x80000000#32)) := by
  native_decide

theorem mul_dm33_zero :
    mulDataModule (BitVec.zeroExtend 33 0#32) (BitVec.signExtend 33 0xDEADBEEF#32)
      = 0#66 := by
  native_decide

theorem mul_dm33_zext_rand2 :
    mulDataModule (BitVec.zeroExtend 33 0xDEADBEEF#32) (BitVec.zeroExtend 33 0xCAFEBABE#32)
      = (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xDEADBEEF#32))
        * (BitVec.signExtend 66 (BitVec.zeroExtend 33 0xCAFEBABE#32)) := by
  native_decide

-- len=33 电路层 = 算术层 抽查（placedSum 已全证，电路层此处为测试覆盖，见报告降级说明）
theorem mul_dm33_eq_placedSum_spot1 :
    mulDataModule (BitVec.signExtend 33 0x80000000#32) (BitVec.signExtend 33 0x7FFFFFFF#32)
      = mulPlacedSum (BitVec.signExtend 33 0x80000000#32) (BitVec.signExtend 33 0x7FFFFFFF#32) := by
  native_decide

theorem mul_dm33_eq_placedSum_spot2 :
    mulDataModule (BitVec.zeroExtend 33 0xFFFFFFFF#32) (BitVec.signExtend 33 0x80000000#32)
      = mulPlacedSum (BitVec.zeroExtend 33 0xFFFFFFFF#32) (BitVec.signExtend 33 0x80000000#32) := by
  native_decide

theorem mul_dm33_eq_placedSum_spot3 :
    mulDataModule (BitVec.signExtend 33 0xFFFFFFFF#32) (BitVec.zeroExtend 33 0xFFFFFFFF#32)
      = mulPlacedSum (BitVec.signExtend 33 0xFFFFFFFF#32) (BitVec.zeroExtend 33 0xFFFFFFFF#32) := by
  native_decide

-- wrapper 具体向量（全部经过 mulPlacedSum 算术层求值）
example : mulWrapOut mulFN_MUL 6#32 7#32 0#32 = 42#32 := by native_decide
example : mulWrapOut mulFN_MUL 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32 = 1#32 := by native_decide
example : mulWrapOut mulFN_MULH 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32 = 0#32 := by native_decide
example : mulWrapOut mulFN_MULH 0x80000000#32 0x7FFFFFFF#32 0#32 = 0xC0000000#32 := by
  native_decide
example : mulWrapOut mulFN_MULHU 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32 = 0xFFFFFFFE#32 := by
  native_decide
-- Q1 现状钉死：MULHSU 返回低 32 位（正确高 32 位为 0xFFFFFFFF）
example : mulWrapOut mulFN_MULHSU 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32 = 1#32 := by native_decide
example : mulWrapOut mulFN_MULHSU 0x80000000#32 0xFFFFFFFF#32 0#32 = 0x80000000#32 := by
  native_decide
-- MAC 四形态（语义见 mul_wrap_macc/nmsac/madd/nmsub）
example : mulWrapOut mulFN_MACC 3#32 4#32 5#32 = 17#32 := by native_decide
example : mulWrapOut mulFN_NMSAC 3#32 4#32 5#32 = 0xFFFFFFF9#32 := by native_decide
example : mulWrapOut mulFN_MADD 5#32 4#32 3#32 = 17#32 := by native_decide
example : mulWrapOut mulFN_NMSUB 5#32 4#32 3#32 = 0xFFFFFFF9#32 := by native_decide
example : mulWrapOut mulFN_MACC 0xFFFFFFFF#32 0xFFFFFFFF#32 1#32 = 2#32 := by native_decide

/- ========================================================================= -/
/- 9. 公理审计                                                               -/
/- ========================================================================= -/

#print axioms mulC53_spec
#print axioms mulFidRow0
#print axioms mulFidMid
#print axioms mulFidLast
#print axioms mulBaseRow0
#print axioms mulBaseMid
#print axioms mulBaseLast
#print axioms mulTelescope
#print axioms mulWindow32_eq6
#print axioms mulCorr_window32_eq0
#print axioms mul_sext33_corr0
#print axioms mul_zext33_corr0
#print axioms mulPlacedSum_eq
#print axioms mulPlacedSum_eq_of_corr0
#print axioms mulPlacedSum_quirk
#print axioms mulRes_mulhsu
#print axioms mul_mulhsu_diverges
#print axioms mul_mulhsu_witness
#print axioms mul_wrap_macc
#print axioms mul_wrap_nmsub
#print axioms mulPipe_two_cycles
#print axioms mul_dataModule8_exhaustive
#print axioms mul_dm33_sext_zext_witness

end Ventus.Arith

