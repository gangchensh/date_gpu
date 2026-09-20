/- ========================================================================= -/
/-                      Spec/FloatSpec.lean                                  -/
/-  IEEE 754 浮点语义位级规约（doc/17 §3 路径 A 的落点）                        -/
/-                                                                           -/
/-  目的：把契约登记册（Contracts.lean）中 H-FPU 族黑盒假设从"行为假设"        -/
/-  收窄为"满足可逐条核对的位级规约"。本文件为纯规约层：不建模任何硬件          -/
/-  流水线，只定义"正确的 IEEE 754 结果应该是什么位模式"。                     -/
/-                                                                           -/
/-  ---------------- H-FPU 族契约收窄对应表 ----------------                  -/
/-  H-FPU-1（ctrl 透传，execution.scala:746-804）：控制面假设，与数值无关，     -/
/-    本规约不收窄（维持 axiomatic，仍由 ExeSFU 侧消费形态约束）。              -/
/-  H-FPU-2（Decoupled/Irrevocable 握手）：时序面假设，本规约不收窄。           -/
/-  H-FPU-3（FPU 数值正确性黑盒）：【核心收窄】收窄为第 9 节的                  -/
/-    specFpuBinOk / specFpuFmaOk / specFpuCmpOk / specFpuCvtOk /             -/
/-    specFpuClassOk 族——"VectorFPU 的数值输出等于本文件位级规约函数的值"。     -/
/-    假设内容由此变成可逐条审计的 Prop（对任意输入、任意合法舍入模式）。        -/
/-  H-FPU-4（result 取低 32 位，execution.scala:785）：execution.scala:758      -/
/-    实例化 VectorFPU(8, 24)，len = 8+24 = 32（定理 fsF32_len）——f32 全宽      -/
/-    即 32 位，(31,0) 截取对 f32 运算为恒等；该条的"真实宽度待查"疑点由此      -/
/-    关闭（fudian 的 len = expWidth+precision，见 fudian/FPU.scala:9,52）。    -/
/-  H-FDIV-1（FloatDivSqrt 黑盒，FloatDivSqrt.scala:303,342）：数值部分收窄     -/
/-    为 specFdivDivOk / specFdivSqrtOk；该模块 f32-only（FloatDivSqrt.scala:   -/
/-    114-115 取 Float32.expWidth/fracWidth）。延迟/反压稳定部分维持原状。      -/
/-                                                                           -/
/-  ---------------- 舍入模式（核实结论，修正"Ventus 只用 RNE"的说法） -------  -/
/-  fudian 支持 RNE/RTZ/RDN/RUP/RMM 五种（fudian/package.scala:6-10，编码       -/
/-  0..4）。Ventus 的 FPU rm 端口来自 per-warp CSR（pipe.scala:403-408），      -/
/-  且 force_rm_rtz 可强制 RTZ——舍入模式是运行时可变的，并非只有 RNE。         -/
/-  故本规约对全部五种模式参数化（FsRM），编码与 fudian 一致。                  -/
/-                                                                           -/
/-  ---------------- 格式覆盖 ----------------                                -/
/-  规约对任意 FsFormat（expWidth, precision，fudian 惯例 precision 含隐藏位）   -/
/-  参数化；实例 fsF16(5,11) / fsF32(8,24) / fsF64(11,53)。Ventus 实际例化       -/
/-  仅 f32（execution.scala:758 的 VectorFPU(8,24)；FloatDivSqrt f32-only）；    -/
/-  测试以 f32 全覆盖为主，f16/f64 各配代表性数值锚点（转换/加法/sqrt）。        -/
/-                                                                           -/
/-  ---------------- 测试锚点来源（I-18 教训：独立于实现推导） ---------------  -/
/-  所有期望值由 python3 标准库独立推导并交叉验证（2026-09-10）：               -/
/-  (1) struct 模块的 IEEE 半/单/双精度硬件编码（'e'/'f'/'d'）；                -/
/-  (2) fractions.Fraction 精确有理数 + 独立编写的 RNE 舍入器（与本文件          -/
/-      算法独立实现，两者对全部舍入锚点一致）；                                -/
/-  (3) IEEE 754-2019 / RISC-V F 扩展文献标准值（如 INT_MAX→f32=0x4F000000、    -/
/-      f16 65520 平局舍入到 inf、fclass 位定义、FToI 饱和语义）。              -/
/-  推导过程中已抓到一次先入为主错误（0.1f+0.2f 的 f32 和是 0x3E99999A 而        -/
/-  非凭印象的 0x3EAAAAAB）——锚点独立推导确实必要。                            -/
/-                                                                           -/
/-  数值测试一律 native_decide（Nat 大数运算内核归约慢）；位结构测试用           -/
/-  decide。native_decide 定理带每定理私有的 …._native.native_decide.ax_*        -/
/-  信任公理（Lean 4.31），见文件尾审计块。                                    -/
/- ========================================================================= -/

namespace Ventus.Spec

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 格式（fudian FloatPoint 惯例：precision 含隐藏位，len = expWidth+precision） -/
/- ========================================================================= -/

/-- IEEE 754 二进制格式参数（与 fudian `FloatPoint(expWidth, precision)` 对应；
    fudian/package.scala:26 的 `sigWidth = precision - 1`） -/
structure FsFormat where
  /-- 指数域宽度 -/
  expWidth : Nat
  /-- 精度（含隐藏位）；尾数域宽度 = precision - 1 -/
  precision : Nat
deriving DecidableEq, Repr

namespace FsFormat

/-- 位宽（fudian FPU.scala:9 的 `len = expWidth + precision`） -/
def len (f : FsFormat) : Nat := f.expWidth + f.precision
/-- 尾数域宽度 -/
def sigWidth (f : FsFormat) : Nat := f.precision - 1
/-- 指数偏置（fudian/package.scala:51-53 expBias = 2^(expWidth-1) - 1） -/
def bias (f : FsFormat) : Nat := 2 ^ (f.expWidth - 1) - 1
/-- 最小正规格化无偏指数 emin = 1 - bias -/
def emin (f : FsFormat) : Int := 1 - (f.bias : Int)
/-- 最大正规格化无偏指数 emax = bias -/
def emax (f : FsFormat) : Int := (f.bias : Int)

end FsFormat

/-- IEEE 754 binary16 -/
def fsF16 : FsFormat := ⟨5, 11⟩
/-- IEEE 754 binary32（Ventus FPU 唯一例化格式，execution.scala:758） -/
def fsF32 : FsFormat := ⟨8, 24⟩
/-- IEEE 754 binary64 -/
def fsF64 : FsFormat := ⟨11, 53⟩

/-- 【H-FPU-4 收窄支撑】f32 全宽 = 32 位，故 execution.scala:785 的 (31,0)
    截取对 f32 结果为恒等 -/
theorem fsF32_len : fsF32.len = 32 := rfl
theorem fsF16_len : fsF16.len = 16 := rfl
theorem fsF64_len : fsF64.len = 64 := rfl

/- ========================================================================= -/
/- 2. 舍入模式（编码与 fudian/package.scala:6-10 一致）                        -/
/- ========================================================================= -/

/-- IEEE 754 舍入模式：RNE 最近偶 / RTZ 向零 / RDN 向负无穷 / RUP 向正无穷 /
    RMM 最近远离零（fudian RMM，编码 4） -/
inductive FsRM where
  | RNE
  | RTZ
  | RDN
  | RUP
  | RMM
deriving DecidableEq, Repr, BEq

/-- 模式 → fudian 3 位编码 -/
def FsRM.toBits : FsRM → BitVec 3
  | .RNE => 0#3
  | .RTZ => 1#3
  | .RDN => 2#3
  | .RUP => 3#3
  | .RMM => 4#3

/-- fudian 3 位编码 → 模式（5-7 为保留编码，返回 none） -/
def fsRMOfBits (b : BitVec 3) : Option FsRM :=
  match b.toNat with
  | 0 => some .RNE
  | 1 => some .RTZ
  | 2 => some .RDN
  | 3 => some .RUP
  | 4 => some .RMM
  | _ => none

/- ========================================================================= -/
/- 3. 字段提取与组装（Nat 运算实现，全可计算）                                  -/
/- ========================================================================= -/

/-- 符号位 -/
def fsSignB (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (x.toNat >>> (fmt.len - 1)) = 1
/-- 指数域（无偏置原始值） -/
def fsExpField (fmt : FsFormat) (x : BitVec fmt.len) : Nat :=
  (x.toNat >>> fmt.sigWidth) % 2 ^ fmt.expWidth
/-- 尾数域 -/
def fsFrac (fmt : FsFormat) (x : BitVec fmt.len) : Nat :=
  x.toNat % 2 ^ fmt.sigWidth
/-- 组装：sign ++ exp ++ frac（fudian FloatPoint.fromUInt 的逆，
    package.scala:57-62） -/
def fsPack (fmt : FsFormat) (s : Bool) (e f : Nat) : BitVec fmt.len :=
  BitVec.ofNat fmt.len ((s.toNat * 2 ^ fmt.expWidth + e) * 2 ^ fmt.sigWidth + f)

/- ========================================================================= -/
/- 4. 特殊值判定与构造（对应 fudian FPDecodeBundle，package.scala:31-48）       -/
/- ========================================================================= -/

/-- 指数域全 1 的原始值 -/
def fsExpAllOnes (fmt : FsFormat) : Nat := 2 ^ fmt.expWidth - 1

def fsIsZero (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (fsExpField fmt x == 0) && (fsFrac fmt x == 0)
def fsIsSubnormal (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (fsExpField fmt x == 0) && (fsFrac fmt x != 0)
def fsIsNormal (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (fsExpField fmt x != 0) && (fsExpField fmt x != fsExpAllOnes fmt)
def fsIsInf (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (fsExpField fmt x == fsExpAllOnes fmt) && (fsFrac fmt x == 0)
def fsIsNaN (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  (fsExpField fmt x == fsExpAllOnes fmt) && (fsFrac fmt x != 0)
/-- quiet NaN：尾数最高位 1 -/
def fsIsQNaN (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  fsIsNaN fmt x && (fsFrac fmt x ≥ 2 ^ (fmt.sigWidth - 1))
/-- signaling NaN：尾数最高位 0 且非零 -/
def fsIsSNaN (fmt : FsFormat) (x : BitVec fmt.len) : Bool :=
  fsIsNaN fmt x && (fsFrac fmt x < 2 ^ (fmt.sigWidth - 1))

/-- 规范 NaN（fudian defaultNaN，package.scala:64-69：符号 0、指数全 1、
    尾数最高位 1 其余 0；f32 = 0x7FC00000） -/
def fsCanonNaN (fmt : FsFormat) : BitVec fmt.len :=
  fsPack fmt false (fsExpAllOnes fmt) (2 ^ (fmt.sigWidth - 1))
/-- ±∞ -/
def fsInfBits (fmt : FsFormat) (s : Bool) : BitVec fmt.len :=
  fsPack fmt s (fsExpAllOnes fmt) 0
/-- 最大正规格化数（指数域全 1 减 1，尾数全 1） -/
def fsMaxNormBits (fmt : FsFormat) (s : Bool) : BitVec fmt.len :=
  fsPack fmt s (fsExpAllOnes fmt - 1) (2 ^ fmt.sigWidth - 1)
/-- ±0 -/
def fsZeroBits (fmt : FsFormat) (s : Bool) : BitVec fmt.len :=
  fsPack fmt s 0 0
/-- 符号位翻转（fneg 的位级语义） -/
def fsNegBits (fmt : FsFormat) (x : BitVec fmt.len) : BitVec fmt.len :=
  fsPack fmt (!(fsSignB fmt x)) (fsExpField fmt x) (fsFrac fmt x)

/- ========================================================================= -/
/- 5. 有限值解码为精确有理数：(符号, p, q) 表示值 = (-1)^s · (p/q)，p,q 为     -/
/-    Nat 且 q > 0；零表示为 (s, 0, 1)。NaN/Inf 输入给出无意义值（调用方先     -/
/-    过滤），不在本函数的规约范围内。                                         -/
/- ========================================================================= -/

/-- 有限浮点值 → (符号, 分子, 分母)。次正规：exp=emin、无隐藏位；
    正规格化：sig = 2^sigWidth + frac、exp = expField - bias -/
def fsDecodeFin (fmt : FsFormat) (x : BitVec fmt.len) : Bool × Nat × Nat :=
  let s := fsSignB fmt x
  let ef := fsExpField fmt x
  let fr := fsFrac fmt x
  if (ef == 0) && (fr == 0) then (s, 0, 1)
  else
    let sig := if ef == 0 then fr else 2 ^ fmt.sigWidth + fr
    let e : Int := if ef == 0
      then fmt.emin - (fmt.sigWidth : Int)
      else (ef : Int) - (fmt.bias : Int) - (fmt.sigWidth : Int)
    if e ≥ 0 then (s, sig * 2 ^ e.toNat, 1) else (s, sig, 2 ^ (-e).toNat)

/-- (符号, p, q) → Rat 值 -/
def fsFinRat (s : Bool) (p q : Nat) : Rat :=
  let v : Rat := (p : Rat) / (q : Rat)
  if s then -v else v

/-- 有限值严格小于（不经过 Rat，直接交叉相乘；调用方保证输入均为有限值
    且已排除"双方均零"的情形） -/
def fsFinLt (sa : Bool) (pa qa : Nat) (sb : Bool) (pb qb : Nat) : Bool :=
  if sa != sb then sa
  else if sa then (pb * qa < pa * qb)   -- 同为负：|b| < |a| ⟺ a < b
  else (pa * qb < pb * qa)

/-- 有限值小于等于 -/
def fsFinLeq (sa : Bool) (pa qa : Nat) (sb : Bool) (pb qb : Nat) : Bool :=
  if sa != sb then sa
  else if sa then (pb * qa ≤ pa * qb)
  else (pa * qb ≤ pb * qa)

/- ========================================================================= -/
/- 6. 核心舍入：正有理数 p/q 按模式 rm、符号 s 舍入到格式 fmt                   -/
/- ========================================================================= -/

/-- floor(log2(p/q))（要求 p,q > 0）。e0 = log2⌊p⌋ - log2⌊q⌋ 与答案至多差 1，
    用一次比较定案 -/
def fsLog2Floor (p q : Nat) : Int :=
  let e0 : Int := (Nat.log2 p : Int) - (Nat.log2 q : Int)
  let ge : Bool :=
    if e0 ≥ 0 then (p ≥ q * 2 ^ e0.toNat)
    else (p * 2 ^ (-e0).toNat ≥ q)
  if ge then e0 else e0 - 1

/-- 有理数 N/D 按模式舍入到整数（neg = 真值符号，RDN/RUP 方向由此定） -/
def fsRoundDiv (rm : FsRM) (neg : Bool) (N D : Nat) : Nat :=
  let q := N / D
  let r := N % D
  match rm with
  | .RTZ => q
  | .RDN => if neg && (r > 0) then q + 1 else q
  | .RUP => if (!neg) && (r > 0) then q + 1 else q
  | .RNE => if (r * 2 > D) || ((r * 2 == D) && (q % 2 == 1)) then q + 1 else q
  | .RMM => if r * 2 ≥ D then q + 1 else q

/-- 把"无偏指数 eT、precision 位有效数字 n"组装为位模式：
    进位（n = 2^precision）→ 指数 +1；上溢按模式给 inf 或最大正规格化数
    （IEEE 754-2019 §7.4）；否则按正规格化/次正规编码（n < 2^(precision-1)
    即次正规，n = 0 即带符号零） -/
def fsAssemble (fmt : FsFormat) (rm : FsRM) (s : Bool) (eT : Int) (n : Nat) :
    BitVec fmt.len :=
  let (eT, n) := if n ≥ 2 ^ fmt.precision then (eT + 1, n / 2) else (eT, n)
  if eT > fmt.emax then
    match rm with
    | .RNE | .RMM => fsInfBits fmt s
    | .RTZ => fsMaxNormBits fmt s
    | .RDN => if s then fsInfBits fmt s else fsMaxNormBits fmt s
    | .RUP => if s then fsMaxNormBits fmt s else fsInfBits fmt s
  else if n ≥ 2 ^ (fmt.precision - 1) then
    fsPack fmt s (eT + fmt.bias).toNat (n - 2 ^ (fmt.precision - 1))
  else
    fsPack fmt s 0 n

/-- 核心舍入函数：值 (-1)^s · (p/q) 舍入到 fmt（q > 0；p = 0 → 带符号零）。
    次正规下溢与上溢均在 fsAssemble 内按 IEEE 处理 -/
def fsRoundMag (fmt : FsFormat) (rm : FsRM) (s : Bool) (p q : Nat) :
    BitVec fmt.len :=
  if p == 0 then fsZeroBits fmt s
  else
    let e := fsLog2Floor p q
    let eT := max e fmt.emin
    let sh := eT - ((fmt.precision : Int) - 1)
    let (N, D) :=
      if sh ≥ 0 then (p, q * 2 ^ sh.toNat) else (p * 2 ^ (-sh).toNat, q)
    fsAssemble fmt rm s eT (fsRoundDiv rm s N D)

/-- Rat 舍入入口（r = 0 → +0，精确零的符号规则由运算层处理） -/
def fsRoundRat (fmt : FsFormat) (rm : FsRM) (r : Rat) : BitVec fmt.len :=
  fsRoundMag fmt rm (r < 0) r.num.natAbs r.den

/-- 整数平方根（core 无 Nat.sqrt，自实现）：二分搜索，不变式
    lo² ≤ n < hi²，fuel 200 对 n < 2¹²⁸ 足够（每次区间减半）。
    正确性由第 10.6 节数值锚点背书（含次正规输入、f64 √2） -/
def fsIsqrtFuel (n lo hi : Nat) : Nat → Nat
  | 0 => lo
  | k + 1 =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid ≤ n then fsIsqrtFuel n mid hi k
      else fsIsqrtFuel n lo mid k

/-- ⌊√n⌋ -/
def fsIsqrt (n : Nat) : Nat :=
  fsIsqrtFuel n 0 (2 ^ (Nat.log2 n / 2 + 1)) 200

/-- sqrt 的精确舍入：对 p/q > 0 求 round(√(p/q))。
    w = (p/q) / 2^(2·sh) 完全以整数对 (wn, wd) 表示，n0 = ⌊√w⌋ 由
    fsIsqrt(wn/wd) 精确给出；RNE/RMM 的中点比较 4·wn ? (2·n0+1)²·wd 精确 -/
def fsSqrtRound (fmt : FsFormat) (rm : FsRM) (p q : Nat) : BitVec fmt.len :=
  let e := fsLog2Floor p q
  let eS := e.ediv 2
  let eT := max eS fmt.emin
  let sh := eT - ((fmt.precision : Int) - 1)
  let sh2 := 2 * sh
  let (wn, wd) :=
    if sh2 ≥ 0 then (p, q * 2 ^ sh2.toNat) else (p * 2 ^ (-sh2).toNat, q)
  let n0 := fsIsqrt (wn / wd)
  let exact := (n0 * n0 * wd == wn)
  let up : Bool :=
    match rm with
    | .RTZ => false
    | .RDN => false
    | .RUP => !exact
    | .RNE => (4 * wn > (2 * n0 + 1) ^ 2 * wd) ||
              ((4 * wn == (2 * n0 + 1) ^ 2 * wd) && (n0 % 2 == 1))
    | .RMM => 4 * wn ≥ (2 * n0 + 1) ^ 2 * wd
  fsAssemble fmt rm false eT (if up then n0 + 1 else n0)

/- ========================================================================= -/
/- 7. 运算规约（位级精确；特殊值优先，有限路径 = 精确实数结果一次舍入）          -/
/- ========================================================================= -/

/-- IEEE 754 加法（含全部特殊值；异号精确零：RDN 给 -0，其余 +0） -/
def fsAdd (fmt : FsFormat) (rm : FsRM) (a b : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then fsCanonNaN fmt
  else if fsIsInf fmt a && fsIsInf fmt b then
    if sa = sb then fsInfBits fmt sa else fsCanonNaN fmt
  else if fsIsInf fmt a then fsInfBits fmt sa
  else if fsIsInf fmt b then fsInfBits fmt sb
  else if (pa == 0) && (pb == 0) then
    if sa = sb then fsZeroBits fmt sa else fsZeroBits fmt (rm == .RDN)
  else
    let r := fsFinRat sa pa qa + fsFinRat sb pb qb
    if r == 0 then fsZeroBits fmt (rm == .RDN) else fsRoundRat fmt rm r

/-- IEEE 754 减法 = 加符号翻转后的操作数 -/
def fsSub (fmt : FsFormat) (rm : FsRM) (a b : BitVec fmt.len) : BitVec fmt.len :=
  fsAdd fmt rm a (fsNegBits fmt b)

/-- IEEE 754 乘法 -/
def fsMul (fmt : FsFormat) (rm : FsRM) (a b : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then fsCanonNaN fmt
  else if (fsIsInf fmt a && (pb == 0)) || (fsIsInf fmt b && (pa == 0)) then
    fsCanonNaN fmt
  else if fsIsInf fmt a || fsIsInf fmt b then fsInfBits fmt (xor sa sb)
  else if (pa == 0) || (pb == 0) then fsZeroBits fmt (xor sa sb)
  else fsRoundRat fmt rm (fsFinRat sa pa qa * fsFinRat sb pb qb)

/-- IEEE 754 除法（x/0 = ±inf 见 IEEE §7.3；0/0、inf/inf = NaN） -/
def fsDiv (fmt : FsFormat) (rm : FsRM) (a b : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then fsCanonNaN fmt
  else if fsIsInf fmt a && fsIsInf fmt b then fsCanonNaN fmt
  else if fsIsInf fmt a then fsInfBits fmt (xor sa sb)
  else if fsIsInf fmt b then fsZeroBits fmt (xor sa sb)
  else if pb == 0 then
    if pa == 0 then fsCanonNaN fmt else fsInfBits fmt (xor sa sb)
  else if pa == 0 then fsZeroBits fmt (xor sa sb)
  else fsRoundRat fmt rm (fsFinRat sa pa qa / fsFinRat sb pb qb)

/-- IEEE 754 平方根（-0 → -0；负非零 → 规范 NaN；+inf → +inf） -/
def fsSqrt (fmt : FsFormat) (rm : FsRM) (a : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  if fsIsNaN fmt a then fsCanonNaN fmt
  else if sa && (pa != 0) then fsCanonNaN fmt
  else if fsIsInf fmt a then fsInfBits fmt false
  else if pa == 0 then fsZeroBits fmt sa
  else fsSqrtRound fmt rm pa qa

/-- 融合乘加族公共核：negMul = false 为 a·b+c（fmadd/fmsub 对 c 取负），
    true 为 -(a·b)+c（fnmadd/fnmsub 再对 c 取负）。单次舍入（fused）。
    精确零符号：乘积与加数同号取该号，异号 RDN 给 -0 其余 +0 -/
def fsFmaGen (fmt : FsFormat) (rm : FsRM) (negMul : Bool)
    (a b c : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  let (sc, pc, qc) := fsDecodeFin fmt c
  let ps := xor (xor sa sb) negMul
  if fsIsNaN fmt a || fsIsNaN fmt b || fsIsNaN fmt c then fsCanonNaN fmt
  else if (fsIsInf fmt a && (pb == 0)) || (fsIsInf fmt b && (pa == 0)) then
    fsCanonNaN fmt
  else if fsIsInf fmt a || fsIsInf fmt b then
    if fsIsInf fmt c && (sc != ps) then fsCanonNaN fmt else fsInfBits fmt ps
  else if fsIsInf fmt c then fsInfBits fmt sc
  else
    let r := fsFinRat ps (pa * pb) (qa * qb) + fsFinRat sc pc qc
    if r == 0 then
      if ps = sc then fsZeroBits fmt ps else fsZeroBits fmt (rm == .RDN)
    else fsRoundRat fmt rm r

/-- fmadd：a·b + c -/
def fsFmadd (fmt : FsFormat) (rm : FsRM) (a b c : BitVec fmt.len) : BitVec fmt.len :=
  fsFmaGen fmt rm false a b c
/-- fmsub：a·b - c -/
def fsFmsub (fmt : FsFormat) (rm : FsRM) (a b c : BitVec fmt.len) : BitVec fmt.len :=
  fsFmaGen fmt rm false a b (fsNegBits fmt c)
/-- fnmadd：-(a·b) + c -/
def fsFnmadd (fmt : FsFormat) (rm : FsRM) (a b c : BitVec fmt.len) : BitVec fmt.len :=
  fsFmaGen fmt rm true a b c
/-- fnmsub：-(a·b) - c -/
def fsFnmsub (fmt : FsFormat) (rm : FsRM) (a b c : BitVec fmt.len) : BitVec fmt.len :=
  fsFmaGen fmt rm true a b (fsNegBits fmt c)

/-- IEEE minNum / RISC-V fmin：双 NaN → 规范 NaN；单 NaN → 另一个；
    -0 < +0 -/
def fsMin (fmt : FsFormat) (a b : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a && fsIsNaN fmt b then fsCanonNaN fmt
  else if fsIsNaN fmt a then b
  else if fsIsNaN fmt b then a
  else if fsIsInf fmt a then (if sa then a else b)
  else if fsIsInf fmt b then (if sb then b else a)
  else if (pa == 0) && (pb == 0) then (if sa then a else (if sb then b else a))
  else if fsFinLeq sa pa qa sb pb qb then a else b

/-- IEEE maxNum / RISC-V fmax：双 NaN → 规范 NaN；单 NaN → 另一个；
    +0 > -0 -/
def fsMax (fmt : FsFormat) (a b : BitVec fmt.len) : BitVec fmt.len :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a && fsIsNaN fmt b then fsCanonNaN fmt
  else if fsIsNaN fmt a then b
  else if fsIsNaN fmt b then a
  else if fsIsInf fmt a then (if sa then b else a)
  else if fsIsInf fmt b then (if sb then a else b)
  else if (pa == 0) && (pb == 0) then (if sa then (if sb then a else b) else a)
  else if fsFinLeq sa pa qa sb pb qb then b else a

/-- quiet 相等比较：任何 NaN → false；-0 = +0 -/
def fsFeq (fmt : FsFormat) (a b : BitVec fmt.len) : Bool :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then false
  else if (pa == 0) && (pb == 0) then true
  else if fsIsInf fmt a || fsIsInf fmt b then
    (fsIsInf fmt a && fsIsInf fmt b) && (sa = sb)
  else (sa == sb) && (pa * qb == pb * qa)

/-- quiet 小于比较：任何 NaN → false（RISC-V 的 NV 标志不在本规约范围） -/
def fsFlt (fmt : FsFormat) (a b : BitVec fmt.len) : Bool :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then false
  else if fsIsInf fmt a && fsIsInf fmt b then (sa && !sb)
  else if fsIsInf fmt a then sa
  else if fsIsInf fmt b then !sb
  else if (pa == 0) && (pb == 0) then false
  else fsFinLt sa pa qa sb pb qb

/-- quiet 小于等于比较 -/
def fsFle (fmt : FsFormat) (a b : BitVec fmt.len) : Bool :=
  let (sa, pa, qa) := fsDecodeFin fmt a
  let (sb, pb, qb) := fsDecodeFin fmt b
  if fsIsNaN fmt a || fsIsNaN fmt b then false
  else if fsIsInf fmt a && fsIsInf fmt b then (sa || !sb)
  -- 2026-09-12 修正（F-III-1，N1 试点发现）：原为 `sa = sb` 笔误——
  -- 唯一错误组合是 fle(-inf,+inf)：应 true 却给 false（(+inf,-inf) 原即正确）。
  -- 正确形式：双 inf 时 a≤b ⟺ sa || !sb（-inf≤一切；+inf 只 ≤+inf）。
  -- 见证：VentusF/FpuCmp.lean 的 fcIII1_witness（fudian/fpuv2 此处正确）
  else if fsIsInf fmt a then sa
  else if fsIsInf fmt b then !sb
  else if (pa == 0) && (pb == 0) then true
  else fsFinLeq sa pa qa sb pb qb

/-- RISC-V fclass 十位掩码：
    0:-inf 1:-norm 2:-sub 3:-0 4:+0 5:+sub 6:+norm 7:+inf 8:sNaN 9:qNaN -/
def fsClassify (fmt : FsFormat) (x : BitVec fmt.len) : BitVec 10 :=
  let s := fsSignB fmt x
  let i : Nat :=
    if fsIsSNaN fmt x then 8
    else if fsIsQNaN fmt x then 9
    else if fsIsInf fmt x then (if s then 0 else 7)
    else if fsIsZero fmt x then (if s then 3 else 4)
    else if fsIsSubnormal fmt x then (if s then 2 else 5)
    else (if s then 1 else 6)
  BitVec.ofNat 10 (2 ^ i)

/- ========================================================================= -/
/- 8. 转换规约                                                                 -/
/- ========================================================================= -/

/-- 浮点→浮点（NaN → 目标格式规范 NaN；inf → inf；有限值按 rm 一次舍入；
    扩宽自然精确） -/
def fsFToF (sf df : FsFormat) (rm : FsRM) (x : BitVec sf.len) : BitVec df.len :=
  let (s, p, q) := fsDecodeFin sf x
  if fsIsNaN sf x then fsCanonNaN df
  else if fsIsInf sf x then fsInfBits df s
  else fsRoundMag df rm s p q

/-- 整数→浮点（signed = true 按二进制补码解释） -/
def fsIToF (fmt : FsFormat) (rm : FsRM) (w : Nat) (signed : Bool)
    (x : BitVec w) : BitVec fmt.len :=
  let v : Int := if signed then x.toInt else (x.toNat : Int)
  if v ≥ 0 then fsRoundMag fmt rm false v.toNat 1
  else fsRoundMag fmt rm true v.natAbs 1

/-- 有理数按模式舍入到整数（RNE 平局到偶数整数） -/
def fsRoundToInt (rm : FsRM) (r : Rat) : Int :=
  let n := r.num
  let d : Int := (r.den : Int)
  let fl := n.ediv d
  let rem := n - d * fl
  match rm with
  | .RTZ => if n ≥ 0 then fl else (if rem > 0 then fl + 1 else fl)
  | .RDN => fl
  | .RUP => if rem > 0 then fl + 1 else fl
  | .RNE =>
    if (2 * rem > d) || ((2 * rem == d) && (fl % 2 == 1)) then fl + 1 else fl
  | .RMM =>
    -- 2026-09-15 修正（F-III-2，N2 发现）：平局且 n<0 时 fl+1 是"向零"，
    -- 与 IEEE 754 roundTiesToAway（远离零）矛盾——负平局应停在 fl（地板=
    -- 更远离零）。见证：VentusF/FpuCvt.lean 的 fcv_fiii2_witness
    -- （fsRoundToInt .RMM (-(5/2)) 原给 -2，fudian 硬件 -3 正确）
    if 2 * rem > d || ((2 * rem == d) && n ≥ 0) then fl + 1 else fl

/-- 浮点→整数（RISC-V fcvt 语义：按 rm 舍入后饱和到 [lo, hi]；
    NaN → hi；+inf → hi；-inf → lo） -/
def fsFToI (fmt : FsFormat) (rm : FsRM) (w : Nat) (signed : Bool)
    (x : BitVec fmt.len) : BitVec w :=
  let lo : Int := if signed then -(2 ^ (w - 1) : Int) else 0
  let hi : Int := if signed then (2 ^ (w - 1) : Int) - 1 else (2 ^ w : Int) - 1
  let (s, p, q) := fsDecodeFin fmt x
  if fsIsNaN fmt x then BitVec.ofInt w hi
  else if fsIsInf fmt x then BitVec.ofInt w (if s then lo else hi)
  else
    let t := fsRoundToInt rm (fsFinRat s p q)
    BitVec.ofInt w (min hi (max lo t))

/- ========================================================================= -/
/- 9. 契约收窄形态：H-FPU-3 / H-FDIV-1 的"数值正确"由此获得可逐条核对的        -/
/-    Prop 定义（对 f32——Ventus 唯一例化格式；任意合法舍入模式）               -/
/- ========================================================================= -/

/-- FPU 二元数值运算族 -/
inductive FsBinOp where
  | fadd
  | fsub
  | fmul
  | fmin
  | fmax
deriving DecidableEq, Repr

/-- 二元运算族的规约函数（fmin/fmax 无舍入模式参数） -/
def FsBinOp.apply (fmt : FsFormat) (rm : FsRM) : FsBinOp →
    BitVec fmt.len → BitVec fmt.len → BitVec fmt.len
  | .fadd => fsAdd fmt rm
  | .fsub => fsSub fmt rm
  | .fmul => fsMul fmt rm
  | .fmin => fun a _b => fsMin fmt a _b
  | .fmax => fun a _b => fsMax fmt a _b

/-- FPU 融合乘加族 -/
inductive FsFmaOp where
  | fmadd
  | fmsub
  | fnmadd
  | fnmsub
deriving DecidableEq, Repr

/-- 融合乘加族的规约函数 -/
def FsFmaOp.apply (fmt : FsFormat) (rm : FsRM) : FsFmaOp →
    BitVec fmt.len → BitVec fmt.len → BitVec fmt.len → BitVec fmt.len
  | .fmadd => fsFmadd fmt rm
  | .fmsub => fsFmsub fmt rm
  | .fnmadd => fsFnmadd fmt rm
  | .fnmsub => fsFnmsub fmt rm

/-- FPU 比较族 -/
inductive FsCmpOp where
  | feq
  | flt
  | fle
deriving DecidableEq, Repr

/-- 比较族的规约函数 -/
def FsCmpOp.apply (fmt : FsFormat) : FsCmpOp →
    BitVec fmt.len → BitVec fmt.len → Bool
  | .feq => fsFeq fmt
  | .flt => fsFlt fmt
  | .fle => fsFle fmt

/-- 【H-FPU-3 收窄形态·二元运算】f32 FPU 二元运算输出必须等于位级规约值 -/
def specFpuBinOk (op : FsBinOp) (rm : FsRM) (a b res : BitVec 32) : Prop :=
  res = op.apply fsF32 rm a b

/-- 【H-FPU-3 收窄形态·融合乘加】f32 FPU 融合乘加输出必须等于位级规约值 -/
def specFpuFmaOk (op : FsFmaOp) (rm : FsRM) (a b c res : BitVec 32) : Prop :=
  res = op.apply fsF32 rm a b c

/-- 【H-FPU-3 收窄形态·比较】f32 FPU 比较输出必须等于位级规约值 -/
def specFpuCmpOk (op : FsCmpOp) (a b : BitVec 32) (flag : Bool) : Prop :=
  flag = op.apply fsF32 a b

/-- 【H-FPU-3 收窄形态·格式转换】浮点互转输出必须等于位级规约值
    （f32↔f16/f64 由 sfmt/dfmt 实例化） -/
def specFpuFToFOk (sfmt dfmt : FsFormat) (rm : FsRM)
    (x : BitVec sfmt.len) (res : BitVec dfmt.len) : Prop :=
  res = fsFToF sfmt dfmt rm x

/-- 【H-FPU-3 收窄形态·整数转换】 -/
def specFpuIToFOk (rm : FsRM) (w : Nat) (signed : Bool)
    (x : BitVec w) (res : BitVec 32) : Prop :=
  res = fsIToF fsF32 rm w signed x

/-- 【H-FPU-3 收窄形态·浮点转整数】 -/
def specFpuFToIOk (rm : FsRM) (w : Nat) (signed : Bool)
    (x : BitVec 32) (res : BitVec w) : Prop :=
  res = fsFToI fsF32 rm w signed x

/-- 【H-FPU-3 收窄形态·classify】 -/
def specFpuClassOk (x : BitVec 32) (res : BitVec 10) : Prop :=
  res = fsClassify fsF32 x

/-- 【H-FDIV-1 收窄形态·除法】f32 除法输出必须等于位级规约值 -/
def specFdivDivOk (rm : FsRM) (a b res : BitVec 32) : Prop :=
  res = fsDiv fsF32 rm a b

/-- 【H-FDIV-1 收窄形态·平方根】f32 平方根输出必须等于位级规约值 -/
def specFdivSqrtOk (rm : FsRM) (a res : BitVec 32) : Prop :=
  res = fsSqrt fsF32 rm a

/- ========================================================================= -/
/- 10. 数值自洽测试族（期望值来源见文件头"测试锚点来源"；f32 全覆盖 +          -/
/-     f16/f64 代表性锚点）                                                    -/
/- ========================================================================= -/

section FsTests

-- ---------- 10.1 格式与位结构（decide） ----------
/-- f16/f32/f64 的 bias/emin/emax（IEEE 754-2019 表值） -/
theorem fsT_fmt_f32 : fsF32.bias = 127 ∧ fsF32.emin = -126 ∧ fsF32.emax = 127 := by
  decide
theorem fsT_fmt_f16 : fsF16.bias = 15 ∧ fsF16.emin = -14 ∧ fsF16.emax = 15 := by decide
theorem fsT_fmt_f64 : fsF64.bias = 1023 := by decide

/-- pack 1.0f = 0x3F800000（IEEE 文献标准值） -/
theorem fsT_pack_one : fsPack fsF32 false 127 0 = 0x3F800000#32 := by decide
/-- -5.0 = 0xC0A00000 的字段分解（独立手算：sign=1, exp=129, frac=0x200000） -/
theorem fsT_unpack_neg5 :
    fsSignB fsF32 0xC0A00000#32 = true ∧
    fsExpField fsF32 0xC0A00000#32 = 129 ∧
    fsFrac fsF32 0xC0A00000#32 = 0x200000 := by decide
/-- pack/extract 往返（0.1f = 0x3DCCCCCD，IEEE 文献标准值） -/
theorem fsT_pack_roundtrip :
    fsPack fsF32 (fsSignB fsF32 0x3DCCCCCD#32)
      (fsExpField fsF32 0x3DCCCCCD#32) (fsFrac fsF32 0x3DCCCCCD#32)
      = 0x3DCCCCCD#32 := by decide
/-- 舍入模式编码往返（fudian 编码 0..4） -/
theorem fsT_rm_roundtrip :
    [FsRM.RNE, .RTZ, .RDN, .RUP, .RMM].all
      (fun r => fsRMOfBits r.toBits == some r) = true := by decide
/-- 保留编码 7 无模式 -/
theorem fsT_rm_reserved : fsRMOfBits 7#3 = none := by decide
/-- 规范 NaN = fudian defaultNaN（f32 0x7FC00000 / f16 0x7E00 /
    f64 0x7FF8000000000000） -/
theorem fsT_canon_nan :
    fsCanonNaN fsF32 = 0x7FC00000#32 ∧
    fsCanonNaN fsF16 = 0x7E00#16 ∧
    fsCanonNaN fsF64 = 0x7FF8000000000000#64 := by decide

-- ---------- 10.2 classify（decide；RISC-V fclass 位定义） ----------
theorem fsT_classify :
    fsClassify fsF32 0xFF800000#32 = 0b0000000001#10 ∧   -- -inf → bit0
    fsClassify fsF32 0xBF800000#32 = 0b0000000010#10 ∧   -- -1.0 → bit1
    fsClassify fsF32 0x80400000#32 = 0b0000000100#10 ∧   -- -次正规 → bit2
    fsClassify fsF32 0x80000000#32 = 0b0000001000#10 ∧   -- -0 → bit3
    fsClassify fsF32 0x00000000#32 = 0b0000010000#10 ∧   -- +0 → bit4
    fsClassify fsF32 0x00000001#32 = 0b0000100000#10 ∧   -- +次正规 → bit5
    fsClassify fsF32 0x3F800000#32 = 0b0001000000#10 ∧   -- +1.0 → bit6
    fsClassify fsF32 0x7F800000#32 = 0b0010000000#10 ∧   -- +inf → bit7
    fsClassify fsF32 0x7F800001#32 = 0b0100000000#10 ∧   -- sNaN → bit8
    fsClassify fsF32 0x7FC00000#32 = 0b1000000000#10 := by decide  -- qNaN → bit9

-- ---------- 10.3 加法/减法（锚点：python3 Fraction 精确推导 + struct 交叉验证） ----------
/-- 0.1f + 0.2f = 0x3E99999A（精确和 0.300000004470348358... 的 RNE 最近值；
    与候选 0x3E999999 的距离比为 1:3，独立推导确认） -/
theorem fsT_add_point1_point2 :
    fsAdd fsF32 .RNE 0x3DCCCCCD#32 0x3E4CCCCD#32 = 0x3E99999A#32 := by native_decide
/-- 1 + 2⁻²⁴：恰为平局，RNE 平局到偶 → 1.0 -/
theorem fsT_add_tie_even :
    fsAdd fsF32 .RNE 0x3F800000#32 0x33800000#32 = 0x3F800000#32 := by native_decide
/-- 同一下输入 RUP → 1.0 + 1 ulp -/
theorem fsT_add_tie_rup :
    fsAdd fsF32 .RUP 0x3F800000#32 0x33800000#32 = 0x3F800001#32 := by native_decide
/-- 1 + 2⁻²³ 精确 -/
theorem fsT_add_ulp :
    fsAdd fsF32 .RNE 0x3F800000#32 0x34000000#32 = 0x3F800001#32 := by native_decide
/-- 1 - 2⁻²⁵：平局，RNE → 1.0 -/
theorem fsT_sub_tie_rne :
    fsSub fsF32 .RNE 0x3F800000#32 0x33000000#32 = 0x3F800000#32 := by native_decide
/-- 同一下输入 RTZ → 0x3F7FFFFF（1 - 2⁻²⁴，可精确表示的最大较小值） -/
theorem fsT_sub_tie_rtz :
    fsSub fsF32 .RTZ 0x3F800000#32 0x33000000#32 = 0x3F7FFFFF#32 := by native_decide
/-- 最小次正规 + 最小次正规 = 2·2⁻¹⁴⁹（次正规精确累加） -/
theorem fsT_add_subnorm :
    fsAdd fsF32 .RNE 0x00000001#32 0x00000001#32 = 0x00000002#32 := by native_decide
/-- 最大次正规 + 最小次正规 = 最小正规格化数 0x00800000（次正规→正规格化进位） -/
theorem fsT_add_subnorm_carry :
    fsAdd fsF32 .RNE 0x007FFFFF#32 0x00000001#32 = 0x00800000#32 := by native_decide
/-- max + max 上溢：RNE → +inf（IEEE §7.4） -/
theorem fsT_add_ovf_rne :
    fsAdd fsF32 .RNE 0x7F7FFFFF#32 0x7F7FFFFF#32 = 0x7F800000#32 := by native_decide
/-- 同上 RTZ → 最大正规格化数 -/
theorem fsT_add_ovf_rtz :
    fsAdd fsF32 .RTZ 0x7F7FFFFF#32 0x7F7FFFFF#32 = 0x7F7FFFFF#32 := by native_decide
/-- 同上 RDN（正值，向负无穷）→ 最大正规格化数 -/
theorem fsT_add_ovf_rdn :
    fsAdd fsF32 .RDN 0x7F7FFFFF#32 0x7F7FFFFF#32 = 0x7F7FFFFF#32 := by native_decide
/-- 同上 RUP → +inf；RMM → +inf -/
theorem fsT_add_ovf_rup_rmm :
    fsAdd fsF32 .RUP 0x7F7FFFFF#32 0x7F7FFFFF#32 = 0x7F800000#32 ∧
    fsAdd fsF32 .RMM 0x7F7FFFFF#32 0x7F7FFFFF#32 = 0x7F800000#32 := by native_decide
/-- (+inf) + (-inf) = 规范 NaN -/
theorem fsT_add_inf_cancel :
    fsAdd fsF32 .RNE 0x7F800000#32 0xFF800000#32 = 0x7FC00000#32 := by native_decide
/-- NaN 传播为规范 NaN（sNaN 输入同） -/
theorem fsT_add_nan :
    fsAdd fsF32 .RNE 0x7FC00001#32 0x3F800000#32 = 0x7FC00000#32 ∧
    fsAdd fsF32 .RNE 0x7F800001#32 0x3F800000#32 = 0x7FC00000#32 := by native_decide
/-- (+0) + (-0)：RNE → +0；RDN → -0（IEEE §6.3） -/
theorem fsT_add_zero_sign :
    fsAdd fsF32 .RNE 0x00000000#32 0x80000000#32 = 0x00000000#32 ∧
    fsAdd fsF32 .RDN 0x00000000#32 0x80000000#32 = 0x80000000#32 := by native_decide
/-- (-0) + (-0) = -0 -/
theorem fsT_add_neg_zero :
    fsAdd fsF32 .RNE 0x80000000#32 0x80000000#32 = 0x80000000#32 := by native_decide
/-- 1 - 1 精确零：RNE → +0；RDN → -0 -/
theorem fsT_sub_exact_zero :
    fsSub fsF32 .RNE 0x3F800000#32 0x3F800000#32 = 0x00000000#32 ∧
    fsSub fsF32 .RDN 0x3F800000#32 0x3F800000#32 = 0x80000000#32 := by native_decide
/-- f16：1.0 + 1.0 = 2.0 = 0x4000 -/
theorem fsT_add_f16 :
    fsAdd fsF16 .RNE 0x3C00#16 0x3C00#16 = 0x4000#16 := by native_decide
/-- f64：0.1d + 0.2d = 0x3FD3333333333334（经典文献锚点） -/
theorem fsT_add_f64 :
    fsAdd fsF64 .RNE 0x3FB999999999999A#64 0x3FC999999999999A#64
      = 0x3FD3333333333334#64 := by native_decide

-- ---------- 10.4 乘法 ----------
/-- 0.1f × 0.2f = 0x3CA3D70B（Fraction 精确积的 RNE） -/
theorem fsT_mul_point :
    fsMul fsF32 .RNE 0x3DCCCCCD#32 0x3E4CCCCD#32 = 0x3CA3D70B#32 := by native_decide
/-- inf × 0 = 规范 NaN -/
theorem fsT_mul_inf_zero :
    fsMul fsF32 .RNE 0x7F800000#32 0x00000000#32 = 0x7FC00000#32 := by native_decide
/-- (-2) × 3 = -6 = 0xC0C00000 -/
theorem fsT_mul_neg :
    fsMul fsF32 .RNE 0xC0000000#32 0x40400000#32 = 0xC0C00000#32 := by native_decide
/-- 最小次正规 × 0.5 = 2⁻¹⁵⁰：平局，RNE 到偶 → +0；RUP → 最小次正规 -/
theorem fsT_mul_subnorm_tie :
    fsMul fsF32 .RNE 0x00000001#32 0x3F000000#32 = 0x00000000#32 ∧
    fsMul fsF32 .RUP 0x00000001#32 0x3F000000#32 = 0x00000001#32 := by native_decide
/-- max × 2 上溢：RNE → +inf；RTZ → max -/
theorem fsT_mul_ovf :
    fsMul fsF32 .RNE 0x7F7FFFFF#32 0x40000000#32 = 0x7F800000#32 ∧
    fsMul fsF32 .RTZ 0x7F7FFFFF#32 0x40000000#32 = 0x7F7FFFFF#32 := by native_decide
/-- f16 次正规相乘下溢到零：0x0001 × 0x0001 = +0 -/
theorem fsT_mul_f16_underflow :
    fsMul fsF16 .RNE 0x0001#16 0x0001#16 = 0x0000#16 := by native_decide

-- ---------- 10.5 除法（H-FDIV-1 数值语义） ----------
/-- 1/3 = 0x3EAAAAAB（RNE；精确值介于 AA 与 AB 之间，距 AB 恰一半之半） -/
theorem fsT_div_third :
    fsDiv fsF32 .RNE 0x3F800000#32 0x40400000#32 = 0x3EAAAAAB#32 := by native_decide
/-- 1/3 RTZ 截断 → 0x3EAAAAAA（RNE 上舍入时 RTZ 低 1 ulp） -/
theorem fsT_div_third_rtz :
    fsDiv fsF32 .RTZ 0x3F800000#32 0x40400000#32 = 0x3EAAAAAA#32 := by native_decide
/-- x/0 = ±inf（IEEE §7.3）；0/0 = NaN；inf/inf = NaN -/
theorem fsT_div_specials :
    fsDiv fsF32 .RNE 0x3F800000#32 0x00000000#32 = 0x7F800000#32 ∧
    fsDiv fsF32 .RNE 0xBF800000#32 0x00000000#32 = 0xFF800000#32 ∧
    fsDiv fsF32 .RNE 0x00000000#32 0x00000000#32 = 0x7FC00000#32 ∧
    fsDiv fsF32 .RNE 0x7F800000#32 0xFF800000#32 = 0x7FC00000#32 := by native_decide
/-- 1/inf = +0；0.1f/0.2f = 0.5 精确（0.2f 的尾数与 0.1f 相同、指数 +1） -/
theorem fsT_div_inf_exact :
    fsDiv fsF32 .RNE 0x3F800000#32 0x7F800000#32 = 0x00000000#32 ∧
    fsDiv fsF32 .RNE 0x3DCCCCCD#32 0x3E4CCCCD#32 = 0x3F000000#32 := by native_decide

-- ---------- 10.6 平方根（H-FDIV-1 数值语义） ----------
/-- √4 = 2；√0.25 = 0.5 -/
theorem fsT_sqrt_exact :
    fsSqrt fsF32 .RNE 0x40800000#32 = 0x40000000#32 ∧
    fsSqrt fsF32 .RNE 0x3E800000#32 = 0x3F000000#32 := by native_decide
/-- √2 = 0x3FB504F3（IEEE 文献标准值） -/
theorem fsT_sqrt_two :
    fsSqrt fsF32 .RNE 0x40000000#32 = 0x3FB504F3#32 := by native_decide
/-- √(最小次正规 2⁻¹⁴⁹) = 2⁻⁷⁴·⁵ → 0x1A3504F3（次正规输入、正规格化输出；
    独立推导：sig = ⌊2²³·⁵⌋ = 11863283 = 2²³ + 0x3504F3，指数域 52） -/
theorem fsT_sqrt_subnormal :
    fsSqrt fsF32 .RNE 0x00000001#32 = 0x1A3504F3#32 := by native_decide
/-- √(-1) = 规范 NaN；√(-0) = -0；√(+inf) = +inf -/
theorem fsT_sqrt_specials :
    fsSqrt fsF32 .RNE 0xBF800000#32 = 0x7FC00000#32 ∧
    fsSqrt fsF32 .RNE 0x80000000#32 = 0x80000000#32 ∧
    fsSqrt fsF32 .RNE 0x7F800000#32 = 0x7F800000#32 := by native_decide
/-- f64：√2 = 0x3FF6A09E667F3BCD（IEEE 文献标准值） -/
theorem fsT_sqrt_f64 :
    fsSqrt fsF64 .RNE 0x4000000000000000#64 = 0x3FF6A09E667F3BCD#64 := by
  native_decide

-- ---------- 10.7 融合乘加（单次舍入判别锚点） ----------
/-- fma(1+2⁻¹², 1+2⁻¹², -1) = 2⁻¹¹ + 2⁻²⁴ = 0x3A000400（融合单次舍入；
    分步 mul-then-add 得 0x3A000000——乘积 1+2⁻¹¹+2⁻²⁴ 先舍入丢 2⁻²⁴。
    本锚点区分"真融合"与"伪融合"实现） -/
theorem fsT_fma_fused :
    fsFmadd fsF32 .RNE 0x3F800800#32 0x3F800800#32 0xBF800000#32
      = 0x3A000400#32 := by native_decide
/-- inf × 0 + c = 规范 NaN（c 为任何值） -/
theorem fsT_fma_inf_zero :
    fsFmadd fsF32 .RNE 0x7F800000#32 0x00000000#32 0x3F800000#32
      = 0x7FC00000#32 := by native_decide
/-- fma(1,1,1) = 2；fmsub(2,3,1) = 5；fnmadd(1,1,1) = +0（-(1)+1 精确零，
    异号 → RNE 给 +0） -/
theorem fsT_fma_variants :
    fsFmadd fsF32 .RNE 0x3F800000#32 0x3F800000#32 0x3F800000#32 = 0x40000000#32 ∧
    fsFmsub fsF32 .RNE 0x40000000#32 0x40400000#32 0x3F800000#32 = 0x40A00000#32 ∧
    fsFnmadd fsF32 .RNE 0x3F800000#32 0x3F800000#32 0x3F800000#32 = 0x00000000#32 := by
  native_decide
/-- fma(+inf, 2, -inf) = 规范 NaN -/
theorem fsT_fma_inf_cancel :
    fsFmadd fsF32 .RNE 0x7F800000#32 0x40000000#32 0xFF800000#32
      = 0x7FC00000#32 := by native_decide

-- ---------- 10.8 min/max（IEEE minNum/maxNum、RISC-V fmin/fmax 语义） ----------
theorem fsT_minmax_nan :
    fsMin fsF32 0x7FC00000#32 0x3F800000#32 = 0x3F800000#32 ∧
    fsMax fsF32 0x3F800000#32 0x7FC00000#32 = 0x3F800000#32 ∧
    fsMin fsF32 0x7FC00000#32 0x7F800001#32 = 0x7FC00000#32 := by native_decide
/-- min(+0,-0) = -0；max(+0,-0) = +0 -/
theorem fsT_minmax_zero :
    fsMin fsF32 0x00000000#32 0x80000000#32 = 0x80000000#32 ∧
    fsMax fsF32 0x00000000#32 0x80000000#32 = 0x00000000#32 := by native_decide
/-- min(-5,3) = -5；max(-inf,1) = 1 -/
theorem fsT_minmax_value :
    fsMin fsF32 0xC0A00000#32 0x40400000#32 = 0xC0A00000#32 ∧
    fsMax fsF32 0xFF800000#32 0x3F800000#32 = 0x3F800000#32 := by native_decide

-- ---------- 10.9 比较 ----------
theorem fsT_cmp :
    fsFeq fsF32 0x80000000#32 0x00000000#32 = true ∧     -- -0 = +0
    fsFeq fsF32 0x7FC00000#32 0x7FC00000#32 = false ∧    -- NaN ≠ NaN
    fsFlt fsF32 0xFF800000#32 0x00000000#32 = true ∧     -- -inf < +0
    fsFlt fsF32 0x3F800000#32 0x3F800000#32 = false ∧
    fsFle fsF32 0x3F800000#32 0x3F800000#32 = true ∧
    fsFle fsF32 0x7FC00000#32 0x3F800000#32 = false ∧    -- NaN 比较全 false
    fsFlt fsF32 0x3DCCCCCD#32 0x3E4CCCCD#32 = true := by native_decide

-- ---------- 10.10 转换 ----------
/-- INT32_MAX → f32：RNE → 2³¹ = 0x4F000000（经典文献锚点）；
    RTZ → 0x4EFFFFFF -/
theorem fsT_itof_intmax :
    fsIToF fsF32 .RNE 32 true 0x7FFFFFFF#32 = 0x4F000000#32 ∧
    fsIToF fsF32 .RTZ 32 true 0x7FFFFFFF#32 = 0x4EFFFFFF#32 := by native_decide
/-- UINT32_MAX → f32 RNE = 2³² = 0x4F800000；-1（有符号）→ -1.0 -/
theorem fsT_itof_uint :
    fsIToF fsF32 .RNE 32 false 0xFFFFFFFF#32 = 0x4F800000#32 ∧
    fsIToF fsF32 .RNE 32 true 0xFFFFFFFF#32 = 0xBF800000#32 := by native_decide
/-- 2²⁴+1 → f32：平局 RNE → 2²⁴ = 0x4B800000；RMM → 2²⁴+2 = 0x4B800001 -/
theorem fsT_itof_tie :
    fsIToF fsF32 .RNE 32 true 0x01000001#32 = 0x4B800000#32 ∧
    fsIToF fsF32 .RMM 32 true 0x01000001#32 = 0x4B800001#32 := by native_decide
/-- fcvt 舍入：3.5 → 4（RNE）；2.5 → 2（平局到偶）；-2.5 → -2 -/
theorem fsT_ftoi_round :
    fsFToI fsF32 .RNE 32 true 0x40600000#32 = 4#32 ∧
    fsFToI fsF32 .RNE 32 true 0x40200000#32 = 2#32 ∧
    fsFToI fsF32 .RNE 32 true 0xC0200000#32 = 0xFFFFFFFE#32 := by native_decide
/-- fcvt 饱和与特殊值（RISC-V 语义）：1e30 → INT32_MAX；-1e30 → INT32_MIN；
    NaN → INT32_MAX；+inf → INT32_MAX；-inf → INT32_MIN -/
theorem fsT_ftoi_sat :
    fsFToI fsF32 .RNE 32 true 0x7149F2CA#32 = 0x7FFFFFFF#32 ∧
    fsFToI fsF32 .RNE 32 true 0xF149F2CA#32 = 0x80000000#32 ∧
    fsFToI fsF32 .RNE 32 true 0x7FC00000#32 = 0x7FFFFFFF#32 ∧
    fsFToI fsF32 .RNE 32 true 0x7F800000#32 = 0x7FFFFFFF#32 ∧
    fsFToI fsF32 .RNE 32 true 0xFF800000#32 = 0x80000000#32 := by native_decide
/-- fcvt 无符号：-1.0 → 0；1e30 → UINT32_MAX；3.7 RTZ → 3 -/
theorem fsT_ftoi_unsigned :
    fsFToI fsF32 .RNE 32 false 0xBF800000#32 = 0#32 ∧
    fsFToI fsF32 .RNE 32 false 0x7149F2CA#32 = 0xFFFFFFFF#32 ∧
    fsFToI fsF32 .RTZ 32 true 0x406CCCCD#32 = 3#32 := by native_decide
/-- f32→f16：1.0 → 0x3C00；65504（f16 max）→ 0x7BFF；65520 平局 → inf
    （IEEE 754 §7.4 平局上溢舍入到 inf；struct 'e' 交叉验证） -/
theorem fsT_ftof_narrow :
    fsFToF fsF32 fsF16 .RNE 0x3F800000#32 = 0x3C00#16 ∧
    fsFToF fsF32 fsF16 .RNE 0x477FE000#32 = 0x7BFF#16 ∧
    fsFToF fsF32 fsF16 .RNE 0x477FF000#32 = 0x7C00#16 := by native_decide
/-- f32→f16 次正规：2⁻²⁴ → 0x0001（f16 最小次正规）；2⁻²⁵ 平局到偶 → 0；
    3·2⁻²⁵ → 0x0002；2⁻¹⁴（f16 最小正规格化）→ 0x0400 -/
theorem fsT_ftof_subnormal :
    fsFToF fsF32 fsF16 .RNE 0x33800000#32 = 0x0001#16 ∧
    fsFToF fsF32 fsF16 .RNE 0x33000000#32 = 0x0000#16 ∧
    fsFToF fsF32 fsF16 .RNE 0x33C00000#32 = 0x0002#16 ∧
    fsFToF fsF32 fsF16 .RNE 0x38800000#32 = 0x0400#16 := by native_decide
/-- f16→f32 扩宽精确：0x3C01 → 0x3F802000；次正规 0x0001 → 2⁻²⁴ = 0x33800000；
    inf → inf；qNaN → 规范 NaN -/
theorem fsT_ftof_widen :
    fsFToF fsF16 fsF32 .RNE 0x3C01#16 = 0x3F802000#32 ∧
    fsFToF fsF16 fsF32 .RNE 0x0001#16 = 0x33800000#32 ∧
    fsFToF fsF16 fsF32 .RNE 0x7C00#16 = 0x7F800000#32 ∧
    fsFToF fsF16 fsF32 .RNE 0x7E00#16 = 0x7FC00000#32 := by native_decide
/-- f64→f32：(0.1+0.2)d → 0x3E99999A；f32→f64：1.0 精确扩宽 -/
theorem fsT_ftof_f64 :
    fsFToF fsF64 fsF32 .RNE 0x3FD3333333333334#64 = 0x3E99999A#32 ∧
    fsFToF fsF32 fsF64 .RNE 0x3F800000#32 = 0x3FF0000000000000#64 := by native_decide

-- ---------- 10.11 契约收窄形态的使用示例（spec 谓词可被逐条核对） ----------
/-- specFpuBinOk 实例：0.1f+0.2f 这条断言本身可判定、可核对 -/
theorem fsT_spec_bin_ok :
    specFpuBinOk .fadd .RNE 0x3DCCCCCD#32 0x3E4CCCCD#32 0x3E99999A#32 := by
  unfold specFpuBinOk; native_decide
/-- specFdivDivOk / specFdivSqrtOk 实例 -/
theorem fsT_spec_fdiv_ok :
    specFdivDivOk .RNE 0x3F800000#32 0x40400000#32 0x3EAAAAAB#32 ∧
    specFdivSqrtOk .RNE 0x40000000#32 0x3FB504F3#32 := by
  unfold specFdivDivOk specFdivSqrtOk; native_decide
/-- specFpuFmaOk 实例（融合判别锚点） -/
theorem fsT_spec_fma_ok :
    specFpuFmaOk .fmadd .RNE 0x3F800800#32 0x3F800800#32 0xBF800000#32
      0x3A000400#32 := by
  unfold specFpuFmaOk; native_decide

end FsTests

/- ========================================================================= -/
/- 11. 公理审计（native_decide 测试定理带每定理私有的                             -/
/-     …._native.native_decide.ax_* 信任公理（Lean 4.31），按 AGENTS.md            -/
/-     归档注明；decide 定理与本文件全部定义无公理；无 sorry、无自定义公理）      -/
/- ========================================================================= -/

#print axioms fsT_add_point1_point2
#print axioms fsT_fma_fused
#print axioms fsT_sqrt_subnormal
#print axioms fsT_ftof_subnormal
#print axioms fsT_spec_fdiv_ok
#print axioms fsT_classify
#print axioms fsF32_len

end Ventus.Spec
