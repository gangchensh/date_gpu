/- ========================================================================= -/
/-                     Arith/IntDivMod.lean                                  -/
/-  不恢复余数除法器（IntDivMod）的 Lean 4 时序模型 + 测试 + 证明              -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/IntDivMod.scala    -/
/-    （全文 135 行；5 状态 FSM：s_idle/s_pre/s_compute/s_recovery/s_finish； -/
/-      execution.scala:846 例化 num_sfu 份，xLen=32）                        -/
/-  本文件建模单个 IntDivMod 实例，参数化 xLen（测试取 4/8/32）。             -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 信号 = BitVec/Bool；时序 = DivState structure + divStep 纯函数；      -/
/-      输入打拍（:28-42 的 RegEnable(io.in.fire)）建模为 idle 态 fire 时     -/
/-      捕获进 DivState 字段。                                                -/
/-  D2. iterReg（:53，RegEnable(iter, state===s_pre)）在全模块中无任何        -/
/-      消费者（:118 用的是组合 iter），属死寄存器，不建模（同 Scoreboard     -/
/-      的 D3 惯例）。zeroQReg（:54）有消费者（:77），必须建模。              -/
/-  D3. Chisel `tail(n)` = 去掉最高 n 位（取低 w-n 位），`head(n)` = 最高     -/
/-      n 位。证据：:35 INT_MIN 检测 `a.head(1) && !a.tail(1).orR`（MSB=1     -/
/-      且低 31 位全 0）。据此 :65 `(aReg<<1).tail(1)` = 左移后取低 xLen+2    -/
/-      位，等价于 Lean 同宽 `<<<`（天然截断高位），建模为 aReg <<< 1。       -/
/-      审查结论：aShift 无 bug（初读易误判为"丢 LSB 等于没移位"）。          -/
/-  D4. 宽度语义逐行对齐 Chisel 推断宽度：                                    -/
/-      - aLez/dLez：PriorityEncoder(32 输入) → log2Ceil(32)=5 位             -/
/-        （:44-45），通用为 divW xLen = ⌈log2 xLen⌉ = Nat.log2 (xLen-1)+1； -/
/-      - iter（:46）：Chisel 6 下 `dLez - aLez + 1.U` 为 5 位回绕运算（值 = (dLez-aLez+1) mod 32；Chisel ≤3 升宽语义下为 6 位值后被 connect 截断——两者数值恒等），模型用 divW+1 位 + setWidth 表达；     -/
/-        → divW+1 位；                                                       -/
/-      - cnt（:56）：log2Up(32)=5 位 → divW 位；`:118 cnt := iter` 是       -/
/-        6→5 位 connect，Chisel/FIRRTL 宽→窄静默截断，建模为 setWidth        -/
/-        （取低位）。此截断即 BUG1 机制（见 Q 区 Q4）。                      -/
/-      - aReg/dReg/aShift/aNext/dNorm/dNegNorm：xLen+2 位（:48-52,:65-66）； -/
/-      - recoveryR（:70）：xLen 位——Chisel 6 的 `+` 是回绕加（=%+，不升宽， -/
/-        见 Q7 撤案记录）；:71 `>>dLez` 为同宽右移，(xLen-1,0) 截取为恒等；  -/
/-      - Q/QN/commonQ/commonR：xLen 位回绕运算。                             -/
/-  D5. divLez（PriorityEncoder(asBools.reverse)，:44-45）= 前导零个数        -/
/-      （最高置位位之上连续 0 比特数）；x=0 时 PriorityEncoder 全零输入       -/
/-      退化为输出 0（不是 xLen！），模型忠实保留此退化（a=0 被 zeroQ 拦截， -/
/-      退化值不可达 compute，见 Q1）。                                       -/
/-  D6. 无复位的 RegEnable 寄存器（qSign/rSign/rawA/unsignedA/D/overflow/     -/
/-      divByZero/zeroQ/commonQ/commonR）在真实硬件中初值不定；模型 divInit   -/
/-      取全 0（与 ChiselSim 未随机化时一致）。BUG2（Q5）表明 zeroQ 的        -/
/-      陈旧值可被消费，故该选择对功能正确性有实际影响，已在报告中标注。      -/
/-  D7. RISC-V 规约（divSpecQ/divSpecR）按 RISC-V 语义自行陈述：除零          -/
/-      q=全1/r=a，signed INT_MIN ÷ -1 溢出 q=INT_MIN/r=0，其余截断向零         -/
/-      除法。不引用 Base.bits_div（其除零约定为 0，≠ RISC-V）。              -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1. :46 `Mux(aLez > dLez, 0.U, ...)` 的 0 支在 FSM 可达状态下是死逻辑：   -/
/-      compute 仅当 ¬zeroQ（|a| ≥ |d|）进入；aLez > dLez ⟺ msb(|a|) <       -/
/-      msb(|d|) ⟹ |a| < |d| ⟹ 必被 :93 zeroQ 分支送往 s_finish。a=0 时      -/
/-      aLez 退化为 0（D5），同样被 zeroQ 拦截。故装入 cnt 的 iter ∈ [1,      -/
/-      xLen]（含 BUG1 的 32）。同时 :53 iterReg 是死寄存器（D2）。           -/
/-  Q2. :50-52 归一化移位无高位损失：aLez 是 |a| 的前导零数 ⟹ |a|<<<aLez     -/
/-      < 2^xLen，取低 xLen 位无损；dNegNorm 中 (~|d|+1)<<<dLez 的低 xLen     -/
/-      位 = 2^xLen - |d|·2^dLez（|d|·2^dLez ∈ [2^(xLen-1), 2^xLen)，无损）， -/
/-      且 dNegNorm ≡ -dNorm (mod 2^(xLen+2))（Cat 的 1.U 补出符号位）。      -/
/-      a=0 退化时 aNorm=0，但被 zeroQ 拦截（Q1）。结论：无损，非 bug。       -/
/-  Q3. :69 commonQ 两种形式【不等价】：Q + ~QN ≡ Q - QN - 1 (mod 2^xLen)，  -/
/-      恰差 1——这是不恢复余数除法的标准修正（余数为负时商减 1），属设计       -/
/-      意图而非笔误（xLen=4 全穷举 + xLen=8 全穷举均验证通过）。             -/
/-  Q4.【I 类 bug 候选 BUG1：cnt 位宽不足导致 iter=32 截断为 0】               -/
/-      :56 `cnt : UInt(log2Up(xLen).W)` = 5 位（xLen=32），但 :46 iter 是    -/
/-      6 位且可达 32（aLez=0 且 dLez=31，即 |a| ≥ 2^31 且 |d| = 1；例如       -/
/-      unsigned a ∈ [0x80000000, 0xFFFFFFFF], d=1；signed a=INT_MIN, d=1）。 -/
/-      :118 `cnt := iter` 宽→窄截断 → cnt=0 → s_compute 只迭代 1 次（应为    -/
/-      32 次）→ Q=1, QN=0, remIsNeg=false → commonQ=1 → 输出                 -/
/-      q = qSign ? 全1 : 1，r = 0，与真值完全不符。                          -/
/-      注意：iter=32 【不】伴随 |a|<|d|（|a| ≥ 2^31 ≥ 1 = |d|），zeroQ       -/
/-      不拦截——任务简报中"iter=32 必伴随 |a|<|d|"的猜想不成立（简报把        -/
/-      aLez=0 误当成 |a|=1；实际 aLez=0 ⟺ |a| 的 MSB 置位，dLez=31 ⟺       -/
/-      |d|=1）。witness（本文件 native_decide 钉死）：                       -/
/-        unsigned 0x80000000/1 → 硬件 (q=1, r=0)，RISC-V (q=0x80000000, 0)； -/
/-        signed   INT_MIN/1     → 硬件 (q=0xFFFFFFFF, 0)，RISC-V (INT_MIN, 0)。-/
/-      修复建议（2026-09-07 修订，doc/23 §7）：cnt 加宽【且】iter 算术加宽——Chisel 6 回绕语义下仅加宽 cnt 无效。            -/
/-  Q5.【I 类 bug 候选 BUG2：陈旧 zeroQReg 污染 overflow 余数】                -/
/-      :77 specialR = Mux(divByZeroReg||zeroQReg, rawAReg, 0)，但 overflow/  -/
/-      divByZero 从事务在 s_idle 直接跳 s_finish（:88），不经过 s_pre，       -/
/-      zeroQReg（:54 仅 state===s_pre 时更新，且无复位）保持上一事务的陈旧   -/
/-      值。若上一事务 |a|<|d|（zeroQ=1），紧随其后 INT_MIN ÷ -1（signed）的     -/
/-      out.r = rawA = 0x80000000，而 RISC-V 规定 overflow 时 r=0。divByZero -/
/-      路径免疫（r=rawA 本就正确）；q 输出免疫（specialQ 不含 zeroQReg）。   -/
/-      定理 div_t1_overflow 把 r 钉为 `if s.zeroQ then i.a else 0`，          -/
/-      精确刻画该 bug；div_test_stale_zeroQ 给出复现序列。                   -/
/-      修复建议：specialR 条件改为 divByZeroReg||（zeroQReg&&经pre路径）或    -/
/-      overflow 时强制 r=0（如 specialR 增加 overflowReg 优先级支路）。       -/
/-  Q6. :77 行内注释 "divByZero|zeroDivSth -> overflow" 语义不明，疑为        -/
/-      遗留注释，无功能影响。                                                -/
/-  Q7.【已撤案（2026-09-07，doc/23）：原 BUG3/I-18 系 II 类误译，RTL 无此   -/
/-      bug】原分析把 :70 的 aReg.tail(1).head(xLen)+dReg.tail(1).head(xLen)  -/
/-      当作升宽加（xLen+1 位），推出 remIsNeg 时 commonR = |r_true| +        -/
/-      2^(xLen-dLez)，并在 xLen=4/8 全穷举中与模型自洽。但 Chisel 6 的 `+`   -/
/-      是【回绕加】（chisel3 Bits.scala:479 `do_+ = do_+%`，结果位宽 =       -/
/-      max(操作数) = xLen，不升宽；升宽须显式写 +&）：负部分余数补码的       -/
/-      2^xLen 借位项被回绕丢弃，(aPart + dPart) mod 2^xLen = (P+dNorm)/2     -/
/-      mod 2^xLen 恰为正确恢复值（P+dNorm ∈ [0,2^(xLen+1))，/2 < 2^xLen      -/
/-      无损）。RTL 实测（doc/22）：4/3(u)=(1,1)、0xDEADBEEF/0x1234(u)=       -/
/-      (0xC3BA5,0x76B)，均与规约一致，与修正后模型逐值吻合。已按回绕加       -/
/-      修正 divCommonRNext（移除 zeroExtend 升宽）；IntDivModFixed 的        -/
/-      "I-18 修复"（先加后截）在修正后模型上与原版在可达状态逐位等价         -/
/-      （dReg 恒为偶），i18 补丁是语义保持的 no-op，建议撤回上游交付。       -/
/-      教训：Chisel 3→6 的 `+` 语义变化（升宽→回绕）是系统性 II 类风险，     -/
/-      凡按"升 1 位"翻译的 `+` 皆需重审。原"13% 输入余数错误"仅为模型       -/
/-      自身的假象，从未存在于 RTL。BUG1（Q4）与 BUG2（Q5）不依赖此路径，     -/
/-      已在 RTL 精确复现（doc/22），结论不变。                               -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 宽度与组合辅助函数（:28-71）                                            -/
/- ========================================================================= -/

/-- Chisel `log2Up(xLen)`（:56 cnt 位宽；PriorityEncoder 输出位宽 log2Ceil 同值）。
    ⌈log2 n⌉ = ⌊log2 (n-1)⌋ + 1（n ≥ 2）：xLen=32 → 5，xLen=4 → 2。 -/
def divW (xLen : Nat) : Nat := Nat.log2 (xLen - 1) + 1

/-- INT_MIN 位型（:75 overflow 支）：Cat(1.U(1.W), 0.U((xLen-1).W)) = 2^(xLen-1) -/
def divIntMin (xLen : Nat) : BitVec xLen := BitVec.ofNat xLen (2 ^ (xLen - 1))

/-- 符号判定（:28-29）：signed 且 MSB -/
def divSign (x : BitVec xLen) (sgn : Bool) : Bool := sgn && x.msb

/-- 取绝对值（:32-33）：Mux(sign, ~x+1, x) -/
def divAbs (x : BitVec xLen) (sgn : Bool) : BitVec xLen :=
  if divSign x sgn then ~~~x + 1 else x

/-- overflow 检测（:35）：signed 且 a=INT_MIN 且 d=全1（-1） -/
def divOvfDet (a d : BitVec xLen) (sgn : Bool) : Bool :=
  sgn && a.msb && (a.extractLsb' 0 (xLen - 1) == 0) && (d == BitVec.allOnes xLen)

/-- divByZero 检测（:36） -/
def divDbzDet (d : BitVec xLen) : Bool := d == 0

/-- PriorityEncoder 扫描递归：从 bit i 向下数连续 0 比特（见 D5） -/
def divLezGo {n : Nat} (x : BitVec n) : Nat → Nat → Nat
  | 0, acc => if x.getLsbD 0 then acc else acc + 1
  | i + 1, acc => if x.getLsbD (i + 1) then acc else divLezGo x i (acc + 1)

/-- PriorityEncoder(asBools.reverse)（:44-45）= 前导零个数；x=0 退化为 0（D5） -/
def divLez {n : Nat} (x : BitVec n) : BitVec (divW n) :=
  if x == 0 then 0 else BitVec.ofNat (divW n) (divLezGo x (n - 1) 0)

/-- iter（:46），宽度 divW+1（Chisel 推断 6 位@xLen=32，见 D4） -/
def divIter {xLen : Nat} (aLez dLez : BitVec (divW xLen)) : BitVec (divW xLen + 1) :=
  if BitVec.ult dLez aLez then 0 else (dLez - aLez).zeroExtend _ + 1

/-- aNorm（:50）：Cat(0.U(2.W), (unsignedA<<aLez)(xLen-1,0))；同宽 <<< 天然截断 -/
def divANorm {xLen : Nat} (unsignedA : BitVec xLen) (aLez : BitVec (divW xLen)) :
    BitVec (xLen + 2) :=
  (unsignedA <<< aLez).zeroExtend (xLen + 2)

/-- dNorm（:51）：Cat(0.U(1.W), (unsignedD<<dLez)(xLen-1,0), 0.U(1.W)) -/
def divDNorm {xLen : Nat} (unsignedD : BitVec xLen) (dLez : BitVec (divW xLen)) :
    BitVec (xLen + 2) :=
  ((unsignedD <<< dLez).zeroExtend (xLen + 2)) <<< 1

/-- dNegNorm（:52）：Cat(1.U(1.W), ((~unsignedD+1)<<dLez)(xLen-1,0), 0.U(1.W))；
    ≡ -dNorm (mod 2^(xLen+2))（Q2） -/
def divDNegNorm {xLen : Nat} (unsignedD : BitVec xLen) (dLez : BitVec (divW xLen)) :
    BitVec (xLen + 2) :=
  ((1 : BitVec (xLen + 2)) <<< (xLen + 1)) |||
    ((((~~~unsignedD + 1) <<< dLez).zeroExtend (xLen + 2)) <<< 1)

/-- cnt_next（:57） -/
def divCntNext {w : Nat} (c : BitVec w) : BitVec w := if c == 0 then 0 else c - 1

/-- sel_pos（:62）：aReg(xLen, xLen-1) == 01 -/
def divSelPos {xLen : Nat} (aReg : BitVec (xLen + 2)) : Bool :=
  aReg.extractLsb' (xLen - 1) 2 == 1

/-- sel_neg（:63）：aReg(xLen, xLen-1) == 10 -/
def divSelNeg {xLen : Nat} (aReg : BitVec (xLen + 2)) : Bool :=
  aReg.extractLsb' (xLen - 1) 2 == 2

/-- aShift（:65）：(aReg<<1) 的低 xLen+2 位（D3） -/
def divAShift {xLen : Nat} (aReg : BitVec (xLen + 2)) : BitVec (xLen + 2) := aReg <<< 1

/-- aNext（:66）；dNormV/dNegNormV 为组合值（:51-52，非 dReg） -/
def divANext {xLen : Nat} (aReg dNormV dNegNormV : BitVec (xLen + 2)) :
    BitVec (xLen + 2) :=
  if divSelPos aReg then divAShift aReg + dNegNormV
  else if divSelNeg aReg then divAShift aReg + dNormV
  else divAShift aReg

/-- commonQ 右值（:69）：remIsNeg=aReg.head(1)=MSB；负时 Q+~QN（≡Q-QN-1，Q3） -/
def divCommonQNext {xLen : Nat} (aReg : BitVec (xLen + 2)) (Q QN : BitVec xLen) :
    BitVec xLen :=
  if aReg.msb then Q + ~~~QN else Q - QN

/-- commonR 右值（:70-71）：两个加数各取 bits[xLen:1]（xLen 位）后【回绕】相加，
    再 >>dLez（:71 的 (xLen-1,0) 截取对 xLen 位 recoveryR 是恒等）。
    宽度关键（Q7/doc/23）：Chisel 6 的 `+` = `+%` 回绕加（chisel3
    Bits.scala:479 `do_+ = do_+%`），结果为 xLen 位而非 xLen+1 位；曾误译为
    zeroExtend 升宽加，多出的 2^xLen 进位经 >>dLez 落成 +2^(xLen-dLez) 的
    伪偏差（原 BUG3/I-18，已撤案）。 -/
def divCommonRNext {xLen : Nat} (aReg dReg : BitVec (xLen + 2))
    (dLez : BitVec (divW xLen)) : BitVec xLen :=
  let aPart : BitVec xLen := aReg.extractLsb' 1 xLen
  let dPart : BitVec xLen := dReg.extractLsb' 1 xLen
  let recoveryR := if aReg.msb then aPart + dPart else aPart
  recoveryR >>> dLez

/- ========================================================================= -/
/- 2. 状态、输入、单拍转移（:25-135）                                         -/
/- ========================================================================= -/

/-- FSM 状态（:25） -/
inductive DivPhase where
  | idle | pre | compute | recovery | finish
deriving BEq, DecidableEq, Repr

/-- LawfulBEq 不能 derive，手工给（枚举上逐构造子证明） -/
instance : LawfulBEq DivPhase where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> first | rfl | contradiction
  rfl := by intro a; cases a <;> decide

/-- 寄存器状态（:26-71；iterReg 为死寄存器不建模，D2） -/
structure DivState (xLen : Nat) where
  phase     : DivPhase             -- :26
  qSign     : Bool                 -- :30
  rSign     : Bool                 -- :31
  rawA      : BitVec xLen          -- :38
  unsignedA : BitVec xLen          -- :39
  unsignedD : BitVec xLen          -- :40
  overflow  : Bool                 -- :41
  divByZero : Bool                 -- :42
  zeroQ     : Bool                 -- :54（无复位、仅 s_pre 更新 → BUG2，Q5）
  aReg      : BitVec (xLen + 2)    -- :48
  dReg      : BitVec (xLen + 2)    -- :49
  cnt       : BitVec (divW xLen)   -- :56（5 位@xLen=32，iter 可达 32 → BUG1，Q4）
  Q         : BitVec xLen          -- :59
  QN        : BitVec xLen          -- :60
  commonQ   : BitVec xLen          -- :69
  commonR   : BitVec xLen          -- :71

/-- 输入（:17-24 的 io.in.bits + io.out.ready） -/
structure DivInputs (xLen : Nat) where
  in_valid  : Bool
  a         : BitVec xLen
  d         : BitVec xLen
  signed    : Bool
  out_ready : Bool

/-- 初始状态（RegInit 部分 :26,:48-49,:56,:59-60 为 0；无复位寄存器取 0，D6） -/
def divInit (xLen : Nat) : DivState xLen where
  phase := .idle
  qSign := false; rSign := false
  rawA := 0; unsignedA := 0; unsignedD := 0
  overflow := false; divByZero := false; zeroQ := false
  aReg := 0; dReg := 0; cnt := 0; Q := 0; QN := 0
  commonQ := 0; commonR := 0

/-- 单拍状态转移（:85-135 两个 switch + :28-42 输入打拍） -/
def divStep {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen) : DivState xLen :=
  match s.phase with
  | .idle =>
      let base := { s with aReg := 0, dReg := 0, cnt := 0 }           -- :107-111
      if i.in_valid then              -- in.ready = true（:82, idle），io.in.fire
        let ovf := divOvfDet i.a i.d i.signed                         -- :35
        let dbz := divDbzDet i.d                                      -- :36
        { base with
          phase     := if ovf || dbz then .finish else .pre,          -- :88-89
          qSign     := divSign i.a i.signed != divSign i.d i.signed,  -- :30（aSign^dSign）
          rSign     := divSign i.a i.signed,                          -- :31
          rawA      := i.a,                                           -- :38
          unsignedA := divAbs i.a i.signed,                           -- :39
          unsignedD := divAbs i.d i.signed,                           -- :40
          overflow  := ovf,                                           -- :41
          divByZero := dbz }                                          -- :42
      else base
  | .pre =>
      let zq := BitVec.ult s.unsignedA s.unsignedD                    -- :54/:93/:113
      let base := { s with zeroQ := zq }                              -- :54
      if zq then { base with phase := .finish, cnt := 0 }             -- :93, :113-114
      else
        let aL := divLez s.unsignedA                                  -- :44
        let dL := divLez s.unsignedD                                  -- :45
        { base with
          phase := .compute,                                          -- :94
          aReg  := divANorm s.unsignedA aL,                           -- :116
          dReg  := divDNorm s.unsignedD dL,                           -- :117
          cnt   := (divIter aL dL).setWidth (divW xLen),              -- :118（6→5 截断：BUG1）
          Q     := 0, QN := 0 }                                       -- :119-120
  | .compute =>
      let cN := divCntNext s.cnt                                      -- :57
      let dL := divLez s.unsignedD                                    -- :45
      { s with
        phase := if cN == 0 then .recovery else .compute,             -- :97-98
        cnt   := cN,                                                  -- :124
        aReg  := divANext s.aReg (divDNorm s.unsignedD dL)
                             (divDNegNorm s.unsignedD dL),            -- :125
        Q     := (s.Q <<< 1) ||| (if divSelPos s.aReg then 1 else 0), -- :126
        QN    := (s.QN <<< 1) ||| (if divSelNeg s.aReg then 1 else 0) } -- :127
  | .recovery =>
      { s with
        phase   := .finish,                                           -- :100
        cnt     := 0,                                                 -- :130
        commonQ := divCommonQNext s.aReg s.Q s.QN,                    -- :69
        commonR := divCommonRNext s.aReg s.dReg (divLez s.unsignedD) } -- :71
  | .finish =>
      let base := { s with cnt := 0 }                                 -- :133
      if i.out_ready then { base with phase := .idle } else base      -- :101-102（io.out.fire）

/- ========================================================================= -/
/- 3. 输出（:73-82）                                                          -/
/- ========================================================================= -/

/-- signedQ（:73） -/
def divSignedQ {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.qSign then ~~~s.commonQ + 1 else s.commonQ

/-- signedR（:74） -/
def divSignedR {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.rSign then ~~~s.commonR + 1 else s.commonR

/-- specialQ（:75） -/
def divSpecialQ {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.divByZero then BitVec.allOnes xLen
  else if s.overflow then divIntMin xLen
  else 0

/-- specialR（:77；zeroQ 陈旧值在此被消费 → BUG2，Q5） -/
def divSpecialR {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ then s.rawA else 0

/-- io.out.bits.q（:79） -/
def divOutQ {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ || s.overflow then divSpecialQ s else divSignedQ s

/-- io.out.bits.r（:80） -/
def divOutR {xLen : Nat} (s : DivState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ || s.overflow then divSpecialR s else divSignedR s

/-- io.out.valid（:81） -/
def divOutValid {xLen : Nat} (s : DivState xLen) : Bool := s.phase == .finish

/-- io.in.ready（:82） -/
def divInReady {xLen : Nat} (s : DivState xLen) : Bool := s.phase == .idle

/- ========================================================================= -/
/- 4. RISC-V 规约（D7）与执行/检查脚手架                                      -/
/- ========================================================================= -/

/-- 截断向零除法（RISC-V DIV/DIVU 语义；b=0 另行特判，此处给 0 占位） -/
def divTdiv (a b : Int) : Int :=
  if b = 0 then 0
  else if (a < 0) = (b < 0) then (a.natAbs / b.natAbs : Nat)
  else -((a.natAbs / b.natAbs : Nat) : Int)

/-- 截断向零取余：r = a - q·d（RISC-V REM/REMU 语义） -/
def divTmod (a b : Int) : Int := a - divTdiv a b * b

/-- RISC-V 商规约：除零 → 全1；signed INT_MIN ÷ -1 → INT_MIN；signed → 截断向零 -/
def divSpecQ {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : BitVec xLen :=
  if d == 0 then BitVec.allOnes xLen
  else if sgn && a == divIntMin xLen && d == BitVec.allOnes xLen then divIntMin xLen
  else if sgn then BitVec.ofInt xLen (divTdiv a.toInt d.toInt)
  else BitVec.ofNat xLen (a.toNat / d.toNat)

/-- RISC-V 余数规约：除零 → a；overflow → 0；其余对应截断向零余数 -/
def divSpecR {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : BitVec xLen :=
  if d == 0 then a
  else if sgn && a == divIntMin xLen && d == BitVec.allOnes xLen then 0
  else if sgn then BitVec.ofInt xLen (divTmod a.toInt d.toInt)
  else BitVec.ofNat xLen (a.toNat % d.toNat)

/-- 空输入（in_valid=0, out_ready=1）：事务推进一拍 -/
def divNop (xLen : Nat) : DivInputs xLen := ⟨false, 0, 0, false, true⟩

/-- 跑到 s_finish 为止（带 fuel；到达 finish 后停机，过供油无害） -/
def divRunTo {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen) :
    Nat → DivState xLen
  | 0 => s
  | n + 1 => if s.phase == .finish then s else divRunTo (divStep s i) i n

/-- 从 divInit 执行单事务（idle 必接受），返回停机状态 -/
def divExecState {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : DivState xLen :=
  divRunTo (divStep (divInit xLen) ⟨true, a, d, sgn, true⟩) (divNop xLen) (2 * xLen + 8)

/-- 单事务输出 (q, r) -/
def divExec {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : BitVec xLen × BitVec xLen :=
  let sf := divExecState a d sgn
  (divOutQ sf, divOutR sf)

/-- BUG1 触发锥（Q4）：iter = xLen ⟺ aLez=0 ∧ dLez=xLen-1 ⟺ msb(|a|) ∧ |d|=1，
    且不被 divByZero/overflow/zeroQ 拦截（|a| ≥ 2^(xLen-1) ≥ 1 = |d| ⟹ ¬zeroQ） -/
def divCorner {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : Bool :=
  let absA := divAbs a sgn
  let absD := divAbs d sgn
  (d != 0) && (absD == 1) && absA.msb &&
  !(sgn && a == divIntMin xLen && d == BitVec.allOnes xLen)

/-- BUG1 触发锥上的错误输出预测（Q4 推导：1 次迭代后 Q=1,QN=0,remIsNeg=false） -/
def divCornerBuggyQ {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : BitVec xLen :=
  if divSign a sgn != divSign d sgn then BitVec.allOnes xLen else 1

/-- 单点检查（停机 + 非触发锥行为 + 触发锥行为）。非触发锥：q、r 双双恒等于
    RISC-V 规约（I-18 撤案后余数恢复路径亦正确，Q7/doc/23）；触发锥 = BUG1
    错误值且确与规约不同。 -/
def divCheckOne {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : Bool :=
  let sf := divExecState a d sgn
  let q := divOutQ sf
  let r := divOutR sf
  (sf.phase == .finish) &&
  if divCorner a d sgn then
    (q == divCornerBuggyQ a d sgn) && (r == 0) &&
    !(q == divSpecQ a d sgn && r == divSpecR a d sgn)
  else
    (q == divSpecQ a d sgn) && (r == divSpecR a d sgn)

/-- 全输入空间检查（2^xLen × 2^xLen × signed） -/
def divCheckAll (xLen : Nat) : Bool :=
  (List.range (2 ^ xLen)).all fun av =>
    (List.range (2 ^ xLen)).all fun dv =>
      [false, true].all fun sgn =>
        divCheckOne (BitVec.ofNat xLen av) (BitVec.ofNat xLen dv) sgn

/-- 统计 BUG1 触发锥大小 -/
def divCountCorners (xLen : Nat) : Nat :=
  (List.range (2 ^ xLen)).foldl (fun acc av =>
    (List.range (2 ^ xLen)).foldl (fun acc2 dv =>
      acc2 + [false, true].countP (fun sgn =>
        divCorner (BitVec.ofNat xLen av) (BitVec.ofNat xLen dv) sgn)) acc) 0

/- ========================================================================= -/
/- 5. 数值回归测试（先测试）                                                  -/
/- ========================================================================= -/

section DivRegressionTests

-- 5.1 基础件单元测试（by decide）
example : divW 32 = 5 := by decide
example : divW 8 = 3 := by decide
example : divW 4 = 2 := by decide

-- divLez（:44-45，D5）
example : divLez (0b0101 : BitVec 4) = 1 := by decide      -- 前导零 1
example : divLez (0b1000 : BitVec 4) = 0 := by decide      -- MSB 置位
example : divLez (0b0001 : BitVec 4) = 3 := by decide      -- |a|=1 → 前导零 3
example : divLez (0 : BitVec 4) = 0 := by decide           -- 退化：全零输入 → 0（≠ 4）
example : divLez (0x80000000 : BitVec 32) = 0 := by decide
example : divLez (1 : BitVec 32) = 31 := by decide

-- divAbs / divOvfDet（:32-35）
example : divAbs (0xFFFFFFF9 : BitVec 32) true = 7 := by decide   -- |-7| = 7
example : divAbs (7 : BitVec 32) true = 7 := by decide
example : divAbs (7 : BitVec 32) false = 7 := by decide
example : divOvfDet (0x80000000 : BitVec 32) 0xFFFFFFFF true = true := by decide
example : divOvfDet (0x80000000 : BitVec 32) 0xFFFFFFFF false = false := by decide
example : divOvfDet (0x80000001 : BitVec 32) 0xFFFFFFFF true = false := by decide

-- 截断向零除法（规约辅助）
example : divTdiv (-7) 2 = -3 := by decide
example : divTmod (-7) 2 = -1 := by decide
example : divTdiv 7 (-2) = -3 := by decide
example : divTmod 7 (-2) = 1 := by decide
example : divTdiv (-7) (-2) = 3 := by decide
example : divTmod (-7) (-2) = -1 := by decide

-- 规约自身健全性（xLen=4）
example : divSpecQ (7 : BitVec 4) 2 false = 3 := by decide
example : divSpecR (7 : BitVec 4) 2 false = 1 := by decide
example : divSpecQ (0xF : BitVec 4) 1 true = 0xF := by decide     -- -1/1 = -1
example : divSpecQ (8 : BitVec 4) 0xF true = 8 := by decide       -- INT_MIN ÷ -1 → INT_MIN
example : divSpecR (8 : BitVec 4) 0xF true = 0 := by decide       -- overflow → r = 0
example : divSpecQ (5 : BitVec 4) 0 false = 0xF := by decide      -- 除零 → 全1
example : divSpecR (5 : BitVec 4) 0 false = 5 := by decide        -- 除零 → r = a
example : divSpecQ (9 : BitVec 4) 2 true = 0xD := by decide       -- -7/2 = -3
example : divSpecR (9 : BitVec 4) 2 true = 0xF := by decide       -- -7%2 = -1

-- BUG1 机制（Q4）：iter 可达 32（6 位），装入 5 位 cnt 截断为 0
example : divIter (divLez (0x80000000 : BitVec 32)) (divLez (1 : BitVec 32))
    = (32 : BitVec (divW 32 + 1)) := by decide
example : (divIter (divLez (0x80000000 : BitVec 32)) (divLez (1 : BitVec 32))).setWidth (divW 32)
    = (0 : BitVec (divW 32)) := by decide
-- iter=0 支不可达 compute 的旁证：|a| ≥ |d| > 0 时 iter ≥ 1（xLen=4 全枚举）
example : ∀ a d : BitVec 4, d ≠ 0 → ¬(a < d) →
    divIter (divLez a) (divLez d) ≠ (0 : BitVec (divW 4 + 1)) := by decide

-- 5.2 xLen=4 全穷举（16×16×2 = 512 组合；非触发锥：q、r 双双 = RISC-V 规约；
--     触发锥 = BUG1 错误值且必发散；含停机检查）
theorem div_test_xlen4_exhaustive : divCheckAll 4 = true := by native_decide

-- BUG1 触发锥大小：xLen=4 → 9（unsigned a∈[8,15],d=1 计 8；signed a=-8,d=1 计 1）
theorem div_test_xlen4_corners : divCountCorners 4 = 9 := by native_decide

-- 5.3 xLen=8 全穷举（256×256×2 = 131072 组合；T3 的降级穷举证据）
theorem div_test_xlen8_exhaustive : divCheckAll 8 = true := by native_decide

-- BUG1 触发锥大小：xLen=8 → 129（unsigned a∈[128,255],d=1 计 128；signed a=-128,d=1 计 1）
theorem div_test_xlen8_corners : divCountCorners 8 = 129 := by native_decide

-- 5.4 xLen=32 定向向量
-- 特殊情形（T1 的实证侧）
theorem div_test_32_div_by_zero_u :
    divExec (5 : BitVec 32) 0 false = (0xFFFFFFFF#32, 5#32) := by native_decide
theorem div_test_32_div_by_zero_s :
    divExec (0xFFFFFFF9 : BitVec 32) 0 true = (0xFFFFFFFF#32, 0xFFFFFFF9#32) := by native_decide
theorem div_test_32_zero_div_zero :
    divExec (0 : BitVec 32) 0 false = (0xFFFFFFFF#32, 0#32) := by native_decide
theorem div_test_32_overflow_fresh :      -- INT_MIN ÷ -1，zeroQ 干净 → 符合 RISC-V
    divExec (0x80000000 : BitVec 32) 0xFFFFFFFF true = (0x80000000#32, 0#32) := by native_decide
theorem div_test_32_zero_dividend :
    divExec (0 : BitVec 32) 5 false = (0#32, 0#32) := by native_decide
theorem div_test_32_zeroq :               -- |a|<|d| → (0, a)
    divExec (1 : BitVec 32) 0x80000000 false = (0#32, 1#32) := by native_decide

-- 一般情形（非触发锥 ⇒ 符合规约）
theorem div_test_32_div_x1 :              -- x/1 且 msb(|x|)=0：不受 BUG1 影响
    divExec (5 : BitVec 32) 1 false = (5#32, 0#32) := by native_decide
theorem div_test_32_basic_u :
    divExec (7 : BitVec 32) 2 false = (3#32, 1#32) := by native_decide
theorem div_test_32_neg_pos :
    divExec (0xFFFFFFF9 : BitVec 32) 2 true = (0xFFFFFFFD#32, 0xFFFFFFFF#32) := by native_decide  -- -7/2=(-3,-1)
theorem div_test_32_pos_neg :
    divExec (7 : BitVec 32) 0xFFFFFFFE true = (0xFFFFFFFD#32, 1#32) := by native_decide          -- 7/-2=(-3,1)
theorem div_test_32_neg_neg :
    divExec (0xFFFFFFF9 : BitVec 32) 0xFFFFFFFE true = (3#32, 0xFFFFFFFF#32) := by native_decide -- -7/-2=(3,-1)
theorem div_test_32_intmin_div2 :
    divExec (0x80000000 : BitVec 32) 2 true = (0xC0000000#32, 0#32) := by native_decide          -- INT_MIN/2
theorem div_test_32_big_div2_u :          -- msb(a)=1 但 iter=31 不截断（非触发锥）
    divExec (0xFFFFFFFD : BitVec 32) 2 false = (0x7FFFFFFE#32, 1#32) := by native_decide
theorem div_test_32_random_u :            -- 恢复路径（remIsNeg）；与 ChiselSim
    divExec (0xDEADBEEF : BitVec 32) 0x1234 false = (0xC3BA5#32, 0x76B#32) := by native_decide
theorem div_test_32_random_s :            -- I-18b 实测逐值一致（doc/22）
    divExec (0xDEADBEEF : BitVec 32) 0x1234 true = (0xFFFE2B63#32, 0xFFFFF8D3#32) := by native_decide

-- 余数恢复（Q7；I-18 撤案后的回归钉）：remIsNeg 路径输出 = RISC-V 规约，
-- 与 ChiselSim 实测（doc/22：4/3(u)=(1,1)）逐值一致
theorem div_test_32_recovery_unsigned :
    divExec (4 : BitVec 32) 3 false = (1#32, 1#32) := by native_decide
theorem div_test_32_recovery_signed :     -- -4/3 → (-1, -1)
    divExec (0xFFFFFFFC : BitVec 32) 3 true = (0xFFFFFFFF#32, 0xFFFFFFFF#32) := by native_decide
theorem div_test_32_recovery_eq_spec :
    divExec (4 : BitVec 32) 3 false =
      (divSpecQ (4 : BitVec 32) 3 false, divSpecR (4 : BitVec 32) 3 false) := by native_decide

-- BUG1 witness（Q4）：模型输出 = 预测错误值，≠ RISC-V 规约
theorem div_test_32_bug1_unsigned :
    divExec (0x80000000 : BitVec 32) 1 false = (1#32, 0#32) := by native_decide
theorem div_test_32_bug1_unsigned_max :
    divExec (0xFFFFFFFF : BitVec 32) 1 false = (1#32, 0#32) := by native_decide
theorem div_test_32_bug1_signed :
    divExec (0x80000000 : BitVec 32) 1 true = (0xFFFFFFFF#32, 0#32) := by native_decide
theorem div_test_32_bug1_ne_spec :        -- 与规约确实不同（bug 实证）
    divExec (0x80000000 : BitVec 32) 1 false ≠
      (divSpecQ (0x80000000 : BitVec 32) 1 false,
       divSpecR (0x80000000 : BitVec 32) 1 false) := by native_decide

-- BUG2 复现（Q5）：txn1 |a|<|d|（zeroQ 置 1）→ 回 idle → txn2 INT_MIN ÷ -1（直达 finish）
def divBug2Seq : DivState 32 :=
  let s1 := divExecState (3 : BitVec 32) 5 false            -- zeroQ 事务，zeroQReg←1
  let s2 := divStep s1 (divNop 32)                          -- out.fire → s_idle
  divRunTo (divStep s2 ⟨true, 0x80000000, 0xFFFFFFFF, true, true⟩) (divNop 32) 72

theorem div_test_stale_zeroQ_bug2 :       -- q 正确（INT_MIN），r 错误（rawA，应为 0）
    divOutQ divBug2Seq = 0x80000000#32 ∧ divOutR divBug2Seq = 0x80000000#32 := by native_decide
theorem div_test_stale_zeroQ_ne_spec :    -- 与规约确实不同
    divOutR divBug2Seq ≠ divSpecR (0x80000000 : BitVec 32) 0xFFFFFFFF true := by native_decide

end DivRegressionTests

/- ========================================================================= -/
/- 6. T1 特殊情形（任意 xLen，不经 compute）                                  -/
/- ========================================================================= -/

/-- T1a divByZero：idle 受理 d=0 的事务，下一拍直达 finish，
    输出 (q, r) = (全1, a)——RISC-V 除零语义（:75,:77,:79-80,:88） -/
theorem div_t1_divByZero {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true) (hdz : i.d = 0) :
    (divStep s i).phase = .finish ∧
    divOutQ (divStep s i) = BitVec.allOnes xLen ∧
    divOutR (divStep s i) = i.a := by
  simp [divStep, h, hv, hdz, divDbzDet, divOutQ, divOutR, divSpecialQ, divSpecialR]

/-- T1b overflow：idle 受理 signed INT_MIN ÷ -1，下一拍直达 finish，q = INT_MIN；
    r = if s.zeroQ then i.a else 0——【r 依赖陈旧 zeroQReg，即 BUG2（Q5）的
    精确刻画】：zeroQ=1（上一事务 |a|<|d|）时 r=rawA ≠ 0，违反 RISC-V。 -/
theorem div_t1_overflow {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hovf : divOvfDet i.a i.d i.signed = true) (hndz : i.d ≠ 0) :
    (divStep s i).phase = .finish ∧
    divOutQ (divStep s i) = divIntMin xLen ∧
    divOutR (divStep s i) = (if s.zeroQ then i.a else 0) := by
  -- simp 把 (0 : BitVec w) 规范为 0#w（BitVec.ofNat 形式），假设须同形
  have hndz' : i.d ≠ (0#xLen) := hndz
  simp [divStep, h, hv, hovf, hndz', divDbzDet, divOutQ, divOutR, divSpecialQ, divSpecialR]

/-- T1b 推论（无 bug 面）：zeroQReg 干净时 overflow 余数 = 0，符合 RISC-V -/
theorem div_t1_overflow_r_zero {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hovf : divOvfDet i.a i.d i.signed = true) (hndz : i.d ≠ 0)
    (hzq : s.zeroQ = false) :
    divOutR (divStep s i) = 0 := by
  have ⟨_, _, hr⟩ := div_t1_overflow s i h hv hovf hndz
  rw [hr]; simp [hzq]

/-- T1b 推论（BUG2 实证面）：zeroQReg 陈旧为 1 时 overflow 余数 = rawA，违反 RISC-V -/
theorem div_t1_overflow_r_stale {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hovf : divOvfDet i.a i.d i.signed = true) (hndz : i.d ≠ 0)
    (hzq : s.zeroQ = true) :
    divOutR (divStep s i) = i.a := by
  have ⟨_, _, hr⟩ := div_t1_overflow s i h hv hovf hndz
  rw [hr]; simp [hzq]

/-- T1c zeroQ：idle 受理非特殊事务（|a|<|d|），经 s_pre 一拍直达 finish，
    输出 (q, r) = (0, a)（:77,:93）——与第二拍输入 j 无关 -/
theorem div_t1_zeroQ {xLen : Nat} (s : DivState xLen) (i j : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hnovf : divOvfDet i.a i.d i.signed = false) (hndz : i.d ≠ 0)
    (hlt : BitVec.ult (divAbs i.a i.signed) (divAbs i.d i.signed) = true) :
    (divStep (divStep s i) j).phase = .finish ∧
    divOutQ (divStep (divStep s i) j) = 0 ∧
    divOutR (divStep (divStep s i) j) = i.a := by
  have hndz' : i.d ≠ (0#xLen) := hndz
  simp [divStep, h, hv, hnovf, hndz', hlt, divDbzDet, divOutQ, divOutR, divSpecialQ, divSpecialR]

/- ========================================================================= -/
/- 7. T2 终止性                                                               -/
/- ========================================================================= -/

/-- 停机于 finish 后不再离开 -/
theorem divRunTo_finish {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .finish) : ∀ n, (divRunTo s i n).phase = .finish := by
  intro n; cases n <;> simp [divRunTo, h]

/-- 未停机时 divRunTo 展开一拍 -/
theorem divRunTo_step {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase ≠ .finish) (n : Nat) :
    divRunTo s i (n + 1) = divRunTo (divStep s i) i n := by
  simp [divRunTo, beq_false_of_ne h]

/-- s_recovery 下一拍到 s_finish（:100） -/
theorem divRunTo_recovery_finish {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .recovery) {n : Nat} (hn : 1 ≤ n) :
    (divRunTo s i n).phase = .finish := by
  cases n with
  | zero => omega
  | succ m =>
      have hstep : (divStep s i).phase = .finish := by simp [divStep, h]
      have hnf : s.phase ≠ .finish := by simp [h]
      rw [divRunTo_step s i hnf m]
      exact divRunTo_finish _ i hstep m

/-- toNat = 0 的位向量即 0 -/
theorem div_toNat_eq_zero {w : Nat} {c : BitVec w} (h : c.toNat = 0) : c = 0 :=
  BitVec.toNat_inj.mp (by simp [h])

/-- 非零计数值减一：toNat 同步减一（cnt 严格递减的算术侧） -/
theorem div_toNat_sub_one {w : Nat} (hw : 1 ≤ w) {c : BitVec w} (h : c ≠ 0) :
    (c - 1).toNat = c.toNat - 1 := by
  rw [BitVec.toNat_sub]
  -- 目标中的 1 是 OfNat 形式，toNat_one 针对 1#w（ofNat 形式），二者 defeq
  have h1 : (1 : BitVec w).toNat = 1 := BitVec.toNat_one (by omega)
  rw [h1]
  have hc : 1 ≤ c.toNat := by
    by_cases hz : c.toNat = 0
    · exact absurd (div_toNat_eq_zero hz) h
    · omega
  have hlt : c.toNat - 1 < 2 ^ w := by have := BitVec.isLt c; omega
  have h2w : 0 < 2 ^ w := Nat.two_pow_pos w
  have he : (2 ^ w - 1) + c.toNat = (c.toNat - 1) + 2 ^ w := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- T2 核心：s_compute 中 cnt 严格递减，至多 cnt.toNat+1 拍到 recovery，
    再 1 拍到 finish（合计 cnt.toNat+2 拍内必停机） -/
theorem div_compute_finish {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen) :
    ∀ k : Nat, s.phase = .compute → s.cnt.toNat ≤ k →
      (divRunTo s i (k + 2)).phase = .finish := by
  intro k
  induction k generalizing s with
  | zero =>
      intro hp hk
      have hc0 : s.cnt = 0 := div_toNat_eq_zero (Nat.le_zero.mp hk)
      have hnf : s.phase ≠ .finish := by simp [hp]
      have hs1 : (divStep s i).phase = .recovery := by
        simp [divStep, hp, hc0, divCntNext]
      show (divRunTo s i (1 + 1)).phase = .finish
      rw [divRunTo_step s i hnf 1]
      exact divRunTo_recovery_finish _ i hs1 (by omega)
  | succ k ih =>
      intro hp hk
      have hnf : s.phase ≠ .finish := by simp [hp]
      show (divRunTo s i ((k + 2) + 1)).phase = .finish
      rw [divRunTo_step s i hnf (k + 2)]
      by_cases hz0 : s.cnt.toNat = 0
      · have hc0 : s.cnt = 0 := div_toNat_eq_zero hz0
        have hs1 : (divStep s i).phase = .recovery := by
          simp [divStep, hp, hc0, divCntNext]
        exact divRunTo_recovery_finish _ i hs1 (by omega)
      · have hne : s.cnt ≠ 0 := fun hc => hz0 (by rw [hc]; exact BitVec.toNat_zero)
        cases hcn : (divCntNext s.cnt == 0) with
        | true =>
            have hcn' : divCntNext s.cnt = 0 := eq_of_beq hcn
            have hs1 : (divStep s i).phase = .recovery := by
              simp [divStep, hp, hcn']
            exact divRunTo_recovery_finish _ i hs1 (by omega)
        | false =>
            have hcn' : divCntNext s.cnt ≠ 0 := ne_of_beq_false hcn
            -- simp 把 (0 : BitVec w) 规范为 0#w（BitVec.ofNat 形式），假设须同形
            have hcn'' : divCntNext s.cnt ≠ (0#(divW xLen)) := hcn'
            have hne' : s.cnt ≠ (0#(divW xLen)) := hne
            have hw : 1 ≤ divW xLen := by simp [divW]
            have hsub : (s.cnt - 1).toNat = s.cnt.toNat - 1 := div_toNat_sub_one hw hne
            have hs1p : (divStep s i).phase = .compute := by
              simp [divStep, hp, hcn'']
            have hs1c : (divStep s i).cnt.toNat ≤ k := by
              have hc1 : (divStep s i).cnt = divCntNext s.cnt := by simp [divStep, hp]
              have hdn : divCntNext s.cnt = s.cnt - 1 := by
                simp [divCntNext, hne']
              rw [hc1, hdn, hsub]; omega
            exact ih _ hs1p hs1c

/-- T2 整机：idle 受理（in.fire）后，至多 2^divW(xLen)+4 拍内 out.valid
    （xLen=32 时上界 36；精细路径 1(idle)+1(pre)+(cnt+1)(compute)+1(recovery)
    ≈ iter+4，BUG1 时 cnt 为截断值） -/
theorem div_terminates {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true) :
    (divRunTo s i (2 ^ divW xLen + 4)).phase = .finish := by
  have hnf : s.phase ≠ .finish := by simp [h]
  rw [show 2 ^ divW xLen + 4 = (2 ^ divW xLen + 3) + 1 from by omega,
    divRunTo_step s i hnf _]
  cases hsp : (divOvfDet i.a i.d i.signed || divDbzDet i.d) with
  | true =>
      have hs1 : (divStep s i).phase = .finish := by simp [divStep, h, hv, hsp]
      exact divRunTo_finish _ i hs1 _
  | false =>
      have hs1 : (divStep s i).phase = .pre := by simp [divStep, h, hv, hsp]
      have hnf1 : (divStep s i).phase ≠ .finish := by simp [hs1]
      rw [show 2 ^ divW xLen + 3 = (2 ^ divW xLen + 2) + 1 from by omega,
        divRunTo_step _ i hnf1 _]
      cases hzq : BitVec.ult (divAbs i.a i.signed) (divAbs i.d i.signed) with
      | true =>
          have hs2 : (divStep (divStep s i) i).phase = .finish := by
            simp [divStep, h, hv, hsp, hzq]
          exact divRunTo_finish _ i hs2 _
      | false =>
          have hs2 : (divStep (divStep s i) i).phase = .compute := by
            simp [divStep, h, hv, hsp, hzq]
          have hcnt : (divStep (divStep s i) i).cnt.toNat ≤ 2 ^ divW xLen :=
            Nat.le_of_lt (BitVec.isLt _)
          exact div_compute_finish _ i _ hs2 hcnt

/- ========================================================================= -/
/- 8. T4 握手契约（:81-82, :101-102）                                         -/
/- ========================================================================= -/

/-- in.ready 当且仅当 s_idle -/
theorem div_in_ready_iff {xLen : Nat} (s : DivState xLen) :
    divInReady s = true ↔ s.phase = .idle := by
  cases h : s.phase <;> simp [divInReady, h] <;> decide

/-- out.valid 当且仅当 s_finish -/
theorem div_out_valid_iff {xLen : Nat} (s : DivState xLen) :
    divOutValid s = true ↔ s.phase = .finish := by
  cases h : s.phase <;> simp [divOutValid, h] <;> decide

/-- T4 Irrevocable：s_finish 且 out.fire 不发生（out_ready=0）时，
    状态停留 s_finish，q/r 输出稳定（寄存器直出，:132-134 只清 cnt），
    valid 保持为 1 -/
theorem div_finish_stable {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .finish) (hr : i.out_ready = false) :
    (divStep s i).phase = .finish ∧
    divOutQ (divStep s i) = divOutQ s ∧
    divOutR (divStep s i) = divOutR s ∧
    divOutValid (divStep s i) = true := by
  simp [divStep, h, hr, divOutQ, divOutR, divSpecialQ, divSpecialR,
    divSignedQ, divSignedR, divOutValid] <;> decide

/- ========================================================================= -/
/- 9. 公理审计（native_decide 引入 Lean.ofReduceBool；bv_decide 未使用）      -/
/- ========================================================================= -/

#print axioms div_t1_divByZero
#print axioms div_t1_overflow
#print axioms div_t1_zeroQ
#print axioms div_compute_finish
#print axioms div_terminates
#print axioms div_finish_stable
#print axioms div_test_xlen4_exhaustive
#print axioms div_test_xlen8_exhaustive
#print axioms div_test_32_bug1_unsigned
#print axioms div_test_32_recovery_unsigned
#print axioms div_test_stale_zeroQ_bug2

end Ventus.Arith
