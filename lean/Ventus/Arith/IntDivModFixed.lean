/- ========================================================================= -/
/-                     Arith/IntDivModFixed.lean                             -/
/-  IntDivMod 已确认 bug 的"修复即验证"（I-17/I-19；I-18 已于 2026-09-07 撤案，doc/23）：         -/
/-  修复版模型 dvfStep（原 divStep 的变体，原文件不动）+ 修复有效性 +          -/
/-  一般正确性（穷举/定向/符号三档）+ 回归安全性。                             -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/IntDivMod.scala    -/
/-    （快照 6811725；行号下同）                                              -/
/-                                                                           -/
/- ======================== Chisel 最小修复 diff（供上游参考） =============== -/
/-                                                                           -/
/-  I-17（:56，cnt 加宽 1 位）。【2026-09-07 修订（doc/23 §7）：仅加宽 cnt 在 Chisel 6 下【不够】——`+`/`-` 是回绕运算，:46 的 dLez - aLez + 1.U 在 5 位内回绕（iter=32 已回绕为 0），加宽 cnt 只是零扩展装入 0。必须同时加宽 iter 算术，如 iter = Mux(aLez > dLez, 0.U, (dLez -& aLez) +& 1.U)（7 位值，装入 6 位 cnt 无损）】： -/
/-  -  val cnt = RegInit(0.U(log2Up(xLen).W))                                 -/
/-  +  val cnt = RegInit(0.U((log2Up(xLen) + 1).W))                           -/
/-  （cnt_next/:97-98 的判零逻辑不受影响；:118 变同宽连接。Lean 修复版 dvfStep 的 cnt := divIter 对应『cnt 加宽 + iter 完整送达』的【修订后】diff）                  -/
/-                                                                           -/
/-  I-18【已撤案（2026-09-07，doc/23）：RTL 无此 bug，本 diff 勿交付上游】。          -/
/-      撤案缘由：Chisel 6 的 `+` 是回绕加（Bits.scala:479 do_+ = do_+%），原版       -/
/-      本就正确；下方 diff 与原版在可达状态（dReg 恒偶）下逐位等价（no-op）：               -/
/-  -  val recoveryR = Mux(remIsNeg.asBool,                                   -/
/-  -      aReg.tail(1).head(xLen) + dReg.tail(1).head(xLen),                 -/
/-  -      aReg.tail(1).head(xLen))                                           -/
/-  +  val recoveryR = Mux(remIsNeg.asBool,                                   -/
/-  +      (aReg +% dReg).tail(1).head(xLen), aReg.tail(1).head(xLen))        -/
/-  （注：Chisel 6 下原 recoveryR 本就是 xLen 位回绕加，宽度无变化；+% 写法安全等价） -/
/-                                                                           -/
/-  I-19（03 报告给了两个修复方案，本文件选取"s_idle 拍清 zeroQReg"方案；      -/
/-      另一方案是 :77 specialR 改用当拍组合值 unsignedAReg<unsignedDReg）：   -/
/-     is(s_idle){                                                            -/
/-       aReg := 0.U                                                          -/
/-       dReg := 0.U                                                          -/
/-       cnt := 0.U                                                           -/
/-  +    zeroQReg := false.B                                                  -/
/-     }                                                                      -/
/-  （安全性：zeroQReg 唯一的消费者是 :77/:79-80 的 finish 输出；任何经        -/
/-    s_pre 的事务都会重写 zeroQReg（:54），idle 清零只影响直达 finish 的     -/
/-    overflow/divByZero 事务——此时正确值恰为"zeroQ=0"的行为：divByZero 由    -/
/-    divByZeroReg 独立保证 r=rawA，overflow 要求 r=0。）                      -/
/-                                                                           -/
/- ======================== 与原模型的对应 ================================== -/
/-  DvfState = DivState 但 cnt : BitVec (divW xLen + 1)（I-17）；dvfStep 与   -/
/-  divStep 逐字相同，仅三处修复：                                             -/
/-    (1) idle 分支 base 增加 zeroQ := false（I-19）；                         -/
/-    (2) pre 分支 cnt := divIter aL dL（不再 setWidth 截断，I-17）；          -/
/-    (3) recovery 分支 commonR 用 dvfCommonRNext（先加后截；I-18 撤案后与原版等价）。          -/
/-  输出函数 dvfOutQ/dvfOutR 与 divOutQ/divOutR 逐字对应（specialR 结构不变， -/
/-  I-19 靠 idle 清零生效）。                                                  -/
/-                                                                           -/
/-  公理审计：多拍数值测试用 native_decide（多 Lean.ofReduceBool，归档注明）； -/
/-  符号证明不使用 bv_decide。                                                 -/
/- ========================================================================= -/

import Ventus.Arith.IntDivMod

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 修复版模型（DvfState + dvfStep + 输出）                                  -/
/- ========================================================================= -/

/-- 修复版寄存器状态：字段与 DivState 一一对应，唯一差异是 cnt 加宽 1 位
    （I-17 修复，对照 :56） -/
structure DvfState (xLen : Nat) where
  phase     : DivPhase                -- :26
  qSign     : Bool                    -- :30
  rSign     : Bool                    -- :31
  rawA      : BitVec xLen             -- :38
  unsignedA : BitVec xLen             -- :39
  unsignedD : BitVec xLen             -- :40
  overflow  : Bool                    -- :41
  divByZero : Bool                    -- :42
  zeroQ     : Bool                    -- :54
  aReg      : BitVec (xLen + 2)       -- :48
  dReg      : BitVec (xLen + 2)       -- :49
  cnt       : BitVec (divW xLen + 1)  -- :56（I-17 修复：divW+1 位）
  Q         : BitVec xLen             -- :59
  QN        : BitVec xLen             -- :60
  commonQ   : BitVec xLen             -- :69
  commonR   : BitVec xLen             -- :71

/-- 初始状态（同 divInit；无复位寄存器取 0，见 IntDivMod.lean D6） -/
def dvfInit (xLen : Nat) : DvfState xLen where
  phase := .idle
  qSign := false; rSign := false
  rawA := 0; unsignedA := 0; unsignedD := 0
  overflow := false; divByZero := false; zeroQ := false
  aReg := 0; dReg := 0; cnt := 0; Q := 0; QN := 0
  commonQ := 0; commonR := 0

/-- I-18 修复版 commonR 右值（:70-71）：先加后截——
    Mux(remIsNeg, aReg +% dReg, aReg).tail(1).head(xLen) 再 >>dLez 取低 xLen 位。
    【I-18 撤案（doc/23）后】本函数与修正后的 divCommonRNext 在 dReg 为偶时
    （可达状态：dReg ∈ {0, dNorm}，dNorm 由 Cat 构造成偶）逐位相等——
    "修复"是语义保持的 no-op；remIsNeg=0 时无条件相等
    （dvf_commonR_eq_orig_of_not_neg）。 -/
def dvfCommonRNext {xLen : Nat} (aReg dReg : BitVec (xLen + 2))
    (dLez : BitVec (divW xLen)) : BitVec xLen :=
  let sum : BitVec (xLen + 2) := if aReg.msb then aReg + dReg else aReg
  let recR : BitVec (xLen + 1) := (sum.extractLsb' 1 xLen).zeroExtend (xLen + 1)
  (recR >>> dLez).setWidth xLen

/-- 修复版单拍状态转移：与 divStep 逐字相同，仅三处修复（注释标注） -/
def dvfStep {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen) : DvfState xLen :=
  match s.phase with
  | .idle =>
      -- I-19 修复：s_idle 拍清 zeroQ（Chisel diff 见文件头）
      let base := { s with aReg := 0, dReg := 0, cnt := 0, zeroQ := false }
      if i.in_valid then
        let ovf := divOvfDet i.a i.d i.signed
        let dbz := divDbzDet i.d
        { base with
          phase     := if ovf || dbz then .finish else .pre,
          qSign     := divSign i.a i.signed != divSign i.d i.signed,
          rSign     := divSign i.a i.signed,
          rawA      := i.a,
          unsignedA := divAbs i.a i.signed,
          unsignedD := divAbs i.d i.signed,
          overflow  := ovf,
          divByZero := dbz }
      else base
  | .pre =>
      let zq := BitVec.ult s.unsignedA s.unsignedD
      let base := { s with zeroQ := zq }
      if zq then { base with phase := .finish, cnt := 0 }
      else
        let aL := divLez s.unsignedA
        let dL := divLez s.unsignedD
        { base with
          phase := .compute,
          aReg  := divANorm s.unsignedA aL,
          dReg  := divDNorm s.unsignedD dL,
          cnt   := divIter aL dL,          -- I-17 修复：同宽连接，无截断
          Q     := 0, QN := 0 }
  | .compute =>
      let cN := divCntNext s.cnt
      let dL := divLez s.unsignedD
      { s with
        phase := if cN == 0 then .recovery else .compute,
        cnt   := cN,
        aReg  := divANext s.aReg (divDNorm s.unsignedD dL)
                             (divDNegNorm s.unsignedD dL),
        Q     := (s.Q <<< 1) ||| (if divSelPos s.aReg then 1 else 0),
        QN    := (s.QN <<< 1) ||| (if divSelNeg s.aReg then 1 else 0) }
  | .recovery =>
      { s with
        phase   := .finish,
        cnt     := 0,
        commonQ := divCommonQNext s.aReg s.Q s.QN,
        commonR := dvfCommonRNext s.aReg s.dReg (divLez s.unsignedD) }  -- I-18 修复
  | .finish =>
      let base := { s with cnt := 0 }
      if i.out_ready then { base with phase := .idle } else base

/-- signedQ（:73） -/
def dvfSignedQ {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.qSign then ~~~s.commonQ + 1 else s.commonQ

/-- signedR（:74） -/
def dvfSignedR {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.rSign then ~~~s.commonR + 1 else s.commonR

/-- specialQ（:75） -/
def dvfSpecialQ {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.divByZero then BitVec.allOnes xLen
  else if s.overflow then divIntMin xLen
  else 0

/-- specialR（:77；结构不变，I-19 由 idle 清零保证此处的 zeroQ 必为当事务值） -/
def dvfSpecialR {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ then s.rawA else 0

/-- io.out.bits.q（:79） -/
def dvfOutQ {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ || s.overflow then dvfSpecialQ s else dvfSignedQ s

/-- io.out.bits.r（:80） -/
def dvfOutR {xLen : Nat} (s : DvfState xLen) : BitVec xLen :=
  if s.divByZero || s.zeroQ || s.overflow then dvfSpecialR s else dvfSignedR s

/-- io.out.valid（:81） -/
def dvfOutValid {xLen : Nat} (s : DvfState xLen) : Bool := s.phase == .finish

/-- io.in.ready（:82） -/
def dvfInReady {xLen : Nat} (s : DvfState xLen) : Bool := s.phase == .idle

/- ========================================================================= -/
/- 2. 执行/检查脚手架（对照 divRunTo/divExecState/divExec）                    -/
/- ========================================================================= -/

/-- 跑到 s_finish 为止（带 fuel） -/
def dvfRunTo {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen) :
    Nat → DvfState xLen
  | 0 => s
  | n + 1 => if s.phase == .finish then s else dvfRunTo (dvfStep s i) i n

/-- 从 dvfInit 执行单事务，返回停机状态 -/
def dvfExecState {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : DvfState xLen :=
  dvfRunTo (dvfStep (dvfInit xLen) ⟨true, a, d, sgn, true⟩) (divNop xLen) (2 * xLen + 8)

/-- 单事务输出 (q, r) -/
def dvfExec {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : BitVec xLen × BitVec xLen :=
  let sf := dvfExecState a d sgn
  (dvfOutQ sf, dvfOutR sf)

/-- 修复版全正确性单点检查：停机且 (q, r) 双双符合 RISC-V 规约 -/
def dvfCheckOne {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : Bool :=
  let sf := dvfExecState a d sgn
  ((sf.phase == .finish) && (dvfOutQ sf == divSpecQ a d sgn)) &&
    (dvfOutR sf == divSpecR a d sgn)

/-- 修复版全输入空间检查（2^xLen × 2^xLen × signed） -/
def dvfCheckAll (xLen : Nat) : Bool :=
  (List.range (2 ^ xLen)).all fun av =>
    (List.range (2 ^ xLen)).all fun dv =>
      [false, true].all fun sgn =>
        dvfCheckOne (BitVec.ofNat xLen av) (BitVec.ofNat xLen dv) sgn

/-- 回归单点检查（单事务，两侧各自从 init 出发）：未触发 I-17（divCorner）且
    原版终态非 remIsNeg 时，修复版与原版输出完全一致。注：I-18 撤案
    （doc/23）后 remIsNeg 排除项已无必要——强化版 dvfRegrOneFull（第 8 节末）
    在除 I-17 锥外的全输入上逐点等价。
    （单事务从 init 出发 zeroQ=false，I-19 不涉及；多事务回归见 dvfT_regr_*。） -/
def dvfRegrOne {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : Bool :=
  let so := divExecState a d sgn
  (divCorner a d sgn || so.aReg.msb) || (divExec a d sgn == dvfExec a d sgn)

/-- 回归全输入空间检查 -/
def dvfRegrAll (xLen : Nat) : Bool :=
  (List.range (2 ^ xLen)).all fun av =>
    (List.range (2 ^ xLen)).all fun dv =>
      [false, true].all fun sgn =>
        dvfRegrOne (BitVec.ofNat xLen av) (BitVec.ofNat xLen dv) sgn

/- ========================================================================= -/
/- 3. 修复有效性：三个 bug 的 witness 在修复版下变绿（对照 IntDivMod.lean      -/
/-    5.3/5.4 的同名输入；全部为 xLen=32，native_decide）                      -/
/- ========================================================================= -/

section DvfWitnessTests

-- I-17（对照 div_test_32_bug1_*：原版输出 (1,0)/(1,0)/(0xFFFFFFFF,0)）
theorem dvfT_i17_unsigned :
    dvfExec (0x80000000 : BitVec 32) 1 false = (0x80000000#32, 0#32) := by native_decide
theorem dvfT_i17_unsigned_max :
    dvfExec (0xFFFFFFFF : BitVec 32) 1 false = (0xFFFFFFFF#32, 0#32) := by native_decide
theorem dvfT_i17_signed :        -- INT_MIN ÷ 1
    dvfExec (0x80000000 : BitVec 32) 1 true = (0x80000000#32, 0#32) := by native_decide
theorem dvfT_i17_eq_spec :       -- 且恰为 RISC-V 规约值
    dvfExec (0x80000000 : BitVec 32) 1 false =
      (divSpecQ (0x80000000 : BitVec 32) 1 false,
       divSpecR (0x80000000 : BitVec 32) 1 false) := by native_decide

-- I-18（撤案后：修正版原版模型在这些输入上亦为规约值，doc/23）
theorem dvfT_i18_unsigned :      -- 4/3 → (1, 1)
    dvfExec (4 : BitVec 32) 3 false = (1#32, 1#32) := by native_decide
theorem dvfT_i18_signed :        -- -4/3 → (-1, -1)
    dvfExec (0xFFFFFFFC : BitVec 32) 3 true = (0xFFFFFFFF#32, 0xFFFFFFFF#32) := by native_decide
theorem dvfT_i18_random_u :      -- 0xDEADBEEF/0x1234：r = 0x76B（原版 0x276B）
    dvfExec (0xDEADBEEF : BitVec 32) 0x1234 false = (0xC3BA5#32, 0x76B#32) := by native_decide
theorem dvfT_i18_random_s :      -- signed 同输入：r = -0x72D（|a|=0x21524111，原版 0xFFFFD8D3）
    dvfExec (0xDEADBEEF : BitVec 32) 0x1234 true = (0xFFFE2B63#32, 0xFFFFF8D3#32) := by
  native_decide
theorem dvfT_i18_eq_spec :
    dvfExec (4 : BitVec 32) 3 false =
      (divSpecQ (4 : BitVec 32) 3 false, divSpecR (4 : BitVec 32) 3 false) := by
  native_decide

-- I-19（对照 divBug2Seq/div_test_stale_zeroQ_bug2：原版 r=rawA=0x80000000）
def dvfBug2Seq : DvfState 32 :=
  let s1 := dvfExecState (3 : BitVec 32) 5 false            -- zeroQ 事务，zeroQReg←1
  let s2 := dvfStep s1 (divNop 32)                          -- out.fire → s_idle
  dvfRunTo (dvfStep s2 ⟨true, 0x80000000, 0xFFFFFFFF, true, true⟩) (divNop 32) 72

theorem dvfT_i19_fixed :         -- q = INT_MIN 且 r = 0（RISC-V overflow 语义）
    dvfOutQ dvfBug2Seq = 0x80000000#32 ∧ dvfOutR dvfBug2Seq = 0#32 := by native_decide
theorem dvfT_i19_eq_spec :
    dvfOutR dvfBug2Seq = divSpecR (0x80000000 : BitVec 32) 0xFFFFFFFF true := by
  native_decide

end DvfWitnessTests

/- ========================================================================= -/
/- 4. T1 特殊情形符号证明（任意 xLen；对照第 6 节 div_t1_*）                   -/
/- ========================================================================= -/

/-- T1a divByZero：输出 (q, r) = (全1, a)——修复不改变此路径 -/
theorem dvf_t1_divByZero {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true) (hdz : i.d = 0) :
    (dvfStep s i).phase = .finish ∧
    dvfOutQ (dvfStep s i) = BitVec.allOnes xLen ∧
    dvfOutR (dvfStep s i) = i.a := by
  simp [dvfStep, h, hv, hdz, divDbzDet, dvfOutQ, dvfOutR, dvfSpecialQ, dvfSpecialR]

/-- T1b overflow（I-19 修复有效性的符号形式）：signed INT_MIN ÷ (-1) 直达
    finish，q = INT_MIN 且 **r = 0 无条件成立**——不再依赖陈旧 zeroQReg
    （对照原版 div_t1_overflow 的 r = if s.zeroQ then i.a else 0） -/
theorem dvf_t1_overflow {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hovf : divOvfDet i.a i.d i.signed = true) (hndz : i.d ≠ 0) :
    (dvfStep s i).phase = .finish ∧
    dvfOutQ (dvfStep s i) = divIntMin xLen ∧
    dvfOutR (dvfStep s i) = 0 := by
  have hndz' : i.d ≠ (0#xLen) := hndz
  simp [dvfStep, h, hv, hovf, hndz', divDbzDet, dvfOutQ, dvfOutR, dvfSpecialQ, dvfSpecialR]

/-- T1c zeroQ：|a|<|d| 事务输出 (0, a)——修复不改变此路径 -/
theorem dvf_t1_zeroQ {xLen : Nat} (s : DvfState xLen) (i j : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hnovf : divOvfDet i.a i.d i.signed = false) (hndz : i.d ≠ 0)
    (hlt : BitVec.ult (divAbs i.a i.signed) (divAbs i.d i.signed) = true) :
    (dvfStep (dvfStep s i) j).phase = .finish ∧
    dvfOutQ (dvfStep (dvfStep s i) j) = 0 ∧
    dvfOutR (dvfStep (dvfStep s i) j) = i.a := by
  have hndz' : i.d ≠ (0#xLen) := hndz
  simp [dvfStep, h, hv, hnovf, hndz', hlt, divDbzDet, dvfOutQ, dvfOutR, dvfSpecialQ, dvfSpecialR]

/-- I-17 修复有效性的符号形式：s_pre 装入 cnt 的是**完整 iter**（不再截断）。
    对照原版 :118 的 (divIter aL dL).setWidth (divW xLen)。 -/
theorem dvf_pre_cnt_full {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .pre) (hzq : BitVec.ult s.unsignedA s.unsignedD = false) :
    (dvfStep s i).cnt = divIter (divLez s.unsignedA) (divLez s.unsignedD) := by
  simp [dvfStep, h, hzq]

/-- I-17 的 32 位实例：BUG1 输入（|a| MSB 置位、|d|=1）下 iter=32 完整装入
    6 位 cnt（原版本同输入装入 5 位 cnt 得 0，见 IntDivMod.lean 5.1） -/
example : divIter (divLez (0x80000000 : BitVec 32)) (divLez (1 : BitVec 32))
    = (32 : BitVec (divW 32 + 1)) := by decide

/- ========================================================================= -/
/- 5. T2 终止性（修复版；对照第 7 节，cnt 位宽 divW+1）                        -/
/- ========================================================================= -/

/-- 停机于 finish 后不再离开 -/
theorem dvfRunTo_finish {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .finish) : ∀ n, (dvfRunTo s i n).phase = .finish := by
  intro n; cases n <;> simp [dvfRunTo, h]

/-- 未停机时 dvfRunTo 展开一拍 -/
theorem dvfRunTo_step {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase ≠ .finish) (n : Nat) :
    dvfRunTo s i (n + 1) = dvfRunTo (dvfStep s i) i n := by
  simp [dvfRunTo, beq_false_of_ne h]

/-- s_recovery 下一拍到 s_finish -/
theorem dvfRunTo_recovery_finish {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .recovery) {n : Nat} (hn : 1 ≤ n) :
    (dvfRunTo s i n).phase = .finish := by
  cases n with
  | zero => omega
  | succ m =>
      have hstep : (dvfStep s i).phase = .finish := by simp [dvfStep, h]
      have hnf : s.phase ≠ .finish := by simp [h]
      rw [dvfRunTo_step s i hnf m]
      exact dvfRunTo_finish _ i hstep m

/-- T2 核心：s_compute 中 cnt 严格递减，至多 cnt.toNat+2 拍到 finish -/
theorem dvf_compute_finish {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen) :
    ∀ k : Nat, s.phase = .compute → s.cnt.toNat ≤ k →
      (dvfRunTo s i (k + 2)).phase = .finish := by
  intro k
  induction k generalizing s with
  | zero =>
      intro hp hk
      have hc0 : s.cnt = 0 := div_toNat_eq_zero (Nat.le_zero.mp hk)
      have hnf : s.phase ≠ .finish := by simp [hp]
      have hs1 : (dvfStep s i).phase = .recovery := by
        simp [dvfStep, hp, hc0, divCntNext]
      show (dvfRunTo s i (1 + 1)).phase = .finish
      rw [dvfRunTo_step s i hnf 1]
      exact dvfRunTo_recovery_finish _ i hs1 (by omega)
  | succ k ih =>
      intro hp hk
      have hnf : s.phase ≠ .finish := by simp [hp]
      show (dvfRunTo s i ((k + 2) + 1)).phase = .finish
      rw [dvfRunTo_step s i hnf (k + 2)]
      by_cases hz0 : s.cnt.toNat = 0
      · have hc0 : s.cnt = 0 := div_toNat_eq_zero hz0
        have hs1 : (dvfStep s i).phase = .recovery := by
          simp [dvfStep, hp, hc0, divCntNext]
        exact dvfRunTo_recovery_finish _ i hs1 (by omega)
      · have hne : s.cnt ≠ 0 := fun hc => hz0 (by rw [hc]; exact BitVec.toNat_zero)
        cases hcn : (divCntNext s.cnt == 0) with
        | true =>
            have hcn' : divCntNext s.cnt = 0 := eq_of_beq hcn
            have hs1 : (dvfStep s i).phase = .recovery := by
              simp [dvfStep, hp, hcn']
            exact dvfRunTo_recovery_finish _ i hs1 (by omega)
        | false =>
            have hcn' : divCntNext s.cnt ≠ 0 := ne_of_beq_false hcn
            have hcn'' : divCntNext s.cnt ≠ (0#(divW xLen + 1)) := hcn'
            have hne' : s.cnt ≠ (0#(divW xLen + 1)) := hne
            have hw : 1 ≤ divW xLen + 1 := by omega
            have hsub : (s.cnt - 1).toNat = s.cnt.toNat - 1 := div_toNat_sub_one hw hne
            have hs1p : (dvfStep s i).phase = .compute := by
              simp [dvfStep, hp, hcn'']
            have hs1c : (dvfStep s i).cnt.toNat ≤ k := by
              have hc1 : (dvfStep s i).cnt = divCntNext s.cnt := by simp [dvfStep, hp]
              have hdn : divCntNext s.cnt = s.cnt - 1 := by
                simp [divCntNext, hne']
              rw [hc1, hdn, hsub]; omega
            exact ih _ hs1p hs1c

/-- T2 整机：idle 受理后至多 2^(divW(xLen)+1)+4 拍内 out.valid
    （xLen=32 时上界 68；iter 完整装入后实际 ≤ iter+4 ≤ xLen+4） -/
theorem dvf_terminates {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true) :
    (dvfRunTo s i (2 ^ (divW xLen + 1) + 4)).phase = .finish := by
  have hnf : s.phase ≠ .finish := by simp [h]
  rw [show 2 ^ (divW xLen + 1) + 4 = (2 ^ (divW xLen + 1) + 3) + 1 from by omega,
    dvfRunTo_step s i hnf _]
  cases hsp : (divOvfDet i.a i.d i.signed || divDbzDet i.d) with
  | true =>
      have hs1 : (dvfStep s i).phase = .finish := by simp [dvfStep, h, hv, hsp]
      exact dvfRunTo_finish _ i hs1 _
  | false =>
      have hs1 : (dvfStep s i).phase = .pre := by simp [dvfStep, h, hv, hsp]
      have hnf1 : (dvfStep s i).phase ≠ .finish := by simp [hs1]
      rw [show 2 ^ (divW xLen + 1) + 3 = (2 ^ (divW xLen + 1) + 2) + 1 from by omega,
        dvfRunTo_step _ i hnf1 _]
      cases hzq : BitVec.ult (divAbs i.a i.signed) (divAbs i.d i.signed) with
      | true =>
          have hs2 : (dvfStep (dvfStep s i) i).phase = .finish := by
            simp [dvfStep, h, hv, hsp, hzq]
          exact dvfRunTo_finish _ i hs2 _
      | false =>
          have hs2 : (dvfStep (dvfStep s i) i).phase = .compute := by
            simp [dvfStep, h, hv, hsp, hzq]
          have hcnt : (dvfStep (dvfStep s i) i).cnt.toNat ≤ 2 ^ (divW xLen + 1) :=
            Nat.le_of_lt (BitVec.isLt _)
          exact dvf_compute_finish _ i _ hs2 hcnt

/- ========================================================================= -/
/- 6. 不变式部分引理（compute 阶段单拍投影 + sel 互斥）                         -/
/- ========================================================================= -/

/-- sel_pos 与 sel_neg 互斥（aReg(xLen, xLen-1) 是单值）——不恢复余数除法
    三择一（加 dNegNorm / 加 dNorm / 不加）的排他性前提 -/
theorem dvf_selPos_ne_selNeg {xLen : Nat} (a : BitVec (xLen + 2)) :
    ¬(divSelPos a = true ∧ divSelNeg a = true) := by
  intro ⟨h1, h2⟩
  unfold divSelPos at h1
  unfold divSelNeg at h2
  rw [beq_iff_eq] at h1 h2
  exact absurd (h1.symm.trans h2) (by decide)

/-- compute 拍 Q 投影（:126）：Q' = Cat(Q.tail(1), sel_pos) -/
theorem dvf_compute_Q {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .compute) :
    (dvfStep s i).Q = ((s.Q <<< 1) ||| (if divSelPos s.aReg then 1 else 0)) := by
  simp [dvfStep, h]

/-- compute 拍 QN 投影（:127）：QN' = Cat(QN.tail(1), sel_neg) -/
theorem dvf_compute_QN {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .compute) :
    (dvfStep s i).QN = ((s.QN <<< 1) ||| (if divSelNeg s.aReg then 1 else 0)) := by
  simp [dvfStep, h]

/-- compute 拍 aReg 投影（:125，:66）：aReg' = aNext -/
theorem dvf_compute_aReg {xLen : Nat} (s : DvfState xLen) (i : DivInputs xLen)
    (h : s.phase = .compute) :
    (dvfStep s i).aReg =
      divANext s.aReg (divDNorm s.unsignedD (divLez s.unsignedD))
        (divDNegNorm s.unsignedD (divLez s.unsignedD)) := by
  simp [dvfStep, h]

/- ========================================================================= -/
/- 7. 一般正确性（数值档）：xLen=4/8 全穷举 + xLen=32 定向                     -/
/- ========================================================================= -/

section DvfExhaustive

/-- xLen=4 全穷举（16×16×2 = 512 组合，含 9 个 I-17 触发锥与全部 remIsNeg
    输入）：修复版逐点符合 RISC-V 规约（q 截断向零、r = a − q·d、除零/溢出
    按规约），且全部停机 -/
theorem dvf_test_xlen4_exhaustive : dvfCheckAll 4 = true := by native_decide

/-- xLen=8 全穷举（256×256×2 = 131072 组合；I-17 触发锥 129 个；曾报的
    I-18 "13% 出错率"系模型 II 类误译假象（doc/23）——修复版零失配） -/
theorem dvf_test_xlen8_exhaustive : dvfCheckAll 8 = true := by native_decide

-- xLen=32 定向：特殊情形（T1 数值侧，与符号定理 dvf_t1_* 互证）
theorem dvf_test_32_div_by_zero_u :
    dvfExec (5 : BitVec 32) 0 false = (0xFFFFFFFF#32, 5#32) := by native_decide
theorem dvf_test_32_div_by_zero_s :
    dvfExec (0xFFFFFFF9 : BitVec 32) 0 true = (0xFFFFFFFF#32, 0xFFFFFFF9#32) := by
  native_decide
theorem dvf_test_32_zero_div_zero :
    dvfExec (0 : BitVec 32) 0 false = (0xFFFFFFFF#32, 0#32) := by native_decide
theorem dvf_test_32_overflow_fresh :
    dvfExec (0x80000000 : BitVec 32) 0xFFFFFFFF true = (0x80000000#32, 0#32) := by
  native_decide
theorem dvf_test_32_zero_dividend :
    dvfExec (0 : BitVec 32) 5 false = (0#32, 0#32) := by native_decide
theorem dvf_test_32_zeroq :
    dvfExec (1 : BitVec 32) 0x80000000 false = (0#32, 1#32) := by native_decide

-- xLen=32 定向：一般情形（对照 IntDivMod.lean 5.4 同名输入，修复版=规约）
theorem dvf_test_32_div_x1 :
    dvfExec (5 : BitVec 32) 1 false = (5#32, 0#32) := by native_decide
theorem dvf_test_32_basic_u :
    dvfExec (7 : BitVec 32) 2 false = (3#32, 1#32) := by native_decide
theorem dvf_test_32_neg_pos :      -- -7/2 = (-3, -1)
    dvfExec (0xFFFFFFF9 : BitVec 32) 2 true = (0xFFFFFFFD#32, 0xFFFFFFFF#32) := by
  native_decide
theorem dvf_test_32_pos_neg :      -- 7/-2 = (-3, 1)
    dvfExec (7 : BitVec 32) 0xFFFFFFFE true = (0xFFFFFFFD#32, 1#32) := by native_decide
theorem dvf_test_32_neg_neg :      -- -7/-2 = (3, -1)
    dvfExec (0xFFFFFFF9 : BitVec 32) 0xFFFFFFFE true = (3#32, 0xFFFFFFFF#32) := by
  native_decide
theorem dvf_test_32_intmin_div2 :
    dvfExec (0x80000000 : BitVec 32) 2 true = (0xC0000000#32, 0#32) := by native_decide
theorem dvf_test_32_big_div2_u :   -- iter=31，原版本本就不截断，修复版保持一致
    dvfExec (0xFFFFFFFD : BitVec 32) 2 false = (0x7FFFFFFE#32, 1#32) := by native_decide

-- xLen=32 定向：全部直接对规约（q/r 双分量）
theorem dvf_test_32_spec_random_u :
    dvfExec (0xDEADBEEF : BitVec 32) 0x1234 false =
      (divSpecQ (0xDEADBEEF : BitVec 32) 0x1234 false,
       divSpecR (0xDEADBEEF : BitVec 32) 0x1234 false) := by native_decide
theorem dvf_test_32_spec_random_s :
    dvfExec (0xDEADBEEF : BitVec 32) 0x1234 true =
      (divSpecQ (0xDEADBEEF : BitVec 32) 0x1234 true,
       divSpecR (0xDEADBEEF : BitVec 32) 0x1234 true) := by native_decide
theorem dvf_test_32_spec_intmin_1_s :
    dvfExec (0x80000000 : BitVec 32) 1 true =
      (divSpecQ (0x80000000 : BitVec 32) 1 true,
       divSpecR (0x80000000 : BitVec 32) 1 true) := by native_decide

end DvfExhaustive

/- ========================================================================= -/
/- 8. 回归安全性：修复版与原版在未触发三 bug 的输入域上逐步等价                 -/
/- ========================================================================= -/

/-- 零扩展后右移再截回原宽 = 原宽直接右移（数值显然：截断位高于原值域） -/
theorem div_setWidth_ushiftRight {xLen : Nat} (e : BitVec xLen) (s : Nat) :
    ((e.setWidth (xLen + 1)) >>> s).setWidth xLen = e >>> s := by
  apply BitVec.toNat_inj.mp
  have hlt : e.toNat < 2 ^ xLen := BitVec.isLt _
  have hpos : 0 < (2 : Nat) ^ xLen := Nat.two_pow_pos xLen
  have h2 : (2 : Nat) ^ xLen < 2 ^ (xLen + 1) := by
    calc (2 : Nat) ^ xLen = 2 ^ xLen * 1 := (Nat.mul_one _).symm
      _ < 2 ^ xLen * 2 := Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ = 2 ^ (xLen + 1) := (Nat.pow_succ ..).symm
  have hsr : e.toNat >>> s < 2 ^ xLen := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans hlt h2), Nat.mod_eq_of_lt hsr,
    BitVec.toNat_ushiftRight]

/-- 组合级回归：remIsNeg=0 时修复版与原版 recoveryR 逐位相同（I-18 撤案后，
    remIsNeg=1 且 dReg 偶时亦相同——"修复"在可达状态为 no-op，doc/23） -/
theorem dvf_commonR_eq_orig_of_not_neg {xLen : Nat} (aReg dReg : BitVec (xLen + 2))
    (dL : BitVec (divW xLen)) (h : aReg.msb = false) :
    dvfCommonRNext aReg dReg dL = divCommonRNext aReg dReg dL := by
  simp [dvfCommonRNext, divCommonRNext, h, div_setWidth_ushiftRight]

/-- 修复版与原版的逐步对应关系：除 cnt 位宽不同外全字段相等，cnt 数值相等 -/
def dvfMatch {xLen : Nat} (s : DivState xLen) (t : DvfState xLen) : Prop :=
  s.phase = t.phase ∧ s.qSign = t.qSign ∧ s.rSign = t.rSign ∧ s.rawA = t.rawA ∧
  s.unsignedA = t.unsignedA ∧ s.unsignedD = t.unsignedD ∧ s.overflow = t.overflow ∧
  s.divByZero = t.divByZero ∧ s.zeroQ = t.zeroQ ∧ s.aReg = t.aReg ∧
  s.dReg = t.dReg ∧ s.cnt.toNat = t.cnt.toNat ∧ s.Q = t.Q ∧ s.QN = t.QN ∧
  s.commonQ = t.commonQ ∧ s.commonR = t.commonR

/-- 对应状态下输出一致（输出只依赖被匹配的字段） -/
theorem dvf_match_out {xLen : Nat} {s : DivState xLen} {t : DvfState xLen}
    (hm : dvfMatch s t) :
    divOutQ s = dvfOutQ t ∧ divOutR s = dvfOutR t := by
  obtain ⟨hp, hqs, hrs, hra, hua, hud, hov, hdb, hzq, ha, hd, hcnt, hq, hqn,
    hcq, hcr⟩ := hm
  simp only [divOutQ, dvfOutQ, divOutR, dvfOutR, divSpecialQ, dvfSpecialQ,
    divSpecialR, dvfSpecialR, divSignedQ, dvfSignedQ, divSignedR, dvfSignedR]
  refine ⟨?_, ?_⟩
  · rw [← hdb, ← hzq, ← hov, ← hqs, ← hcq]
  · rw [← hdb, ← hzq, ← hov, ← hrs, ← hra, ← hcr]

/-- 安全步条件（"未触发三 bug"的逐拍形式）：
    - idle：zeroQ 已清零（I-19 修复与原版分歧仅当陈旧 zeroQ=1）；
    - pre：zeroQ 分支，或 iter 无截断（< 2^divW，I-17 不动点）；
    - recovery：部分余数非负（原 I-18 域；撤案后该条件对等价性已无必要）。 -/
def dvfSafeStep {xLen : Nat} (s : DivState xLen) : Prop :=
  (s.phase = .idle → s.zeroQ = false) ∧
  (s.phase = .pre →
    BitVec.ult s.unsignedA s.unsignedD = true ∨
      (divIter (divLez s.unsignedA) (divLez s.unsignedD)).toNat < 2 ^ divW xLen) ∧
  (s.phase = .recovery → s.aReg.msb = false)

/-- beq 0 的 toNat 刻画 -/
theorem dvf_beq_zero_iff {w : Nat} (c : BitVec w) :
    (c == 0) = decide (c.toNat = 0) := by
  by_cases hz : c.toNat = 0
  · have e : c = 0 := div_toNat_eq_zero hz
    simp [e]
  · have e1 : (c == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hce
      exact hz (by rw [hce]; exact BitVec.toNat_zero)
    have e2 : decide (c.toNat = 0) = false := by
      cases hdec : decide (c.toNat = 0) with
      | false => rfl
      | true => exact absurd (of_decide_eq_true hdec) hz
    rw [e1, e2]

/-- cnt_next 在数值相等（可异宽）的计数器上结果数值相等 -/
theorem dvf_cntNext_toNat {w w' : Nat} (hw : 1 ≤ w) (hw' : 1 ≤ w')
    (c : BitVec w) (c' : BitVec w') (h : c.toNat = c'.toNat) :
    (divCntNext c).toNat = (divCntNext c').toNat := by
  by_cases hz : c.toNat = 0
  · have e0 : c = 0 := div_toNat_eq_zero hz
    have e0' : c' = 0 := div_toNat_eq_zero (h ▸ hz)
    simp [divCntNext, e0, e0']
  · have hne : c ≠ (0#w) := fun e => hz (by rw [e]; exact BitVec.toNat_zero)
    have hne' : c' ≠ (0#w') :=
      fun e => hz (h.trans (by rw [e]; exact BitVec.toNat_zero))
    have d1 : divCntNext c = c - 1 := by simp [divCntNext, hne]
    have d2 : divCntNext c' = c' - 1 := by simp [divCntNext, hne']
    rw [d1, d2, div_toNat_sub_one hw hne, div_toNat_sub_one hw' hne', h]

/-- cnt_next 判零在数值相等（可异宽）的计数器上一致 -/
theorem dvf_cntNext_beq_zero {w w' : Nat} (c : BitVec w) (c' : BitVec w')
    (h : c.toNat = c'.toNat) :
    (divCntNext c == 0) = (divCntNext c' == 0) := by
  rw [dvf_beq_zero_iff, dvf_beq_zero_iff]
  by_cases hz : c.toNat = 0
  · have e0 : c = 0 := div_toNat_eq_zero hz
    have e0' : c' = 0 := div_toNat_eq_zero (h ▸ hz)
    simp [divCntNext, e0, e0']
  · have hw : 1 ≤ w := by
      by_cases hw0 : w = 0
      · subst hw0; exact absurd (Nat.lt_one_iff.mp (BitVec.isLt c)) hz
      · omega
    have hw' : 1 ≤ w' := by
      by_cases hw0 : w' = 0
      · subst hw0
        exact absurd (Nat.lt_one_iff.mp (BitVec.isLt c')) (h ▸ hz)
      · omega
    have hne : c ≠ (0#w) := fun e => hz (by rw [e]; exact BitVec.toNat_zero)
    have hne' : c' ≠ (0#w') :=
      fun e => hz (h.trans (by rw [e]; exact BitVec.toNat_zero))
    have d1 : divCntNext c = c - 1 := by simp [divCntNext, hne]
    have d2 : divCntNext c' = c' - 1 := by simp [divCntNext, hne']
    rw [d1, d2, div_toNat_sub_one hw hne, div_toNat_sub_one hw' hne', h]

/-- **单拍回归**：对应状态 + 安全步条件 ⟹ 单拍后仍对应 -/
theorem dvf_step_match {xLen : Nat} (s : DivState xLen) (t : DvfState xLen)
    (i : DivInputs xLen) (hm : dvfMatch s t) (hs : dvfSafeStep s) :
    dvfMatch (divStep s i) (dvfStep t i) := by
  obtain ⟨hp, hqs, hrs, hra, hua, hud, hov, hdb, hzq, ha, hd, hcnt, hq, hqn,
    hcq, hcr⟩ := hm
  obtain ⟨hsi, hsp, hsr⟩ := hs
  cases hphase : s.phase with
  | idle =>
      have hpt : t.phase = .idle := hp ▸ hphase
      have hz0 : s.zeroQ = false := hsi hphase
      cases hv : i.in_valid <;>
        simp [dvfMatch, divStep, dvfStep, hphase, hpt, hv, hz0, ← hzq,
          ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← ha, ← hd,
          ← hq, ← hqn, ← hcq, ← hcr]
  | pre =>
      have hpt : t.phase = .pre := hp ▸ hphase
      cases hz : BitVec.ult s.unsignedA s.unsignedD with
      | true =>
          simp [dvfMatch, divStep, dvfStep, hphase, hpt, hz,
            ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← hzq, ← ha, ← hd,
            ← hq, ← hqn, ← hcq, ← hcr]
      | false =>
          have hb : (divIter (divLez s.unsignedA) (divLez s.unsignedD)).toNat
              < 2 ^ divW xLen := by
            obtain h1 | h2 := hsp hphase
            · exact absurd h1 (by rw [hz]; decide)
            · exact h2
          simp [dvfMatch, divStep, dvfStep, hphase, hpt, hz,
            ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← hzq, ← ha, ← hd,
            ← hq, ← hqn, ← hcq, ← hcr,
            BitVec.toNat_setWidth, Nat.mod_eq_of_lt hb]
  | compute =>
      have hpt : t.phase = .compute := hp ▸ hphase
      have hw1 : 1 ≤ divW xLen := by simp [divW]
      have hw2 : 1 ≤ divW xLen + 1 := by omega
      have hcn := dvf_cntNext_toNat hw1 hw2 s.cnt t.cnt hcnt
      have hiff : (divCntNext s.cnt = (0#(divW xLen))) ↔
          (divCntNext t.cnt = (0#(divW xLen + 1))) := by
        constructor <;> intro hh
        · exact div_toNat_eq_zero (by
            have e1 : (divCntNext s.cnt).toNat = 0 := by rw [hh]; exact BitVec.toNat_zero
            rwa [hcn] at e1)
        · exact div_toNat_eq_zero (by
            have e1 : (divCntNext t.cnt).toNat = 0 := by rw [hh]; exact BitVec.toNat_zero
            rwa [← hcn] at e1)
      simp [dvfMatch, divStep, dvfStep, hphase, hpt, hcn, hiff,
        ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← hzq, ← ha, ← hd,
        ← hq, ← hqn, ← hcq, ← hcr]
  | recovery =>
      have hpt : t.phase = .recovery := hp ▸ hphase
      have hmsb : s.aReg.msb = false := hsr hphase
      have hcr' : divCommonRNext s.aReg s.dReg (divLez s.unsignedD) =
          dvfCommonRNext t.aReg t.dReg (divLez t.unsignedD) := by
        rw [← ha, ← hd, ← hud]
        exact (dvf_commonR_eq_orig_of_not_neg s.aReg s.dReg (divLez s.unsignedD) hmsb).symm
      simp [dvfMatch, divStep, dvfStep, hphase, hpt, hcr',
        ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← hzq, ← ha, ← hd,
        ← hq, ← hqn, ← hcq, ← hcr]
  | finish =>
      have hpt : t.phase = .finish := hp ▸ hphase
      cases hr2 : i.out_ready <;>
        simp [dvfMatch, divStep, dvfStep, hphase, hpt, hr2,
          ← hqs, ← hrs, ← hra, ← hua, ← hud, ← hov, ← hdb, ← hzq, ← ha, ← hd,
          ← hq, ← hqn, ← hcq, ← hcr]

/-- **多拍回归（归纳）**：原版本轨迹上每一拍都满足安全步条件，则两版
    整条轨迹逐步对应 -/
theorem dvf_run_match {xLen : Nat} (s : DivState xLen) (t : DvfState xLen)
    (i : DivInputs xLen) (n : Nat)
    (hm : dvfMatch s t)
    (hsafe : ∀ k, k ≤ n → dvfSafeStep (divRunTo s i k)) :
    dvfMatch (divRunTo s i n) (dvfRunTo t i n) := by
  induction n generalizing s t with
  | zero => exact hm
  | succ n ih =>
      by_cases hf : s.phase = .finish
      · have htf : t.phase = .finish := hm.1 ▸ hf
        have e1 : divRunTo s i (n + 1) = s := by simp [divRunTo, hf]
        have e2 : dvfRunTo t i (n + 1) = t := by simp [dvfRunTo, htf]
        rw [e1, e2]; exact hm
      · have htnf : t.phase ≠ .finish := fun e => hf (hm.1.trans e)
        rw [divRunTo_step s i hf n, dvfRunTo_step t i htnf n]
        apply ih
        · exact dvf_step_match s t i hm (hsafe 0 (Nat.zero_le _))
        · intro k hk
          have e := hsafe (k + 1) (by omega)
          rwa [divRunTo_step s i hf k] at e

/-- **回归安全性（单事务输出级，任意 xLen）**：从各自初始状态受理同一事务，
    只要原版本运行轨迹上每一拍都未触发三个 bug 的触发条件
    （dvfSafeStep：无陈旧 zeroQ、iter 无截断、recovery 时部分余数非负），
    修复版与原版本的输出完全一致 -/
theorem dvf_exec_eq_orig_of_safe {xLen : Nat} (a d : BitVec xLen) (sgn : Bool)
    (hsafe : ∀ k, k ≤ 2 * xLen + 8 →
      dvfSafeStep (divRunTo (divStep (divInit xLen) ⟨true, a, d, sgn, true⟩)
        (divNop xLen) k)) :
    divExec a d sgn = dvfExec a d sgn := by
  have hm0 : dvfMatch (divInit xLen) (dvfInit xLen) := by
    simp [dvfMatch, divInit, dvfInit]
  have hs0 : dvfSafeStep (divInit xLen) := by
    refine ⟨fun _ => by simp [divInit], fun h => ?_, fun h => ?_⟩
    · simp [divInit] at h
    · simp [divInit] at h
  have hm1 := dvf_step_match (divInit xLen) (dvfInit xLen) ⟨true, a, d, sgn, true⟩
    hm0 hs0
  have hrun := dvf_run_match _ _ (divNop xLen) (2 * xLen + 8) hm1 hsafe
  obtain ⟨hq, hr⟩ := dvf_match_out hrun
  show (divOutQ (divRunTo (divStep (divInit xLen) ⟨true, a, d, sgn, true⟩)
          (divNop xLen) (2 * xLen + 8)),
        divOutR (divRunTo (divStep (divInit xLen) ⟨true, a, d, sgn, true⟩)
          (divNop xLen) (2 * xLen + 8))) =
       (dvfOutQ (dvfRunTo (dvfStep (dvfInit xLen) ⟨true, a, d, sgn, true⟩)
          (divNop xLen) (2 * xLen + 8)),
        dvfOutR (dvfRunTo (dvfStep (dvfInit xLen) ⟨true, a, d, sgn, true⟩)
          (divNop xLen) (2 * xLen + 8)))
  exact Prod.ext hq hr

/- ---- 回归的数值证据 ---- -/

/-- xLen=4 全输入回归：非 I-17 触发锥且非 remIsNeg 的输入上两版输出一致 -/
theorem dvf_test_regr_xlen4 : dvfRegrAll 4 = true := by native_decide

/-- xLen=8 全输入回归（131072 组合） -/
theorem dvf_test_regr_xlen8 : dvfRegrAll 8 = true := by native_decide

/-- 【I-18 撤案后的强化回归（2026-09-07，doc/23）】修正后的原版与修复版在
    除 I-17 触发锥外的全部输入上逐点一致——不再需要排除 remIsNeg（原 I-18
    域）。即"i18 补丁在修正后模型上是语义保持 no-op"的全输入数值证据。 -/
def dvfRegrOneFull {xLen : Nat} (a d : BitVec xLen) (sgn : Bool) : Bool :=
  divCorner a d sgn || (divExec a d sgn == dvfExec a d sgn)

/-- 强化回归全输入空间检查 -/
def dvfRegrAllFull (xLen : Nat) : Bool :=
  (List.range (2 ^ xLen)).all fun av =>
    (List.range (2 ^ xLen)).all fun dv =>
      [false, true].all fun sgn =>
        dvfRegrOneFull (BitVec.ofNat xLen av) (BitVec.ofNat xLen dv) sgn

theorem dvf_test_regr_full_xlen4 : dvfRegrAllFull 4 = true := by native_decide
theorem dvf_test_regr_full_xlen8 : dvfRegrAllFull 8 = true := by native_decide

/-- 32 位定向回归实例 -/
theorem dvfT_regr_7_2 :
    divExec (7 : BitVec 32) 2 false = dvfExec (7 : BitVec 32) 2 false := by
  native_decide

/-- 多事务回归（I-19 面）：前一事务非 zeroQ（zeroQReg 不残留）时，紧接的
    overflow 事务两版输出一致且 r = 0 -/
def dvfSeqClean : DvfState 32 :=
  let s1 := dvfExecState (7 : BitVec 32) 2 false
  let s2 := dvfStep s1 (divNop 32)
  dvfRunTo (dvfStep s2 ⟨true, 0x80000000, 0xFFFFFFFF, true, true⟩) (divNop 32) 72

def divSeqClean : DivState 32 :=
  let s1 := divExecState (7 : BitVec 32) 2 false
  let s2 := divStep s1 (divNop 32)
  divRunTo (divStep s2 ⟨true, 0x80000000, 0xFFFFFFFF, true, true⟩) (divNop 32) 72

theorem dvfT_regr_multitxn :
    dvfOutQ dvfSeqClean = divOutQ divSeqClean ∧
    dvfOutR dvfSeqClean = divOutR divSeqClean ∧
    dvfOutR dvfSeqClean = 0#32 := by native_decide

/- ========================================================================= -/
/- 9. 公理审计（native_decide 定理各带一个 _native.native_decide.ax 信任公理， -/
/-    按 AGENTS.md 归档注明；符号证明仅 propext/Classical.choice/Quot.sound）  -/
/- ========================================================================= -/

#print axioms dvfT_i17_unsigned
#print axioms dvfT_i18_unsigned
#print axioms dvfT_i18_random_s
#print axioms dvfT_i19_fixed
#print axioms dvf_t1_divByZero
#print axioms dvf_t1_overflow
#print axioms dvf_t1_zeroQ
#print axioms dvf_pre_cnt_full
#print axioms dvf_compute_finish
#print axioms dvf_terminates
#print axioms dvf_selPos_ne_selNeg
#print axioms dvf_test_xlen4_exhaustive
#print axioms dvf_test_xlen8_exhaustive
#print axioms dvf_commonR_eq_orig_of_not_neg
#print axioms dvf_step_match
#print axioms dvf_run_match
#print axioms dvf_exec_eq_orig_of_safe
#print axioms dvf_test_regr_xlen4
#print axioms dvf_test_regr_xlen8
#print axioms dvf_test_regr_full_xlen8
#print axioms dvfT_regr_multitxn

end Ventus.Arith
