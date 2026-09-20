/- ========================================================================= -/
/-                     Schedule/RRArbiter.lean                               -/
/-  chisel3.util.RRArbiter（round-robin 仲裁器）的 Lean 4 模型、              -/
/-  数值回归测试与仲裁契约证明                                                -/
/-                                                                           -/
/-  Chisel 源码对照（版本：chisel v6.4.0，Ventus 使用版本，见仓库 build.sc:32）：-/
/-    chipsalliance/chisel @ v6.4.0                                          -/
/-    src/main/scala/chisel3/util/Arbiter.scala                              -/
/-    ArbiterCtrl        :41-47   （优先级链：累积或取反）                    -/
/-    LockingArbiterLike :49-76   （io.chosen/out.valid/out.bits :54-56；    -/
/-                                 count>1 的 lock 寄存器组 :58-71；         -/
/-                                 count=1 的 in.ready :72-75）              -/
/-    LockingRRArbiter   :78-95   （lastGrant :81、grantMask :82、           -/
/-                                 validMask :83、grant :85-88、             -/
/-                                 choice :90-94）                           -/
/-    RRArbiter          :118     （= LockingRRArbiter(gen, n, count=1)）    -/
/-  Ventus 侧例化规模：ibuffer2issue/issue/operandArbiter 中 n ∈ {2,4,8,32}  -/
/-  （num_warp=8、num_collectorUnit=8、num_thread=32、4*num_collectorUnit=32）。-/
/-  本模型对任意 n ≥ 1 通用，测试用 n = 1/4/8。                               -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. lastGrant 是 `RegEnable(io.chosen, io.out.fire)`（:81），源码自承      -/
/-      "this register is not initialized on purpose, see #267"（:80）——     -/
/-      无复位初值。本模型把 lastGrant 建模为任意 `Fin n` 状态，不提供 init， -/
/-      全部定理对任意初值量化（T2/T5 表明任何初值下仲裁语义都成立）。        -/
/-  D2. io.chosen 位宽 log2Ceil(n)（:36）；choice/lastGrant 值恒 ≤ n-1，      -/
/-      建模为 `Fin n`。n=1 时 chisel 位宽为 0（退化），`Fin 1` 模型等价      -/
/-      （唯一值 0），测试覆盖。                                             -/
/-  D3. choice 的两个 when 循环（:91-94）是 last-connect-wins：建模为         -/
/-      rraLoopNat（从 hi 递减折叠、后写覆盖 ⇒ 最小索引胜），并用桥接定理     -/
/-      rraChoiceHw_eq 证明它与"环形扫描"语义形式 rraChoiceNat 等价。         -/
/-      rraLoopNat 与 Scala 区间的两点无害差异：n=1 时 loop1 区间             -/
/-      `n-2 to 0 by -1` = `-1 to 0 by -1` 为空、loop2 区间 `0 to 1 by -1`   -/
/-      为空，而 rraLoopNat 会多处理索引 0——rraVM v lg 0 = false（lg<0 不    -/
/-      成立）使 loop2 多处理的索引 0 无效；loop1 在 n=1 时处理索引 0 的     -/
/-      结果与默认值 n-1=0 相同。                                            -/
/-  D4. ArbiterCtrl（:45）的 `scanLeft(_ || _).map(!_)` 建模为递归 rraCtrl：  -/
/-      ctrl(0)=true、ctrl(k+1)=ctrl(k)&&!req(k)，语义由 rraCtrl_eq_true_iff  -/
/-      钉死（ctrl(k) = 前 k 项请求全 false）。                               -/
/-  D5. 数据载荷 gen 建模为泛型 α，io.out.bits（:56）是 in(chosen).bits 的    -/
/-      组合直通；仲裁逻辑只依赖 valid 向量（`BitVec n`，bit i = in(i).valid）。-/
/-  D6. grant（:87）不要求 in.valid：无请求时 grant 可全为 true（ctrl 链全    -/
/-      通），有请求时未选中的无效输入也可能 grant=true。语义刻画见           -/
/-      rraGrant_eq_true_iff；互斥（T1）按 "valid ∧ grant" 表述，与           -/
/-      io.out.valid = in(chosen).valid（:55）共同保证至多一路实际传输。      -/
/-  D7. RRArbiter 令 count=1（:118），:58-71 的 lockCount/lockIdx/locked      -/
/-      整段不生成——**没有任何 lock 寄存器**，io.chosen/out.bits 是纯组合     -/
/-      逻辑（对 RRArbiter 而言 "Locking" 之名不副实）。这是 T3 的核心事实。  -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1（重要，集成须知）：RRArbiter 的 io.out **不是 Irrevocable**。反压      -/
/-      （out.valid ∧ ¬out.ready）期间 lastGrant 不变，但 chosen 是组合的：   -/
/-      若有新请求在环形序上先于当前 chosen 到达，chosen/out.bits 当拍改变。  -/
/-      本文件给出形式化反例 rra3_not_stable（n=4 的 Stable 违反 witness）    -/
/-      与条件稳定性定理 rra3_choice_stable。下游若按 Irrevocable 假设消费    -/
/-      out（例如反压期间锁存 bits），需要外围保证请求集合在反压期间不新增    -/
/-      高优先级请求，或改用 count>1 的 LockingRRArbiter 实例。这不是 chisel  -/
/-      的 bug（RRArbiter 本就不承诺 Irrevocable），但是 Ventus 集成时必须    -/
/-      核实的契约前提（ibuffer2issue/issue/operandArbiter 各例化点待查）。   -/
/-  Q2. lastGrant 无复位初值（:80-81）：上电首拍的优先级起点是随机值。       -/
/-      功能无害——任何 lastGrant 下 grant/choice 语义都成立（本文件 T1/T2/  -/
/-      T5 均对任意 lastGrant 量化），仅记录。                                -/
/-  Q3. grant 非 one-hot（D6）：`in.ready(i) = grant(i) && out.ready`（:74）  -/
/-      可对无效输入为 1。对 Decoupled 协议无害（fire 仍需 valid），但任何    -/
/-      把 in.ready 当作"被选中"信号消费的上游会误读。仅记录。               -/
/-  Q4. n=1 退化：chosen 为 0 位宽（log2Ceil 1 = 0），choice 恒 0，grant(0)  -/
/-      恒 true（rraCtrl 单请求恒通）。测试覆盖（T1 系列小定理对 n=1 亦成立）。-/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.Handshake

namespace Ventus.Schedule

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. ArbiterCtrl（:41-47）                                                   -/
/- ========================================================================= -/

/-- ArbiterCtrl 的递归形式：`rraCtrl req k` = 请求序列 req 的前 k 项全为 false
    （:45 的 `true.B +: scanLeft(_ || _).map(!_)`：ctrl(0)=true，
    ctrl(k+1) = ctrl(k) && !req(k)）。 -/
def rraCtrl (req : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => rraCtrl req k && !req k

theorem rraCtrl_succ (req : Nat → Bool) (k : Nat) :
    rraCtrl req (k + 1) = (rraCtrl req k && !req k) := rfl

/-- ctrl 语义：rraCtrl req k = true 当且仅当前 k 项请求全为 false -/
theorem rraCtrl_eq_true_iff {req : Nat → Bool} {k : Nat} :
    rraCtrl req k = true ↔ ∀ j, j < k → req j = false := by
  induction k with
  | zero => simp [rraCtrl]
  | succ k ih =>
    rw [rraCtrl_succ, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h1, h2⟩ j hj
      by_cases hjk : j < k
      · exact h1 j hjk
      · have e : j = k := by omega
        subst e
        cases hr : req j with
        | false => rfl
        | true => simp [hr] at h2
    · intro h
      refine ⟨fun j hj => h j (by omega), ?_⟩
      have hk := h k (by omega)
      simp [hk]

/- ========================================================================= -/
/- 2. 有界线性扫描 rraFindNat（环形优先级的语义底座）                          -/
/- ========================================================================= -/

/-- 线性扫描：返回 [lo, lo+fuel) 中首个满足 p 的索引（无则 none）。 -/
def rraFindNat (p : Nat → Bool) (lo : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => if p lo then some lo else rraFindNat p (lo + 1) fuel

/-- find 成功则返回的是区间内首个满足 p 的索引 -/
theorem rraFindNat_some_spec {p : Nat → Bool} {lo fuel j : Nat}
    (h : rraFindNat p lo fuel = some j) :
    lo ≤ j ∧ j < lo + fuel ∧ p j = true ∧ ∀ k, lo ≤ k → k < j → p k = false := by
  induction fuel generalizing lo with
  | zero => simp [rraFindNat] at h
  | succ f ih =>
    simp only [rraFindNat] at h
    cases hp : p lo with
    | true =>
      simp [hp] at h
      subst h
      exact ⟨by omega, by omega, hp, fun k h1 h2 => by omega⟩
    | false =>
      simp [hp] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih h
      refine ⟨by omega, by omega, h3, fun k hk1 hk2 => ?_⟩
      by_cases hk0 : k = lo
      · subst hk0; exact hp
      · exact h4 k (by omega) hk2

/-- find 失败则区间内无满足 p 的索引 -/
theorem rraFindNat_none_spec {p : Nat → Bool} {lo fuel : Nat}
    (h : rraFindNat p lo fuel = none) :
    ∀ k, lo ≤ k → k < lo + fuel → p k = false := by
  induction fuel generalizing lo with
  | zero => intro k h1 h2; omega
  | succ f ih =>
    simp only [rraFindNat] at h
    cases hp : p lo with
    | true => simp [hp] at h
    | false =>
      simp [hp] at h
      intro k h1 h2
      by_cases hk0 : k = lo
      · subst hk0; exact hp
      · exact ih h k (by omega) (by omega)

/-- 区间内首个满足 p 的索引必被 find 找到 -/
theorem rraFindNat_some_of_spec {p : Nat → Bool} {lo fuel j : Nat} :
    lo ≤ j → j < lo + fuel → p j = true →
      (∀ k, lo ≤ k → k < j → p k = false) →
      rraFindNat p lo fuel = some j := by
  induction fuel generalizing lo with
  | zero => intro h1 h2; omega
  | succ f ih =>
    intro hlo hhi hpj hmin
    simp only [rraFindNat]
    by_cases hjl : j = lo
    · subst hjl; simp [hpj]
    · have hplo : p lo = false := hmin lo (by omega) (by omega)
      simp [hplo]
      exact ih (lo := lo + 1) (by omega) (by omega) hpj (fun k h1 h2 => hmin k (by omega) h2)

/-- 区间内无满足 p 的索引则 find 失败 -/
theorem rraFindNat_none_of_spec {p : Nat → Bool} {lo fuel : Nat}
    (h : ∀ k, lo ≤ k → k < lo + fuel → p k = false) :
    rraFindNat p lo fuel = none := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ f ih =>
    simp only [rraFindNat]
    have hplo : p lo = false := h lo (by omega) (by omega)
    simp [hplo]
    exact ih (lo := lo + 1) (fun k h1 h2 => h k (by omega) (by omega))

/-- find 的燃料递推：多一格燃料至多把末尾索引纳入扫描 -/
theorem rraFindNat_succ (p : Nat → Bool) (lo f : Nat) :
    rraFindNat p lo (f + 1) =
      (match rraFindNat p lo f with
      | some j => some j
      | none => if p (lo + f) then some (lo + f) else none) := by
  induction f generalizing lo with
  | zero =>
    cases hp : p lo with
    | true => simp [rraFindNat, hp]
    | false => simp [rraFindNat, hp]
  | succ f ih =>
    cases hp : p lo with
    | true => simp [rraFindNat, hp]
    | false =>
      have e1 : rraFindNat p lo (f + 1 + 1) = rraFindNat p (lo + 1) (f + 1) := by
        simp [rraFindNat, hp]
      have e2 : rraFindNat p lo (f + 1) = rraFindNat p (lo + 1) f := by
        simp [rraFindNat, hp]
      rw [e1, e2, ih (lo := lo + 1)]
      have e3 : lo + 1 + f = lo + (f + 1) := by omega
      rw [e3]

/- ========================================================================= -/
/- 3. rraLoopNat：chisel `for (i <- hi to 0 by -1) when(p(i)) choice := i`     -/
/-    的折叠形式（last connect wins ⇒ 最小索引胜）                            -/
/- ========================================================================= -/

/-- 从 hi 递减到 0 的 when 循环：初值 cur，p(i) 为真时 choice 被 i 覆盖。 -/
def rraLoopNat (p : Nat → Bool) (cur : Nat) : Nat → Nat
  | 0 => if p 0 then 0 else cur
  | hi + 1 => rraLoopNat p (if p (hi + 1) then hi + 1 else cur) hi

/-- 循环语义：结果为 [0, hi] 中首个满足 p 的索引（无则保持初值） -/
theorem rraLoopNat_spec (p : Nat → Bool) (cur hi : Nat) :
    rraLoopNat p cur hi = (rraFindNat p 0 (hi + 1)).getD cur := by
  induction hi generalizing cur with
  | zero =>
    cases h0 : p 0 <;> simp [rraLoopNat, rraFindNat, h0]
  | succ hi ih =>
    show rraLoopNat p (if p (hi + 1) then hi + 1 else cur) hi =
      (rraFindNat p 0 (hi + 1 + 1)).getD cur
    rw [ih, rraFindNat_succ p 0 (hi + 1)]
    cases hf : rraFindNat p 0 (hi + 1) with
    | some j => simp
    | none =>
      cases hp : p (hi + 1) <;> simp [hp]

/- ========================================================================= -/
/- 4. 模型：grant / choice / out / step（:54-56, :73-75, :81-94）             -/
/- ========================================================================= -/

/-- validMask（:83）：in(j).valid && j > lastGrant。
    j ≥ n 时 getLsbD 为 false（无害，:83 只枚举 0..n-1）。 -/
def rraVM {n : Nat} (v : BitVec n) (lg : Nat) (j : Nat) : Bool :=
  v.getLsbD j && decide (lg < j)

/-- 拼接请求向量（:86 的 `validMask ++ io.in.map(_.valid)`）：
    j < n 时为 validMask(j)，否则为 valid(j-n)。 -/
def rraReq {n : Nat} (v : BitVec n) (lg : Nat) (j : Nat) : Bool :=
  if j < n then rraVM v lg j else v.getLsbD (j - n)

/-- grant（:87）：ctrl(i) && grantMask(i) || ctrl(i+n)，grantMask(i) = i > lastGrant（:82）。 -/
def rraGrant {n : Nat} (v : BitVec n) (lg i : Fin n) : Bool :=
  (rraCtrl (rraReq v lg.val) i.val && decide (lg.val < i.val)) ||
    rraCtrl (rraReq v lg.val) (i.val + n)

/-- 硬件形式 choice（:90-94）：loop1 = :91-92（valid，n-2 downto 0，默认 n-1），
    loop2 = :93-94（validMask，n-1 downto 1，覆盖 loop1）。与 Scala 区间的差异
    及其无害性见 D3。 -/
def rraChoiceHw {n : Nat} (v : BitVec n) (lg : Nat) : Nat :=
  rraLoopNat (rraVM v lg) (rraLoopNat (fun j => v.getLsbD j) (n - 1) (n - 2)) (n - 1)

/-- 语义形式 choice：lastGrant+1 起环形首个 valid（无 valid 时默认 n-1，:90）。 -/
def rraChoiceNat {n : Nat} (v : BitVec n) (lg : Nat) : Nat :=
  match rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
  | some j => j
  | none =>
    match rraFindNat (fun j => v.getLsbD j) 0 n with
    | some j => j
    | none => n - 1

/-- validMask 段扫描与"lastGrant 之后首个 valid"等价（lg < n 时） -/
theorem rraFindNat_vm_eq {n : Nat} (v : BitVec n) {lg : Nat} (hlg : lg < n) :
    rraFindNat (rraVM v lg) 0 n =
      rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) := by
  cases h : rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
  | some j =>
    obtain ⟨hlo, hhi, hvj, hmin⟩ := rraFindNat_some_spec h
    have hlgj : lg < j := by omega
    have hvmj : rraVM v lg j = true := by simp [rraVM, hvj, hlgj]
    apply rraFindNat_some_of_spec (j := j) (by omega) (by omega) hvmj
    intro k hk0 hkj
    by_cases hkl : lg < k
    · have hvk : v.getLsbD k = false := hmin k (by omega) hkj
      simp [rraVM, hvk]
    · simp [rraVM, hkl]
  | none =>
    apply rraFindNat_none_of_spec
    intro k hk0 hkn
    by_cases hkl : lg < k
    · have hvk : v.getLsbD k = false := rraFindNat_none_spec h k (by omega) (by omega)
      simp [rraVM, hvk]
    · simp [rraVM, hkl]

/-- 桥接定理（D3）：硬件两循环形式 = 环形扫描语义形式 -/
theorem rraChoiceHw_eq {n : Nat} (v : BitVec n) {lg : Nat} (hlg : lg < n) :
    rraChoiceHw v lg = rraChoiceNat v lg := by
  by_cases hn1c : n = 1
  · -- n = 1 退化（Q4）：lg = 0，逐 findNat 调用求值
    subst hn1c
    have hlg0 : lg = 0 := by omega
    subst hlg0
    unfold rraChoiceHw rraChoiceNat
    rw [rraLoopNat_spec, rraLoopNat_spec]
    have hvm : rraVM v 0 0 = false := by
      show (v.getLsbD 0 && decide (0 < 0)) = false
      rw [decide_eq_false (by omega : ¬ 0 < 0)]
      cases v.getLsbD 0 <;> rfl
    have e0 : rraFindNat (fun j => v.getLsbD j) (0 + 1) (1 - (0 + 1)) = none := rfl
    have e1 : rraFindNat (fun j => v.getLsbD j) 0 (1 - 2 + 1) =
        (if v.getLsbD 0 = true then some 0 else none) := rfl
    have e2 : rraFindNat (rraVM v 0) 0 (1 - 1 + 1) =
        (if rraVM v 0 0 = true then some 0 else none) := rfl
    rw [hvm] at e2
    rw [e0, e1, e2]
    cases v.getLsbD 0 <;> rfl
  · have hn2n : 2 ≤ n := by omega
    unfold rraChoiceHw rraChoiceNat
    rw [rraLoopNat_spec (rraVM v lg), rraLoopNat_spec]
    have hn1 : n - 1 + 1 = n := by omega
    have hn2 : n - 2 + 1 = n - 1 := by omega
    rw [hn1, hn2, rraFindNat_vm_eq v hlg]
    cases h1 : rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
    | some j => rfl
    | none =>
      cases h2 : rraFindNat (fun j => v.getLsbD j) 0 (n - 1) with
      | some j =>
        have hs : rraFindNat (fun j => v.getLsbD j) 0 n = some j := by
          have e := rraFindNat_succ (fun j => v.getLsbD j) 0 (n - 1)
          rw [hn1, h2] at e
          exact e
        simp [hs]
      | none =>
        have hs : rraFindNat (fun j => v.getLsbD j) 0 n =
            (if v.getLsbD (n - 1) = true then some (n - 1) else none) := by
          have e := rraFindNat_succ (fun j => v.getLsbD j) 0 (n - 1)
          rw [hn1, h2] at e
          simpa using e
        rw [hs]
        cases hv : v.getLsbD (n - 1) with
        | true => rfl
        | false => rfl

/-- 越界位读为 false（getLsbD = toNat.testBit，toNat < 2^n） -/
theorem rraGetLsbD_false_of_ge {n : Nat} (v : BitVec n) {j : Nat} (h : n ≤ j) :
    v.getLsbD j = false := by
  have hlt : v.toNat < 2 ^ j :=
    Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) h)
  unfold BitVec.getLsbD
  exact Nat.testBit_lt_two_pow hlt

/-- choice 值恒 < n（默认分支 n-1 < n 需 0 < n） -/
theorem rraChoiceNat_lt {n : Nat} (hn : 0 < n) (v : BitVec n) {lg : Nat} (hlg : lg < n) :
    rraChoiceNat v lg < n := by
  unfold rraChoiceNat
  cases h1 : rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
  | some j =>
    obtain ⟨hlo, hhi, -, -⟩ := rraFindNat_some_spec h1
    show j < n
    omega
  | none =>
    cases h2 : rraFindNat (fun j => v.getLsbD j) 0 n with
    | some j =>
      obtain ⟨hlo, hhi, -, -⟩ := rraFindNat_some_spec h2
      show j < n
      omega
    | none =>
      show n - 1 < n
      omega

/-- io.chosen（:54）：choice 的 Fin 形式 -/
def rraChoice {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) : Fin n :=
  ⟨rraChoiceNat v lg.val, rraChoiceNat_lt hn v lg.isLt⟩

/-- io.out.valid（:55）：in(chosen).valid -/
def rraOutValid {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) : Bool :=
  v.getLsbD (rraChoice hn v lg).val

/-- io.out.bits（:56）：in(chosen).bits，组合直通 -/
def rraOutBits {n : Nat} {α : Type} (hn : 0 < n) (bits : Fin n → α)
    (v : BitVec n) (lg : Fin n) : α :=
  bits (rraChoice hn v lg)

/-- io.in(i).ready（:73-74，count=1 分支）：grant(i) && out.ready。
    count>1 的 lock 分支（:58-71）对 RRArbiter 不生成（D7）。 -/
def rraInReady {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) (outReady : Bool)
    (i : Fin n) : Bool :=
  rraGrant v lg i && outReady

/-- 单拍状态转移（:81 `RegEnable(io.chosen, io.out.fire)`）：
    out.fire = out.valid && out.ready 时 lastGrant := chosen，否则保持。
    out.valid = in(chosen).valid（:55）。 -/
def rraStep {n : Nat} (hn : 0 < n) (v : BitVec n) (outReady : Bool) (lg : Fin n) : Fin n :=
  if v.getLsbD (rraChoice hn v lg).val && outReady then rraChoice hn v lg else lg

/-- 恒定输入下的多拍迭代（无饥饿定理用） -/
def rraRunN {n : Nat} (hn : 0 < n) (v : BitVec n) (r : Bool) (lg : Fin n) : Nat → Fin n
  | 0 => lg
  | t + 1 => rraStep hn v r (rraRunN hn v r lg t)

/-- 多拍运行：输入为每拍的 (valid 向量, out.ready) 列表 -/
def rraRun {n : Nat} (hn : 0 < n) (lg : Fin n) : List (BitVec n × Bool) → Fin n
  | [] => lg
  | (v, r) :: ins => rraRun hn (rraStep hn v r lg) ins

/-- 首步剥离引理：第 t+1 拍的状态 = 走一步后再走 t 拍 -/
theorem rraRunN_succ_step {n : Nat} (hn : 0 < n) (v : BitVec n) (r : Bool) (lg : Fin n)
    (t : Nat) :
    rraRunN hn v r lg (t + 1) = rraRunN hn v r (rraStep hn v r lg) t := by
  induction t generalizing lg with
  | zero => rfl
  | succ t ih =>
    show rraStep hn v r (rraRunN hn v r lg (t + 1)) =
      rraStep hn v r (rraRunN hn v r (rraStep hn v r lg) t)
    rw [ih]

/- ========================================================================= -/
/- 5. 环形距离 rraRotDist                                                     -/
/- ========================================================================= -/

/-- 环形距离：从 lastGrant 之后开始数，i 是第几个。
    值域 [1, n]；i = lg 时为 n（环形序的最后一席）。 -/
def rraRotDist {n : Nat} (lg i : Nat) : Nat := (i + n - lg - 1) % n + 1

theorem rraRotDist_of_lt {n lg i : Nat} (h : lg < i) (hi : i < n) :
    rraRotDist (n := n) lg i = i - lg := by
  unfold rraRotDist
  have e : i + n - lg - 1 = n + (i - lg - 1) := by omega
  rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i - lg - 1 < n)]
  omega

theorem rraRotDist_of_eq {n lg i : Nat} (hn : 0 < n) (h : i = lg) (hl : lg < n) :
    rraRotDist (n := n) lg i = n := by
  unfold rraRotDist
  rw [h]
  have e : lg + n - lg - 1 = n - 1 := by omega
  rw [e, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  omega

theorem rraRotDist_of_gt {n lg i : Nat} (h : i < lg) (hl : lg < n) :
    rraRotDist (n := n) lg i = i + n - lg := by
  unfold rraRotDist
  rw [Nat.mod_eq_of_lt (by omega : i + n - lg - 1 < n)]
  omega

theorem rraRotDist_ge_one {n lg i : Nat} : 1 ≤ rraRotDist (n := n) lg i := by
  unfold rraRotDist; omega

theorem rraRotDist_le {n lg i : Nat} (hn : 0 < n) : rraRotDist (n := n) lg i ≤ n := by
  unfold rraRotDist
  have h := Nat.mod_lt (i + n - lg - 1) hn
  omega

/-- 环形距离的递推：j 在环形序上严格先于 i 时，
    从 j 到 i 的距离 = 从 lg 到 i 的距离 − 从 lg 到 j 的距离 -/
theorem rraRotDist_between {n lg i j : Nat} (hl : lg < n) (hi : i < n) (hj : j < n)
    (h : rraRotDist (n := n) lg j < rraRotDist (n := n) lg i) :
    rraRotDist (n := n) j i = rraRotDist (n := n) lg i - rraRotDist (n := n) lg j := by
  have hn : 0 < n := by omega
  by_cases h1 : lg < j
  · have e1 : rraRotDist (n := n) lg j = j - lg := rraRotDist_of_lt h1 hj
    rw [e1] at h
    by_cases h2 : lg < i
    · have e2 : rraRotDist (n := n) lg i = i - lg := rraRotDist_of_lt h2 hi
      rw [e2] at h
      rw [rraRotDist_of_lt (by omega : j < i) hi, e2, e1]
      omega
    · by_cases h3 : i = lg
      · have e2 : rraRotDist (n := n) lg i = n := rraRotDist_of_eq hn h3 hl
        rw [e2] at h
        rw [rraRotDist_of_gt (by omega : i < j) hj, e2, e1]
        omega
      · have h4 : i < lg := by omega
        have e2 : rraRotDist (n := n) lg i = i + n - lg := rraRotDist_of_gt h4 hl
        rw [e2] at h
        rw [rraRotDist_of_gt (by omega : i < j) hj, e2, e1]
        omega
  · by_cases h1' : j = lg
    · have e1 : rraRotDist (n := n) lg j = n := rraRotDist_of_eq hn h1' hl
      rw [e1] at h
      have hle : rraRotDist (n := n) lg i ≤ n := rraRotDist_le hn
      omega
    · have h1 : j < lg := by omega
      have e1 : rraRotDist (n := n) lg j = j + n - lg := rraRotDist_of_gt h1 hl
      rw [e1] at h
      by_cases h2 : lg < i
      · have e2 : rraRotDist (n := n) lg i = i - lg := rraRotDist_of_lt h2 hi
        rw [e2] at h
        omega
      · by_cases h3 : i = lg
        · have e2 : rraRotDist (n := n) lg i = n := rraRotDist_of_eq hn h3 hl
          rw [e2] at h
          rw [rraRotDist_of_lt (by omega : j < i) hi, e2, e1]
          omega
        · have h4 : i < lg := by omega
          have e2 : rraRotDist (n := n) lg i = i + n - lg := rraRotDist_of_gt h4 hl
          rw [e2] at h
          have h5 : j < i := by omega
          rw [rraRotDist_of_lt h5 hi, e2, e1]
          omega

/- ========================================================================= -/
/- 6. T2 选择正确性：chosen = lastGrant 之后环形首个 valid                     -/
/- ========================================================================= -/

/-- 有 valid 输入时 chosen 必 valid（out.valid 的充分条件） -/
theorem rraChoiceNat_valid {n : Nat} (v : BitVec n) {lg : Nat} (hlg : lg < n)
    (hex : ∃ j, v.getLsbD j = true) :
    v.getLsbD (rraChoiceNat v lg) = true := by
  unfold rraChoiceNat
  cases h1 : rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
  | some j =>
    obtain ⟨-, -, hvj, -⟩ := rraFindNat_some_spec h1
    show v.getLsbD j = true
    exact hvj
  | none =>
    cases h2 : rraFindNat (fun j => v.getLsbD j) 0 n with
    | some j =>
      obtain ⟨-, -, hvj, -⟩ := rraFindNat_some_spec h2
      show v.getLsbD j = true
      exact hvj
    | none =>
      exfalso
      obtain ⟨j, hvj⟩ := hex
      by_cases hjn : j < n
      · have hf := rraFindNat_none_spec h2 j (by omega) (by omega)
        rw [hf] at hvj; contradiction
      · have hf := rraGetLsbD_false_of_ge v (by omega : n ≤ j)
        rw [hf] at hvj; contradiction

/-- 选择正确性（Nat 形式）：chosen 是所有 valid 中环形距离 lastGrant 最小者 -/
theorem rraChoiceNat_first {n : Nat} (v : BitVec n) {lg : Nat} (hlg : lg < n)
    {j : Nat} (hvj : v.getLsbD j = true) (hjn : j < n)
    (hne : j ≠ rraChoiceNat v lg) :
    rraRotDist (n := n) lg (rraChoiceNat v lg) < rraRotDist (n := n) lg j := by
  have hn : 0 < n := by omega
  unfold rraChoiceNat
  cases h1 : rraFindNat (fun j => v.getLsbD j) (lg + 1) (n - (lg + 1)) with
  | some c =>
    obtain ⟨hloc, hhic, hvc, hminc⟩ := rraFindNat_some_spec h1
    have hcn : c < n := by omega
    have hne' : j ≠ c := by
      intro he
      apply hne
      rw [he]
      unfold rraChoiceNat
      rw [h1]
    show rraRotDist (n := n) lg c < rraRotDist (n := n) lg j
    have hlgc : lg < c := by omega
    rw [rraRotDist_of_lt hlgc hcn]
    by_cases hlgj : lg < j
    · -- lg < j：c 是 (lg, n) 中首个 valid，故 c ≤ j；j ≠ c 得 c < j
      by_cases hjc : j < c
      · have hf := hminc j (by omega) hjc
        rw [hf] at hvj; contradiction
      · rw [rraRotDist_of_lt hlgj hjn]
        omega
    · by_cases hje : j = lg
      · rw [rraRotDist_of_eq hn hje hlg]
        omega
      · have hjl : j < lg := by omega
        rw [rraRotDist_of_gt hjl hlg]
        omega
  | none =>
    cases h2 : rraFindNat (fun j => v.getLsbD j) 0 n with
    | some c =>
      obtain ⟨hloc, hhic, hvc, hminc⟩ := rraFindNat_some_spec h2
      have hcn : c < n := by omega
      have hne' : j ≠ c := by
        intro he
        apply hne
        rw [he]
        unfold rraChoiceNat
        rw [h1, h2]
      show rraRotDist (n := n) lg c < rraRotDist (n := n) lg j
      -- (lg, n) 中无 valid（h1），故 c、j 都 ≤ lg
      have hclg : c ≤ lg := by
        by_cases hgt : lg < c
        · have hf := rraFindNat_none_spec h1 c (by omega) (by omega)
          rw [hf] at hvc; contradiction
        · omega
      have hjlg : j ≤ lg := by
        by_cases hgt : lg < j
        · have hf := rraFindNat_none_spec h1 j (by omega) (by omega)
          rw [hf] at hvj; contradiction
        · omega
      -- c 是 [0, n) 中首个 valid，故 c ≤ j；j ≠ c 得 c < j
      have hcj : c < j := by
        by_cases hgt : j < c
        · have hf := hminc j (by omega) hgt
          rw [hf] at hvj; contradiction
        · by_cases heq : j = c
          · exact absurd heq hne'
          · omega
      have hclt : c < lg := by omega
      rw [rraRotDist_of_gt hclt hlg]
      by_cases hje : j = lg
      · rw [rraRotDist_of_eq hn hje hlg]
        omega
      · have hjl : j < lg := by omega
        rw [rraRotDist_of_gt hjl hlg]
        omega
    | none =>
      exfalso
      have hf := rraFindNat_none_spec h2 j (by omega) (by omega)
      rw [hf] at hvj; contradiction

/-- T2a：out.valid ↔ 存在 valid 输入（:55 的直接推论） -/
theorem rra2_choice_valid {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) :
    v.getLsbD (rraChoice hn v lg).val = true ↔ ∃ i : Fin n, v.getLsbD i.val = true := by
  constructor
  · intro h
    exact ⟨rraChoice hn v lg, h⟩
  · intro ⟨i, hi⟩
    exact rraChoiceNat_valid v lg.isLt ⟨i.val, hi⟩

/-- T2b 选择正确性：任何其他 valid 输入的环形距离都严格大于 chosen 的 -/
theorem rra2_choice_first {n : Nat} (hn : 0 < n) (v : BitVec n) (lg j : Fin n)
    (hvj : v.getLsbD j.val = true) (hne : j.val ≠ (rraChoice hn v lg).val) :
    rraRotDist (n := n) lg.val (rraChoice hn v lg).val <
      rraRotDist (n := n) lg.val j.val :=
  rraChoiceNat_first v lg.isLt hvj j.isLt hne

/-- T2c 默认值：无 valid 输入时 chosen = n-1（:90 的 WireDefault） -/
theorem rra2_choice_default {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (hnone : ∀ i : Fin n, v.getLsbD i.val = false) :
    (rraChoice hn v lg).val = n - 1 := by
  show rraChoiceNat v lg.val = n - 1
  unfold rraChoiceNat
  cases h1 : rraFindNat (fun j => v.getLsbD j) (lg.val + 1) (n - (lg.val + 1)) with
  | some j =>
    obtain ⟨hlo, hhi, hvj, -⟩ := rraFindNat_some_spec h1
    have hf := hnone ⟨j, by omega⟩
    rw [hf] at hvj; contradiction
  | none =>
    cases h2 : rraFindNat (fun j => v.getLsbD j) 0 n with
    | some j =>
      obtain ⟨hlo, hhi, hvj, -⟩ := rraFindNat_some_spec h2
      have hf := hnone ⟨j, by omega⟩
      rw [hf] at hvj; contradiction
    | none => rfl

/- ========================================================================= -/
/- 7. T0 grant 语义刻画 与 T1 互斥/一致性                                     -/
/- ========================================================================= -/

/-- ctrl(i) 段的语义：(lg, i) 区间内无 valid -/
theorem rraCtrl_req_lt {n : Nat} (v : BitVec n) (lg i : Fin n) :
    rraCtrl (rraReq v lg.val) i.val = true ↔
      ∀ j, lg.val < j → j < i.val → v.getLsbD j = false := by
  rw [rraCtrl_eq_true_iff]
  constructor
  · intro h j hlgj hji
    have hj := h j hji
    unfold rraReq rraVM at hj
    rw [if_pos (by omega : j < n)] at hj
    by_cases hv : v.getLsbD j = true
    · simp [hv, hlgj] at hj
    · cases hc : v.getLsbD j with
      | false => rfl
      | true => exact absurd hc hv
  · intro h j hji
    unfold rraReq rraVM
    rw [if_pos (by omega : j < n)]
    by_cases hlgj : lg.val < j
    · have hf := h j hlgj hji
      simp [hf, hlgj]
    · simp [hlgj]

/-- ctrl(i+n) 段的语义：(lg, n) 内无 valid 且 [0, i) 内无 valid -/
theorem rraCtrl_req_add {n : Nat} (v : BitVec n) (lg i : Fin n) :
    rraCtrl (rraReq v lg.val) (i.val + n) = true ↔
      (∀ j, lg.val < j → j < n → v.getLsbD j = false) ∧
        ∀ j, j < i.val → v.getLsbD j = false := by
  rw [rraCtrl_eq_true_iff]
  constructor
  · intro h
    constructor
    · intro j hlgj hjn
      have hj := h j (by omega)
      unfold rraReq rraVM at hj
      rw [if_pos hjn] at hj
      by_cases hv : v.getLsbD j = true
      · simp [hv, hlgj] at hj
      · cases hc : v.getLsbD j with
        | false => rfl
        | true => exact absurd hc hv
    · intro j hji
      have hj := h (j + n) (by omega)
      unfold rraReq rraVM at hj
      rw [if_neg (by omega : ¬ j + n < n)] at hj
      have e : j + n - n = j := by omega
      rw [e] at hj
      exact hj
  · intro ⟨h1, h2⟩ j hj
    by_cases hjn : j < n
    · unfold rraReq rraVM
      rw [if_pos hjn]
      by_cases hlgj : lg.val < j
      · have hf := h1 j hlgj hjn
        simp [hf, hlgj]
      · simp [hlgj]
    · unfold rraReq rraVM
      rw [if_neg hjn]
      exact h2 (j - n) (by omega)

/-- T0 grant 语义刻画（D6）：grant(i) = 环形开区间 (lg, i) 内无 valid。
    两个析取支分别对应 i > lg（:87 的 ctrl(i) && grantMask(i) 支）
    与 i ≤ lg（:87 的 ctrl(i+n) 支）。 -/
theorem rraGrant_eq_true_iff {n : Nat} (v : BitVec n) (lg i : Fin n) :
    rraGrant v lg i = true ↔
      (lg.val < i.val ∧ ∀ j, lg.val < j → j < i.val → v.getLsbD j = false) ∨
        (i.val ≤ lg.val ∧ (∀ j, lg.val < j → j < n → v.getLsbD j = false) ∧
          ∀ j, j < i.val → v.getLsbD j = false) := by
  unfold rraGrant
  by_cases hli : lg.val < i.val
  · -- i > lg：grant = ctrl(i)（ctrl(i+n) 被 ctrl(i) 吸收）
    have hmono : rraCtrl (rraReq v lg.val) (i.val + n) = true →
        rraCtrl (rraReq v lg.val) i.val = true := by
      intro h
      rw [rraCtrl_eq_true_iff] at h ⊢
      intro j hj
      exact h j (by omega)
    have heq : ((rraCtrl (rraReq v lg.val) i.val && decide (lg.val < i.val)) ||
        rraCtrl (rraReq v lg.val) (i.val + n)) = rraCtrl (rraReq v lg.val) i.val := by
      have hd : decide (lg.val < i.val) = true := decide_eq_true hli
      rw [hd]
      generalize hA : rraCtrl (rraReq v lg.val) i.val = A
      generalize hA' : rraCtrl (rraReq v lg.val) (i.val + n) = A'
      cases A with
      | true => simp
      | false =>
        cases A' with
        | true => rw [hmono hA'] at hA; contradiction
        | false => rfl
    rw [heq, rraCtrl_req_lt]
    constructor
    · intro h
      exact Or.inl ⟨hli, h⟩
    · intro h
      cases h with
      | inl hh => exact hh.2
      | inr hh => omega
  · -- i ≤ lg：grant = ctrl(i+n)
    have hle : i.val ≤ lg.val := by omega
    have hd : decide (lg.val < i.val) = false := decide_eq_false hli
    rw [hd]
    simp only [Bool.and_false, Bool.false_or]
    rw [rraCtrl_req_add]
    constructor
    · intro h
      exact Or.inr ⟨hle, h⟩
    · intro h
      cases h with
      | inl hh => omega
      | inr hh => exact hh.2

/-- T1a 一致性：valid 的 chosen 必获 grant（grant 与 chosen 对齐） -/
theorem rra1_choice_granted {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (hv : v.getLsbD (rraChoice hn v lg).val = true) :
    rraGrant v lg (rraChoice hn v lg) = true := by
  rw [rraGrant_eq_true_iff]
  generalize hc : rraChoice hn v lg = c
  by_cases hlc : lg.val < c.val
  · left
    refine ⟨hlc, ?_⟩
    intro j hlgj hjc
    by_cases hvj : v.getLsbD j = true
    · exfalso
      have hjn : j < n := by omega
      have hlt := rra2_choice_first hn v lg ⟨j, hjn⟩ hvj (by
        rw [hc]
        show j ≠ c.val
        omega)
      rw [hc] at hlt
      rw [rraRotDist_of_lt hlc c.isLt, rraRotDist_of_lt hlgj hjn] at hlt
      omega
    · cases hd : v.getLsbD j with
      | false => rfl
      | true => exact absurd hd hvj
  · right
    have hle : c.val ≤ lg.val := by omega
    refine ⟨hle, ?_, ?_⟩
    · intro j hlgj hjn
      by_cases hvj : v.getLsbD j = true
      · exfalso
        have hlt := rra2_choice_first hn v lg ⟨j, hjn⟩ hvj (by
          rw [hc]
          show j ≠ c.val
          omega)
        rw [hc] at hlt
        rw [rraRotDist_of_lt hlgj hjn] at hlt
        rcases Nat.eq_or_lt_of_le hle with heq | hlt'
        · rw [rraRotDist_of_eq hn heq lg.isLt] at hlt
          omega
        · rw [rraRotDist_of_gt hlt' lg.isLt] at hlt
          omega
      · cases hd : v.getLsbD j with
        | false => rfl
        | true => exact absurd hd hvj
    · intro j hjc
      by_cases hvj : v.getLsbD j = true
      · exfalso
        have hjn : j < n := by omega
        have hlt := rra2_choice_first hn v lg ⟨j, hjn⟩ hvj (by
          rw [hc]
          show j ≠ c.val
          omega)
        rw [hc] at hlt
        have hjl : j < lg.val := by omega
        rw [rraRotDist_of_gt hjl lg.isLt] at hlt
        rcases Nat.eq_or_lt_of_le hle with heq | hlt'
        · rw [rraRotDist_of_eq hn heq lg.isLt] at hlt
          omega
        · rw [rraRotDist_of_gt hlt' lg.isLt] at hlt
          omega
      · cases hd : v.getLsbD j with
        | false => rfl
        | true => exact absurd hd hvj

/-- T1b 一致性：valid 且获 grant 的输入必为 chosen -/
theorem rra1_grant_valid_eq_choice {n : Nat} (hn : 0 < n) (v : BitVec n) (lg i : Fin n)
    (hvi : v.getLsbD i.val = true) (hg : rraGrant v lg i = true) :
    i = rraChoice hn v lg := by
  apply Classical.byContradiction
  intro hne
  have hne' : i.val ≠ (rraChoice hn v lg).val := fun h => hne (Fin.ext h)
  have hlt := rra2_choice_first hn v lg i hvi hne'
  rw [rraGrant_eq_true_iff] at hg
  generalize hc : rraChoice hn v lg = c
  rw [hc] at hlt
  have hcv : v.getLsbD c.val = true := by
    rw [← hc]
    exact (rra2_choice_valid hn v lg).mpr ⟨i, hvi⟩
  cases hg with
  | inl h =>
    obtain ⟨hli, hnone⟩ := h
    rw [rraRotDist_of_lt hli i.isLt] at hlt
    by_cases hlc : lg.val < c.val
    · rw [rraRotDist_of_lt hlc c.isLt] at hlt
      have hf := hnone c.val hlc (by omega)
      rw [hf] at hcv; contradiction
    · have hle : c.val ≤ lg.val := by omega
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · rw [rraRotDist_of_eq hn heq lg.isLt] at hlt
        omega
      · rw [rraRotDist_of_gt hlt' lg.isLt] at hlt
        omega
  | inr h =>
    obtain ⟨hli, hnone1, hnone2⟩ := h
    have hcl : c.val ≤ lg.val := by
      by_cases hgt : lg.val < c.val
      · have hf := hnone1 c.val hgt c.isLt
        rw [hf] at hcv; contradiction
      · omega
    have hci : i.val ≤ c.val := by
      by_cases hgt : c.val < i.val
      · have hf := hnone2 c.val hgt
        rw [hf] at hcv; contradiction
      · omega
    rcases Nat.eq_or_lt_of_le hli with heqi | hlti
    · have hceq : c.val = i.val := by omega
      exact hne ((Fin.ext hceq.symm).trans hc.symm)
    · rw [rraRotDist_of_gt hlti lg.isLt] at hlt
      rcases Nat.eq_or_lt_of_le hcl with heqc | hltc
      · rw [rraRotDist_of_eq hn heqc lg.isLt] at hlt
        omega
      · rw [rraRotDist_of_gt hltc lg.isLt] at hlt
        omega

/-- T1 互斥：至多一个 valid 输入获 grant（结合 :55，至多一路实际传输） -/
theorem rra1_mutex {n : Nat} (hn : 0 < n) (v : BitVec n) (lg i j : Fin n)
    (hvi : v.getLsbD i.val = true) (hgi : rraGrant v lg i = true)
    (hvj : v.getLsbD j.val = true) (hgj : rraGrant v lg j = true) :
    i = j := by
  rw [rra1_grant_valid_eq_choice hn v lg i hvi hgi]
  rw [rra1_grant_valid_eq_choice hn v lg j hvj hgj]

/- ========================================================================= -/
/- 8. T3 反压期间的稳定性：无 lock（D7）⇒ 条件稳定 + Irrevocable 反例         -/
/- ========================================================================= -/

/-- T3 条件稳定性：反压期间（lastGrant 不变）若下一拍 chosen 仍 valid 且
    环形区间 (lg, chosen) 内无新增 valid，则 chosen 不变（out.bits 亦不变）。
    这是 RRArbiter 在无 lock 情况下能给出的最强稳定性（对照 Q1）。 -/
theorem rra3_choice_stable {n : Nat} (hn : 0 < n) (v v' : BitVec n) (lg : Fin n)
    (hcv : v'.getLsbD (rraChoice hn v lg).val = true)
    (hno : ∀ j : Fin n,
      rraRotDist (n := n) lg.val j.val <
        rraRotDist (n := n) lg.val (rraChoice hn v lg).val →
      v'.getLsbD j.val = false) :
    rraChoice hn v' lg = rraChoice hn v lg := by
  apply Classical.byContradiction
  intro hne
  have hcv' : v'.getLsbD (rraChoice hn v' lg).val = true :=
    (rra2_choice_valid hn v' lg).mpr ⟨rraChoice hn v lg, hcv⟩
  have hlt := rra2_choice_first hn v' lg (rraChoice hn v lg) hcv (by
    intro he
    exact hne (Fin.ext he.symm))
  have hf := hno (rraChoice hn v' lg) hlt
  rw [hf] at hcv'; contradiction

/-- T3 反压正例的步进形式：ready=false 时 lastGrant 不变 -/
theorem rra3_step_not_ready {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) :
    rraStep hn v false lg = lg := by
  simp [rraStep]

-- T3 反例（Q1 的 witness）：n=4，反压期间新到高优先级请求改变 chosen/out.bits
section RraCounterexample

open Ventus.Base Handshake

/-- 各输入的 payload：bits(i) = 16*i + 1 -/
def rraCexBits : Fin 4 → BitVec 8 := fun i => BitVec.ofNat 8 (i.val * 16 + 1)

/-- 请求序列：第 0 拍仅输入 0 请求，第 1 拍起输入 0、3 请求
    （lg=2 时 3 在环形序上先于 0） -/
def rraCexV : Nat → BitVec 4
  | 0 => 0b0001#4
  | _ => 0b1001#4

/-- 反压（ready 恒 false）下 lastGrant 恒为初值 2 -/
def rraCexLgSeq : Nat → Fin 4
  | 0 => ⟨2, by decide⟩
  | t + 1 => rraStep (by decide) (rraCexV t) false (rraCexLgSeq t)

/-- out 通道观测迹 -/
def rraCexTrace : Trace (BitVec 8) := fun t =>
  ⟨rraOutValid (by decide) (rraCexV t) (rraCexLgSeq t), false,
    rraOutBits (by decide) rraCexBits (rraCexV t) (rraCexLgSeq t)⟩

/-- T3 反例：RRArbiter 的 out 不满足 Stable（故不 Irrevocable）。
    第 0 拍 out.valid=1、ready=0、bits=0x01（chosen=0）；
    第 1 拍 chosen 跳到 3，bits=0x31——反压期间 bits 改变。 -/
theorem rra3_not_stable : ¬ Stable rraCexTrace := by
  intro h
  have hs := h 0 (by decide) (by decide)
  have h0 : (rraCexTrace 0).bits = 0x01#8 := by decide
  have h1 : (rraCexTrace 1).bits = 0x31#8 := by decide
  rw [h0, h1] at hs
  contradiction

end RraCounterexample

/- ========================================================================= -/
/- 9. T4 lastGrant 更新（:81）                                                -/
/- ========================================================================= -/

/-- T4a：out.fire（chosen valid 且 ready）时 lastGrant := chosen -/
theorem rra4_step_of_fire {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (hv : v.getLsbD (rraChoice hn v lg).val = true) :
    rraStep hn v true lg = rraChoice hn v lg := by
  unfold rraStep
  rw [hv]
  rfl

/-- T4b：out.valid = false 时 lastGrant 不变（RegEnable 使能无效） -/
theorem rra4_step_of_not_valid {n : Nat} (hn : 0 < n) (v : BitVec n) (r : Bool) (lg : Fin n)
    (hv : v.getLsbD (rraChoice hn v lg).val = false) :
    rraStep hn v r lg = lg := by
  unfold rraStep
  rw [hv]
  cases r <;> rfl

/-- T4c：out.ready = false 时 lastGrant 不变 -/
theorem rra4_step_of_not_ready {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n) :
    rraStep hn v false lg = lg :=
  rra3_step_not_ready hn v lg

/- ========================================================================= -/
/- 10. T5 无饥饿：持续 valid + 下游恒 ready ⇒ 至多 n-1 拍内被授予              -/
/- ========================================================================= -/

/-- 无饥饿主引理：按环形距离强归纳。
    每拍若 i 未被授予，则 chosen（j ≠ i）fire，lastGrant 前移到 j，
    i 的环形距离严格减小（rraRotDist_between）。 -/
theorem rra5_aux {n : Nat} (hn : 0 < n) (v : BitVec n) (i : Fin n)
    (hv : v.getLsbD i.val = true) :
    ∀ d : Nat, ∀ lg : Fin n, rraRotDist (n := n) lg.val i.val = d →
      ∃ t, t ≤ d - 1 ∧ rraChoice hn v (rraRunN hn v true lg t) = i := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d IH =>
    intro lg hdist
    generalize hc : rraChoice hn v lg = c
    have hcv : v.getLsbD c.val = true := by
      rw [← hc]
      exact (rra2_choice_valid hn v lg).mpr ⟨i, hv⟩
    by_cases hci : c = i
    · refine ⟨0, by have := rraRotDist_ge_one (n := n) (lg := lg.val) (i := i.val); omega, ?_⟩
      show rraChoice hn v (rraRunN hn v true lg 0) = i
      show rraChoice hn v lg = i
      rw [hc]
      exact hci
    · -- c ≠ i：本拍 c fire，lastGrant := c，距离严格减小
      have hne : i.val ≠ (rraChoice hn v lg).val := by
        rw [hc]
        intro he
        exact hci (Fin.ext he.symm)
      have hlt : rraRotDist (n := n) lg.val (rraChoice hn v lg).val <
          rraRotDist (n := n) lg.val i.val :=
        rra2_choice_first hn v lg i hv hne
      rw [hc] at hlt
      have hbet : rraRotDist (n := n) c.val i.val =
          rraRotDist (n := n) lg.val i.val - rraRotDist (n := n) lg.val c.val :=
        rraRotDist_between lg.isLt i.isLt c.isLt hlt
      have hpos : 1 ≤ rraRotDist (n := n) c.val i.val :=
        rraRotDist_ge_one (n := n) (lg := c.val) (i := i.val)
      have hpos' : 1 ≤ rraRotDist (n := n) lg.val c.val :=
        rraRotDist_ge_one (n := n) (lg := lg.val) (i := c.val)
      have hd2 : rraRotDist (n := n) c.val i.val < d := by omega
      obtain ⟨t', ht'1, ht'2⟩ := IH (rraRotDist (n := n) c.val i.val) hd2 c rfl
      refine ⟨t' + 1, by omega, ?_⟩
      have hstep : rraStep hn v true lg = c := by
        unfold rraStep
        rw [hc, hcv]
        rfl
      rw [rraRunN_succ_step, hstep]
      exact ht'2

/-- T5 无饥饿：恒定 valid 向量中持续请求 i、下游恒 ready 时，
    至多 n-1 拍后 i 成为 chosen（并被授予传输）。
    对任意初始 lastGrant 成立（D1/Q2：无复位初值亦无碍）。 -/
theorem rra5_no_starvation {n : Nat} (hn : 0 < n) (v : BitVec n) (i lg : Fin n)
    (hv : v.getLsbD i.val = true) :
    ∃ t, t ≤ n - 1 ∧ rraChoice hn v (rraRunN hn v true lg t) = i := by
  obtain ⟨t, ht1, ht2⟩ := rra5_aux hn v i hv (rraRotDist (n := n) lg.val i.val) lg rfl
  have hle := rraRotDist_le (n := n) (lg := lg.val) (i := i.val) hn
  exact ⟨t, by omega, ht2⟩

/- ========================================================================= -/
/- 11. 数值回归测试（先测试；全部 `by decide`）                                -/
/- ========================================================================= -/

section RraRegressionTests

/-- n=4 的 lastGrant 构造简写 -/
def rraLg4 (k : Nat) (h : k < 4 := by decide) : Fin 4 := ⟨k, h⟩

/-- n=4 测试用 payload：bits(i) = 16*i -/
def rraBits4 : Fin 4 → BitVec 8 := fun i => BitVec.ofNat 8 (i.val * 16)

-- T1 无请求：chosen 默认 n-1（:90）、out.valid=false（:55）、grant 全通（D6/Q3）
example : (rraChoice (by decide) 0#4 (rraLg4 2)).val = 3 := by decide
example : rraOutValid (by decide) 0#4 (rraLg4 2) = false := by decide
example : rraGrant 0#4 (rraLg4 2) (rraLg4 0) = true := by decide
example : rraGrant 0#4 (rraLg4 2) (rraLg4 1) = true := by decide
example : rraGrant 0#4 (rraLg4 2) (rraLg4 2) = true := by decide
example : rraGrant 0#4 (rraLg4 2) (rraLg4 3) = true := by decide

-- T2 单请求：任意 lastGrant 下 chosen 都是该请求
example : (rraChoice (by decide) 0b0100#4 (rraLg4 0)).val = 2 := by decide
example : (rraChoice (by decide) 0b0100#4 (rraLg4 1)).val = 2 := by decide
example : (rraChoice (by decide) 0b0100#4 (rraLg4 2)).val = 2 := by decide
example : (rraChoice (by decide) 0b0100#4 (rraLg4 3)).val = 2 := by decide
example : rraOutValid (by decide) 0b0100#4 (rraLg4 3) = true := by decide
example : rraOutBits (by decide) rraBits4 0b0100#4 (rraLg4 3) = 0x20#8 := by decide
example : rraGrant 0b0100#4 (rraLg4 3) (rraLg4 2) = true := by decide

-- T3 全请求 + 恒 ready：环形轮转 0→1→2→3→0（初值 lg=3）
example : (rraChoice (by decide) 0b1111#4 (rraLg4 3)).val = 0 := by decide
example : rraRun (by decide) (rraLg4 3) [(0b1111#4, true)] = rraLg4 0 := by decide
example : rraRun (by decide) (rraLg4 3) (List.replicate 2 (0b1111#4, true)) = rraLg4 1 := by decide
example : rraRun (by decide) (rraLg4 3) (List.replicate 3 (0b1111#4, true)) = rraLg4 2 := by decide
example : rraRun (by decide) (rraLg4 3) (List.replicate 4 (0b1111#4, true)) = rraLg4 3 := by decide
example : rraRun (by decide) (rraLg4 3) (List.replicate 5 (0b1111#4, true)) = rraLg4 0 := by decide
example : (rraChoice (by decide) 0b1111#4
    (rraRun (by decide) (rraLg4 3) (List.replicate 4 (0b1111#4, true)))).val = 0 := by decide

-- T4 环形优先级：lg=1、请求 {0,2}：先授 2（(lg,n) 首个），fire 后环绕授 0
example : (rraChoice (by decide) 0b0101#4 (rraLg4 1)).val = 2 := by decide
example : (rraChoice (by decide) 0b0101#4
    (rraStep (by decide) 0b0101#4 true (rraLg4 1))).val = 0 := by decide
example : (rraChoice (by decide) 0b0101#4
    (rraRun (by decide) (rraLg4 1) (List.replicate 2 (0b0101#4, true)))).val = 2 := by decide

-- T5 grant 语义（D6/Q3 的非 one-hot 行为）：lg=1、请求 {0}：
-- grant = {0, 2, 3}（0 是环绕区首个 valid；2、3 在 (1, n) 中无 valid 遮蔽），grant(1)=false
example : rraGrant 0b0001#4 (rraLg4 1) (rraLg4 0) = true := by decide
example : rraGrant 0b0001#4 (rraLg4 1) (rraLg4 1) = false := by decide
example : rraGrant 0b0001#4 (rraLg4 1) (rraLg4 2) = true := by decide
example : rraGrant 0b0001#4 (rraLg4 1) (rraLg4 3) = true := by decide
-- in.ready = grant && out.ready（:74）
example : rraInReady (by decide) 0b0001#4 (rraLg4 1) true (rraLg4 0) = true := by decide
example : rraInReady (by decide) 0b0001#4 (rraLg4 1) false (rraLg4 0) = false := by decide

-- T6 反压且请求不变：chosen/bits/lastGrant 均不变（rra3_choice_stable 的正例）
example : (rraChoice (by decide) 0b1001#4 (rraLg4 2)).val = 3 := by decide
example : rraRun (by decide) (rraLg4 2) (List.replicate 3 (0b1001#4, false)) = rraLg4 2 := by decide
example : (rraChoice (by decide) 0b1001#4
    (rraRun (by decide) (rraLg4 2) (List.replicate 3 (0b1001#4, false)))).val = 3 := by decide

-- T7 反压但请求模式变化（Q1 witness 的逐步版本）：chosen 从 0 跳到 3
example : (rraChoice (by decide) 0b0001#4 (rraLg4 2)).val = 0 := by decide
example : (rraChoice (by decide) 0b1001#4 (rraLg4 2)).val = 3 := by decide
example : rraOutBits (by decide) rraBits4 0b0001#4 (rraLg4 2) = 0x00#8 := by decide
example : rraOutBits (by decide) rraBits4 0b1001#4 (rraLg4 2) = 0x30#8 := by decide

-- T8 lastGrant 更新时机（:81）：fire 才更新
example : rraStep (by decide) 0b0101#4 true (rraLg4 1) = rraLg4 2 := by decide
example : rraStep (by decide) 0b0101#4 false (rraLg4 1) = rraLg4 1 := by decide
example : rraStep (by decide) 0b0000#4 true (rraLg4 1) = rraLg4 1 := by decide

-- T9 硬件形式与语义形式在具体实例上一致（rraChoiceHw_eq 的抽查）
example : rraChoiceHw 0b0101#4 1 = rraChoiceNat 0b0101#4 1 := by decide
example : rraChoiceHw 0b1111#4 3 = rraChoiceNat 0b1111#4 3 := by decide
example : rraChoiceHw 0b0000#4 2 = rraChoiceNat 0b0000#4 2 := by decide

-- T10 n=8 抽查：环绕与跨段
example : (rraChoice (by decide) 0b00100000#8 (⟨7, by decide⟩ : Fin 8)).val = 5 := by decide
example : (rraChoice (by decide) 0b10000001#8 (⟨7, by decide⟩ : Fin 8)).val = 0 := by decide
example : (rraChoice (by decide) 0b10000001#8 (⟨2, by decide⟩ : Fin 8)).val = 7 := by decide
example : rraRun (by decide) (⟨7, by decide⟩ : Fin 8)
    (List.replicate 2 (0b10000001#8, true)) = (⟨7, by decide⟩ : Fin 8) := by decide

-- T11 n=1 退化（Q4）：chosen 恒 0；grant(0) 恒 true
example : (rraChoice (by decide) 1#1 (⟨0, by decide⟩ : Fin 1)).val = 0 := by decide
example : rraOutValid (by decide) 1#1 (⟨0, by decide⟩ : Fin 1) = true := by decide
example : (rraChoice (by decide) 0#1 (⟨0, by decide⟩ : Fin 1)).val = 0 := by decide
example : rraOutValid (by decide) 0#1 (⟨0, by decide⟩ : Fin 1) = false := by decide
example : rraGrant 1#1 (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) = true := by decide
example : rraGrant 0#1 (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) = true := by decide

end RraRegressionTests

/- 公理审计：正式定理应只剩 Lean 标准公理（propext / Classical.choice /
   Quot.sound）；测试中的 decide 不引入公理。 -/
#print axioms rraChoiceHw_eq
#print axioms rraGrant_eq_true_iff
#print axioms rra1_mutex
#print axioms rra1_choice_granted
#print axioms rra1_grant_valid_eq_choice
#print axioms rra2_choice_valid
#print axioms rra2_choice_first
#print axioms rra2_choice_default
#print axioms rra3_choice_stable
#print axioms rra3_not_stable
#print axioms rra4_step_of_fire
#print axioms rra5_no_starvation

end Ventus.Schedule
