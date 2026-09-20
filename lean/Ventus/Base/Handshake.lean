/- ========================================================================= -/
/-                           Handshake.lean                                  -/
/-  valid/ready 握手契约库（对应 chisel3.util.Decoupled / Valid 语义）         -/
/-                                                                           -/
/-  建模：通道在某拍的观测为 (valid, ready, bits) 三元组（`Obs`），            -/
/-  一条迹 `Trace α = Nat → Obs α` 给出每拍观测；契约全部是迹上的谓词。        -/
/-  核心契约 `Irrevocable = Stable ∧ NoWithdraw`，对应                        -/
/-  original/coralnpu-main/hdl/chisel/src/common/Library.scala:268-293        -/
/-  中 IrrevocableChecker 的运行时断言意图：                                  -/
/-  “valid 置位且当拍未被 ready 接收时，下一拍 valid 必须保持、bits 必须不变”。  -/
/-                                                                           -/
/-  设计取舍：                                                                -/
/-    * 不做 category 式泛化，迹就是函数，契约就是 ∀ t 的逐拍谓词；           -/
/-    * `Irrevocable` 直接定义为合取，`irrevocable_iff` 给出合并形式，        -/
/-      父模块验证时按需投影/重组（假设-保证消解）；                          -/
/-    * `countFires` 用递归定义而非 List.countP，归纳证明直接 rfl 展开。     -/
/-                                                                           -/
/-  移植记录：2026-08-25 自 coralNPU/lean/CoralNPU/Base/Handshake.lean         -/
/-  逐行移植（仅 CoralNPU.Base → Ventus.Base 改名），移植时逐定义重审语义      -/
/-  （"移植即重审"），审查结论见第 7 节回归测试的头部注释。                    -/
/- ========================================================================= -/

import Ventus.Base.Defs

namespace Ventus.Base
namespace Handshake

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 通道观测与迹                                                            -/
/- ========================================================================= -/

/-- 一拍观测：Decoupled 通道在某拍呈现的三元组。
    valid/bits 由源（producer）驱动，ready 由汇（consumer）驱动。 -/
structure Obs (α : Type) where
  valid : Bool
  ready : Bool
  bits  : α

/-- 迹：每拍的通道观测（组合/时序行为在时间轴上的外化）。
    定义为 `def` 而非 `abbrev`，使 `tr.shift` 等点记法可解析到 `Trace.*`。 -/
def Trace (α : Type) : Type := Nat → Obs α

/-- 一拍传输（fire）：valid 与 ready 同拍为高。 -/
def fires (valid ready : Bool) : Bool := valid && ready

theorem fires_eq (v r : Bool) : fires v r = (v && r) := rfl

theorem fires_true_iff (v r : Bool) : fires v r = true ↔ v = true ∧ r = true := by
  simp [fires, Bool.and_eq_true]

theorem fires_of {v r : Bool} (hv : v = true) (hr : r = true) : fires v r = true := by
  rw [fires_true_iff]; exact ⟨hv, hr⟩

theorem fires_comm (v r : Bool) : fires v r = fires r v := Bool.and_comm v r

namespace Obs

/-- 该拍是否发生传输。 -/
def fires {α : Type} (o : Obs α) : Bool := o.valid && o.ready

@[simp] theorem fires_mk {α : Type} (v r : Bool) (b : α) :
    (Obs.mk v r b).fires = (v && r) := rfl

theorem fires_true_iff {α : Type} (o : Obs α) :
    o.fires = true ↔ o.valid = true ∧ o.ready = true := by
  simp [Obs.fires, Bool.and_eq_true]

/-- 与全局 `fires` 的关系（同一定义的两种视角，便于重写）。 -/
theorem fires_eq_fires {α : Type} (o : Obs α) :
    o.fires = Handshake.fires o.valid o.ready := rfl

end Obs

/- ========================================================================= -/
/- 2. 核心契约谓词                                                            -/
/- ========================================================================= -/

variable {α β : Type}

/-- 数据稳定（Stable）：valid 被反压（valid ∧ ¬ready）时，下一拍 bits 不变。 -/
def Stable (tr : Trace α) : Prop :=
  ∀ t, (tr t).valid = true → (tr t).ready = false → (tr (t + 1)).bits = (tr t).bits

/-- 不撤有效（NoWithdraw）：valid 被反压时，下一拍 valid 保持为高。 -/
def NoWithdraw (tr : Trace α) : Prop :=
  ∀ t, (tr t).valid = true → (tr t).ready = false → (tr (t + 1)).valid = true

/-- 不可撤销契约（Irrevocable，对应 Chisel IrrevocableIO 的断言语义）。
    定义为 Stable ∧ NoWithdraw 的合取，方便分别假设、分别证明。 -/
def Irrevocable (tr : Trace α) : Prop := Stable tr ∧ NoWithdraw tr

/-- 合并形式：与 IrrevocableChecker 的两条断言逐字对应。 -/
theorem irrevocable_iff {tr : Trace α} :
    Irrevocable tr ↔
      ∀ t, (tr t).valid = true → (tr t).ready = false →
        (tr (t + 1)).valid = true ∧ (tr (t + 1)).bits = (tr t).bits := by
  constructor
  · intro h t hv hr
    exact ⟨h.2 t hv hr, h.1 t hv hr⟩
  · intro h
    exact ⟨fun t hv hr => (h t hv hr).2, fun t hv hr => (h t hv hr).1⟩

/-- 合取消解：Irrevocable 即 Stable 与 NoWithdraw 的合取（定义即如此）。 -/
theorem irrevocable_and_stable_noWithdraw {tr : Trace α} :
    Irrevocable tr ↔ Stable tr ∧ NoWithdraw tr := Iff.rfl

/-- 由两个子契约合成 Irrevocable。 -/
theorem irrevocable_of {tr : Trace α} (hs : Stable tr) (hn : NoWithdraw tr) :
    Irrevocable tr := ⟨hs, hn⟩

theorem Irrevocable.stable {tr : Trace α} (h : Irrevocable tr) : Stable tr := h.1

theorem Irrevocable.noWithdraw {tr : Trace α} (h : Irrevocable tr) : NoWithdraw tr := h.2

/-- 恒 ready：下游永畅通。 -/
def AlwaysReady (tr : Trace α) : Prop := ∀ t, (tr t).ready = true

/-- 恒 valid：上游永提供数据。 -/
def AlwaysValid (tr : Trace α) : Prop := ∀ t, (tr t).valid = true

/-- 永不 valid：空源。 -/
def NeverValid (tr : Trace α) : Prop := ∀ t, (tr t).valid = false

/-- 恒 ready 的通道 vacuously 满足 Irrevocable（反压前提永不成立）。 -/
theorem irrevocable_of_alwaysReady {tr : Trace α} (h : AlwaysReady tr) : Irrevocable tr := by
  constructor <;> intro t _ hr <;> simp [h t] at hr

/-- 永不 valid 的通道 vacuously 满足 Irrevocable。 -/
theorem irrevocable_of_neverValid {tr : Trace α} (h : NeverValid tr) : Irrevocable tr := by
  constructor <;> intro t hv <;> simp [h t] at hv

/-- valid 蕴含当拍 ready（从不受反压，如组合透传）则 Irrevocable。 -/
theorem irrevocable_of_valid_imp_ready {tr : Trace α}
    (h : ∀ t, (tr t).valid = true → (tr t).ready = true) : Irrevocable tr := by
  constructor <;> intro t hv hr <;> simp [h t hv] at hr

/- ========================================================================= -/
/- 3. 传输计数                                                                -/
/- ========================================================================= -/

/-- 前 n 拍（区间 [0, n)）内的传输次数。 -/
def countFires (tr : Trace α) : Nat → Nat
  | 0     => 0
  | n + 1 => countFires tr n + (if (tr n).fires then 1 else 0)

/-- 前 n 拍内 valid 置位的拍数（AlwaysReady 下等于传输次数）。 -/
def countValid (tr : Trace α) : Nat → Nat
  | 0     => 0
  | n + 1 => countValid tr n + (if (tr n).valid then 1 else 0)

@[simp] theorem countFires_zero (tr : Trace α) : countFires tr 0 = 0 := rfl

@[simp] theorem countFires_succ (tr : Trace α) (n : Nat) :
    countFires tr (n + 1) = countFires tr n + (if (tr n).fires then 1 else 0) := rfl

@[simp] theorem countValid_succ (tr : Trace α) (n : Nat) :
    countValid tr (n + 1) = countValid tr n + (if (tr n).valid then 1 else 0) := rfl

/-- 第 n 拍 fire，则计数 +1。 -/
theorem countFires_succ_of_fires {tr : Trace α} {n : Nat} (h : (tr n).fires = true) :
    countFires tr (n + 1) = countFires tr n + 1 := by
  rw [countFires_succ]; simp [h]

/-- 第 n 拍未 fire，则计数不变。 -/
theorem countFires_succ_of_not_fires {tr : Trace α} {n : Nat} (h : (tr n).fires = false) :
    countFires tr (n + 1) = countFires tr n := by
  rw [countFires_succ]; simp [h]

/-- 传输次数上界：每拍至多传一次。 -/
theorem countFires_le (tr : Trace α) (n : Nat) : countFires tr n ≤ n := by
  induction n with
  | zero => exact Nat.zero_le 0
  | succ k ih =>
    rw [countFires_succ]
    cases h : (tr k).fires <;> simp <;> omega

/-- 计数单调：窗口扩大，传输次数不减。 -/
theorem countFires_mono {tr : Trace α} {m n : Nat} (h : m ≤ n) :
    countFires tr m ≤ countFires tr n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- 计数只取决于前 n 拍的观测（限长一致性）。 -/
theorem countFires_congr {tr1 tr2 : Trace α} {n : Nat}
    (h : ∀ t, t < n → tr1 t = tr2 t) :
    countFires tr1 n = countFires tr2 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [countFires_succ, countFires_succ,
        ih (fun t ht => h t (Nat.lt_trans ht (Nat.lt_succ_self k))),
        h k (Nat.lt_succ_self k)]

/-- 窗口内发生过传输 ⇀ 计数为正。 -/
theorem countFires_pos_of_fires {tr : Trace α} {t n : Nat}
    (hf : (tr t).fires = true) (ht : t < n) : 0 < countFires tr n := by
  have h1 : countFires tr (t + 1) = countFires tr t + 1 := countFires_succ_of_fires hf
  have h2 : countFires tr (t + 1) ≤ countFires tr n := countFires_mono ht
  omega

/-- 第 t 拍 fire 严格增大计数：第 t 拍之前的计数 < 覆盖第 t 拍的计数。
    （“第 k 次传输发生在第几拍”类推理的基本引理。） -/
theorem fires_lt_countFires {tr : Trace α} {t n : Nat}
    (hf : (tr t).fires = true) (ht : t < n) :
    countFires tr t < countFires tr n := by
  have h1 : countFires tr (t + 1) = countFires tr t + 1 := countFires_succ_of_fires hf
  have h2 : countFires tr (t + 1) ≤ countFires tr n := countFires_mono ht
  omega

/- ========================================================================= -/
/- 4. 迹变换与契约保持                                                         -/
/- ========================================================================= -/

/-- 平移：丢弃前 k 拍，从第 k 拍起观测（suffix / 限长的对偶）。 -/
def Trace.shift (tr : Trace α) (k : Nat) : Trace α := fun t => tr (k + t)

/-- 拼接：前 n 拍取 tr1，第 n 拍起取 tr2。 -/
def Trace.append (n : Nat) (tr1 tr2 : Trace α) : Trace α :=
  fun t => if t < n then tr1 t else tr2 (t - n)

/-- bits 经组合函数 f 变换、握手信号直连（纯组合映射级）。 -/
def Trace.map (f : α → β) (tr : Trace α) : Trace β :=
  fun t => ⟨(tr t).valid, (tr t).ready, f (tr t).bits⟩

/-- 恒定迹：每拍观测相同。 -/
def Trace.const (o : Obs α) : Trace α := fun _ => o

/-- 空源迹：valid 恒为 false。 -/
def Trace.idle (bits : α) (ready : Bool) : Trace α := const ⟨false, ready, bits⟩

/-- 恒传输迹：valid/ready 恒真、bits 恒定（每拍都在传输）。 -/
def Trace.constFiring (bits : α) : Trace α := const ⟨true, true, bits⟩

@[simp] theorem Trace.shift_apply (tr : Trace α) (k t : Nat) :
    tr.shift k t = tr (k + t) := rfl

theorem Trace.append_apply_of_lt {n : Nat} {tr1 tr2 : Trace α} {t : Nat} (ht : t < n) :
    Trace.append n tr1 tr2 t = tr1 t := by
  simp [Trace.append, ht]

theorem Trace.append_apply_of_le {n : Nat} {tr1 tr2 : Trace α} {t : Nat} (ht : n ≤ t) :
    Trace.append n tr1 tr2 t = tr2 (t - n) := by
  have h : ¬ t < n := Nat.not_lt.mpr ht
  simp [Trace.append, h]

/-- 限长保持：Irrevocable 的 suffix 仍 Irrevocable。 -/
theorem stable_shift {tr : Trace α} (h : Stable tr) (k : Nat) : Stable (tr.shift k) :=
  fun t hv hr => h (k + t) hv hr

theorem noWithdraw_shift {tr : Trace α} (h : NoWithdraw tr) (k : Nat) :
    NoWithdraw (tr.shift k) :=
  fun t hv hr => h (k + t) hv hr

theorem irrevocable_shift {tr : Trace α} (h : Irrevocable tr) (k : Nat) :
    Irrevocable (tr.shift k) :=
  ⟨stable_shift h.1 k, noWithdraw_shift h.2 k⟩

/-- 计数分段可加：前 m+n 拍 = 前 m 拍 + suffix 的前 n 拍。 -/
theorem countFires_add (tr : Trace α) (m n : Nat) :
    countFires tr (m + n) = countFires tr m + countFires (tr.shift m) n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, countFires_succ, countFires_succ, ih,
        Trace.shift_apply, Nat.add_assoc]

/-- 组合映射级保持 Stable。 -/
theorem stable_map (f : α → β) {tr : Trace α} (h : Stable tr) : Stable (tr.map f) :=
  fun t hv hr => congrArg f (h t hv hr)

/-- 组合映射级保持 NoWithdraw。 -/
theorem noWithdraw_map (f : α → β) {tr : Trace α} (h : NoWithdraw tr) :
    NoWithdraw (tr.map f) :=
  fun t hv hr => h t hv hr

/-- 假设-保证（组合映射级）：输入通道 Irrevocable ⇒ 输出通道 Irrevocable。 -/
theorem irrevocable_map (f : α → β) {tr : Trace α} (h : Irrevocable tr) :
    Irrevocable (tr.map f) :=
  ⟨stable_map f h.1, noWithdraw_map f h.2⟩

/-- 组合映射级不改变握手时序：传输计数不变。 -/
theorem countFires_map (f : α → β) (tr : Trace α) (n : Nat) :
    countFires (tr.map f) n = countFires tr n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [countFires_succ, countFires_succ, ih]
    have hf : (Trace.map f tr k).fires = (tr k).fires := rfl
    rw [hf]

/-- 拼接保持 Irrevocable：两段各自满足契约，且接缝处满足衔接条件
    （若 tr1 尾拍 valid 被反压，则 tr2 首拍继续 valid 且 bits 不变）。 -/
theorem irrevocable_append {n : Nat} {tr1 tr2 : Trace α}
    (h1 : Irrevocable tr1) (h2 : Irrevocable tr2)
    (hb : (tr1 (n - 1)).valid = true → (tr1 (n - 1)).ready = false →
          (tr2 0).valid = true ∧ (tr2 0).bits = (tr1 (n - 1)).bits) :
    Irrevocable (Trace.append n tr1 tr2) := by
  rw [irrevocable_iff] at h1 h2
  have key : ∀ t, (Trace.append n tr1 tr2 t).valid = true →
      (Trace.append n tr1 tr2 t).ready = false →
      (Trace.append n tr1 tr2 (t + 1)).valid = true ∧
      (Trace.append n tr1 tr2 (t + 1)).bits = (Trace.append n tr1 tr2 t).bits := by
    intro t hv hr
    by_cases hlt : t + 1 < n
    · -- 两拍都在 tr1 段
      have ht : t < n := Nat.lt_trans (Nat.lt_succ_self t) hlt
      rw [Trace.append_apply_of_lt ht] at hv hr
      rw [Trace.append_apply_of_lt hlt, Trace.append_apply_of_lt ht]
      exact h1 t hv hr
    · by_cases heq : t + 1 = n
      · -- 接缝：第 t 拍在 tr1 段尾，第 t+1 拍是 tr2 段首
        subst heq
        have ht : t < t + 1 := Nat.lt_succ_self t
        have hnlt : ¬ t + 1 < t + 1 := Nat.lt_irrefl _
        have e1 : Trace.append (t + 1) tr1 tr2 t = tr1 t := by simp [Trace.append, ht]
        have e2 : Trace.append (t + 1) tr1 tr2 (t + 1) = tr2 0 := by
          simp [Trace.append, hnlt]
        rw [e1] at hv hr
        rw [e2, e1]
        exact hb hv hr
      · -- 两拍都在 tr2 段
        have hle : n ≤ t := by omega
        have hsucc : t + 1 - n = t - n + 1 := by omega
        have e1 : Trace.append n tr1 tr2 t = tr2 (t - n) := Trace.append_apply_of_le hle
        have e2 : Trace.append n tr1 tr2 (t + 1) = tr2 (t - n + 1) := by
          rw [Trace.append_apply_of_le (by omega : n ≤ t + 1), hsucc]
        rw [e1] at hv hr
        rw [e2, e1]
        exact h2 (t - n) hv hr
  rw [irrevocable_iff]
  exact key

/-- 拼接迹的计数：前 n 拍落在 tr1，之后落在 tr2。 -/
theorem countFires_append {n : Nat} {tr1 tr2 : Trace α} (m : Nat) :
    countFires (Trace.append n tr1 tr2) (n + m) = countFires tr1 n + countFires tr2 m := by
  induction m with
  | zero =>
    rw [Nat.add_zero, countFires_zero, Nat.add_zero]
    exact countFires_congr (fun t ht => Trace.append_apply_of_lt ht)
  | succ k ih =>
    have hlt : ¬ n + k < n := by omega
    have hidx : n + k - n = k := by omega
    have hobs : Trace.append n tr1 tr2 (n + k) = tr2 k := by simp [Trace.append, hlt, hidx]
    rw [Nat.add_succ, countFires_succ, countFires_succ, ih, hobs, Nat.add_assoc]

/- ========================================================================= -/
/- 5. 常量通道（单位构造）及其契约引理                                         -/
/- ========================================================================= -/

/-- 恒定迹满足 Irrevocable（观测不变，契约条件平凡成立）。 -/
theorem irrevocable_const (o : Obs α) : Irrevocable (Trace.const o) :=
  ⟨fun _ _ _ => rfl, fun _ hv _ => hv⟩

/-- 空源迹满足 Irrevocable。 -/
theorem irrevocable_idle (b : α) (r : Bool) : Irrevocable (Trace.idle b r) :=
  irrevocable_const _

/-- 恒传输迹满足 Irrevocable。 -/
theorem irrevocable_constFiring (b : α) : Irrevocable (Trace.constFiring b) :=
  irrevocable_const _

/-- 恒定迹的传输计数：要么每拍都传（n 次），要么一拍不传（0 次）。 -/
theorem countFires_const (o : Obs α) (n : Nat) :
    countFires (Trace.const o) n = (if o.fires then n else 0) := by
  induction n with
  | zero => cases h : o.fires <;> simp
  | succ k ih =>
    rw [countFires_succ]
    have hc : (Trace.const o k).fires = o.fires := rfl
    rw [hc, ih]
    cases h : o.fires <;> simp

/-- 空源迹永不传输。 -/
theorem countFires_idle (b : α) (r : Bool) (n : Nat) :
    countFires (Trace.idle b r) n = 0 := by
  simp [Trace.idle, countFires_const, Obs.fires]

/-- 恒传输迹每拍都传输。 -/
theorem countFires_constFiring (b : α) (n : Nat) :
    countFires (Trace.constFiring b) n = n := by
  simp [Trace.constFiring, countFires_const, Obs.fires]

/- ========================================================================= -/
/- 6. 假设-保证组合定理（父模块验证用的消解模式实例）                          -/
/-                                                                           -/
/-  模式：P（对输入通道/对侧的假设）→ Q（对输出通道/本侧的保证）。           -/
/-    * irrevocable_map            ：输入 Irrevocable ⇒ 输出 Irrevocable      -/
/-    * irrevocable_stable_until   ：源 Irrevocable ⇒ 反压期间数据稳定        -/
/-    * irrevocable_bits_at_fire   ：源 Irrevocable ⇒ 汇消费到的即首断言数据  -/
/-    * countFires_eq_countValid   ：下游 AlwaysReady ⇒ 吞吐 = valid 拍数     -/
/-    * countFires_eq_zero_of_neverValid ：上游 NeverValid ⇒ 零传输           -/
/- ========================================================================= -/

/-- 源保证 Irrevocable 时，从 valid 置位且持续被反压的第 s 拍到之后任意
    第 t 拍：valid 保持为高且 bits 不变（数据稳定直到被接收）。 -/
theorem irrevocable_stable_until {tr : Trace α} (h : Irrevocable tr) {s t : Nat} (hst : s ≤ t)
    (hv : (tr s).valid = true)
    (hblock : ∀ u, s ≤ u → u < t → (tr u).ready = false) :
    (tr t).valid = true ∧ (tr t).bits = (tr s).bits := by
  induction hst with
  | refl => exact ⟨hv, rfl⟩
  | step hsm ih =>
    rename_i m
    have ih' := ih (fun u hu hum => hblock u hu (Nat.lt_trans hum (Nat.lt_succ_self m)))
    have hrm : (tr m).ready = false := hblock m hsm (Nat.lt_succ_self m)
    exact ⟨h.2 m ih'.1 hrm, (h.1 m ih'.1 hrm).trans ih'.2⟩

/-- 汇侧可假设：源保证 Irrevocable 时，传输拍读到的 bits 等于 valid
    首次置位拍的 bits（反压期间数据未被篡改）。 -/
theorem irrevocable_bits_at_fire {tr : Trace α} (h : Irrevocable tr) {s t : Nat} (hst : s ≤ t)
    (hv : (tr s).valid = true)
    (hblock : ∀ u, s ≤ u → u < t → (tr u).ready = false)
    (hfire : (tr t).fires = true) :
    (tr t).bits = (tr s).bits :=
  (irrevocable_stable_until h hst hv hblock).2

/-- 下游恒 ready 时，fires 当且仅当 valid：每拍 valid 必被当拍消费。 -/
theorem fires_of_alwaysReady {tr : Trace α} (h : AlwaysReady tr) (t : Nat) :
    (tr t).fires = (tr t).valid := by
  simp [Obs.fires, h t]

/-- 吞吐保证：下游恒 ready 时，前 n 拍传输次数 = valid 置位拍数。 -/
theorem countFires_eq_countValid {tr : Trace α} (h : AlwaysReady tr) (n : Nat) :
    countFires tr n = countValid tr n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [countFires_succ, countValid_succ, ih, fires_of_alwaysReady h k]

/-- 空源保证：上游永不 valid 时，任意窗口内传输次数为 0。 -/
theorem countFires_eq_zero_of_neverValid {tr : Trace α} (h : NeverValid tr) (n : Nat) :
    countFires tr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [countFires_succ, ih]
    simp [Obs.fires, h k]

/- ========================================================================= -/
/- 7. 数值回归测试（移植重审的判收依据）                                       -/
/-                                                                           -/
/-  移植重审结论（2026-08-25，逐定义对照文档注释）：全部定义与注释语义一致，   -/
/-  未发现行为性疑点，无需"审查疑点"标注。唯一审查观察：                       -/
/-  `irrevocable_append` 的接缝条件 `hb` 在 n = 0 时引用 `tr1 (0 - 1)`         -/
/-  （= `tr1 0`），但此时接缝分支不可达（t + 1 = 0 无解），该假设实际不会      -/
/-  被使用——非 bug，定理对 n = 0 仍成立（拼接迹恒等于 tr2）。                -/
/- ========================================================================= -/

section HandshakeRegressionTests

/-- 测试迹 A：t=0 valid 被反压（bits 在 t=1 保持 0xAA）、t=1 fire、t=2 idle、
    t=3 fire、t≥4 停转（valid/ready 均 false）。满足 Irrevocable。 -/
def testTrA : Trace (Bits 8)
  | 0 => ⟨true,  false, 0xAA⟩
  | 1 => ⟨true,  true,  0xAA⟩
  | 2 => ⟨false, true,  0x00⟩
  | 3 => ⟨true,  true,  0x55⟩
  | _ => ⟨false, false, 0x00⟩

/-- 测试迹 B：前 4 拍与 testTrA 完全相同，t≥4 每拍都 fire（与 A 不同）。 -/
def testTrB : Trace (Bits 8)
  | 0 => ⟨true,  false, 0xAA⟩
  | 1 => ⟨true,  true,  0xAA⟩
  | 2 => ⟨false, true,  0x00⟩
  | 3 => ⟨true,  true,  0x55⟩
  | _ => ⟨true,  true,  0xFF⟩

-- fires / Obs.fires
example : fires true true = true := by decide
example : fires true false = false := by decide
example : fires false false = false := by decide
example : fires true false = fires false true := fires_comm _ _
example : fires true true = true := fires_of rfl rfl
example : (⟨true, true, 0xAA⟩ : Obs (Bits 8)).fires = true := by decide
example : (⟨true, false, 0xAA⟩ : Obs (Bits 8)).fires = false := by decide
example : (⟨true, true, 0xAA⟩ : Obs (Bits 8)).fires = true :=
  (Obs.fires_true_iff _).mpr ⟨rfl, rfl⟩
example : (⟨true, false, 0xAA⟩ : Obs (Bits 8)).fires = Handshake.fires true false :=
  Obs.fires_eq_fires _

-- countFires / countValid（testTrA：fires 在 t=1,3；valid 在 t=0,1,3）
example : countFires testTrA 0 = 0 := by decide
example : countFires testTrA 1 = 0 := by decide    -- t=0 被反压，未 fire
example : countFires testTrA 2 = 1 := by decide
example : countFires testTrA 3 = 1 := by decide
example : countFires testTrA 4 = 2 := by decide
example : countFires testTrA 5 = 2 := by decide    -- t≥4 停转
example : countValid testTrA 2 = 2 := by decide
example : countValid testTrA 4 = 3 := by decide
example : countValid testTrA 5 = 3 := by decide

-- countFires 引理的具体实例
example : countFires testTrA 2 = countFires testTrA 1 + 1 :=
  countFires_succ_of_fires (by decide)
example : countFires testTrA 3 = countFires testTrA 2 :=
  countFires_succ_of_not_fires (by decide)
example : countFires testTrA 5 ≤ 5 := countFires_le _ _
example : countFires testTrA 2 ≤ countFires testTrA 4 := countFires_mono (by decide)
example : 0 < countFires testTrA 4 :=
  countFires_pos_of_fires (by decide : (testTrA 1).fires = true) (by decide : 1 < 4)
example : countFires testTrA 1 < countFires testTrA 4 :=
  fires_lt_countFires (by decide : (testTrA 1).fires = true) (by decide : 1 < 4)

-- countFires_congr：A、B 前 4 拍一致 ⇒ 前 4 拍计数一致
example : countFires testTrA 4 = countFires testTrB 4 :=
  countFires_congr (fun t ht => by
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        cases t with
        | zero => rfl
        | succ t =>
          cases t with
          | zero => rfl
          | succ _ => omega)

-- 契约谓词在测试迹 A 上成立（逐拍验证反压条件）
theorem testTrA_stable : Stable testTrA := by
  intro t hv hr
  cases t with
  | zero => rfl                       -- t=0：bits 在 t=1 保持 0xAA
  | succ t =>
    cases t with
    | zero => contradiction           -- t=1：ready = true，前提 hr 矛盾
    | succ t =>
      cases t with
      | zero => contradiction         -- t=2：ready = true
      | succ t =>
        cases t with
        | zero => contradiction       -- t=3：ready = true
        | succ _ => contradiction     -- t≥4：valid = false，前提 hv 矛盾

theorem testTrA_noWithdraw : NoWithdraw testTrA := by
  intro t hv hr
  cases t with
  | zero => rfl                       -- t=0：valid 在 t=1 保持
  | succ t =>
    cases t with
    | zero => contradiction
    | succ t =>
      cases t with
      | zero => contradiction
      | succ t =>
        cases t with
        | zero => contradiction
        | succ _ => contradiction

theorem testTrA_irrevocable : Irrevocable testTrA :=
  irrevocable_of testTrA_stable testTrA_noWithdraw

example : Stable testTrA ∧ NoWithdraw testTrA :=
  irrevocable_and_stable_noWithdraw.mp testTrA_irrevocable
example : Stable testTrA := testTrA_irrevocable.stable
example : NoWithdraw testTrA := testTrA_irrevocable.noWithdraw
example : ∀ t, (testTrA t).valid = true → (testTrA t).ready = false →
    (testTrA (t + 1)).valid = true ∧ (testTrA (t + 1)).bits = (testTrA t).bits :=
  irrevocable_iff.mp testTrA_irrevocable

-- vacuous / 蕴含式 Irrevocable 构造
example : Irrevocable (Trace.constFiring (0x11 : Bits 8)) :=
  irrevocable_of_alwaysReady (fun _ => rfl)
example : Irrevocable (Trace.idle (0x11 : Bits 8) true) :=
  irrevocable_of_neverValid (fun _ => rfl)
example : Irrevocable (Trace.constFiring (0x11 : Bits 8)) :=
  irrevocable_of_valid_imp_ready (fun _ _ => rfl)
example : Irrevocable (Trace.const (⟨false, false, 0x42⟩ : Obs (Bits 8))) :=
  irrevocable_const _
example : Irrevocable (Trace.idle (0x42 : Bits 8) false) := irrevocable_idle _ _
example : Irrevocable (Trace.constFiring (0x42 : Bits 8)) := irrevocable_constFiring _

-- 迹变换取值：shift / append / map / const / idle / constFiring
example : testTrA.shift 2 0 = (⟨false, true, 0x00⟩ : Obs (Bits 8)) := rfl
example : testTrA.shift 2 1 = (⟨true, true, 0x55⟩ : Obs (Bits 8)) := rfl
example : Stable (testTrA.shift 1) := stable_shift testTrA_stable 1
example : NoWithdraw (testTrA.shift 2) := noWithdraw_shift testTrA_noWithdraw 2
example : Irrevocable (testTrA.shift 3) := irrevocable_shift testTrA_irrevocable 3
example : Trace.const (⟨true, false, 0x42⟩ : Obs (Bits 8)) 7 = ⟨true, false, 0x42⟩ := rfl
example : Trace.idle (0x42 : Bits 8) true 3 = (⟨false, true, 0x42⟩ : Obs (Bits 8)) := rfl
example : Trace.constFiring (0x42 : Bits 8) 9 = (⟨true, true, 0x42⟩ : Obs (Bits 8)) := rfl

-- map：bits 变换、握手信号与计数不变
example : (testTrA.map (· + 1) 1).bits = 0xAB := by decide
example : (testTrA.map (· + 1) 3).bits = 0x56 := by decide
example : (testTrA.map (· + 1) 1).fires = (testTrA 1).fires := by decide
example : countFires (testTrA.map (· + 1)) 5 = countFires testTrA 5 := by decide
example : Stable (testTrA.map (· + 1)) := stable_map _ testTrA_stable
example : NoWithdraw (testTrA.map (· + 1)) := noWithdraw_map _ testTrA_noWithdraw
example : Irrevocable (testTrA.map (· + 1)) := irrevocable_map _ testTrA_irrevocable

-- append：分段取值、计数分段可加、契约保持
example : Trace.append 2 testTrA (Trace.constFiring 0xFF) 1 = testTrA 1 := rfl
example : Trace.append 2 testTrA (Trace.constFiring 0xFF) 2 =
    (⟨true, true, 0xFF⟩ : Obs (Bits 8)) := rfl
example : Trace.append 2 testTrA (Trace.constFiring 0xFF) 4 =
    (⟨true, true, 0xFF⟩ : Obs (Bits 8)) := rfl
example : Trace.append 2 testTrA (Trace.constFiring 0xFF) 1 = testTrA 1 :=
  Trace.append_apply_of_lt (by decide)
example : Trace.append 2 testTrA (Trace.constFiring 0xFF) 3 =
    (⟨true, true, 0xFF⟩ : Obs (Bits 8)) :=
  Trace.append_apply_of_le (by decide)
example : countFires testTrA (2 + 2) = countFires testTrA 2 + countFires (testTrA.shift 2) 2 :=
  countFires_add testTrA 2 2
example : countFires (Trace.append 2 testTrA (Trace.constFiring (0xFF : Bits 8))) (2 + 3) =
    countFires testTrA 2 + countFires (Trace.constFiring (0xFF : Bits 8)) 3 :=
  countFires_append 3
example : countFires (Trace.append 2 testTrA (Trace.constFiring (0xFF : Bits 8))) 5 = 4 :=
  by decide
example : Irrevocable (Trace.append 2 (Trace.constFiring (0x11 : Bits 8))
    (Trace.constFiring 0x11)) :=
  irrevocable_append (irrevocable_constFiring _) (irrevocable_constFiring _)
    (fun _ _ => ⟨rfl, rfl⟩)
example : Irrevocable (Trace.append 4 testTrA (Trace.constFiring 0x55)) :=
  irrevocable_append testTrA_irrevocable (irrevocable_constFiring _) (fun _ _ => ⟨rfl, rfl⟩)

-- 常量迹计数
example : countFires (Trace.const (⟨true, true, 0x42⟩ : Obs (Bits 8))) 5 = 5 := by decide
example : countFires (Trace.const (⟨true, false, 0x42⟩ : Obs (Bits 8))) 5 = 0 := by decide
example : countFires (Trace.const (⟨true, false, 0x42⟩ : Obs (Bits 8))) 3 =
    (if (⟨true, false, 0x42⟩ : Obs (Bits 8)).fires then 3 else 0) := countFires_const _ _
example : countFires (Trace.idle (0x42 : Bits 8) true) 7 = 0 := by decide
example : countFires (Trace.constFiring (0x42 : Bits 8)) 7 = 7 := by decide
example : countValid (Trace.constFiring (0x42 : Bits 8)) 7 = 7 := by decide

-- 假设-保证组合定理的具体实例
example : (testTrA 1).valid = true ∧ (testTrA 1).bits = (testTrA 0).bits :=
  irrevocable_stable_until testTrA_irrevocable (by decide : 0 ≤ 1) rfl
    (fun u _ hut => by cases u with | zero => rfl | succ _ => omega)
example : (testTrA 1).bits = (testTrA 0).bits :=
  irrevocable_bits_at_fire testTrA_irrevocable (by decide : 0 ≤ 1) rfl
    (fun u _ hut => by cases u with | zero => rfl | succ _ => omega) (by decide)
example : ((Trace.constFiring (0x42 : Bits 8)) 3).fires =
    ((Trace.constFiring (0x42 : Bits 8)) 3).valid :=
  fires_of_alwaysReady (fun _ => rfl) 3
example : countFires (Trace.constFiring (0x42 : Bits 8)) 6 =
    countValid (Trace.constFiring (0x42 : Bits 8)) 6 :=
  countFires_eq_countValid (fun _ => rfl) 6
example : countFires (Trace.idle (0x42 : Bits 8) true) 6 = 0 :=
  countFires_eq_zero_of_neverValid (fun _ => rfl) 6

end HandshakeRegressionTests

end Handshake
end Ventus.Base
