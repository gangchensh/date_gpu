/- ========================================================================= -/
/-                      BvInduction.lean                                     -/
/-  doc/32 P0：参数化位级基础设施（对位宽/长度归纳的引理库 + 归纳书写惯例）   -/
/-                                                                           -/
/-  定位：浮点运算器"参数化 + 归纳法"新路线（doc/32）的 P0 波次。本文件全部    -/
/-  定理对位宽 w（或格式参数 s）全量化，全部用归纳/符号证明，**零 bv_decide、  -/
/-  零 native_decide**——本文件的存在性证明目标就是"无 SAT 路线可行"。          -/
/-  唯二允许的自动化：omega（Presburger 线性算术，内核可证）与 decide          -/
/-  （内核归约，仅用于 §5 数值回归）。                                        -/
/-                                                                           -/
/-  命名纪律：本文件所有定义/定理以 bvi 为前缀（Base 包内防撞名）。            -/
/-                                                                           -/
/-  结构：                                                                    -/
/-    §1 Nat 幂（2^k）工具族——omega 不理解变量指数，一切含 2^k 的算术先入      -/
/-       "原子等式"（hs : 2^(k+1) = 2 * 2^k 型）再交 omega。                  -/
/-    §2 参数化位级代数律（BitVec w，w 全量化）：toNat/移位/拼接/截断/掩码/    -/
/-       进位分解/getLsbD 互译/顶位-幅值桥/log2 桥。                          -/
/-    §3 归纳书写模板 T1-T6（每个模板配可工作的示范定理）。                    -/
/-    §4 参数化"位序=幅值序"：N1 的 fcMagLex（f32 定点，VentusF/FpuCmp.lean    -/
/-       :378）对尾数域宽 s 的参数化推广。                                    -/
/-    §5 数值回归（by decide + 定理实例化应用，双形式）。                      -/
/-    §6 公理审计块（#print axioms，应全部仅 [propext, Quot.sound] 等标准公    -/
/-       理，无 sorryAx、无 _native.bv_decide.ax_*、无 ofReduceBool）。        -/
/-    §7 参数化证明书写指南（供 P1/P2 波次简报引用）。                         -/
/-                                                                           -/
/-  本文件零 sorry。                                                          -/
/- ========================================================================= -/

import Ventus.Base.Defs

namespace Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- §1. Nat 幂（2^k）工具族                                                   -/
/-                                                                           -/
/-  惯例（P0 核心纪律）：omega 把 2^k 当不透明原子且**不做乘法单项式推理**。   -/
/-  凡含变量指数的等式/不等式，先用手工重写把指数归一（pow_succ/pow_add），    -/
/-  使目标里 2^k 只以线性系数（0/1/2 倍）出现，再交 omega。                   -/
/- ========================================================================= -/

/-- 2 的幂恒正 -/
theorem bviPow2pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

/-- 幂单调（≤） -/
theorem bviPow2le {m k : Nat} (h : m ≤ k) : 2 ^ m ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

/-- 幂严格单调 -/
theorem bviPow2lt {m k : Nat} (h : m < k) : 2 ^ m < 2 ^ k :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) h

/-- 后继展开：2^(k+1) = 2·2^k（原子等式的标准件，写 `have hs := bviPow2succ k`
    后 rw 或供 omega 引用） -/
theorem bviPow2succ (k : Nat) : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- 加法定理：2^(m+k) = 2^m·2^k -/
theorem bviPow2add (m k : Nat) : (2 : Nat) ^ (m + k) = 2 ^ m * 2 ^ k := Nat.pow_add 2 m k

/- ========================================================================= -/
/- §2. 参数化位级代数律（BitVec w，w 全量化）                                 -/
/-                                                                           -/
/-  4.31 核心库事实备忘（探针核实，/tmp/bvi_probe*.lean）：                    -/
/-  - BitVec.getLsbD x i 展开为**裸** x.toNat.testBit i（无宽度守卫；          -/
/-    i ≥ w 时由 toNat < 2^w 保证 testBit = false）。                          -/
/-  - BitVec.msb_eq_decide : x.msb = decide (2^(w-1) ≤ x.toNat)。              -/
/-  - BitVec.toNat_append 是 <<< n ||| 形；数值形用                              -/
/-    Nat.shiftLeft_add_eq_or_of_lt + Nat.shiftLeft_eq 归一。                  -/
/- ========================================================================= -/

/-- 值域 -/
theorem bviIsLt {w : Nat} (x : BitVec w) : x.toNat < 2 ^ w := x.isLt

/-- 拼接的数值语义：(x ++ y).toNat = x.toNat · 2^n + y.toNat -/
theorem bviToNat_append {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- 左移（一般形，带回绕）：(x <<< k).toNat = (x.toNat · 2^k) % 2^w -/
theorem bviToNat_shiftLeft {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k).toNat = (x.toNat * 2 ^ k) % 2 ^ w := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- 左移（无溢出形）：不越界时模消失——"移位=乘法"的可用形态 -/
theorem bviToNat_shiftLeft_of_lt {w : Nat} (x : BitVec w) (k : Nat)
    (h : x.toNat * 2 ^ k < 2 ^ w) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- 逻辑右移=除法：(x >>> k).toNat = x.toNat / 2^k -/
theorem bviToNat_ushiftRight {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- getLsbD 与"移位取位"互译（核心形）：第 i 位 = (toNat / 2^i) % 2 = 1。
    注意 4.31 的 getLsbD 是裸 testBit（见 §2 头注）。 -/
theorem bviGetLsbD_eq {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = decide (x.toNat / 2 ^ i % 2 = 1) := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]

/-- getLsbD 的 iff 形（建议用法：位断言一律先转此形再进算术） -/
theorem bviGetLsbD_true_iff {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = true ↔ x.toNat / 2 ^ i % 2 = 1 := by
  rw [bviGetLsbD_eq, decide_eq_true_iff]

/-- 右移后取位 = 平移取位（getLsbD 与移位的另一向互译） -/
theorem bviGetLsbD_ushiftRight {w : Nat} (x : BitVec w) (k i : Nat) :
    (x >>> k).getLsbD i = x.getLsbD (k + i) :=
  BitVec.getLsbD_ushiftRight x k i

/-- 低位截取的数值：extractLsb' 0 k = mod 2^k -/
theorem bviExtractLow_toNat {w : Nat} (x : BitVec w) (k : Nat) :
    (x.extractLsb' 0 k).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- 任意截取的数值：extractLsb' s l = (toNat / 2^s) % 2^l -/
theorem bviExtract_toNat {w : Nat} (x : BitVec w) (s l : Nat) :
    (x.extractLsb' s l).toNat = x.toNat / 2 ^ s % 2 ^ l := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- 全 1 掩码的数值 -/
theorem bviAllOnes_toNat (w : Nat) : (BitVec.allOnes w).toNat = 2 ^ w - 1 :=
  BitVec.toNat_allOnes

/-- 全 1 掩码是 and 的单位元 -/
theorem bviAndAllOnes {w : Nat} (x : BitVec w) : x &&& BitVec.allOnes w = x :=
  BitVec.and_allOnes

/-- 低 k 位掩码（k ≤ w）：与 2^k − 1 按位与 = 模 2^k -/
theorem bviAndMaskLow_toNat {w k : Nat} (x : BitVec w) (hk : k ≤ w) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by
      have h1 : 2 ^ k ≤ 2 ^ w := bviPow2le hk
      have h2 : 0 < 2 ^ w := bviPow2pos w
      omega),
    Nat.and_two_pow_sub_one_eq_mod]

/-- 加法的模形式 -/
theorem bviAdd_toNat {w : Nat} (a b : BitVec w) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ w := BitVec.toNat_add a b

/-- 加法进位分解：真实和 = 回绕结果 + 进位·2^w。
    这是"硬件加法 = 数学加法 mod 2^w"的精确化，参数化证明中替代 bv_decide
    处理进位的标准形。 -/
theorem bviAdd_decomp {w : Nat} (a b : BitVec w) :
    a.toNat + b.toNat =
      (a + b).toNat + (if a.toNat + b.toNat < 2 ^ w then 0 else 2 ^ w) := by
  rw [BitVec.toNat_add]
  by_cases h : a.toNat + b.toNat < 2 ^ w
  · rw [if_pos h, Nat.mod_eq_of_lt h, Nat.add_zero]
  · rw [if_neg h]
    have hge : 2 ^ w ≤ a.toNat + b.toNat := by omega
    have hlt : a.toNat + b.toNat < 2 * 2 ^ w := by
      have h1 := a.isLt
      have h2 := b.isLt
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

/-- 减法的分情形数值形 -/
theorem bviSub_toNat {w : Nat} (a b : BitVec w) :
    (a - b).toNat =
      if b.toNat ≤ a.toNat then a.toNat - b.toNat else a.toNat + 2 ^ w - b.toNat := by
  rw [BitVec.toNat_sub]
  by_cases h : b.toNat ≤ a.toNat
  · rw [if_pos h]
    have h1 : 2 ^ w - b.toNat + a.toNat = 2 ^ w + (a.toNat - b.toNat) := by
      have h2 := b.isLt
      omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  · rw [if_neg h]
    rw [Nat.mod_eq_of_lt (by
      have ha := a.isLt
      have hb := b.isLt
      omega)]
    omega

/-- 范围内字面值的 toNat -/
theorem bviOfNat_toNat_of_lt {w : Nat} (v : Nat) (h : v < 2 ^ w) :
    (BitVec.ofNat w v).toNat = v :=
  (BitVec.toNat_ofNat v w).trans (Nat.mod_eq_of_lt h)

/-- ofNat 往返：toNat 后再 ofNat 复原（w 不变时 setWidth 恒等） -/
theorem bviOfNat_toNat_roundtrip {w : Nat} (x : BitVec w) :
    BitVec.ofNat w x.toNat = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- 【顶位分解桥】BitVec (w+1) = 顶位·2^w + 低 w 位。
    "对位宽归纳"的标准分解：BitVec 的宽度在类型里，w 变化时类型不互通，
    归纳步必须把 BitVec (w+1) 拆回 BitVec w——本引理就是那座桥。 -/
theorem bviTopBit_toNat {w : Nat} (x : BitVec (w + 1)) :
    x.toNat = (x.getLsbD w).toNat * 2 ^ w + (x.extractLsb' 0 w).toNat := by
  have hdec := Nat.div_add_mod x.toNat (2 ^ w)
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have hbit : (x.getLsbD w).toNat = x.toNat / 2 ^ w := by
    rw [bviGetLsbD_eq]
    have hq2 : x.toNat / 2 ^ w < 2 := by
      rw [Nat.div_lt_iff_lt_mul (bviPow2pos w)]
      have hlt := x.isLt
      rw [bviPow2succ w] at hlt
      exact hlt
    have hB := bviPow2pos w
    have hq : x.toNat / 2 ^ w = 0 ∨ x.toNat / 2 ^ w = 1 := by
      -- omega 对变量除数的 div/mod 不给 div_add_mod 关联（d 可能被判负）——
      -- 用 eq_zero_or_pos 拆出非负性再交 omega（doc/02：变量除数坑）
      rcases Nat.eq_zero_or_pos (x.toNat / 2 ^ w) with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    rcases hq with h0 | h0 <;> rw [h0] <;> decide
  rw [hbit, Nat.mul_comm]
  exact hdec.symm

/-- 顶位分解桥的 msb 形 -/
theorem bviMsb_toNat {w : Nat} (x : BitVec (w + 1)) :
    x.toNat = x.msb.toNat * 2 ^ w + (x.extractLsb' 0 w).toNat := by
  rw [BitVec.msb_eq_getLsbD_last]
  exact bviTopBit_toNat x

/-- 顶位置位 ⟹ 值 ∈ [2^w, 2^(w+1))（CLZ/LZA 幅值界的基本桥） -/
theorem bviMsb_true_ge {w : Nat} (x : BitVec (w + 1)) (h : x.msb = true) :
    2 ^ w ≤ x.toNat := by
  rw [BitVec.msb_eq_decide] at h
  exact of_decide_eq_true h

/-- 顶位清零 ⟹ 值 < 2^w -/
theorem bviMsb_false_lt {w : Nat} (x : BitVec (w + 1)) (h : x.msb = false) :
    x.toNat < 2 ^ w := by
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not] at h
  exact Nat.lt_of_not_ge h

/-- 幅值区间 ⟹ 指定位必置位（任意位置 p 的版本，供 LZA off-by-one 类证明） -/
theorem bviGetLsbD_true_of_range {w p : Nat} (x : BitVec w)
    (h1 : 2 ^ p ≤ x.toNat) (h2 : x.toNat < 2 ^ (p + 1)) :
    x.getLsbD p = true := by
  rw [bviGetLsbD_true_iff]
  have hq1 : 1 ≤ x.toNat / 2 ^ p := (Nat.one_le_div_iff (bviPow2pos p)).mpr h1
  have hq2 : x.toNat / 2 ^ p < 2 := by
    rw [Nat.div_lt_iff_lt_mul (bviPow2pos p)]
    have hs := bviPow2succ p
    rw [hs] at h2
    exact h2
  omega

/-- 拆合互逆：高位段 ++ 低位段 = 原向量（拼接/截断的往返律） -/
theorem bviAppend_extract {n m : Nat} (x : BitVec (n + m)) :
    (x.extractLsb' m n) ++ (x.extractLsb' 0 m) = x := by
  apply BitVec.toNat_inj.mp
  rw [bviToNat_append, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat < 2 ^ (n + m) := x.isLt
  rw [bviPow2add n m] at hlt
  have hq : x.toNat / 2 ^ m < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (bviPow2pos m)]
    exact hlt
  rw [Nat.mod_eq_of_lt hq, Nat.mul_comm]
  exact Nat.div_add_mod x.toNat (2 ^ m)

/-- log2 双边界（核心库引理的捆绑形） -/
theorem bviLog2_bounds {v : Nat} (hv : v ≠ 0) :
    2 ^ v.log2 ≤ v ∧ v < 2 ^ (v.log2 + 1) :=
  ⟨Nat.log2_self_le hv, Nat.lt_log2_self⟩

/-- 幅值区间 ⟺ log2 定值：2^p ≤ v < 2^(p+1) ⟹ log2 v = p。
    LZA off-by-one 界（2^(p-1) ≤ sigRaw < 2^(p+1) 形）的 Nat 侧落点。 -/
theorem bviLog2_eq {v p : Nat} (hv : v ≠ 0) (h1 : 2 ^ p ≤ v) (h2 : v < 2 ^ (p + 1)) :
    v.log2 = p :=
  (Nat.log2_eq_iff hv).mpr ⟨h1, h2⟩

/- ========================================================================= -/
/- §3. 归纳书写模板（每个模板配一个可工作的示范定理）                          -/
/-                                                                           -/
/-  T1 对 Nat 归纳 + generalizing（累加器参数必须泛化，否则 ih 把参数钉死）    -/
/-  T2 List.foldl 不变式（归纳表与累加器同时泛化）                             -/
/-  T3 Fin n 包装器：转 Nat+界 / 外延 / Fin.induction 消除器                   -/
/-  T4 强归纳 Nat.strongRecOn（term 式 refine + 显式 motive，绕开 case 命名    -/
/-     不确定性与 motive 推断坑）                                              -/
/-  T5 fun_induction（递归 def 按方程分裂）                                    -/
/-  T6 对位宽 w 归纳（经 bviTopBit_toNat 分解桥；归纳会 auto-revert 依赖       -/
/-     假设——BitVec w 的 x 依赖 w，ih 自动获得 ∀ x 形）                        -/
/- ========================================================================= -/

/-- T1 载体：尾递归累加 -/
def bviSumTo : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => bviSumTo n (acc + (n + 1))

/-- 【模板 T1 示范】对 n 归纳、`generalizing acc`。
    反模式：漏写 generalizing 时 ih 形如"对当前 acc 成立"，归纳步的
    acc + (n+1) 无处安放——这是参数化证明里最高频的 motive 事故。 -/
theorem bviSumTo_eq (n acc : Nat) : 2 * bviSumTo n acc = 2 * acc + n * (n + 1) := by
  induction n generalizing acc with
  | zero => simp only [bviSumTo]; omega
  | succ n ih =>
    simp only [bviSumTo]
    rw [ih (acc + (n + 1)), Nat.mul_add]
    -- 目标：2*acc + 2*(n+1) + n*(n+1) = 2*acc + (n+1)*(n+1+1)
    -- 乘法单项式 omega 不做，手工分配律装配（doc/02：omega 线性纪律）
    rw [show (n + 1) * (n + 1 + 1) = 2 * (n + 1) + n * (n + 1) from by
      rw [show n + 1 + 1 = 2 + n from by omega, ← Nat.add_mul]
      exact Nat.mul_comm _ _, Nat.add_assoc]

/-- 【模板 T2 示范】List.foldl 的加法不变式：归纳表 l 与累加器 acc 同泛化。
    foldl 不变式的书写惯例：不变式必须以"任意 acc"量化（acc 每步变化）。 -/
theorem bviFoldl_add (l : List Nat) (acc : Nat) :
    l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]
    omega

/-- 【模板 T3a】Fin n 全称的 Nat 化包装器：∀ i : Fin n 的证明一律先转
    ∀ v < n 的 Nat 命题（omega 可用、无 Fin 运算阻碍）。 -/
theorem bviFin_forall_iff {n : Nat} (P : Fin n → Prop) :
    (∀ i : Fin n, P i) ↔ ∀ (v : Nat) (h : v < n), P ⟨v, h⟩ := by
  constructor
  · intro h v hv
    exact h ⟨v, hv⟩
  · intro h i
    exact h i.val i.isLt

/-- 【模板 T3b】Fin 函数外延：逐点（Nat 值）相等 ⟹ 函数相等 -/
theorem bviFin_ext {n : Nat} {α : Type} (f g : Fin n → α)
    (h : ∀ (v : Nat) (hv : v < n), f ⟨v, hv⟩ = g ⟨v, hv⟩) : f = g := by
  funext i
  exact h i.val i.isLt

/-- T3b 使用示范：索引重建恒等 -/
theorem bviFin_ext_demo {n : Nat} (f : Fin n → Nat) :
    f = fun i => f ⟨i.val, i.isLt⟩ := by
  apply bviFin_ext
  intro v hv
  rfl

/-- 【模板 T3c】Fin (n+1) 的 0/succ 情形分析——term 式 Fin.induction
    （显式 motive；induction ... using 的 case 名随版本漂移，term 式最稳） -/
theorem bviFin_zero_or_succ {n : Nat} (i : Fin (n + 1)) :
    i = 0 ∨ ∃ j : Fin n, i = j.succ := by
  refine Fin.induction (motive := fun i => i = 0 ∨ ∃ j : Fin n, i = j.succ) ?_ ?_ i
  · exact Or.inl rfl
  · intro j _ih
    exact Or.inr ⟨j, rfl⟩

/-- 【模板 T4 示范】强归纳（Nat.strongRecOn，term 式 + 显式 motive）：
    任意非零自然数有 2-adic 分解 n = 2^k · m（m 奇）。
    （CLZ/LZA 与"log2 域"证明的基本工具；同时示范强归纳的标准写法。） -/
theorem bviExists_twoPow_mul_odd {n : Nat} (hn : n ≠ 0) :
    ∃ k m : Nat, n = 2 ^ k * m ∧ m % 2 = 1 := by
  refine Nat.strongRecOn
    (motive := fun n => n ≠ 0 → ∃ k m : Nat, n = 2 ^ k * m ∧ m % 2 = 1)
    n (fun n ih => ?_) hn
  intro hn
  by_cases hodd : n % 2 = 1
  · exact ⟨0, n, by simp, hodd⟩
  · have hn2 : n % 2 = 0 := by omega
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hhalf : n / 2 < n := Nat.div_lt_self hpos (by decide)
    have hdm := Nat.div_add_mod n 2
    rw [hn2, Nat.add_zero] at hdm
    have hne2 : n / 2 ≠ 0 := by
      intro hz
      rw [hz, Nat.mul_zero] at hdm
      exact hn hdm.symm
    obtain ⟨k, m, hk, hm⟩ := ih (n / 2) hhalf hne2
    refine ⟨k + 1, m, ?_, hm⟩
    rw [hk] at hdm
    -- hdm : 2 * (2^k * m) = n；目标 n = 2^(k+1) * m
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    exact hdm.symm

/-- T5 载体：列表中 true 的个数 -/
def bviCountOnes : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + bviCountOnes bs

/-- 【模板 T5 示范】fun_induction：按递归定义的方程分裂目标，
    归纳假设自动对应递归调用点。 -/
theorem bviCountOnes_le (l : List Bool) : bviCountOnes l ≤ l.length := by
  fun_induction bviCountOnes l with
  | case1 => decide
  | case2 b bs ih =>
    -- fun_induction 已在分支目标里展开 bviCountOnes（勿再 simp only 之）
    cases b
    · simp only [List.length_cons]
      have hz : (false : Bool).toNat = 0 := rfl
      omega
    · simp only [List.length_cons]
      have ho : (true : Bool).toNat = 1 := rfl
      omega

/-- 【模板 T6 示范】对位宽 w 归纳：重证 isLt（示范性质——模式本身是真产物）。
    要点：(a) x : BitVec w 依赖 w，induction w 会自动 revert 并泛化 x，
    ih 得 ∀ 形；(b) 归纳步经 bviTopBit_toNat 把 BitVec (w+1) 拆为
    顶位（Bool，cases 消元）+ 低 w 位（ih 适用）；(c) Bool.toNat 归约后
    目标线性，omega 收口。 -/
theorem bviToNat_lt_indDemo (w : Nat) (x : BitVec w) : x.toNat < 2 ^ w := by
  induction w with
  | zero => exact x.isLt
  | succ w ih =>
    rw [bviTopBit_toNat, bviPow2succ w]
    have hlo : (x.extractLsb' 0 w).toNat < 2 ^ w := ih _
    have hB := bviPow2pos w
    cases hb : x.getLsbD w
    · -- cases 已把目标里的 getLsbD 替换为字面 Bool（勿再 rw [hb]）
      show 0 * 2 ^ w + (x.extractLsb' 0 w).toNat < 2 * 2 ^ w
      omega
    · show 1 * 2 ^ w + (x.extractLsb' 0 w).toNat < 2 * 2 ^ w
      omega

/- ========================================================================= -/
/- §4. 参数化"位序=幅值序"（fcMagLex 的 s 参数化推广）                        -/
/-                                                                           -/
/-  来源：VentusF/FpuCmp.lean 的 fcMagOf/fcMagLex/fcMagLexConv/fcMagOf_inj     -/
/-  （N1，f32 定点：s = 23 写死）。此处把尾数域宽 s 提为参数——证明逐行同构，  -/
/-  仅把 2^23/2^24 换成 2^s/2^(s+1)（2^(s+1) = 2·2^s 由 bviPow2succ 提供）。   -/
/-  语义：位型 (s,e,f) 对应的缩放幅值；真实值 = bviMagOf s e f · 2^(emin−s)。  -/
/-  e = 0：次正规/零（无隐藏位）；e ≥ 1：正规格化/inf（隐藏位 2^s）。          -/
/-  inf（e = 全 1, f = 0）自然落入本框架，无需特判。                          -/
/- ========================================================================= -/

/-- 参数化缩放幅值 -/
def bviMagOf (s e f : Nat) : Nat := if e = 0 then f else (2 ^ s + f) * 2 ^ (e - 1)

/-- e = 0 展开（避免多处 if_pos/if_neg 脆弱重写——N1 惯例沿用） -/
theorem bviMagOf_zero (s f : Nat) : bviMagOf s 0 f = f := by
  rw [bviMagOf, if_pos rfl]

/-- e ≠ 0 展开 -/
theorem bviMagOf_pos (s : Nat) {e : Nat} (h : e ≠ 0) (f : Nat) :
    bviMagOf s e f = (2 ^ s + f) * 2 ^ (e - 1) := by
  rw [bviMagOf, if_neg h]

/-- 【主引理】字典序 ⟹ 幅值序（IEEE 同号位序 = 数值序的核心，任意格式参数 s） -/
theorem bviMagLex {s ea fa eb fb : Nat} (ha : fa < 2 ^ s) (hb : fb < 2 ^ s) :
    ea < eb ∨ (ea = eb ∧ fa < fb) → bviMagOf s ea fa < bviMagOf s eb fb := by
  intro hlex
  rcases hlex with h | ⟨he, hf⟩
  · rcases Nat.eq_zero_or_pos ea with h0 | hpos
    · subst h0
      rw [bviMagOf_zero, bviMagOf_pos s (by omega : eb ≠ 0)]
      calc fa < 2 ^ s := ha
        _ = 2 ^ s * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ s * 2 ^ (eb - 1) :=
          Nat.mul_le_mul (Nat.le_refl _) (Nat.one_le_pow _ _ (by decide))
        _ ≤ (2 ^ s + fb) * 2 ^ (eb - 1) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_refl _)
    · rw [bviMagOf_pos s (by omega : ea ≠ 0), bviMagOf_pos s (by omega : eb ≠ 0)]
      have h3 : (2 : Nat) ^ (s + 1) * 2 ^ (ea - 1) = 2 ^ s * 2 ^ ea := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      have hB : 0 < 2 ^ (s + 1) := bviPow2pos _
      calc (2 ^ s + fa) * 2 ^ (ea - 1) ≤ (2 ^ (s + 1) - 1) * 2 ^ (ea - 1) :=
            Nat.mul_le_mul (by
              have hs1 := bviPow2succ s
              omega) (Nat.le_refl _)
        _ < 2 ^ (s + 1) * 2 ^ (ea - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (bviPow2pos _)
        _ = 2 ^ s * 2 ^ ea := h3
        _ ≤ 2 ^ s * 2 ^ (eb - 1) :=
          Nat.mul_le_mul (Nat.le_refl _) (bviPow2le (by omega))
        _ ≤ (2 ^ s + fb) * 2 ^ (eb - 1) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_refl _)
  · subst ea
    by_cases h0 : eb = 0
    · subst h0
      rw [bviMagOf_zero, bviMagOf_zero]
      exact hf
    · rw [bviMagOf_pos s h0, bviMagOf_pos s h0]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (bviPow2pos _)

/-- 幅值序 ⟹ 字典序（bviMagLex 的反向） -/
theorem bviMagLexConv {s ea fa eb fb : Nat} (ha : fa < 2 ^ s) (hb : fb < 2 ^ s)
    (h : bviMagOf s ea fa < bviMagOf s eb fb) :
    ea < eb ∨ (ea = eb ∧ fa < fb) := by
  have htri : ea < eb ∨ ea = eb ∨ eb < ea := by omega
  rcases htri with h1 | h1 | h1
  · exact Or.inl h1
  · subst ea
    by_cases h0 : eb = 0
    · subst h0
      rw [bviMagOf_zero, bviMagOf_zero] at h
      exact Or.inr ⟨rfl, h⟩
    · rw [bviMagOf_pos s h0, bviMagOf_pos s h0] at h
      have h2 := (Nat.mul_lt_mul_right (bviPow2pos (eb - 1))).mp h
      exact Or.inr ⟨rfl, by omega⟩
  · exact absurd h (Nat.lt_asymm (bviMagLex hb ha (Or.inl h1)))

/-- 位序 ⟺ 幅值序（合并且最便于 rw 的形式） -/
theorem bviMagLex_iff {s ea fa eb fb : Nat} (ha : fa < 2 ^ s) (hb : fb < 2 ^ s) :
    bviMagOf s ea fa < bviMagOf s eb fb ↔ ea < eb ∨ (ea = eb ∧ fa < fb) :=
  ⟨bviMagLexConv ha hb, bviMagLex ha hb⟩

/-- 幅值单射（同号位型的数值相等 ⟺ 位相等的关键） -/
theorem bviMagOf_inj {s ea fa eb fb : Nat} (ha : fa < 2 ^ s) (hb : fb < 2 ^ s)
    (h : bviMagOf s ea fa = bviMagOf s eb fb) : ea = eb ∧ fa = fb := by
  have key : ea = eb := by
    have htri : ea < eb ∨ ea = eb ∨ eb < ea := by omega
    rcases htri with h1 | h1 | h1
    · exact absurd h (Nat.ne_of_lt (bviMagLex ha hb (Or.inl h1)))
    · exact h1
    · exact absurd h.symm (Nat.ne_of_lt (bviMagLex hb ha (Or.inl h1)))
  subst ea
  by_cases h0 : eb = 0
  · subst h0
    rw [bviMagOf_zero, bviMagOf_zero] at h
    exact ⟨rfl, h⟩
  · rw [bviMagOf_pos s h0, bviMagOf_pos s h0] at h
    have h2 := Nat.mul_right_cancel (bviPow2pos (eb - 1)) h
    exact ⟨rfl, by omega⟩

/- ========================================================================= -/
/- §5. 数值回归测试（by decide + 定理实例化双形式；验证引理可用性）            -/
/- ========================================================================= -/

section BviRegression

-- 幂工具
example : (2 : Nat) ^ 10 = 1024 := by decide
example : (2 : Nat) ^ (3 + 4) = 2 ^ 3 * 2 ^ 4 := bviPow2add 3 4

-- 拼接 toNat
example : (0xA#4 ++ 0x5#4).toNat = 0xA5 := by decide
example : ((0xAB : BitVec 8) ++ (0xCD : BitVec 8)).toNat =
    (0xAB : BitVec 8).toNat * 2 ^ 8 + (0xCD : BitVec 8).toNat := bviToNat_append _ _

-- 移位
example : ((0x0F#8) <<< 4).toNat = (0x0F#8).toNat * 2 ^ 4 :=
  bviToNat_shiftLeft_of_lt _ _ (by decide)
example : ((0xFF#8) <<< 4).toNat = ((0xFF#8).toNat * 2 ^ 4) % 2 ^ 8 :=
  bviToNat_shiftLeft _ _
example : ((0xFF#8) <<< 4).toNat = 0xF0 := by decide
example : ((0xA5#8) >>> 3).toNat = (0xA5#8).toNat / 2 ^ 3 := bviToNat_ushiftRight _ _
example : ((0xA5#8) >>> 3).toNat = 20 := by decide

-- getLsbD 互译（含越界位——4.31 裸 testBit 语义）
example : (0xA5#8).getLsbD 0 = true := by decide
example : (0xA5#8).getLsbD 1 = false := by decide
example : (0xA5#8).getLsbD 8 = false := by decide
example : (0xA5#8).getLsbD 5 = decide ((0xA5#8).toNat / 2 ^ 5 % 2 = 1) :=
  bviGetLsbD_eq _ _
example : ((0xA5#8) >>> 3).getLsbD 2 = (0xA5#8).getLsbD (3 + 2) :=
  bviGetLsbD_ushiftRight _ _ _

-- 截取
example : ((0xABCD : BitVec 16).extractLsb' 0 8).toNat = 0xCD := by decide
example : ((0xABCD : BitVec 16).extractLsb' 0 8).toNat = (0xABCD : BitVec 16).toNat % 2 ^ 8 :=
  bviExtractLow_toNat _ _
example : ((0xABCD : BitVec 16).extractLsb' 4 8).toNat =
    (0xABCD : BitVec 16).toNat / 2 ^ 4 % 2 ^ 8 := bviExtract_toNat _ _ _

-- 掩码
example : (0xA5#8 &&& BitVec.allOnes 8) = 0xA5#8 := bviAndAllOnes _
example : (BitVec.allOnes 8).toNat = 2 ^ 8 - 1 := bviAllOnes_toNat 8
example : ((0xA5#8) &&& BitVec.ofNat 8 (2 ^ 3 - 1)).toNat = (0xA5#8).toNat % 2 ^ 3 :=
  bviAndMaskLow_toNat _ (by decide)
example : ((0xA5#8) &&& BitVec.ofNat 8 (2 ^ 3 - 1)).toNat = 5 := by decide

-- 加法进位分解（含回绕与不回绕两形）
example : (0xFF#8).toNat + (1#8).toNat =
    ((0xFF#8) + (1#8)).toNat +
      (if (0xFF#8).toNat + (1#8).toNat < 2 ^ 8 then 0 else 2 ^ 8) := bviAdd_decomp _ _
example : (0xFF#8).toNat + (1#8).toNat = ((0xFF#8) + (1#8)).toNat + 2 ^ 8 := by decide
example : (0x10#8).toNat + (0x20#8).toNat = ((0x10#8) + (0x20#8)).toNat := by decide

-- 减法分情形
example : ((0x05#8) - (0x03#8)).toNat = 2 := by decide
example : ((0x03#8) - (0x05#8)).toNat = 254 := by decide
example : ((0x03#8) - (0x05#8)).toNat =
    (if (5#8).toNat ≤ (3#8).toNat then (3#8).toNat - (5#8).toNat
     else (3#8).toNat + 2 ^ 8 - (5#8).toNat) := bviSub_toNat _ _

-- ofNat 往返
example : (BitVec.ofNat 8 300).toNat = 44 := by decide
example : (BitVec.ofNat 8 200).toNat = 200 := bviOfNat_toNat_of_lt _ (by decide)
example : BitVec.ofNat 8 (0xA5#8).toNat = 0xA5#8 := bviOfNat_toNat_roundtrip _

-- 顶位分解桥与幅值界
example : (0xA5#8).toNat =
    ((0xA5#8).getLsbD 7).toNat * 2 ^ 7 + ((0xA5#8).extractLsb' 0 7).toNat :=
  bviTopBit_toNat _
example : (0xA5#8).toNat =
    (0xA5#8).msb.toNat * 2 ^ 7 + ((0xA5#8).extractLsb' 0 7).toNat := bviMsb_toNat _
example : 2 ^ 7 ≤ (0xA5#8).toNat := bviMsb_true_ge _ (by decide)
example : (0x75#8).toNat < 2 ^ 7 := bviMsb_false_lt _ (by decide)
example : (0x25#8).getLsbD 5 = true :=
  bviGetLsbD_true_of_range _ (by decide) (by decide)

-- 拆合互逆
example : (0xA5#8).extractLsb' 4 4 ++ (0xA5#8).extractLsb' 0 4 = 0xA5#8 :=
  bviAppend_extract _

-- log2 桥
example : (165 : Nat).log2 = 7 := by decide
example : (200 : Nat).log2 = 7 := bviLog2_eq (by decide) (by decide) (by decide)

-- T1 示范：尾递归累加
example : bviSumTo 10 0 = 55 := by decide
example : 2 * bviSumTo 10 0 = 2 * 0 + 10 * (10 + 1) := bviSumTo_eq 10 0
example : 2 * bviSumTo 4 3 = 2 * 3 + 4 * 5 := by decide

-- T2 示范：foldl 不变式
example : [1, 2, 3, 4].foldl (· + ·) 0 = 10 := by decide
example : [1, 2, 3, 4].foldl (· + ·) 0 = 0 + [1, 2, 3, 4].sum := bviFoldl_add _ _

-- T3 示范：Fin 包装器
example : (∀ i : Fin 4, i.val < 4) ↔ ∀ (v : Nat) (h : v < 4), (⟨v, h⟩ : Fin 4).val < 4 :=
  bviFin_forall_iff _
example : (2 : Fin 4) = 0 ∨ ∃ j : Fin 3, (2 : Fin 4) = j.succ := bviFin_zero_or_succ 2

-- T4 示范：2-adic 分解
example : ∃ k m : Nat, 12 = 2 ^ k * m ∧ m % 2 = 1 :=
  bviExists_twoPow_mul_odd (by decide)
example : ∃ k m : Nat, 12 = 2 ^ k * m ∧ m % 2 = 1 := ⟨2, 3, by decide, by decide⟩

-- T5 示范：fun_induction
example : bviCountOnes [true, false, true] = 2 := by decide
example : bviCountOnes [true, false, true] ≤ [true, false, true].length :=
  bviCountOnes_le _

-- T6 示范：位宽归纳（实例即 isLt 本身，回归钉死模式可用性）
example : (0xFF : BitVec 8).toNat < 2 ^ 8 := bviToNat_lt_indDemo 8 _

-- 参数化幅值序（s = 3 小格式 + s = 23 的 f32 实例）
example : bviMagOf 23 0 5 = 5 := by decide
example : bviMagOf 23 1 0 = 2 ^ 23 := by decide
example : bviMagOf 3 2 1 = 18 := by decide
example : bviMagOf 3 1 7 < bviMagOf 3 2 0 :=
  bviMagLex (by decide) (by decide) (Or.inl (by decide))
example : bviMagOf 3 2 1 < bviMagOf 3 2 5 :=
  bviMagLex (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩)
example : bviMagOf 23 150 100 < bviMagOf 23 151 0 := by decide
example : bviMagOf 3 2 1 < bviMagOf 3 2 5 ↔ (2 : Nat) < 2 ∨ (2 = 2 ∧ 1 < 5) :=
  bviMagLex_iff (by decide) (by decide)
example (ea fa : Nat) (ha : fa < 2 ^ 3) (h : bviMagOf 3 ea fa = bviMagOf 3 2 5) :
    ea = 2 ∧ fa = 5 := bviMagOf_inj ha (by decide) h

end BviRegression

/- ========================================================================= -/
/- §6. 公理审计块                                                             -/
/-  预期：全部仅 [propext, Quot.sound]（及可能的 Classical.choice）。          -/
/-  出现 sorryAx / _native.bv_decide.ax_* / ofReduceBool 即为判收失败。        -/
/- ========================================================================= -/

section AxiomAudit

#print axioms bviToNat_append
#print axioms bviToNat_shiftLeft_of_lt
#print axioms bviGetLsbD_eq
#print axioms bviAndMaskLow_toNat
#print axioms bviAdd_decomp
#print axioms bviSub_toNat
#print axioms bviTopBit_toNat
#print axioms bviMsb_true_ge
#print axioms bviGetLsbD_true_of_range
#print axioms bviAppend_extract
#print axioms bviLog2_eq
#print axioms bviSumTo_eq
#print axioms bviFoldl_add
#print axioms bviFin_forall_iff
#print axioms bviFin_zero_or_succ
#print axioms bviExists_twoPow_mul_odd
#print axioms bviCountOnes_le
#print axioms bviToNat_lt_indDemo
#print axioms bviMagLex
#print axioms bviMagLexConv
#print axioms bviMagLex_iff
#print axioms bviMagOf_inj

end AxiomAudit

/- ========================================================================= -/
/- §7. 参数化证明书写指南（供 P1/P2 波次简报引用；BvInduction.lean §7）        -/
/- ========================================================================= -/

/- 1. 位宽纪律
   - 引理一律对 `BitVec w`（字面 BitVec，**不要** abbrev——simp/bv_decide 都
     看不穿）的 w 全量化陈述；索引算术（hi/lo/k）一律 Nat + omega。
   - 位断言先转算术再证：getLsbD → bviGetLsbD_true_iff → toNat / 2^i % 2；
     4.31 的 getLsbD 是裸 testBit（无宽度守卫），越界位由 toNat < 2^w 兜底。
   - 移位一律走 toNat：bviToNat_shiftLeft(_of_lt)/bviToNat_ushiftRight；
     拼接走 bviToNat_append；截走 bviExtract(Low)_toNat；掩码走
     bviAndMaskLow_toNat。BitVec 等式最后由 BitVec.toNat_inj.mp 收口。

  2. omega 纪律（变量指数场景）
   - omega 不做乘法单项式推理：2^a * 2^b、`(位).toNat * 2^w` 这类**两个
     变量原子相乘**的项必须先手工消去。
   - 标准手法：(a) bviPow2succ/bviPow2add 把指数归一；(b) 顶位/布尔系数先
     cases 成字面 0/1（见 bviToNat_lt_indDemo）；(c) 分配律手工装配
     （Nat.add_mul/Nat.mul_add，注意匹配方向，见 bviSumTo_eq）；
     (d) 装配干净后 omega 收口。
   - div/mod 与 2^k 的互转用 Nat.div_lt_iff_lt_mul / Nat.one_le_div_iff /
     Nat.mod_eq_of_lt / Nat.div_add_mod（全部探针核实存在）。

  3. 归纳模板选择表（§3 有各自的可工作示范）
   - 对 n 归纳、参数在递归中变化 → T1（induction n generalizing acc）。
     漏写 generalizing 是最高频 motive 事故。
   - List.foldl 不变式 → T2（l 与 acc 同泛化；不变式必须量化任意 acc）。
   - Fin n 目标 → T3a 先转 Nat+界；Fin 函数相等 → T3b；Fin 情形分析 →
     T3c（term 式 Fin.induction + 显式 motive，避开 case 名漂移）。
   - 需要"对更小的任意值"的 ih（如 n/2）→ T4（Nat.strongRecOn，term 式
     refine + 显式 motive；hn : n ≠ 0 这类依赖假设在归纳后再 intro）。
   - 递归 def → T5（fun_induction，case 名为 case1/case2/…；
     Bool 分支记得 cases 后给字面 toNat 桥）。
   - 对位宽 w 归纳 → T6：BitVec w 不是索引族，w 变化时类型不互通——
     归纳步必须经 bviTopBit_toNat 把 BitVec (w+1) 拆回 Bool + BitVec w；
     induction w 会 auto-revert 依赖 w 的假设（x 进 ih 的 ∀）。
   - 更常见的情况：根本不要对 w 归纳——固定任意 w，用 §2 的代数律直接
     符号推导（w 只是不透明参数）。对 w 的归纳只在"结构本身递归于宽度"
     （如 CLZ/LZA 的树形分解）时才需要。

  4. 证明风格政策（本路线）
   - 本文件零 SAT 零 native_decide：全部符号证明 + omega/decide。
     这证明"无 SAT"路线对参数化位级引理可行；后续波次沿用。
   - 9-18 修订政策（doc/02）：归纳难做而 SAT 明显快的局部场合允许
     bv_decide，但须审计可见 + 文件头注明理由——本文件示范的是默认形态。
   - 每条参数化引理配 by decide 数值实例（§5 双形式：定理实例化 +
     纯数值）——I-18 教训：期望值必须独立于模型推导。

  5. 既有资产的参数化升级路径（P2 参考）
   - fcMagOf/fcMagLex 族 → bviMagOf/bviMagLex 族（§4）：常量 23 → 参数 s，
     证明逐行同构；f32 实例由 s := 23 免费获得（§5 已含实例回归）。
   - DefsSpec 的 cat_toNat 族（w 已参数化）可直接复用；本文件 §2 与之
     正交（cat 走 Cat 定义，bvi 走核心 BitVec.append/extractLsb'）。
   - N4 LZA 位爆引理（faddLzaCore_1..24）归纳化时的入口：
     幅值界 → bviMsb_true_ge/bviMsb_false_lt/bviGetLsbD_true_of_range；
     log2 定值 → bviLog2_eq；逐位断言 → bviGetLsbD_true_iff。
-/

end Ventus.Base
