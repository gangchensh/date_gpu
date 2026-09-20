/- ========================================================================= -/
/-                  Arith/MultiplierCSA.lean                                 -/
/-  CSA 压缩树的电路层通用证明：加权列和不变式贯穿 mulCompress 递归，          -/
/-  从而电路层（mulDataModule）= 算术层（mulPlacedSum），对任意输入（len=33，  -/
/-  即实际例化 ArrayMulDataModule(33)）。                                     -/
/-                                                                           -/
/-  本文件消除 Multiplier.lean 第 8 节"电路层仅 len=8 穷举 + len=33 抽查"的    -/
/-  降级：主定理 mcsaDataModule33_eq_placedSum 对【符号】a b : BitVec 33 全证。  -/
/-  （len=8 的穷举定理仍保留在 Multiplier.lean 作回归测试；其内容对应 len=8    -/
/-   实例，本文件的通用不变式 mcsaCompress_invariant 对任意 len/列阵列成立。） -/
/-                                                                           -/
/-  证明分解：                                                                -/
/-  1. 值函数：mcsaColVal（列内位和）/ mcsaBitsVal（位列表，bit i 权 2^i）/    -/
/-     mcsaColsVal（列阵列，列 j 权 2^j）。                                   -/
/-  2. mcsaAOC_val：单列压缩 mulAddOneColumn 保持 colVal s + 2*(c1+c2) =      -/
/-     colVal col + colVal cin（fun_induction，用 mulC22/32/53_spec）。       -/
/-  3. mcsaAddRound_fold：一轮压缩的 foldl 不变式（进位链 cout1/cout2 的       -/
/-     权重恰为下一列权重）；推论：mcsaColsVal (mulAddRound cols) ≡            -/
/-     mcsaColsVal cols (mod 2^(cols.length))——末列进位被丢弃但权 ≥ 2^n。      -/
/-  4. mcsaCompress_invariant：任意 fuel 下长度与模 2^n 加权列和保持。         -/
/-  5. mulBitsToBv 装配引理（cons 分解 + |||/偶数加法）→ sum+carry ≡ 终态列和  -/
/-     （需终态每列 ≤ 2 位，由形状链提供）。                                  -/
/-  6. mulColumns 桥接：Id.run/forIn → 纯 foldl（List.forIn_pure_yield_eq_     -/
/-     foldl），逐行贡献 = 2^w * 截断位和 ≡ mulPlacedRow.toNat (mod 2^66)。    -/
/-  7. 形状链（全 false 列模拟）证明 len=33 终态每列 ≤ 2 位。                 -/
/-                                                                           -/
/-  ===== 完成状态（2026-08-29，agent-MCSA 续跑）=====                          -/
/-  全部 7 步闭合，零 sorry、零警告。主定理：                                  -/
/-    mcsaDataModule33_eq_placedSum（带形状前提 hfin 的干净版，公理仅           -/
/-    propext/Classical.choice/Quot.sound，无 bv_decide、无 ofReduceBool）；    -/
/-    mcsaDataModule33_eq_placedSum'（无条件版，经 mcsaFin33_all_le2 引用       -/
/-    mcsaShape33_final；形状链已切换为结构递归的 mcsaShapeAOCF                 -/
/-    （mcsaShapeAOC_eq_F 保证与 well-founded 版一致），mcsaShape33_final       -/
/-    用内核 decide 求值，公理同样仅标准三公理，无 ofReduceBool）。             -/
/-  禁 bv_decide 约束全程遵守：证明链只用 induction/fun_induction/omega/rw。   -/
/-                                                                           -/
/-  ===== 新坑记录（Q 区，供后续波次参考）=====                                 -/
/-  Q1. do/forIn 桥接：`forIn` 是根命名空间函数（不能写 l.forIn 点记法，        -/
/-     List.forIn 不存在）；Id 单子中 `do pure PUnit.unit; pure X` 定义等价     -/
/-     于 X（Id.bind/pure 是恒等）；if-then-yield/else-yield 与 yield-of-if     -/
/-     之间不定义等价，需 by_cases + if_pos/if_neg 逐点合并后 funext，再        -/
/-     List.forIn_pure_yield_eq_foldl。mulColumns 外层循环的 defeq 桥接用       -/
/-     `rw [show mulColumns a b = (forIn ...).run from rfl]`（需全文复述        -/
/-     do 块，have/let 样板会 zeta/beta 消去）。                               -/
/-  Q2. `X |>.f` 续行写法在定理语句中会误解析（.f 被当成函数参数）——           -/
/-     多行管道在 statement 里改用小括号嵌套。                                  -/
/-  Q3. `rw [← h]` 且 h : x = 66 时会把目标里 BitVec 66 的隐参宽度 66 一并      -/
/-     改写（motive 不良）——改为 `have h2 := ...; rw [h] at h2` 在假设侧做。   -/
/-  Q4. unfold 递归/自定义 def 会同时展开 foldl 内部出现的同名步进函数，        -/
/-     破坏后续按 def 名匹配的重写——只展开目标外层用 `show`（defeq 暴露        -/
/-     if-分支）代替 unfold。                                                 -/
/-  Q5. omega 对"同一原子的不同乘积分组"（如 2^w*(B+2^e*x) vs 2^w*B+           -/
/-     2^w*(2^e*x)）一律先 Nat.mul_assoc/Nat.left_distrib 归一到一致单项式，   -/
/-     否则不同语法乘积被抽象成无关原子而失败。                                -/
/-  Q6. simp only 不带 List.length_nil 时 `[].length` 不规约，omega 拿到       -/
/-     [].length 原子会失败——长度化简要 simp（默认集）或显式加                -/
/-     List.length_nil。                                                      -/
/-  Q7. `decide P` 里的 P 不能 rw（实例依赖 P，motive 不良）——用              -/
/-     decide_eq_decide.mpr (Iff.of_eq h)。                                   -/
/- ========================================================================= -/

import Ventus.Arith.Multiplier

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 值函数与基础引理                                                        -/
/- =========================================================================-/

/-- 列内位值和（无权） -/
def mcsaColVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + mcsaColVal bs

/-- 位列表加权值：bit i 权 2^i -/
def mcsaBitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * mcsaBitsVal bs

/-- 列阵列加权值：列 j 权 2^j -/
def mcsaColsVal : List (List Bool) → Nat
  | [] => 0
  | c :: cs => mcsaColVal c + 2 * mcsaColsVal cs

theorem mcsaColVal_append (l1 l2 : List Bool) :
    mcsaColVal (l1 ++ l2) = mcsaColVal l1 + mcsaColVal l2 := by
  induction l1 with
  | nil => simp [mcsaColVal]
  | cons b bs ih => simp [mcsaColVal, ih]; omega

theorem mcsaBitsVal_append (l1 l2 : List Bool) :
    mcsaBitsVal (l1 ++ l2) = mcsaBitsVal l1 + 2 ^ l1.length * mcsaBitsVal l2 := by
  induction l1 with
  | nil => simp [mcsaBitsVal]
  | cons b bs ih =>
    simp only [List.cons_append, mcsaBitsVal, ih, List.length_cons]
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    omega

theorem mcsaColsVal_append (l1 l2 : List (List Bool)) :
    mcsaColsVal (l1 ++ l2) = mcsaColsVal l1 + 2 ^ l1.length * mcsaColsVal l2 := by
  induction l1 with
  | nil => simp [mcsaColsVal]
  | cons c cs ih =>
    simp only [List.cons_append, mcsaColsVal, ih, List.length_cons]
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    omega

theorem mcsaColsVal_singleton (c : List Bool) : mcsaColsVal [c] = mcsaColVal c := by
  simp [mcsaColsVal]

theorem mcsaColsVal_replicate_nil (n : Nat) :
    mcsaColsVal (List.replicate n ([] : List Bool)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ]; simp [mcsaColsVal, mcsaColVal, ih]

/-- 列值的 take/drop 分解 -/
theorem mcsaColVal_take_drop (l : List Bool) (n : Nat) :
    mcsaColVal (l.take n) + mcsaColVal (l.drop n) = mcsaColVal l := by
  have h := mcsaColVal_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at h
  exact h.symm

/-- 位值的 take/drop 分解 -/
theorem mcsaBitsVal_take_drop (l : List Bool) (n : Nat) :
    mcsaBitsVal l = mcsaBitsVal (l.take n) + 2 ^ (l.take n).length * mcsaBitsVal (l.drop n) := by
  have h := mcsaBitsVal_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at h
  exact h

/-- 列值 = 头元素 + 尾部和（headD/drop 形式，配 C53 臂的 cin 处理） -/
theorem mcsaColVal_headD_drop (cin : List Bool) :
    mcsaColVal cin = (cin.headD false).toNat + mcsaColVal (cin.drop 1) := by
  cases cin with
  | nil => rfl
  | cons x xs => rfl

/- ========================================================================= -/
/- 2. mulAddOneColumn 单列压缩的三条引理（Multiplier.scala:77-113）            -/
/- =========================================================================-/

/-- L1【值不变式】单列压缩保持加权和：sum 权 1，cout1/cout2 权 2 -/
theorem mcsaAOC_val (col cin : List Bool) :
    mcsaColVal (mulAddOneColumn col cin).1
      + 2 * (mcsaColVal (mulAddOneColumn col cin).2.1
        + mcsaColVal (mulAddOneColumn col cin).2.2)
      = mcsaColVal col + mcsaColVal cin := by
  fun_induction mulAddOneColumn col cin with
  | case1 cin h1 h2 =>
    simp [mcsaColVal]
  | case2 a cin h1 h2 =>
    simp [mcsaColVal]
  | case3 a b cin h1 s2 c2 hc22 h2 =>
    have hspec := mulC22_spec a b
    rw [hc22] at hspec
    simp only [] at hspec
    simp only [List.singleton_append, mcsaColVal]
    omega
  | case4 a b c cin h1 s2 c2 hc32 h2 =>
    have hspec := mulC32_spec a b c
    rw [hc32] at hspec
    simp only [] at hspec
    simp only [List.singleton_append, mcsaColVal]
    omega
  | case5 a b c d cin h1 o0 o1 o2 hc53 h2 =>
    have hspec := mulC53_spec a b c d (cin.headD false)
    rw [hc53] at hspec
    simp only [] at hspec
    simp only [List.singleton_append, mcsaColVal]
    rw [mcsaColVal_headD_drop cin]
    omega
  | case6 col cin h hne0 hne1 hne2 hne3 hne4 hle =>
    cases col with
    | nil => exact (hne0 h rfl (heq_of_eq (proof_irrel h h))).elim
    | cons x1 cs1 =>
      cases cs1 with
      | nil => exact (hne1 x1 h rfl (heq_of_eq (proof_irrel h h))).elim
      | cons x2 cs2 =>
        cases cs2 with
        | nil => exact (hne2 x1 x2 h rfl (heq_of_eq (proof_irrel h h))).elim
        | cons x3 cs3 =>
          cases cs3 with
          | nil => exact (hne3 x1 x2 x3 h rfl (heq_of_eq (proof_irrel h h))).elim
          | cons x4 cs4 =>
            cases cs4 with
            | nil => exact (hne4 x1 x2 x3 x4 h rfl (heq_of_eq (proof_irrel h h))).elim
            | cons x5 cs5 =>
              have h5 : cs5.length + 5 ≤ 4 := hle
              omega
  | case7 col cin h s1 c11 c12 heq1 s2 c21 c22 heq2 ih1 ih2 =>
    rw [heq1] at ih1
    rw [heq2] at ih2
    dsimp only at ih1 ih2
    simp only [mcsaColVal_append]
    have hcol := mcsaColVal_take_drop col 4
    have hcin := mcsaColVal_take_drop cin 1
    omega

-- 冒烟测试（注：Ventus.Base.Defs 的 x[[hi,lo]] 记法使 [[...]] 列表字面量不可解析，
-- 嵌套列表用 :: 构造）
example : mcsaColVal [true, false, true] = 2 := by decide
example : mcsaBitsVal [true, false, true] = 5 := by decide
example : mcsaColsVal ([true] :: [true] :: [true, false] :: ([] : List (List Bool)))
    = 1 + 2 + 4 := by decide

/- ========================================================================= -/
/- 3. mulAddRound 一轮压缩的 foldl 不变式（Multiplier.scala:124-131）           -/
/- =========================================================================-/

/-- mulAddRound 的步进函数（顶层镜像，便于归纳陈述） -/
def mcsaRoundStep (acc : List (List Bool) × List Bool × List Bool) (col : List Bool) :
    List (List Bool) × List Bool × List Bool :=
  match acc with
  | (built, cout1, cout2) =>
      let (s, c1, c2) := mulAddOneColumn col cout1
      (built ++ [s ++ cout2], c1, c2)

/-- 顶层镜像与原定义一致 -/
theorem mulAddRound_eq_foldl (cols : List (List Bool)) :
    mulAddRound cols = (cols.foldl mcsaRoundStep ([], [], [])).1 := rfl

/-- 步进函数展开（Prod eta 使 let 解构定义等价于投影形式） -/
theorem mcsaRoundStep_eq (built : List (List Bool)) (c1 c2 col : List Bool) :
    mcsaRoundStep (built, c1, c2) col
      = (built ++ [(mulAddOneColumn col c1).1 ++ c2],
         (mulAddOneColumn col c1).2.1, (mulAddOneColumn col c1).2.2) := rfl

/-- foldl 长度不变式：每列恰好多出一个输出列 -/
theorem mcsaRoundStep_fold_length (tail : List (List Bool)) (built : List (List Bool))
    (c1 c2 : List Bool) :
    (tail.foldl mcsaRoundStep (built, c1, c2)).1.length = built.length + tail.length := by
  induction tail generalizing built c1 c2 with
  | nil => simp
  | cons col rest ih =>
    rw [List.foldl_cons, mcsaRoundStep_eq, ih, List.length_append,
      List.length_singleton, List.length_cons]
    omega

/-- 【第 3 步核心】一轮压缩的 foldl 值不变式：
    已建列的加权和 + 2^(已处理列数) ·（悬挂进位值）= 初始已建列 + 2^(初始长度) ·（初始进位 + 待处理列加权和）。
    进位 cout1 作为下一列 cin（权 2·2^j = 2^(j+1) 恰为下一列权），cout2 并入下一输出列 -/
theorem mcsaAddRound_fold (tail : List (List Bool)) (built : List (List Bool))
    (c1 c2 : List Bool) :
    mcsaColsVal (tail.foldl mcsaRoundStep (built, c1, c2)).1
      + 2 ^ (built.length + tail.length)
          * (mcsaColVal (tail.foldl mcsaRoundStep (built, c1, c2)).2.1
            + mcsaColVal (tail.foldl mcsaRoundStep (built, c1, c2)).2.2)
    = mcsaColsVal built
      + 2 ^ built.length * (mcsaColVal c1 + mcsaColVal c2 + mcsaColsVal tail) := by
  induction tail generalizing built c1 c2 with
  | nil => simp [mcsaColsVal]
  | cons col rest ih =>
    have ih' := ih (built ++ [(mulAddOneColumn col c1).1 ++ c2])
      (mulAddOneColumn col c1).2.1 (mulAddOneColumn col c1).2.2
    have hlen : (built ++ [(mulAddOneColumn col c1).1 ++ c2]).length
        = built.length + 1 := by
      rw [List.length_append, List.length_singleton]
    rw [hlen] at ih'
    rw [List.foldl_cons, mcsaRoundStep_eq, List.length_cons]
    have hexp : built.length + (rest.length + 1) = built.length + 1 + rest.length :=
      by omega
    rw [hexp, ih']
    have hval := mcsaAOC_val col c1
    rw [mcsaColsVal_append, mcsaColsVal_singleton, mcsaColVal_append, Nat.pow_succ]
    simp only [mcsaColsVal]
    have hinner : mcsaColVal (mulAddOneColumn col c1).1 + mcsaColVal c2
        + 2 * (mcsaColVal (mulAddOneColumn col c1).2.1
          + mcsaColVal (mulAddOneColumn col c1).2.2 + mcsaColsVal rest)
      = mcsaColVal c1 + mcsaColVal c2 + (mcsaColVal col + 2 * mcsaColsVal rest) := by
      omega
    conv => lhs; rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.left_distrib, hinner]

/-- 一轮压缩的值推论：末列进位（权 2^n）被丢弃，其余不变 -/
theorem mcsaAddRound_colsVal (cols : List (List Bool)) :
    mcsaColsVal cols = mcsaColsVal (mulAddRound cols)
      + 2 ^ cols.length
          * (mcsaColVal (cols.foldl mcsaRoundStep ([], [], [])).2.1
            + mcsaColVal (cols.foldl mcsaRoundStep ([], [], [])).2.2) := by
  have h := mcsaAddRound_fold cols [] [] []
  simp only [List.length_nil, Nat.zero_add, mcsaColsVal, mcsaColVal, Nat.pow_zero,
    Nat.one_mul, Nat.add_zero] at h
  rw [mulAddRound_eq_foldl]
  omega

/-- 一轮压缩保持列数 -/
theorem mcsaAddRound_length (cols : List (List Bool)) :
    (mulAddRound cols).length = cols.length := by
  rw [mulAddRound_eq_foldl, mcsaRoundStep_fold_length, List.length_nil, Nat.zero_add]

/-- 一轮压缩保持模 2^n 加权列和 -/
theorem mcsaAddRound_mod (cols : List (List Bool)) :
    mcsaColsVal (mulAddRound cols) % 2 ^ cols.length
      = mcsaColsVal cols % 2 ^ cols.length := by
  conv => rhs; rw [mcsaAddRound_colsVal]
  rw [Nat.add_mul_mod_self_left]

/- ========================================================================= -/
/- 4. mulCompress 全程不变式（Multiplier.scala:116-141）                        -/
/- =========================================================================-/

/-- 压缩保持列数（任意 fuel；提前退出或 fuel 耗尽均成立） -/
theorem mcsaCompress_length (fuel : Nat) (cols : List (List Bool)) :
    (mulCompress fuel cols).length = cols.length := by
  induction fuel generalizing cols with
  | zero => rfl
  | succ f ih =>
    simp only [mulCompress]
    split
    · rfl
    · rw [ih, mcsaAddRound_length]

/-- 【第 4 步核心】任意 fuel 下模 2^n 加权列和保持 -/
theorem mcsaCompress_invariant (fuel : Nat) (cols : List (List Bool)) :
    mcsaColsVal (mulCompress fuel cols) % 2 ^ cols.length
      = mcsaColsVal cols % 2 ^ cols.length := by
  induction fuel generalizing cols with
  | zero => rfl
  | succ f ih =>
    simp only [mulCompress]
    split
    · rfl
    · have h1 := ih (mulAddRound cols)
      rw [mcsaAddRound_length] at h1
      rw [h1]
      exact mcsaAddRound_mod cols

/- ========================================================================= -/
/- 7a. 形状链（只跟踪列长的模拟）：mulAddOneColumn/mulAddRound/mulCompress      -/
/-     的输出列长只依赖输入列长，与位值无关。                                   -/
/- =========================================================================-/

/-- mulAddOneColumn 的形状模拟：(s.length, c1.length, c2.length) -/
def mcsaShapeAOC (colLen cinLen : Nat) : Nat × Nat × Nat :=
  if h : colLen ≤ 4 then
    if colLen = 0 then (cinLen, 0, 0)
    else if colLen = 1 then (1 + cinLen, 0, 0)
    else if colLen ≤ 3 then (1 + cinLen, 0, 1)
    else (1 + (cinLen - 1), 1, 1)
  else
    ((mcsaShapeAOC 4 (min cinLen 1)).1 + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).1,
     (mcsaShapeAOC 4 (min cinLen 1)).2.1 + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).2.1,
     (mcsaShapeAOC 4 (min cinLen 1)).2.2 + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).2.2)
termination_by colLen
decreasing_by all_goals (simp_wf; omega)

/-- 形状模拟在字面上的五条展开引理 -/
theorem mcsaShapeAOC_zero (cinLen : Nat) : mcsaShapeAOC 0 cinLen = (cinLen, 0, 0) := by
  unfold mcsaShapeAOC
  rw [dif_pos (by decide : (0 : Nat) ≤ 4), if_pos rfl]

theorem mcsaShapeAOC_one (cinLen : Nat) : mcsaShapeAOC 1 cinLen = (1 + cinLen, 0, 0) := by
  unfold mcsaShapeAOC
  rw [dif_pos (by decide : (1 : Nat) ≤ 4), if_neg (by decide : ¬ (1 : Nat) = 0),
    if_pos rfl]

theorem mcsaShapeAOC_two (cinLen : Nat) : mcsaShapeAOC 2 cinLen = (1 + cinLen, 0, 1) := by
  unfold mcsaShapeAOC
  rw [dif_pos (by decide : (2 : Nat) ≤ 4), if_neg (by decide : ¬ (2 : Nat) = 0),
    if_neg (by decide : ¬ (2 : Nat) = 1), if_pos (by decide : (2 : Nat) ≤ 3)]

theorem mcsaShapeAOC_three (cinLen : Nat) : mcsaShapeAOC 3 cinLen = (1 + cinLen, 0, 1) := by
  unfold mcsaShapeAOC
  rw [dif_pos (by decide : (3 : Nat) ≤ 4), if_neg (by decide : ¬ (3 : Nat) = 0),
    if_neg (by decide : ¬ (3 : Nat) = 1), if_pos (by decide : (3 : Nat) ≤ 3)]

theorem mcsaShapeAOC_four (cinLen : Nat) :
    mcsaShapeAOC 4 cinLen = (1 + (cinLen - 1), 1, 1) := by
  unfold mcsaShapeAOC
  rw [dif_pos (by decide : (4 : Nat) ≤ 4), if_neg (by decide : ¬ (4 : Nat) = 0),
    if_neg (by decide : ¬ (4 : Nat) = 1), if_neg (by decide : ¬ (4 : Nat) ≤ 3)]

theorem mcsaShapeAOC_gt4 {colLen cinLen : Nat} (h : ¬ colLen ≤ 4) :
    mcsaShapeAOC colLen cinLen
      = ((mcsaShapeAOC 4 (min cinLen 1)).1 + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).1,
         (mcsaShapeAOC 4 (min cinLen 1)).2.1 + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).2.1,
         (mcsaShapeAOC 4 (min cinLen 1)).2.2
           + (mcsaShapeAOC (colLen - 4) (cinLen - 1)).2.2) := by
  conv => lhs; unfold mcsaShapeAOC
  rw [dif_neg h]

/-- mcsaShapeAOC 的结构递归版（fuel 参数）。well-founded 递归内核不能求值，
    mcsaShape33_final 的 `by decide`（内核求值，免 ofReduceBool）需要本版本；
    fuel ≥ colLen 时与原函数相等（mcsaShapeAOC_eq_F）。 -/
def mcsaShapeAOCF : Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _, cinLen => (cinLen, 0, 0)
  | fuel + 1, colLen, cinLen =>
    if colLen ≤ 4 then
      if colLen = 0 then (cinLen, 0, 0)
      else if colLen = 1 then (1 + cinLen, 0, 0)
      else if colLen ≤ 3 then (1 + cinLen, 0, 1)
      else (1 + (cinLen - 1), 1, 1)
    else
      ((mcsaShapeAOCF fuel 4 (min cinLen 1)).1
         + (mcsaShapeAOCF fuel (colLen - 4) (cinLen - 1)).1,
       (mcsaShapeAOCF fuel 4 (min cinLen 1)).2.1
         + (mcsaShapeAOCF fuel (colLen - 4) (cinLen - 1)).2.1,
       (mcsaShapeAOCF fuel 4 (min cinLen 1)).2.2
         + (mcsaShapeAOCF fuel (colLen - 4) (cinLen - 1)).2.2)

/-- fuel ≥ colLen 时结构递归版 = well-founded 版 -/
theorem mcsaShapeAOC_eq_F_aux (fuel colLen cinLen : Nat) (h : colLen ≤ fuel) :
    mcsaShapeAOC colLen cinLen = mcsaShapeAOCF fuel colLen cinLen := by
  induction fuel generalizing colLen cinLen with
  | zero =>
    have h0 : colLen = 0 := by omega
    subst h0
    rw [mcsaShapeAOC_zero]
    rfl
  | succ f ih =>
    by_cases h4 : colLen ≤ 4
    · have hc : colLen = 0 ∨ colLen = 1 ∨ colLen = 2 ∨ colLen = 3 ∨ colLen = 4 := by
        omega
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · rw [mcsaShapeAOC_zero]; rfl
      · rw [mcsaShapeAOC_one]; rfl
      · rw [mcsaShapeAOC_two]; rfl
      · rw [mcsaShapeAOC_three]; rfl
      · rw [mcsaShapeAOC_four]; rfl
    · rw [mcsaShapeAOC_gt4 h4]
      rw [show mcsaShapeAOCF (f + 1) colLen cinLen
          = if colLen ≤ 4 then
              (if colLen = 0 then (cinLen, 0, 0)
               else if colLen = 1 then (1 + cinLen, 0, 0)
               else if colLen ≤ 3 then (1 + cinLen, 0, 1)
               else (1 + (cinLen - 1), 1, 1))
            else ((mcsaShapeAOCF f 4 (min cinLen 1)).1
                + (mcsaShapeAOCF f (colLen - 4) (cinLen - 1)).1,
              (mcsaShapeAOCF f 4 (min cinLen 1)).2.1
                + (mcsaShapeAOCF f (colLen - 4) (cinLen - 1)).2.1,
              (mcsaShapeAOCF f 4 (min cinLen 1)).2.2
                + (mcsaShapeAOCF f (colLen - 4) (cinLen - 1)).2.2) from rfl]
      rw [if_neg h4, ← ih 4 (min cinLen 1) (by omega),
        ← ih (colLen - 4) (cinLen - 1) (by omega)]

/-- 结构递归版（fuel 取 colLen）与原形状模拟相等 -/
theorem mcsaShapeAOC_eq_F (colLen cinLen : Nat) :
    mcsaShapeAOC colLen cinLen = mcsaShapeAOCF colLen colLen cinLen :=
  mcsaShapeAOC_eq_F_aux colLen colLen cinLen (Nat.le_refl colLen)

/-- 形状模拟与真实压缩的输出列长一致 -/
theorem mcsaShapeAOC_spec (col cin : List Bool) :
    (mcsaShapeAOC col.length cin.length).1 = (mulAddOneColumn col cin).1.length
    ∧ (mcsaShapeAOC col.length cin.length).2.1 = (mulAddOneColumn col cin).2.1.length
    ∧ (mcsaShapeAOC col.length cin.length).2.2
        = (mulAddOneColumn col cin).2.2.length := by
  fun_induction mulAddOneColumn col cin with
  | case1 cin h1 h2 =>
    rw [show ([] : List Bool).length = 0 from rfl, mcsaShapeAOC_zero]
    simp
  | case2 a cin h1 h2 =>
    rw [show [a].length = 1 from rfl, mcsaShapeAOC_one]
    simp [Nat.add_comm]
  | case3 a b cin h1 s2 c2 hc22 h2 =>
    rw [show [a, b].length = 2 from rfl, mcsaShapeAOC_two]
    simp [Nat.add_comm]
  | case4 a b c cin h1 s2 c2 hc32 h2 =>
    rw [show [a, b, c].length = 3 from rfl, mcsaShapeAOC_three]
    simp [Nat.add_comm]
  | case5 a b c d cin h1 o0 o1 o2 hc53 h2 =>
    rw [show [a, b, c, d].length = 4 from rfl, mcsaShapeAOC_four]
    simp [Nat.add_comm]
  | case6 col cin h hne0 hne1 hne2 hne3 hne4 hle =>
    cases col with
    | nil => exact (hne0 h rfl (heq_of_eq (proof_irrel h h))).elim
    | cons x1 cs1 =>
      cases cs1 with
      | nil => exact (hne1 x1 h rfl (heq_of_eq (proof_irrel h h))).elim
      | cons x2 cs2 =>
        cases cs2 with
        | nil => exact (hne2 x1 x2 h rfl (heq_of_eq (proof_irrel h h))).elim
        | cons x3 cs3 =>
          cases cs3 with
          | nil => exact (hne3 x1 x2 x3 h rfl (heq_of_eq (proof_irrel h h))).elim
          | cons x4 cs4 =>
            cases cs4 with
            | nil => exact (hne4 x1 x2 x3 x4 h rfl (heq_of_eq (proof_irrel h h))).elim
            | cons x5 cs5 =>
              have h5 : cs5.length + 5 ≤ 4 := hle
              omega
  | case7 col cin h s1 c11 c12 heq1 s2 c21 c22 heq2 ih1 ih2 =>
    rw [heq1] at ih1
    rw [heq2] at ih2
    dsimp only at ih1 ih2
    have ht4 : (col.take 4).length = 4 := by
      rw [List.length_take]; omega
    have ht1 : (cin.take 1).length = min cin.length 1 := by
      rw [List.length_take]; omega
    have hd4 : (col.drop 4).length = col.length - 4 := by rw [List.length_drop]
    have hd1 : (cin.drop 1).length = cin.length - 1 := by rw [List.length_drop]
    rw [ht4, ht1] at ih1
    rw [hd4, hd1] at ih2
    rw [mcsaShapeAOC_gt4 h]
    dsimp only
    simp only [List.length_append]
    omega

/-- mulAddRound 的形状模拟步进（用结构递归版 mcsaShapeAOCF，保证内核可求值） -/
def mcsaShapeRoundStep (acc : List Nat × Nat × Nat) (colLen : Nat) : List Nat × Nat × Nat :=
  match acc with
  | (built, c1, c2) =>
      let (s, c1', c2') := mcsaShapeAOCF colLen colLen c1
      (built ++ [s + c2], c1', c2')

/-- mulAddRound 的形状模拟 -/
def mcsaShapeRound (lens : List Nat) : List Nat :=
  (lens.foldl mcsaShapeRoundStep ([], 0, 0)).1

/-- 形状步进展开（Prod eta；经 mcsaShapeAOC_eq_F 回到 well-founded 版表述） -/
theorem mcsaShapeRoundStep_eq (built : List Nat) (c1 c2 colLen : Nat) :
    mcsaShapeRoundStep (built, c1, c2) colLen
      = (built ++ [(mcsaShapeAOC colLen c1).1 + c2],
         (mcsaShapeAOC colLen c1).2.1, (mcsaShapeAOC colLen c1).2.2) := by
  rw [mcsaShapeAOC_eq_F]
  rfl

/-- 一轮压缩的逐列长度 = 形状模拟 -/
theorem mcsaShapeRound_fold (tail : List (List Bool)) (built : List (List Bool))
    (c1 c2 : List Bool) :
    ((tail.foldl mcsaRoundStep (built, c1, c2)).1).map List.length
      = ((tail.map List.length).foldl mcsaShapeRoundStep
          (built.map List.length, c1.length, c2.length)).1 := by
  induction tail generalizing built c1 c2 with
  | nil => rfl
  | cons col rest ih =>
    rw [List.foldl_cons, mcsaRoundStep_eq, List.map_cons, List.foldl_cons]
    have hspec := mcsaShapeAOC_spec col c1
    have hstep : mcsaShapeRoundStep (built.map List.length, c1.length, c2.length)
        col.length
        = ((built ++ [(mulAddOneColumn col c1).1 ++ c2]).map List.length,
           (mulAddOneColumn col c1).2.1.length, (mulAddOneColumn col c1).2.2.length) := by
      rw [mcsaShapeRoundStep_eq, List.map_append, List.map_singleton,
        List.length_append, ← hspec.1, ← hspec.2.1, ← hspec.2.2]
    rw [hstep]
    exact ih _ _ _

/-- 一轮压缩的列长 = 形状模拟 -/
theorem mcsaAddRound_map_length (cols : List (List Bool)) :
    (mulAddRound cols).map List.length = mcsaShapeRound (cols.map List.length) :=
  mcsaShapeRound_fold cols [] [] []

/-- mulCompress 的形状模拟 -/
def mcsaShapeCompress : Nat → List Nat → List Nat
  | 0, lens => lens
  | fuel + 1, lens =>
    if lens.all (fun l => decide (l ≤ 2)) then lens
    else mcsaShapeCompress fuel (mcsaShapeRound lens)

/-- 压缩全程的列长 = 形状模拟 -/
theorem mcsaCompress_map_length (fuel : Nat) (cols : List (List Bool)) :
    (mulCompress fuel cols).map List.length
      = mcsaShapeCompress fuel (cols.map List.length) := by
  induction fuel generalizing cols with
  | zero => rfl
  | succ f ih =>
    simp only [mulCompress, mcsaShapeCompress]
    have hcond : (cols.all fun c => decide (c.length ≤ 2))
        = ((cols.map List.length).all fun l => decide (l ≤ 2)) := by
      rw [List.all_map]
      rfl
    rw [hcond]
    split
    · rfl
    · rw [ih, mcsaAddRound_map_length]

/- ========================================================================= -/
/- 5. mulBitsToBv 装配：位列表 → BitVec 66 的值引理（无 bv_decide）             -/
/- =========================================================================-/

/-- Nat 辅助：x % 2^(n+1) 的低/当前位分解 -/
theorem mcsaNat_mod_two_pow_succ (x n : Nat) :
    x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := by
  have h1 := Nat.mod_add_div x (2 ^ n)
  have h2 := Nat.mod_add_div (x / 2 ^ n) 2
  rw [Nat.div_div_eq_div_mul] at h2
  have hring : x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) + 2 ^ n * 2 * (x / (2 ^ n * 2))
      = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2 + 2 * (x / (2 ^ n * 2))) := by
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.left_distrib]
  have hx : x = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) + 2 ^ (n + 1) * (x / 2 ^ (n + 1)) := by
    rw [Nat.pow_succ, hring, h2]
    exact h1.symm
  have hlt : x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) < 2 ^ (n + 1) := by
    have hm := Nat.mod_lt x (Nat.two_pow_pos n)
    have hd := Nat.mod_lt (x / 2 ^ n) (show 0 < 2 by decide)
    have hd2 : 2 ^ n * (x / 2 ^ n % 2) ≤ 2 ^ n := by
      have h := Nat.mul_le_mul_left (2 ^ n) (Nat.le_of_lt_succ hd)
      simpa using h
    rw [Nat.pow_succ]
    omega
  conv => lhs; rw [hx]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Bool 位列表（range n 取 getLsbD）的加权和 = toNat 的低 n 位 -/
theorem mcsaBitsVal_range_getLsbD {w : Nat} (v : BitVec w) (n : Nat) :
    mcsaBitsVal ((List.range n).map v.getLsbD) = v.toNat % 2 ^ n := by
  induction n with
  | zero => simp [mcsaBitsVal, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      mcsaBitsVal_append, ih, List.length_map,
      List.length_range, mcsaNat_mod_two_pow_succ]
    have hbit : (v.getLsbD k).toNat = v.toNat / 2 ^ k % 2 := by
      show (Nat.testBit v.toNat k).toNat = _
      rw [Nat.testBit_eq_decide_div_mod_eq]
      by_cases h1 : v.toNat / 2 ^ k % 2 = 1
      · rw [decide_eq_true h1, h1]
        decide
      · have hlt : v.toNat / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
        have h0 : v.toNat / 2 ^ k % 2 = 0 := by omega
        rw [decide_eq_false h1, h0]
        decide
    rw [show mcsaBitsVal [v.getLsbD k] = (v.getLsbD k).toNat from by simp [mcsaBitsVal] ]
    rw [hbit]

/-- mulBvBits 的加权和 = toNat -/
theorem mcsaBitsVal_bvBits {w : Nat} (v : BitVec w) :
    mcsaBitsVal (mulBvBits v) = v.toNat := by
  unfold mulBvBits
  rw [mcsaBitsVal_range_getLsbD, Nat.mod_eq_of_lt v.isLt]

/-- Nat 辅助：第 k 位为 0 时 lor 2^k = 加 2^k -/
theorem mcsaNat_lor_two_pow (x k : Nat) (h : Nat.testBit x k = false) :
    x ||| 2 ^ k = x + 2 ^ k := by
  have hmod : x / 2 ^ k % 2 = 0 := by
    have h1 := Nat.testBit_eq_decide_div_mod_eq (x := x) (i := k)
    rw [h1, decide_eq_false_iff_not] at h
    have hlt : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hdiv : x / 2 ^ k = 2 * (x / 2 ^ (k + 1)) := by
    have h1 := Nat.mod_add_div (x / 2 ^ k) 2
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, hmod, Nat.succ_eq_add_one] at h1
    omega
  have hr : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  have hrlt : x % 2 ^ k < 2 ^ (k + 1) := by rw [hpow]; omega
  -- x = 2^(k+1) * q + r（因第 k 位为 0）
  have hx : x = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) + x % 2 ^ k := by
    have h2 := Nat.mod_add_div x (2 ^ k)
    rw [hdiv, ← Nat.mul_assoc, ← hpow] at h2
    omega
  have h2k : 2 ^ k ||| x % 2 ^ k = 2 ^ k + x % 2 ^ k := by
    have h3 := Nat.two_pow_add_eq_or_of_lt hr (1 : Nat)
    rw [Nat.mul_one] at h3
    exact h3.symm
  have hsum : 2 ^ k + x % 2 ^ k < 2 ^ (k + 1) := by rw [hpow]; omega
  calc x ||| 2 ^ k
      = (2 ^ (k + 1) * (x / 2 ^ (k + 1)) + x % 2 ^ k) ||| 2 ^ k := by
        conv => lhs; rw [hx]
    _ = (2 ^ (k + 1) * (x / 2 ^ (k + 1)) ||| x % 2 ^ k) ||| 2 ^ k := by
        rw [Nat.two_pow_add_eq_or_of_lt hrlt]
    _ = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) ||| (x % 2 ^ k ||| 2 ^ k) := Nat.or_assoc _ _ _
    _ = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) ||| (2 ^ k ||| x % 2 ^ k) := by
        rw [Nat.or_comm (x % 2 ^ k) (2 ^ k)]
    _ = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) ||| (2 ^ k + x % 2 ^ k) := by rw [h2k]
    _ = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) + (2 ^ k + x % 2 ^ k) :=
        (Nat.two_pow_add_eq_or_of_lt hsum _).symm
    _ = x + 2 ^ k := by
        conv => rhs; rw [hx]
        omega

/-- BitVec 66 单位置或：bit k 未置位时 ||| (1<<<k) = +2^k -/
theorem mcsaOrBit_toNat (acc : BitVec 66) (k : Nat) (hk : k < 66)
    (hacc : acc.getLsbD k = false) :
    (acc ||| (1#66 <<< k)).toNat = acc.toNat + 2 ^ k := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ 66 from by decide), Nat.shiftLeft_eq,
    Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  exact mcsaNat_lor_two_pow acc.toNat k hacc

/-- mulBitsToBv 的 foldl 值不变式：acc 的高位（≥ k）为零时，装配 = acc + 2^k·位权和 -/
theorem mcsaBitsToBv_fold (acc : BitVec 66) (bits : List Bool) (k : Nat)
    (hacc : acc.toNat < 2 ^ k)
    (hk : k + bits.length ≤ 66) :
    ((bits.zipIdx k).foldl
      (fun acc p => if p.1 then acc ||| (1#66 <<< p.2) else acc) acc).toNat
      = acc.toNat + 2 ^ k * mcsaBitsVal bits := by
  induction bits generalizing acc k with
  | nil => simp [mcsaBitsVal]
  | cons b bs ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    simp only [List.length_cons] at hk
    have hacc1 : acc.toNat < 2 ^ (k + 1) :=
      Nat.lt_trans hacc (Nat.pow_lt_pow_right (by decide) (by omega))
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih acc (k + 1) hacc1 (by omega)]
      simp only [mcsaBitsVal, Bool.toNat_false, Nat.zero_add, Nat.pow_succ, Nat.mul_assoc]
    | true =>
      have hbit : acc.getLsbD k = false := by
        show Nat.testBit acc.toNat k = false
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hacc]
        decide
      have hor : (acc ||| (1#66 <<< k)).toNat = acc.toNat + 2 ^ k :=
        mcsaOrBit_toNat acc k (by omega) hbit
      have hbound : (acc ||| (1#66 <<< k)).toNat < 2 ^ (k + 1) := by
        rw [hor, Nat.pow_succ]
        omega
      rw [if_pos rfl]
      rw [ih (acc ||| (1#66 <<< k)) (k + 1) hbound (by omega), hor]
      simp only [mcsaBitsVal, Bool.toNat_true]
      conv => lhs; rw [Nat.pow_succ, Nat.mul_assoc]
      conv => rhs; rw [Nat.left_distrib, Nat.mul_one]
      omega

/-- mulBitsToBv 的正确性：长度 ≤ 66 时 toNat = 位权和 -/
theorem mcsaBitsToBv_toNat (bits : List Bool) (h : bits.length ≤ 66) :
    (mulBitsToBv (w := 66) bits).toNat = mcsaBitsVal bits := by
  unfold mulBitsToBv
  rw [mcsaBitsToBv_fold (0#66) bits 0 (by simp) (by simpa using h)]
  simp

/-- 列长 ≤ 2 时列值 = 两位之和 -/
theorem mcsaColVal_eq_getD (c : List Bool) (h : c.length ≤ 2) :
    mcsaColVal c = (c.getD 0 false).toNat + (c.getD 1 false).toNat := by
  cases c with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      cases ys with
      | nil => rfl
      | cons z zs => simp only [List.length_cons] at h; omega

/-- bit0/bit1 两路位权和之和 = 列加权和（终态每列 ≤ 2 位） -/
theorem mcsaBitsVal_map_getD_add (fin : List (List Bool))
    (h : ∀ c ∈ fin, c.length ≤ 2) :
    mcsaBitsVal (fin.map (fun c => c.getD 0 false))
      + mcsaBitsVal (fin.map (fun c => c.getD 1 false))
      = mcsaColsVal fin := by
  induction fin with
  | nil => rfl
  | cons c cs ih =>
    have hc : c.length ≤ 2 := h c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, c'.length ≤ 2 := fun c' hc' => h c' (List.mem_cons_of_mem c hc')
    rw [List.map_cons, List.map_cons]
    simp only [mcsaBitsVal, mcsaColsVal]
    have ihh := ih hcs
    rw [mcsaColVal_eq_getD c hc]
    omega

/-- 【第 5 步主引理】终态列阵列（66 列、每列 ≤ 2 位）的 sum+carry = 列加权和（mod 2^66） -/
theorem mcsaSumCarry_toNat (fin : List (List Bool)) (hlen : fin.length = 66)
    (h2 : ∀ c ∈ fin, c.length ≤ 2) :
    (mulBitsToBv (w := 66) (fin.map (fun c => c.getD 0 false))
      + mulBitsToBv (w := 66) (fin.map (fun c => c.getD 1 false))).toNat
      = mcsaColsVal fin % 2 ^ 66 := by
  rw [BitVec.toNat_add,
    mcsaBitsToBv_toNat _ (by rw [List.length_map]; omega),
    mcsaBitsToBv_toNat _ (by rw [List.length_map]; omega),
    mcsaBitsVal_map_getD_add fin h2]

/- ========================================================================= -/
/- 6. mulColumns 桥接：Id.run/forIn → 纯 foldl；逐行贡献 = mulPlacedRow.toNat   -/
/- =========================================================================-/

/-- 单行放置的列表步进（mulColumns 内层循环的纯形式，Multiplier.scala:70-74） -/
def mcsaPlaceStep (bits : List Bool) (weight : Nat) (l : List (List Bool)) (j : Nat) :
    List (List Bool) :=
  if weight ≤ j ∧ j < weight + bits.length then l.modify j (· ++ [bits.getD (j - weight) false])
  else l

/-- 单行放置的 Array 步进 -/
def mcsaPlaceStepArr (bits : List Bool) (weight : Nat) (r : Array (List Bool)) (j : Nat) :
    Array (List Bool) :=
  if weight ≤ j ∧ j < weight + bits.length then r.modify j (fun c => c ++ [bits.getD (j - weight) false])
  else r

/-- 单行放置（Array foldl 形式） -/
def mcsaPlaceRowArr (r : Array (List Bool)) (bits : List Bool) (weight n : Nat) :
    Array (List Bool) :=
  (List.range n).foldl (mcsaPlaceStepArr bits weight) r

/-- 内层 forIn 循环 = foldl（do 纯样板定义等价消去 + if 分支并入 yield） -/
theorem mcsaInnerForIn (cols : Array (List Bool)) (bits : List Bool) (weight n : Nat) :
    (forIn (m := Id) (List.range n) cols (fun j r =>
      if weight ≤ j ∧ j < weight + bits.length then
        (do pure PUnit.unit
            pure (ForInStep.yield (r.modify j fun c => c ++ [bits.getD (j - weight) false])))
      else
        (do pure PUnit.unit
            pure (ForInStep.yield r))))
    = mcsaPlaceRowArr cols bits weight n := by
  have hstep : ∀ (j : Nat) (r : Array (List Bool)),
      (if weight ≤ j ∧ j < weight + bits.length then
        (do pure PUnit.unit
            pure (ForInStep.yield (r.modify j fun c => c ++ [bits.getD (j - weight) false]))
          : Id (ForInStep (Array (List Bool))))
      else
        (do pure PUnit.unit
            pure (ForInStep.yield r)))
      = pure (ForInStep.yield (mcsaPlaceStepArr bits weight r j)) := by
    intro j r
    by_cases hj : weight ≤ j ∧ j < weight + bits.length
    · rw [if_pos hj]
      show ForInStep.yield (r.modify j fun c => c ++ [bits.getD (j - weight) false])
        = ForInStep.yield (mcsaPlaceStepArr bits weight r j)
      rw [mcsaPlaceStepArr, if_pos hj]
    · rw [if_neg hj]
      show ForInStep.yield r = ForInStep.yield (mcsaPlaceStepArr bits weight r j)
      rw [mcsaPlaceStepArr, if_neg hj]
  rw [funext fun j => funext fun r => hstep j r]
  exact List.forIn_pure_yield_eq_foldl (m := Id)
    (f := fun j r => mcsaPlaceStepArr bits weight r j) _

/-- 【桥接】mulColumns = 外层行 foldl（Array 层） -/
theorem mcsaColumns_eq {len : Nat} (a b : BitVec len) :
    mulColumns a b = (mulRowIndices len).foldl
      (fun cols i => mcsaPlaceRowArr cols (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len))
      (Array.replicate (2 * len) []) := by
  have hbody : ∀ (i : Nat) (r : Array (List Bool)),
      (match mulRowBits a b i with
      | (bits, weight) => do
          let r2 ← forIn (m := Id) (List.range (2 * len)) r fun j r2 =>
            if weight ≤ j ∧ j < weight + bits.length then
              (do pure PUnit.unit
                  pure (ForInStep.yield (r2.modify j fun c => c ++ [bits.getD (j - weight) false])))
            else
              (do pure PUnit.unit
                  pure (ForInStep.yield r2))
          pure (ForInStep.yield r2))
      = pure (ForInStep.yield
          (mcsaPlaceRowArr r (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len))) := by
    intro i r
    obtain ⟨bits, weight⟩ := mulRowBits a b i
    show ForInStep.yield (forIn (m := Id) (List.range (2 * len)) r (fun j r2 =>
        if weight ≤ j ∧ j < weight + bits.length then
          (do pure PUnit.unit
              pure (ForInStep.yield (r2.modify j fun c => c ++ [bits.getD (j - weight) false])))
        else
          (do pure PUnit.unit
              pure (ForInStep.yield r2))))
      = ForInStep.yield (mcsaPlaceRowArr r bits weight (2 * len))
    exact congrArg _ (mcsaInnerForIn r bits weight (2 * len))
  rw [show mulColumns a b = (forIn (m := Id) (mulRowIndices len)
      (Array.replicate (2 * len) [])
      (fun i r => match mulRowBits a b i with
      | (bits, weight) => do
          let r2 ← forIn (m := Id) (List.range (2 * len)) r fun j r2 =>
            if weight ≤ j ∧ j < weight + bits.length then
              (do pure PUnit.unit
                  pure (ForInStep.yield (r2.modify j fun c => c ++ [bits.getD (j - weight) false])))
            else
              (do pure PUnit.unit
                  pure (ForInStep.yield r2))
          pure (ForInStep.yield r2))).run from rfl]
  rw [funext fun i => funext fun r => hbody i r]
  exact List.forIn_pure_yield_eq_foldl (m := Id)
    (f := fun i cols =>
      mcsaPlaceRowArr cols (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len)) _

/-- placeRowArr 保持 Array 大小 -/
theorem mcsaPlaceRowArr_size (r : Array (List Bool)) (bits : List Bool) (weight n : Nat) :
    (mcsaPlaceRowArr r bits weight n).size = r.size := by
  suffices h : ∀ (js : List Nat) (r : Array (List Bool)),
      (js.foldl (mcsaPlaceStepArr bits weight) r).size = r.size from h _ _
  intro js r
  induction js generalizing r with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, ih]
    unfold mcsaPlaceStepArr
    split
    · rw [Array.size_modify]
    · rfl

/-- placeRowArr 的 toList = 列表版 foldl -/
theorem mcsaPlaceRowArr_toList (r : Array (List Bool)) (bits : List Bool) (weight n : Nat) :
    (mcsaPlaceRowArr r bits weight n).toList
    = (List.range n).foldl (mcsaPlaceStep bits weight) r.toList := by
  suffices h : ∀ (js : List Nat) (r : Array (List Bool)),
      (js.foldl (mcsaPlaceStepArr bits weight) r).toList
        = js.foldl (mcsaPlaceStep bits weight) r.toList from h _ _
  intro js r
  induction js generalizing r with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, List.foldl_cons, ih,
      show (mcsaPlaceStepArr bits weight r j).toList = mcsaPlaceStep bits weight r.toList j from by
        unfold mcsaPlaceStepArr mcsaPlaceStep
        rw [apply_ite Array.toList, Array.toList_modify] ]

/-- mulColumns 的列数 = 2·len -/
theorem mcsaColumns_size {len : Nat} (a b : BitVec len) : (mulColumns a b).size = 2 * len := by
  rw [mcsaColumns_eq]
  suffices h : ∀ (rows : List Nat) (cols : Array (List Bool)), cols.size = 2 * len →
      (rows.foldl (fun cols i =>
        mcsaPlaceRowArr cols (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len)) cols).size
        = 2 * len from
    h _ _ Array.size_replicate
  intro rows cols hcols
  induction rows generalizing cols with
  | nil => exact hcols
  | cons i rest ih =>
    rw [List.foldl_cons]
    exact ih _ (by rw [mcsaPlaceRowArr_size, hcols])

theorem mcsaColumns_length {len : Nat} (a b : BitVec len) :
    (mulColumns a b).toList.length = 2 * len := by
  rw [Array.length_toList, mcsaColumns_size]

/-- 单行放置 foldl 保持列表长度 -/
theorem mcsaPlaceFold_length (l0 : List (List Bool)) (bits : List Bool) (weight n : Nat) :
    ((List.range n).foldl (mcsaPlaceStep bits weight) l0).length = l0.length := by
  induction n generalizing l0 with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    show (if weight ≤ k ∧ k < weight + bits.length then
        ((List.range k).foldl (mcsaPlaceStep bits weight) l0).modify k
          (· ++ [bits.getD (k - weight) false])
      else ((List.range k).foldl (mcsaPlaceStep bits weight) l0)).length = l0.length
    split
    · rw [List.length_modify, ih]
    · exact ih l0

/-- 单位位列表的位权和 -/
theorem mcsaBitsVal_singleton (b : Bool) : mcsaBitsVal [b] = b.toNat := by
  simp [mcsaBitsVal]

/-- 向第 j 列追加一位的列加权和变化（j 在界内） -/
theorem mcsaColsVal_modify_append (l : List (List Bool)) (j : Nat) (b : Bool)
    (hj : j < l.length) :
    mcsaColsVal (l.modify j (· ++ [b])) = mcsaColsVal l + 2 ^ j * b.toNat := by
  induction l generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero =>
      rw [List.modify_zero_cons]
      simp only [mcsaColsVal, mcsaColVal_append, mcsaColVal, Nat.pow_zero, Nat.one_mul,
        Nat.add_zero]
      omega
    | succ j =>
      rw [List.modify_succ_cons]
      simp only [mcsaColsVal]
      rw [List.length_cons] at hj
      rw [ih j (by omega), Nat.pow_succ]
      conv => lhs; rw [Nat.left_distrib]
      conv => rhs; rw [Nat.mul_assoc, Nat.mul_left_comm]
      omega

/-- 单行放置 foldl 的值不变式：加上 2^weight ×（截断行位权和） -/
theorem mcsaPlaceFold_colsVal (l0 : List (List Bool)) (bits : List Bool) (weight n : Nat)
    (hlen : n ≤ l0.length) :
    mcsaColsVal ((List.range n).foldl (mcsaPlaceStep bits weight) l0)
    = mcsaColsVal l0 + 2 ^ weight * mcsaBitsVal (bits.take (n - weight)) := by
  induction n with
  | zero => simp [mcsaBitsVal]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlenk : k ≤ l0.length := by omega
    have hkk : k < ((List.range k).foldl (mcsaPlaceStep bits weight) l0).length := by
      rw [mcsaPlaceFold_length]; omega
    show mcsaColsVal (if weight ≤ k ∧ k < weight + bits.length then
        ((List.range k).foldl (mcsaPlaceStep bits weight) l0).modify k
          (· ++ [bits.getD (k - weight) false])
      else ((List.range k).foldl (mcsaPlaceStep bits weight) l0))
      = mcsaColsVal l0 + 2 ^ weight * mcsaBitsVal (bits.take (k + 1 - weight))
    by_cases hcond : weight ≤ k ∧ k < weight + bits.length
    · rw [if_pos hcond, mcsaColsVal_modify_append _ _ _ hkk, ih hlenk]
      have hk1 : k + 1 - weight = k - weight + 1 := by omega
      have hkm : k - weight < bits.length := by omega
      have hget : bits.getD (k - weight) false = bits[k - weight] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkm, Option.getD_some]
      rw [hk1, ← List.take_append_getElem hkm, mcsaBitsVal_append, List.length_take,
        show min (k - weight) bits.length = k - weight from by omega, mcsaBitsVal_singleton,
        hget]
      have hkk2 : 2 ^ k = 2 ^ weight * 2 ^ (k - weight) := by
        conv => lhs; rw [← show weight + (k - weight) = k from by omega]
        rw [Nat.pow_add]
      rw [hkk2, Nat.mul_assoc, Nat.left_distrib]
      omega
    · rw [if_neg hcond, ih hlenk]
      by_cases hw : k < weight
      · have h0a : k + 1 - weight = 0 := by omega
        have h0b : k - weight = 0 := by omega
        rw [h0a, h0b]
      · have hcond' : ¬ k < weight + bits.length := fun h => hcond ⟨by omega, h⟩
        have hkm : bits.length ≤ k - weight := by omega
        have hkm1 : bits.length ≤ k + 1 - weight := by omega
        rw [List.take_of_length_le hkm, List.take_of_length_le hkm1]

/-- 外层行 foldl 的值：逐行贡献累加 -/
theorem mcsaOuterFold_colsVal {len : Nat} (a b : BitVec len) (rows : List Nat)
    (cols0 : Array (List Bool)) (hsize : cols0.size = 2 * len) :
    mcsaColsVal ((rows.foldl (fun cols i =>
        mcsaPlaceRowArr cols (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len)) cols0).toList)
    = mcsaColsVal cols0.toList
      + (rows.map fun i => 2 ^ (mulRowBits a b i).2
          * mcsaBitsVal ((mulRowBits a b i).1.take (2 * len - (mulRowBits a b i).2))).sum := by
  induction rows generalizing cols0 with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (by rw [mcsaPlaceRowArr_size, hsize])]
    rw [mcsaPlaceRowArr_toList,
      mcsaPlaceFold_colsVal _ _ _ _ (by rw [Array.length_toList, hsize]; exact Nat.le_refl _)]
    omega

/-- 初始列阵列的加权列和 = 逐行贡献之和 -/
theorem mcsaColumns_colsVal (a b : BitVec 33) :
    mcsaColsVal (mulColumns a b).toList
    = ((mulRowIndices 33).map fun i => 2 ^ (mulRowBits a b i).2
        * mcsaBitsVal ((mulRowBits a b i).1.take (2 * 33 - (mulRowBits a b i).2))).sum := by
  rw [mcsaColumns_eq, mcsaOuterFold_colsVal a b _ _ Array.size_replicate]
  rw [Array.toList_replicate, mcsaColsVal_replicate_nil, Nat.zero_add]

/-- mulBvBits 长度 -/
theorem mcsaBvBits_length {w : Nat} (v : BitVec w) : (mulBvBits v).length = w := by
  simp [mulBvBits]

/- ---- 行内容/权重的分情形展开（kind 引理） ---- -/

theorem mcsaRowBits0 (a b : BitVec 33) :
    mulRowBits a b 0 = (mulBvBits (mulPpRow0 (mulPpTemp (mulWindow a 0) b)), 0) := by
  unfold mulRowBits
  rw [if_pos rfl]

theorem mcsaRowBitsLastBranch (a b : BitVec 33) (i : Nat) (h : i = 32 ∨ i = 31) :
    mulRowBits a b i
    = (mulBvBits (mulPpRowLast (mulPpTemp (mulWindow a i) b) (mulT (mulWindow a (i - 2)))),
       i - 2) := by
  have h0 : i ≠ 0 := by omega
  unfold mulRowBits
  simp only [if_neg h0, if_pos (show i = 33 - 1 ∨ i = 33 - 2 from by omega)]

theorem mcsaRowBitsMid (a b : BitVec 33) (i : Nat) (h0 : i ≠ 0) (h31 : i ≠ 31) (h32 : i ≠ 32) :
    mulRowBits a b i
    = (mulBvBits (mulPpRowMid (mulPpTemp (mulWindow a i) b) (mulT (mulWindow a (i - 2)))),
       i - 2) := by
  unfold mulRowBits
  simp only [if_neg h0, if_neg (show ¬ (i = 33 - 1 ∨ i = 33 - 2) from by omega)]

theorem mcsaPlacedRow0 (a b : BitVec 33) :
    mulPlacedRow a b 0 = BitVec.zeroExtend 66 (mulPpRow0 (mulPpTemp (mulWindow a 0) b)) := by
  unfold mulPlacedRow
  rw [if_pos rfl]

theorem mcsaPlacedRow32 (a b : BitVec 33) :
    mulPlacedRow a b 32
    = (BitVec.zeroExtend 66 (mulPpRowLast (mulPpTemp (mulWindow a 32) b)
        (mulT (mulWindow a (32 - 2))))) <<< (32 - 2) := by
  unfold mulPlacedRow
  rw [if_neg (by decide : ¬ (32 = 0)), if_pos (by omega : 32 = 32 ∨ 32 = 31)]

theorem mcsaPlacedRowMid (a b : BitVec 33) (i : Nat) (h0 : i ≠ 0) (h31 : i ≠ 31) (h32 : i ≠ 32) :
    mulPlacedRow a b i
    = (BitVec.zeroExtend 66 (mulPpRowMid (mulPpTemp (mulWindow a i) b)
        (mulT (mulWindow a (i - 2))))) <<< (i - 2) := by
  unfold mulPlacedRow
  rw [if_neg h0, if_neg (show ¬ (i = 32 ∨ i = 31) from by omega)]

/- ---- 逐行贡献 = mulPlacedRow.toNat（精确 Nat 等式，无需 mod） ---- -/

/-- 首行（i=0，权 0，无截断） -/
theorem mcsaContrib0 (a b : BitVec 33) :
    2 ^ (mulRowBits a b 0).2 * mcsaBitsVal ((mulRowBits a b 0).1.take (2 * 33 - (mulRowBits a b 0).2))
      = (mulPlacedRow a b 0).toNat := by
  rw [mcsaRowBits0, mcsaPlacedRow0]
  show 2 ^ 0 * mcsaBitsVal ((mulBvBits (mulPpRow0 (mulPpTemp (mulWindow a 0) b))).take (2 * 33 - 0))
    = (BitVec.zeroExtend 66 (mulPpRow0 (mulPpTemp (mulWindow a 0) b))).toNat
  generalize mulPpRow0 (mulPpTemp (mulWindow a 0) b) = v
  rw [List.take_of_length_le (by rw [mcsaBvBits_length]; decide), mcsaBitsVal_bvBits,
    show BitVec.zeroExtend 66 v = BitVec.setWidth 66 v from rfl, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
      (Nat.pow_le_pow_right (by decide) (by decide : 33 + 4 ≤ 66)))]
  simp

/-- 中间行（i 偶，2 ≤ i ≤ 30；权 i-2，无截断无回绕） -/
theorem mcsaContribMid (a b : BitVec 33) (i : Nat)
    (h0 : i ≠ 0) (h31 : i ≠ 31) (h32 : i ≠ 32) (hi : i ≤ 30) :
    2 ^ (mulRowBits a b i).2 * mcsaBitsVal ((mulRowBits a b i).1.take (2 * 33 - (mulRowBits a b i).2))
      = (mulPlacedRow a b i).toNat := by
  rw [mcsaRowBitsMid a b i h0 h31 h32, mcsaPlacedRowMid a b i h0 h31 h32]
  show 2 ^ (i - 2) * mcsaBitsVal ((mulBvBits (mulPpRowMid (mulPpTemp (mulWindow a i) b)
      (mulT (mulWindow a (i - 2))))).take (2 * 33 - (i - 2)))
    = ((BitVec.zeroExtend 66 (mulPpRowMid (mulPpTemp (mulWindow a i) b)
        (mulT (mulWindow a (i - 2))))) <<< (i - 2)).toNat
  generalize mulPpRowMid (mulPpTemp (mulWindow a i) b) (mulT (mulWindow a (i - 2))) = v
  rw [List.take_of_length_le (by rw [mcsaBvBits_length]; omega), mcsaBitsVal_bvBits,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show BitVec.zeroExtend 66 v = BitVec.setWidth 66 v from rfl, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
      (Nat.pow_le_pow_right (by decide) (by decide : 33 + 5 ≤ 66))),
    Nat.mod_eq_of_lt (by
      have h1 := BitVec.isLt v
      calc v.toNat * 2 ^ (i - 2)
          < 2 ^ (33 + 5) * 2 ^ (i - 2) := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
        _ = 2 ^ (33 + 5 + (i - 2)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ 66 := Nat.pow_le_pow_right (by decide) (by omega))]
  rw [Nat.mul_comm]

/-- 末行（i=32，权 30，第 36 位 ~s 被列界限截断 = mod 2^66，D5） -/
theorem mcsaContribLast (a b : BitVec 33) :
    2 ^ (mulRowBits a b 32).2
      * mcsaBitsVal ((mulRowBits a b 32).1.take (2 * 33 - (mulRowBits a b 32).2))
      = (mulPlacedRow a b 32).toNat := by
  rw [mcsaRowBitsLastBranch a b 32 (by omega), mcsaPlacedRow32]
  show 2 ^ 30 * mcsaBitsVal ((mulBvBits (mulPpRowLast (mulPpTemp (mulWindow a 32) b)
      (mulT (mulWindow a 30)))).take 36)
    = ((BitVec.zeroExtend 66 (mulPpRowLast (mulPpTemp (mulWindow a 32) b)
        (mulT (mulWindow a 30)))) <<< 30).toNat
  generalize mulPpRowLast (mulPpTemp (mulWindow a 32) b) (mulT (mulWindow a 30)) = v
  rw [show (mulBvBits v).take 36 = (List.range 36).map v.getLsbD from by
    unfold mulBvBits
    rw [← List.map_take, List.take_range]
    congr 1,
    mcsaBitsVal_range_getLsbD, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show BitVec.zeroExtend 66 v = BitVec.setWidth 66 v from rfl, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
      (Nat.pow_le_pow_right (by decide) (by decide : 33 + 4 ≤ 66)))]
  -- 2^30 · (v % 2^36) = (v · 2^30) % 2^66：高位截断的算术实现
  have hbound : v.toNat % 2 ^ 36 * 2 ^ 30 < 2 ^ 66 := by
    have hm := Nat.mod_lt v.toNat (Nat.two_pow_pos 36)
    calc v.toNat % 2 ^ 36 * 2 ^ 30
        < 2 ^ 36 * 2 ^ 30 := (Nat.mul_lt_mul_right (Nat.two_pow_pos 30)).mpr hm
      _ = 2 ^ 66 := by rw [← Nat.pow_add]
  have h1 := Nat.mod_add_div v.toNat (2 ^ 36)
  conv => rhs; rw [← h1]
  rw [Nat.add_mul, Nat.mul_right_comm, ← Nat.pow_add, show (36 : Nat) + 30 = 66 from rfl,
    Nat.add_mul_mod_self_left]
  conv => rhs; rw [Nat.mod_eq_of_lt hbound]
  rw [Nat.mul_comm]

/-- 行下标表（具体列表，decide 核算） -/
theorem mcsaRowIndices33 : mulRowIndices 33
    = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32] := by
  decide

/-- 初始列加权和 = Σ mulPlacedRow.toNat（精确等式） -/
theorem mcsaColumns_colsVal_eq (a b : BitVec 33) :
    mcsaColsVal (mulColumns a b).toList
    = ((mulRowIndices 33).map fun i => (mulPlacedRow a b i).toNat).sum := by
  rw [mcsaColumns_colsVal, mcsaRowIndices33]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [mcsaContrib0 a b, mcsaContribLast a b,
    mcsaContribMid a b 2 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 4 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 6 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 8 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 10 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 12 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 14 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 16 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 18 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 20 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 22 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 24 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 26 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 28 (by decide) (by decide) (by decide) (by decide),
    mcsaContribMid a b 30 (by decide) (by decide) (by decide) (by decide)]

/-- (a % n + b) % n = (a + b) % n（核心库缺此向） -/
theorem mcsaNat_add_mod_left (a b n : Nat) : (a % n + b) % n = (a + b) % n := by
  have h2 : (a % n + b) % n = (a % n + b % n) % n := by
    conv => lhs; rw [show b = b % n + n * (b / n) from (Nat.mod_add_div b n).symm]
    rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]
  rw [h2, ← Nat.add_mod]

/-- mulPlacedSum 的 toNat = 逐行 toNat 之和 mod 2^66 -/
theorem mcsaPlacedSum_toNat (a b : BitVec 33) :
    (mulPlacedSum a b).toNat
    = ((mulRowIndices 33).map fun i => (mulPlacedRow a b i).toNat).sum % 2 ^ 66 := by
  rw [mcsaRowIndices33]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  unfold mulPlacedSum
  simp only [BitVec.toNat_add, mcsaNat_add_mod_left]
  omega

/- ========================================================================= -/
/- 7b. 形状收尾：mulColumns 的列长与 a b 取值无关，收敛形状由具体计算钉死       -/
/- =========================================================================-/

/-- modify 的 getD 刻画（i 在界内） -/
theorem mcsaGetD_modify (l : List (List Bool)) (i j : Nat) (b : Bool) (hi : i < l.length) :
    (l.modify i (· ++ [b])).getD j [] = if i = j then l.getD j [] ++ [b] else l.getD j [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩]
  · rw [if_neg h, List.getD_eq_getElem?_getD]
    have hid : (fun a : List Bool => if i = j then a ++ [b] else a) = id := by
      funext a
      rw [if_neg h]
      rfl
    rw [hid]
    simp

/-- 单行放置 foldl 的逐列内容刻画 -/
theorem mcsaPlaceFold_getD (l0 : List (List Bool)) (bits : List Bool) (weight n j : Nat)
    (hlen : n ≤ l0.length) :
    ((List.range n).foldl (mcsaPlaceStep bits weight) l0).getD j []
    = if j < n ∧ weight ≤ j ∧ j < weight + bits.length
      then l0.getD j [] ++ [bits.getD (j - weight) false]
      else l0.getD j [] := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlenk : k ≤ l0.length := by omega
    have hkk : k < ((List.range k).foldl (mcsaPlaceStep bits weight) l0).length := by
      rw [mcsaPlaceFold_length]; omega
    show (if weight ≤ k ∧ k < weight + bits.length then
        ((List.range k).foldl (mcsaPlaceStep bits weight) l0).modify k
          (· ++ [bits.getD (k - weight) false])
      else ((List.range k).foldl (mcsaPlaceStep bits weight) l0)).getD j [] = _
    by_cases hcond : weight ≤ k ∧ k < weight + bits.length
    · rw [if_pos hcond, mcsaGetD_modify _ _ _ _ hkk, ih hlenk]
      by_cases hjk : k = j
      · subst hjk
        rw [if_pos rfl, if_neg (fun h => absurd h.1 (by omega)),
          if_pos ⟨by omega, hcond⟩]
      · rw [if_neg hjk]
        by_cases hjn : j < k
        · by_cases hcj : weight ≤ j ∧ j < weight + bits.length
          · rw [if_pos ⟨hjn, hcj⟩, if_pos ⟨by omega, hcj⟩]
          · rw [if_neg (fun h => hcj h.2), if_neg (fun h => hcj h.2)]
        · rw [if_neg (fun h => hjn h.1), if_neg (fun h => absurd h.1 (by omega))]
    · rw [if_neg hcond, ih hlenk]
      by_cases hjk : j = k
      · subst hjk
        rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => hcond h.2)]
      · by_cases hjn : j < k
        · by_cases hcj : weight ≤ j ∧ j < weight + bits.length
          · rw [if_pos ⟨hjn, hcj⟩, if_pos ⟨by omega, hcj⟩]
          · rw [if_neg (fun h => hcj h.2), if_neg (fun h => hcj h.2)]
        · rw [if_neg (fun h => hjn h.1), if_neg (fun h => absurd h.1 (by omega))]

/-- 外层行 foldl 的逐列内容刻画 -/
theorem mcsaOuterFold_getD {len : Nat} (a b : BitVec len) (rows : List Nat)
    (cols0 : Array (List Bool)) (j : Nat) (hsize : cols0.size = 2 * len) :
    ((rows.foldl (fun cols i =>
        mcsaPlaceRowArr cols (mulRowBits a b i).1 (mulRowBits a b i).2 (2 * len)) cols0).toList).getD j []
    = rows.foldl (fun c i =>
        if j < 2 * len ∧ (mulRowBits a b i).2 ≤ j
            ∧ j < (mulRowBits a b i).2 + (mulRowBits a b i).1.length
        then c ++ [(mulRowBits a b i).1.getD (j - (mulRowBits a b i).2) false]
        else c) (cols0.toList.getD j []) := by
  induction rows generalizing cols0 with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih _ (by rw [mcsaPlaceRowArr_size, hsize]), List.foldl_cons,
      mcsaPlaceRowArr_toList,
      mcsaPlaceFold_getD _ _ _ _ _ (by rw [Array.length_toList, hsize]; exact Nat.le_refl _)]

/-- 条件追加 foldl 的累计长度 = 满足条件的行数 -/
theorem mcsaAppendFold_length (rows : List Nat) (cond : Nat → Prop) [∀ i, Decidable (cond i)]
    (bit : Nat → Bool) (acc : List Bool) :
    (rows.foldl (fun c i => if cond i then c ++ [bit i] else c) acc).length
    = acc.length + (rows.filter fun i => decide (cond i)).length := by
  induction rows generalizing acc with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, List.filter_cons, ih]
    by_cases hci : cond i
    · rw [if_pos hci]
      simp [hci]
      omega
    · rw [if_neg hci]
      simp [hci]

/-- len=33 的行权重（与 a b 无关） -/
def mcsaRowWeight33 (i : Nat) : Nat := if i = 0 then 0 else i - 2

/-- len=33 的行位长（与 a b 无关） -/
def mcsaRowLen33 (i : Nat) : Nat := if i = 0 then 37 else if i = 32 ∨ i = 31 then 37 else 38

/-- 行 i 是否覆盖列 j（纯数值谓词） -/
def mcsaRowCover33 (i j : Nat) : Bool :=
  decide (j < 66 ∧ mcsaRowWeight33 i ≤ j ∧ j < mcsaRowWeight33 i + mcsaRowLen33 i)

/-- len=33 的初始列长表（纯数值，供形状模拟求值） -/
def mcsaInitLens33 : List Nat :=
  (List.range 66).map fun j => ((mulRowIndices 33).filter fun i => mcsaRowCover33 i j).length

theorem mcsaRowBits_weight33 (a b : BitVec 33) (i : Nat) :
    (mulRowBits a b i).2 = mcsaRowWeight33 i := by
  by_cases h0 : i = 0
  · subst h0
    rw [mcsaRowBits0]
    rfl
  · by_cases h3231 : i = 32 ∨ i = 31
    · rw [mcsaRowBitsLastBranch a b i h3231]
      show i - 2 = mcsaRowWeight33 i
      unfold mcsaRowWeight33
      rw [if_neg h0]
    · rw [mcsaRowBitsMid a b i h0 (fun h => h3231 (.inr h)) (fun h => h3231 (.inl h))]
      show i - 2 = mcsaRowWeight33 i
      unfold mcsaRowWeight33
      rw [if_neg h0]

theorem mcsaRowBits_length33 (a b : BitVec 33) (i : Nat) :
    (mulRowBits a b i).1.length = mcsaRowLen33 i := by
  by_cases h0 : i = 0
  · subst h0
    rw [mcsaRowBits0]
    show (mulBvBits (mulPpRow0 (mulPpTemp (mulWindow a 0) b))).length = mcsaRowLen33 0
    rw [mcsaBvBits_length]
    rfl
  · by_cases h3231 : i = 32 ∨ i = 31
    · rw [mcsaRowBitsLastBranch a b i h3231]
      show (mulBvBits (mulPpRowLast (mulPpTemp (mulWindow a i) b)
          (mulT (mulWindow a (i - 2))))).length = mcsaRowLen33 i
      rw [mcsaBvBits_length]
      unfold mcsaRowLen33
      rw [if_neg h0, if_pos h3231]
    · rw [mcsaRowBitsMid a b i h0 (fun h => h3231 (.inr h)) (fun h => h3231 (.inl h))]
      show (mulBvBits (mulPpRowMid (mulPpTemp (mulWindow a i) b)
          (mulT (mulWindow a (i - 2))))).length = mcsaRowLen33 i
      rw [mcsaBvBits_length]
      unfold mcsaRowLen33
      rw [if_neg h0, if_neg h3231]

/-- 覆盖条件等价（电路层谓词 = 纯数值谓词） -/
theorem mcsaRowCond_eq (a b : BitVec 33) (i j : Nat) :
    (j < 2 * 33 ∧ (mulRowBits a b i).2 ≤ j ∧ j < (mulRowBits a b i).2 + (mulRowBits a b i).1.length)
    = (j < 66 ∧ mcsaRowWeight33 i ≤ j ∧ j < mcsaRowWeight33 i + mcsaRowLen33 i) := by
  rw [mcsaRowBits_weight33, mcsaRowBits_length33]

/-- mcsaInitLens33 的逐点展开 -/
theorem mcsaInitLens33_getElem (i : Nat) (h : i < mcsaInitLens33.length) :
    mcsaInitLens33[i]'h = ((mulRowIndices 33).filter fun i' => mcsaRowCover33 i' i).length := by
  unfold mcsaInitLens33
  rw [List.getElem_map, List.getElem_range]

/-- 初始列阵列的列长 = 纯数值形状表 -/
theorem mcsaColumns_map_length (a b : BitVec 33) :
    ((mulColumns a b).toList.map List.length) = mcsaInitLens33 := by
  apply List.ext_getElem
  · rw [List.length_map, mcsaColumns_length]
    unfold mcsaInitLens33
    rw [List.length_map, List.length_range]
  · intro i h1 h2
    have h1' : i < (mulColumns a b).toList.length := by
      rw [List.length_map] at h1; exact h1
    rw [List.getElem_map, List.getElem_eq_getD (h := h1') ([] : List Bool),
      mcsaColumns_eq, mcsaOuterFold_getD _ _ _ _ _ Array.size_replicate,
      Array.toList_replicate]
    have hbase : (List.replicate (2 * 33) ([] : List Bool)).getD i [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp
    rw [hbase,
      mcsaAppendFold_length (cond := fun i' =>
        i < 2 * 33 ∧ (mulRowBits a b i').2 ≤ i
          ∧ i < (mulRowBits a b i').2 + (mulRowBits a b i').1.length)
        (bit := fun i' => (mulRowBits a b i').1.getD (i - (mulRowBits a b i').2) false)
        (acc := []),
      List.length_nil, Nat.zero_add]
    rw [mcsaInitLens33_getElem i h2]
    apply congrArg List.length
    apply List.filter_congr
    intro i' _
    show decide (i < 2 * 33 ∧ (mulRowBits a b i').2 ≤ i
        ∧ i < (mulRowBits a b i').2 + (mulRowBits a b i').1.length)
      = decide (i < 66 ∧ mcsaRowWeight33 i' ≤ i ∧ i < mcsaRowWeight33 i' + mcsaRowLen33 i')
    exact decide_eq_decide.mpr (Iff.of_eq (mcsaRowCond_eq a b i' i))

/-- 【7b 核心】len=33 的压缩形状：12 轮内收敛到每列 ≤ 2 位（具体数值计算，
    内核 decide 求值——形状链已切换为结构递归的 mcsaShapeAOCF） -/
theorem mcsaShape33_final :
    (mcsaShapeCompress 12 mcsaInitLens33).all (fun l => decide (l ≤ 2)) = true := by
  decide

/-- 形状实例：len=33 压缩终态每列 ≤ 2 位 -/
theorem mcsaFin33_all_le2 (a b : BitVec 33) :
    ∀ c ∈ mulCompress 12 (mulColumns a b).toList, c.length ≤ 2 := by
  intro c hc
  have hmem : c.length ∈ (mulCompress 12 (mulColumns a b).toList).map List.length :=
    List.mem_map_of_mem hc
  rw [mcsaCompress_map_length, mcsaColumns_map_length] at hmem
  have hall := mcsaShape33_final
  rw [List.all_eq_true] at hall
  exact of_decide_eq_true (hall _ hmem)

/- ========================================================================= -/
/- 主定理与公理审计                                                            -/
/- =========================================================================-/

/-- 【主定理】电路层 mulDataModule = 算术层 mulPlacedSum（len=33，符号 a b 全证）。
    压缩终态形状前提由 mcsaFin33_all_le2 提供（mcsaShape33_final 现为内核
    decide 求值，无 ofReduceBool，两个版本公理同为标准三公理）。 -/
theorem mcsaDataModule33_eq_placedSum (a b : BitVec 33)
    (hfin : ∀ c ∈ mulCompress 12 (mulColumns a b).toList, c.length ≤ 2) :
    mulDataModule a b = mulPlacedSum a b := by
  have hcols : (mulColumns a b).toList.length = 66 := mcsaColumns_length a b
  have hfinlen : (mulCompress 12 (mulColumns a b).toList).length = 66 := by
    rw [mcsaCompress_length, hcols]
  apply BitVec.eq_of_toNat_eq
  show ((mulBitsToBv (w := 66) ((mulCompress 12 (mulColumns a b).toList).map fun c =>
        c.getD 0 false))
      + (mulBitsToBv (w := 66) ((mulCompress 12 (mulColumns a b).toList).map fun c =>
        c.getD 1 false))).toNat
    = (mulPlacedSum a b).toNat
  rw [mcsaSumCarry_toNat _ hfinlen hfin]
  have hinv := mcsaCompress_invariant 12 (mulColumns a b).toList
  rw [hcols] at hinv
  rw [hinv, mcsaColumns_colsVal_eq, mcsaPlacedSum_toNat]

/-- 主定理的无条件形式（经由 mcsaFin33_all_le2；mcsaShape33_final 已改内核
    decide，公理审计为 [propext, Classical.choice, Quot.sound]，无 ofReduceBool） -/
theorem mcsaDataModule33_eq_placedSum' (a b : BitVec 33) :
    mulDataModule a b = mulPlacedSum a b :=
  mcsaDataModule33_eq_placedSum a b (mcsaFin33_all_le2 a b)

#print axioms mcsaDataModule33_eq_placedSum
#print axioms mcsaDataModule33_eq_placedSum'

end Ventus.Arith
