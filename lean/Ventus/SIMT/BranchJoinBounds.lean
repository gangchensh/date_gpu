/- ========================================================================= -/
/-                  SIMT/BranchJoinBounds.lean                               -/
/-  bug 报告 I-2 的收口：合法执行下 branch_join_stack 不溢出（wr ≤ depth）    -/
/-                                                                           -/
/-  背景（03 报告 I-2【机制属实/当前不可达】，BranchJoinOverflow.lean 文件头）： -/
/-  branch_join 栈深 depth_stack = num_thread = 32（pipe.scala:129）恰好按    -/
/-  最坏情况定尺寸。论证链条：                                                -/
/-   (1) 掩码纪律：vbranch 的 mask_init = 指令掩码 ∧ simt_stack.out_mask      -/
/-       （pipe.scala:366），out_mask = thread_masks(wid) 即当前活跃掩码       -/
/-       （branch_join.scala:260）⇒ mask_init ⊆ 活跃掩码；                   -/
/-   (2) takeif 恒选小边（branch_join.scala:145）：taken 路径掩码 popcount     -/
/-       每级至多减半 ⇒ 纯 taken 路径嵌套 ≤ 5 级（32→16→8→4→2→1）；           -/
/-   (3) 逐线程剥离只发生在大边（pushed 路径），且 pushed 路径要等 taken 路径  -/
/-       到 join、先弹路径项才开始执行 ⇒ 每级净占 1 项而非 2 项；             -/
/-   (4) LIFO 弹栈（:57-59）+ RPC 项与路径项配对（:48-56）。                 -/
/-  结论：最深 31 级剥离时栈占用 30（外层 RPC 项）+ 2（最深级两项）= 32。     -/
/-                                                                           -/
/- ======================== 本文件的形式化分层 ============================= -/
/-  §1 PopCount 位级引理（全证）：划分引理、子掩码单调、非零掩码 popcount ≥ 1。 -/
/-  §2 takeif 减半引理（全证）：分化时 taken 侧 popcount ×2 ≤ maskInit 的      -/
/-     popcount；掩码纪律（maskInit ⊆ tmask）⇒ popcount 单调（全证）。        -/
/-  §3 抽象协议模型（全证，任意深度任意步数）：把"层级 = (本层 maskInit 的     -/
/-     popcount m, push 时活跃掩码 popcount hi, 路径项是否在栈 path)"抽象成    -/
/-     Nat 状态，事件 = nop/shrink/push/pop（合法性守卫内置于 step，非法事件   -/
/-     建模为无操作，pop 无守卫＝对真实 join 时机的上近似）。主定理            -/
/-     bjbMain_no_overflow：合法状态下任意事件序列后 wr ≤ 32 且合法性保持。    -/
/-     另有紧密度见证：31 级剥离轨迹在抽象模型上 wr 恰好达到 32（native_decide）。 -/
/-  §4 具体模型桥接（部分降级，明示）：                                        -/
/-     (a) wr 簿记引理（全证）：分化分支 wr+2、有效 pop wr−1、其他不变；      -/
/-     (b) 具体最坏轨迹（native_decide）：nT=depth=6 的 5 级剥离，峰值 wr=6=   -/
/-         depth，逐拍断言掩码纪律成立且 wr ≤ depth，最终排空；               -/
/-         nT=depth=32 的 5 级对半嵌套，wr=10 ≤ 32。                         -/
/-  ★ 降级点（未证部分，逐条列出）：具体模型 → 抽象模型的全精化（要求把具体    -/
/-    轨迹按 bjDivOccur/bjStackJump 对齐到抽象事件并跟踪 cur = popcount tmask   -/
/-    与栈项 popcount 的对应）未证明。该精化所需的全部事实性假设即上列 (1)-(4)， -/
/-    其中 (2) 与 (1) 的 popcount 形式已在 §1/§2 全证；(3)(4) 为 Chisel 源码   -/
/-    直接事实（:57-59 LIFO、:48-56 配对），(1) 另含 wid 时序一致性假设        -/
/-    （input_wid 与 branch_ctl_buf.bits.wid 同源，pipe.scala:293）。          -/
/- ========================================================================= -/

import Ventus.SIMT.BranchJoin

namespace Ventus.SIMT

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. PopCount 位级引理（全证）                                               -/
/- ========================================================================= -/

/-- foldl 加法搬家：从任意累加器出发 = 累加器 + 从 0 出发。 -/
theorem bjbFoldl_add {α : Type} (l : List α) (f : α → Nat) (a : Nat) :
    l.foldl (fun acc i => acc + f i) a = a + l.foldl (fun acc i => acc + f i) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (a + f hd), ih (f hd)]
    omega

/-- 逐点拆分：f = f1 + f2 则 foldl 总和拆分（累加器 generalized 版）。 -/
theorem bjbFoldl_split {α : Type} (l : List α) {f f1 f2 : α → Nat}
    (h : ∀ x ∈ l, f x = f1 x + f2 x) (a1 a2 : Nat) :
    l.foldl (fun acc i => acc + f i) (a1 + a2) =
      l.foldl (fun acc i => acc + f1 i) a1 + l.foldl (fun acc i => acc + f2 i) a2 := by
  induction l generalizing a1 a2 with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hh : a1 + a2 + f hd = (a1 + f1 hd) + (a2 + f2 hd) := by
      rw [h hd (by simp)]
      omega
    rw [hh]
    exact ih (fun x hx => h x (List.mem_cons_of_mem hd hx)) (a1 + f1 hd) (a2 + f2 hd)

/-- foldl 总和为 0 则每项为 0。 -/
theorem bjbFoldl_eq_zero {α : Type} (l : List α) (f : α → Nat)
    (h : l.foldl (fun acc i => acc + f i) 0 = 0) : ∀ x ∈ l, f x = 0 := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    rw [List.foldl_cons, bjbFoldl_add] at h
    have hhd : f hd = 0 := by omega
    have htl : tl.foldl (fun acc i => acc + f i) 0 = 0 := by omega
    intro x hx
    rw [List.mem_cons] at hx
    cases hx with
    | inl he => rw [he]; exact hhd
    | inr hm => exact ih htl x hm

/-- 不相交掩码的 popcount 可加（位级核心引理，全证）。 -/
theorem bjbPopcount_or_of_disjoint {n : Nat} {a b : BitVec n} (h : a &&& b = 0) :
    bjPopcount (a ||| b) = bjPopcount a + bjPopcount b := by
  have hpt : ∀ x ∈ List.finRange n,
      (if (a ||| b).getLsbD x.val then 1 else 0) =
        (if a.getLsbD x.val then 1 else 0) + (if b.getLsbD x.val then 1 else 0) := by
    intro x _
    have hbit : (a.getLsbD x.val && b.getLsbD x.val) = false := by
      have hz : (a &&& b).getLsbD x.val = false := by
        rw [h]; simp
      rwa [BitVec.getLsbD_and] at hz
    rw [BitVec.getLsbD_or]
    cases ha : a.getLsbD x.val <;> cases hb : b.getLsbD x.val <;> simp_all
  have hs := bjbFoldl_split (List.finRange n)
    (f := fun i => if (a ||| b).getLsbD i.val then 1 else 0)
    (f1 := fun i => if a.getLsbD i.val then 1 else 0)
    (f2 := fun i => if b.getLsbD i.val then 1 else 0) hpt 0 0
  exact hs

/-- 掩码划分引理：if 侧（v ∧ m）与 else 侧（¬v ∧ m）的 popcount 拼回 m 的 popcount
    （branch_join.scala:141-142 的 popcount 形式）。 -/
theorem bjbPopcount_partition {n : Nat} (v m : BitVec n) :
    bjPopcount (v &&& m) + bjPopcount (~~~v &&& m) = bjPopcount m := by
  have hdisj : (v &&& m) &&& (~~~v &&& m) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases v.getLsbD i <;> simp
  have hor : (v &&& m) ||| (~~~v &&& m) = m := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      hi, decide_true, Bool.true_and]
    cases v.getLsbD i <;> cases m.getLsbD i <;> simp
  have h := bjbPopcount_or_of_disjoint hdisj
  rw [hor] at h
  exact h.symm

/-- 非零掩码的 popcount ≥ 1。 -/
theorem bjbPopcount_pos {n : Nat} {m : BitVec n} (h : m ≠ 0) : 1 ≤ bjPopcount m := by
  apply Decidable.byContradiction
  intro hn
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hpc : bjPopcount m = 0 := by omega
  have hall := bjbFoldl_eq_zero (List.finRange n)
    (fun i => if m.getLsbD i.val then 1 else 0) hpc
  have hbit := hall ⟨i, hi⟩ (List.mem_finRange _)
  have hb : m.getLsbD i = false := by
    cases hc : m.getLsbD i
    · rfl
    · simp [hc] at hbit
  rw [hb]
  exact (BitVec.getLsbD_zero).symm

/-- popcount 子掩码单调：a ⊆ b（a ∧ b = a）⇒ popcount a ≤ popcount b。 -/
theorem bjbPopcount_le_of_sub {n : Nat} {a b : BitVec n} (h : a &&& b = a) :
    bjPopcount a ≤ bjPopcount b := by
  have hdisj : a &&& (~~~a &&& b) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases a.getLsbD i <;> simp
  have hor : a ||| (~~~a &&& b) = b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit : (a.getLsbD i && b.getLsbD i) = a.getLsbD i := by
      have hh := congrArg (fun x : BitVec n => x.getLsbD i) h
      simpa [BitVec.getLsbD_and] using hh
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      hi, decide_true, Bool.true_and]
    cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all
  have hs := bjbPopcount_or_of_disjoint hdisj
  rw [hor] at hs
  omega

/- ========================================================================= -/
/- 2. takeif 减半引理与掩码纪律（全证）                                        -/
/- ========================================================================= -/

/-- 分化 ⟺ 两侧掩码均非零（branch_join.scala:146-148 的展开）。 -/
theorem bjbDivOccur_iff {nT : Nat} (bi : BjBranchIn nT) :
    bjDivOccur bi = true ↔ bjIfMask bi ≠ 0 ∧ bjElseMask bi ≠ 0 := by
  unfold bjDivOccur bjIfOnly bjElseOnly
  cases h1 : (bjElseMask bi == 0) <;> cases h2 : (bjIfMask bi == 0) <;>
    simp_all [beq_iff_eq]

/-- takeif 选 if 侧时，if 侧为小边：2 × |if_mask| ≤ |mask_init|（:145 的 popcount 形式）。 -/
theorem bjbTakeif_if_half {nT : Nat} (bi : BjBranchIn nT)
    (hdiv : bjDivOccur bi = true) (htk : bjTakeif bi = true) :
    2 * bjPopcount (bjIfMask bi) ≤ bjPopcount bi.maskInit := by
  obtain ⟨_, hifo2⟩ := (bjbDivOccur_iff bi).mp hdiv
  have hifo : bjIfOnly bi = false := beq_false_of_ne hifo2
  have hlt : bjPopcount (bjIfMask bi) < bjPopcount (bjElseMask bi) := by
    have h := htk
    unfold bjTakeif at h
    rw [hifo] at h
    simp [hdiv] at h
    exact h
  have hpart := bjbPopcount_partition bi.valuMask bi.maskInit
  unfold bjIfMask bjElseMask at hlt
  show 2 * bjPopcount (bi.valuMask &&& bi.maskInit) ≤ bjPopcount bi.maskInit
  omega

/-- 不 takeif（走 else 侧）时，else 侧为小边：2 × |else_mask| ≤ |mask_init|。 -/
theorem bjbTakeif_else_half {nT : Nat} (bi : BjBranchIn nT)
    (hdiv : bjDivOccur bi = true) (htk : bjTakeif bi = false) :
    2 * bjPopcount (bjElseMask bi) ≤ bjPopcount bi.maskInit := by
  obtain ⟨_, hifo2⟩ := (bjbDivOccur_iff bi).mp hdiv
  have hifo : bjIfOnly bi = false := beq_false_of_ne hifo2
  have hle : bjPopcount (bjElseMask bi) ≤ bjPopcount (bjIfMask bi) := by
    have h := htk
    unfold bjTakeif at h
    rw [hifo] at h
    simp [hdiv] at h
    exact h
  have hpart := bjbPopcount_partition bi.valuMask bi.maskInit
  unfold bjIfMask bjElseMask at hle
  show 2 * bjPopcount (~~~bi.valuMask &&& bi.maskInit) ≤ bjPopcount bi.maskInit
  omega

/-- 掩码纪律（pipe.scala:366 + branch_join.scala:260）：vbranch 的 maskInit ⊆ 当前
    活跃掩码 tmask。这是"合法输入"的形式化——I-2 不溢出结论的全部输入假设。 -/
def bjbMaskDiscipline {depth nT : Nat} (s : BjSysState depth nT) (bi : BjBranchIn nT) : Prop :=
  bi.maskInit &&& s.tmask = bi.maskInit

/-- 掩码纪律的 popcount 形式：|maskInit| ≤ |tmask|。 -/
theorem bjbDiscipline_popcount {depth nT : Nat} (s : BjSysState depth nT) (bi : BjBranchIn nT)
    (h : bjbMaskDiscipline s bi) : bjPopcount bi.maskInit ≤ bjPopcount s.tmask :=
  bjbPopcount_le_of_sub h

/-- 分化时两侧均非零 ⇒ 两侧 popcount 均 ≥ 1（即抽象模型 push 守卫 t ≥ 1 ∧ s ≥ 1 与
    cur ≥ 2 的具体依据）。 -/
theorem bjbDivOccur_sides_pos {nT : Nat} (bi : BjBranchIn nT)
    (hdiv : bjDivOccur bi = true) :
    1 ≤ bjPopcount (bjIfMask bi) ∧ 1 ≤ bjPopcount (bjElseMask bi) := by
  obtain ⟨h1, h2⟩ := (bjbDivOccur_iff bi).mp hdiv
  exact ⟨bjbPopcount_pos h1, bjbPopcount_pos h2⟩

/- ========================================================================= -/
/- 3. 抽象协议模型与主定理（全证）                                            -/
/-    状态只保留 popcount 级信息；事件合法性守卫内置于 step（非法 = 无操作）。  -/
/- ========================================================================= -/

/-- 抽象层级：m = 该层分化分支 maskInit 的 popcount；hi = push 时活跃掩码的 popcount
    （= RPC 项恢复掩码的 popcount，branch_join.scala:163 threadMask := thread_masks(x)）；
    path = some s 表示路径项在栈（s = sibling 侧 popcount），none 表示路径项已弹。 -/
structure BjbLevel where
  m : Nat
  hi : Nat
  path : Option Nat
deriving DecidableEq

/-- 抽象状态：stk 头 = 栈顶；cur = 当前活跃掩码 popcount。 -/
structure BjbAbsState where
  stk : List BjbLevel
  cur : Nat

/-- 抽象事件：nop（无操作/非匹配 join）；shrink（非分化分支等使活跃掩码缩小到 c'）；
    push（分化分支：t = taken 侧 popcount，s = sibling 侧 popcount）；pop（有效 join）。 -/
inductive BjbAbsEvent where
  | nop
  | shrink (c' : Nat)
  | push (t s : Nat)
  | pop

/-- 单步转移。守卫即"合法输入"假设：shrink 要求 1 ≤ c' ≤ cur（活跃掩码非零且缩小）；
    push 要求 cur ≥ 2（分化的 popcount 依据，见 bjbDivOccur_sides_pos）、1 ≤ t ≤ s
    （takeif 恒选小边，见 bjbTakeif_if_half/bjbTakeif_else_half）、t + s ≤ cur
    （掩码纪律，见 bjbDiscipline_popcount）；pop 无守卫（真实 join 时机的上近似，
    pop 只减占用故上界安全）。守卫不满足时建模为无操作（保守）。 -/
def bjbAbsStep (st : BjbAbsState) (e : BjbAbsEvent) : BjbAbsState :=
  match e with
  | .nop => st
  | .shrink c' => if 1 ≤ c' ∧ c' ≤ st.cur then { st with cur := c' } else st
  | .push t s =>
      if 2 ≤ st.cur ∧ 1 ≤ t ∧ t ≤ s ∧ t + s ≤ st.cur then
        { stk := ⟨t + s, st.cur, some s⟩ :: st.stk, cur := t }
      else st
  | .pop =>
      match st.stk with
      | [] => st
      | u :: rest =>
          match u.path with
          | some sv => { stk := { u with path := none } :: rest, cur := sv }
          | none => { stk := rest, cur := u.hi }

def bjbAbsRun (st : BjbAbsState) (es : List BjbAbsEvent) : BjbAbsState :=
  es.foldl bjbAbsStep st

/-- 每层级的栈占用：路径项在栈 2 项（RPC + 路径），否则 1 项（仅 RPC）。 -/
def bjbLevelSize (u : BjbLevel) : Nat := if u.path.isSome then 2 else 1

/-- 栈占用 = 各层级占用之和（对应具体模型 wr_ptr 的 Nat 值）。 -/
def bjbWr : List BjbLevel → Nat
  | [] => 0
  | u :: rest => bjbLevelSize u + bjbWr rest

/-- 层级自身合法：maskInit ≥ 2（分化前提），maskInit ⊆ hi（掩码纪律），hi ≤ 32。 -/
def bjbLevelOk (u : BjbLevel) : Prop := 2 ≤ u.m ∧ u.m ≤ u.hi ∧ u.hi ≤ 32

/-- 链式不变量：head = 栈顶；参数 = 紧邻其上（更深）层级的 hi（整栈为 none）。
    对每个非栈顶层 u（其上有 hi = ahi 的层级）：
    ahi + 1 ≤ u.m（深层掩码严格小于本层）；若 u 的路径项在栈（sibling s 待执行），
    则 s ≥ 2（深层级在本层 taken 侧执行 ⇒ s ≥ taken ≥ 深层 maskInit ≥ 2）且
    ahi + s ≤ u.m（深层掩码 ⊆ taken 侧 = m − s）且 u.m ≤ 2s（takeif 小边：t ≤ s）。 -/
def bjbChain : Option Nat → List BjbLevel → Prop
  | _, [] => True
  | none, u :: rest => bjbLevelOk u ∧ bjbChain (some u.hi) rest
  | some ahi, u :: rest =>
      bjbLevelOk u ∧ ahi + 1 ≤ u.m ∧
      (∀ s, u.path = some s → 2 ≤ s ∧ ahi + s ≤ u.m ∧ u.m ≤ 2 * s) ∧
      bjbChain (some u.hi) rest

/-- 栈顶条件：cur ⊆ 栈顶层的 hi；栈顶路径项在栈时 cur ⊆ taken 侧（cur + s ≤ m），
    且 m ≤ 2s（takeif 小边）；路径项已弹时 cur ⊆ sibling 侧且严格小（cur + 1 ≤ m）。 -/
def bjbTopCond : List BjbLevel → Nat → Prop
  | [], _ => True
  | u :: _, cur =>
      cur ≤ u.hi ∧
      (∀ s, u.path = some s → 1 ≤ s ∧ cur + s ≤ u.m ∧ u.m ≤ 2 * s) ∧
      (u.path = none → cur + 1 ≤ u.m)

/-- 抽象状态合法性：活跃掩码非零且不超线程数，链式不变量与栈顶条件成立。 -/
def bjbLegal (st : BjbAbsState) : Prop :=
  1 ≤ st.cur ∧ st.cur ≤ 32 ∧ bjbChain none st.stk ∧ bjbTopCond st.stk st.cur

/-- 初始状态（栈空，32 线程全活跃）合法。 -/
theorem bjbLegal_init : bjbLegal ⟨[], 32⟩ := by
  refine ⟨by decide, by decide, trivial, trivial⟩

/-- 栈顶条件对 cur 单调（shrink 保持）。 -/
theorem bjbTopCond_mono (stk : List BjbLevel) {c c' : Nat}
    (h : bjbTopCond stk c) (hc : c' ≤ c) : bjbTopCond stk c' := by
  cases stk with
  | nil => trivial
  | cons u rest =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨Nat.le_trans hc h1, ?_, ?_⟩
    · intro s hs; obtain ⟨a, b, cc⟩ := h2 s hs; exact ⟨a, by omega, cc⟩
    · intro hn; have := h3 hn; omega

/-- push 后旧栈顶变为非顶层：其相对条件由栈顶条件 + cur ≥ 2 给出。 -/
theorem bjbChain_push_below {cur : Nat} {stk : List BjbLevel}
    (hchain : bjbChain none stk) (htop : bjbTopCond stk cur) (hcur2 : 2 ≤ cur) :
    bjbChain (some cur) stk := by
  cases stk with
  | nil => trivial
  | cons v rest =>
    obtain ⟨okv, hrest⟩ := hchain
    obtain ⟨ht1, ht2, ht3⟩ := htop
    refine ⟨okv, ?_, ?_, hrest⟩
    · cases hp : v.path with
      | none => have h := ht3 hp; omega
      | some sv => obtain ⟨hs1, hcs, _⟩ := ht2 sv hp; omega
    · intro sv hp
      obtain ⟨hs1, hcs, h2s⟩ := ht2 sv hp
      exact ⟨by omega, hcs, h2s⟩

/-- 提升引理：以 hi 为上层的链可去掉上层，并把 hi 提升为新的 cur（pop RPC 项时用）。 -/
theorem bjbChain_promote {hi : Nat} {stk : List BjbLevel} (h : bjbChain (some hi) stk) :
    bjbChain none stk ∧ bjbTopCond stk hi := by
  cases stk with
  | nil => exact ⟨trivial, trivial⟩
  | cons v rest =>
    obtain ⟨okv, h1, h2, hrest⟩ := h
    refine ⟨⟨okv, hrest⟩, ?_, ?_, ?_⟩
    · have hm := okv.2.1; omega
    · intro s hs; obtain ⟨hs2, h3, h4⟩ := h2 s hs; exact ⟨by omega, h3, h4⟩
    · intro _; exact h1

/-- 不变量保持：任意（守卫内）事件步进保持合法性（全证）。 -/
theorem bjbLegal_step (st : BjbAbsState) (e : BjbAbsEvent) (h : bjbLegal st) :
    bjbLegal (bjbAbsStep st e) := by
  obtain ⟨stk0, cur0⟩ := st
  obtain ⟨hc1, hc32, hchain, htop⟩ := h
  have hc1' : 1 ≤ cur0 := hc1
  have hc32' : cur0 ≤ 32 := hc32
  cases e with
  | nop => exact ⟨hc1, hc32, hchain, htop⟩
  | shrink c' =>
    show bjbLegal (if 1 ≤ c' ∧ c' ≤ cur0 then { stk := stk0, cur := c' } else ⟨stk0, cur0⟩)
    by_cases hg : 1 ≤ c' ∧ c' ≤ cur0
    · rw [if_pos hg]
      exact ⟨hg.1, Nat.le_trans hg.2 hc32, hchain, bjbTopCond_mono _ htop hg.2⟩
    · rw [if_neg hg]
      exact ⟨hc1, hc32, hchain, htop⟩
  | push t s =>
    show bjbLegal (if 2 ≤ cur0 ∧ 1 ≤ t ∧ t ≤ s ∧ t + s ≤ cur0
      then { stk := ⟨t + s, cur0, some s⟩ :: stk0, cur := t } else ⟨stk0, cur0⟩)
    by_cases hg : 2 ≤ cur0 ∧ 1 ≤ t ∧ t ≤ s ∧ t + s ≤ cur0
    · rw [if_pos hg]
      obtain ⟨hc2, ht1, hts, hsum⟩ := hg
      show 1 ≤ t ∧ t ≤ 32 ∧ bjbChain none (⟨t + s, cur0, some s⟩ :: stk0) ∧
        bjbTopCond (⟨t + s, cur0, some s⟩ :: stk0) t
      refine ⟨ht1, by omega, ?_, ?_⟩
      · show (2 ≤ t + s ∧ t + s ≤ cur0 ∧ cur0 ≤ 32) ∧ bjbChain (some cur0) stk0
        exact ⟨⟨by omega, hsum, hc32⟩, bjbChain_push_below hchain htop hc2⟩
      · show t ≤ cur0 ∧ (∀ sv, some s = some sv → 1 ≤ sv ∧ t + sv ≤ t + s ∧ t + s ≤ 2 * sv) ∧
          (some s = none → t + 1 ≤ t + s)
        refine ⟨by omega, ?_, ?_⟩
        · intro sv hs
          obtain rfl := Option.some.inj hs
          exact ⟨by omega, Nat.le_refl _, by omega⟩
        · intro hn
          exact absurd hn (Option.some_ne_none s)
    · rw [if_neg hg]
      exact ⟨hc1, hc32, hchain, htop⟩
  | pop =>
    cases stk0 with
    | nil => exact ⟨hc1, hc32, hchain, htop⟩
    | cons u rest =>
      obtain ⟨m0, hi0, path0⟩ := u
      cases path0 with
      | some sv =>
        obtain ⟨ht1, ht2, ht3⟩ := htop
        obtain ⟨hs1, hcs, h2s⟩ := ht2 sv rfl
        obtain ⟨okv, hrest⟩ := hchain
        obtain ⟨h2m, hmhi, hhi32⟩ := okv
        have hcs' : cur0 + sv ≤ m0 := hcs
        have hmhi' : m0 ≤ hi0 := hmhi
        have hhi32' : hi0 ≤ 32 := hhi32
        show 1 ≤ sv ∧ sv ≤ 32 ∧ bjbChain none (⟨m0, hi0, none⟩ :: rest) ∧
          bjbTopCond (⟨m0, hi0, none⟩ :: rest) sv
        refine ⟨hs1, by omega, ?_, ?_⟩
        · show (2 ≤ m0 ∧ m0 ≤ hi0 ∧ hi0 ≤ 32) ∧ bjbChain (some hi0) rest
          exact ⟨⟨by omega, hmhi', hhi32'⟩, hrest⟩
        · show sv ≤ hi0 ∧ (∀ s2, (none : Option Nat) = some s2 →
              1 ≤ s2 ∧ sv + s2 ≤ m0 ∧ m0 ≤ 2 * s2) ∧ (none = none → sv + 1 ≤ m0)
          refine ⟨by omega, ?_, ?_⟩
          · intro s2 hs2
            exact absurd hs2.symm (Option.some_ne_none s2)
          · intro _
            omega
      | none =>
        obtain ⟨okv, hrest⟩ := hchain
        obtain ⟨h2m, hmhi, hhi32⟩ := okv
        have h2m' : 2 ≤ m0 := h2m
        have hmhi' : m0 ≤ hi0 := hmhi
        obtain ⟨hprom, htopProm⟩ := bjbChain_promote hrest
        show 1 ≤ hi0 ∧ hi0 ≤ 32 ∧ bjbChain none rest ∧ bjbTopCond rest hi0
        exact ⟨by omega, hhi32, hprom, htopProm⟩

/-- 多步保持（全证）。 -/
theorem bjbLegal_run (st : BjbAbsState) (es : List BjbAbsEvent) (h : bjbLegal st) :
    bjbLegal (bjbAbsRun st es) := by
  induction es generalizing st with
  | nil => exact h
  | cons e t ih =>
    show bjbLegal (bjbAbsRun (bjbAbsStep st e) t)
    exact ih _ (bjbLegal_step st e h)

/-- 栈底 hi：stk 最底层级的 hi（空栈取默认值 d；hi ≥ m，用于上界已足够）。 -/
def bjbBotM : Nat → List BjbLevel → Nat
  | d, [] => d
  | _, u :: rest => bjbBotM u.hi rest

/-- 记账引理：上层 hi + 本链占用 ≤ 栈底 hi（每非顶层贡献 ≥1，路径项在栈再 +1）。 -/
theorem bjbWr_add_le_botM (ahi : Nat) (stk : List BjbLevel) (h : bjbChain (some ahi) stk) :
    bjbWr stk + ahi ≤ bjbBotM ahi stk := by
  induction stk generalizing ahi with
  | nil => exact Nat.le_of_eq (Nat.zero_add _)
  | cons u rest ih =>
    obtain ⟨oku, h1, h2, hrest⟩ := h
    have hstep : ahi + bjbLevelSize u ≤ u.hi := by
      cases hp : u.path with
      | none =>
        have hsz : bjbLevelSize u = 1 := by simp [bjbLevelSize, hp]
        have hmhi := oku.2.1
        omega
      | some sv =>
        obtain ⟨hs2, h3, _⟩ := h2 sv hp
        have hsz : bjbLevelSize u = 2 := by simp [bjbLevelSize, hp]
        have hmhi := oku.2.1
        omega
    have hih := ih u.hi hrest
    show bjbLevelSize u + bjbWr rest + ahi ≤ bjbBotM u.hi rest
    omega

/-- 栈底 hi ≤ 32。 -/
theorem bjbBotM_le_32 (ahi : Nat) (stk : List BjbLevel)
    (h : bjbChain (some ahi) stk) (hahi : ahi ≤ 32) : bjbBotM ahi stk ≤ 32 := by
  induction stk generalizing ahi with
  | nil => exact hahi
  | cons u rest ih =>
    obtain ⟨oku, _, _, hrest⟩ := h
    exact ih u.hi hrest oku.2.2

/-- 上界定理：合法状态的栈占用 ≤ 32（全证）。 -/
theorem bjbWr_le_32 (st : BjbAbsState) (h : bjbLegal st) : bjbWr st.stk ≤ 32 := by
  obtain ⟨stk0, cur0⟩ := st
  obtain ⟨hc1, hc32, hchain, htop⟩ := h
  cases stk0 with
  | nil => exact Nat.zero_le _
  | cons u rest =>
    obtain ⟨oku, hrest⟩ := hchain
    have h1 := bjbWr_add_le_botM u.hi rest hrest
    have h2 := bjbBotM_le_32 u.hi rest hrest oku.2.2
    have hsz : bjbLevelSize u ≤ 2 := by
      cases hp : u.path <;> simp [bjbLevelSize, hp]
    have hm : 2 ≤ u.hi := by have a := oku.1; have b := oku.2.1; omega
    show bjbLevelSize u + bjbWr rest ≤ 32
    omega

/-- 主定理（I-2 不溢出，全证）：合法状态下执行任意事件序列后，栈占用 ≤ 32 = depth_stack，
    且合法性保持（可无限继续）。 -/
theorem bjbMain_no_overflow (st : BjbAbsState) (es : List BjbAbsEvent) (h : bjbLegal st) :
    bjbWr (bjbAbsRun st es).stk ≤ 32 ∧ bjbLegal (bjbAbsRun st es) :=
  ⟨bjbWr_le_32 _ (bjbLegal_run st es h), bjbLegal_run st es h⟩

/- ---- 紧密度见证：31 级逐线程剥离恰好达到 wr = 32（抽象模型，native_decide） ---- -/

/-- 剥离轨迹生成：从活跃掩码 popcount = c 出发，n 次"push 1 (c−1) 后 pop"循环。 -/
def bjbPeelFrom (c : Nat) : Nat → List BjbAbsEvent
  | 0 => []
  | n + 1 => .push 1 (c - 1) :: .pop :: bjbPeelFrom (c - 1) n

/-- 峰值见证：30 次完整循环（wr=30, cur=2）后再 push 1 1，wr 恰好 = 32 = depth_stack。
    这正式确认 32 是紧界：栈是精确定尺寸的（报告 I-2 改判"恰好定尺寸"的定量证据）。 -/
theorem bjbTight_peel_peak :
    bjbWr (bjbAbsRun ⟨[], 32⟩ (bjbPeelFrom 32 30 ++ [.push 1 1])).stk = 32 := by
  native_decide

/-- 峰值状态合法（由通用不变量保持定理免费获得，非计算）。 -/
theorem bjbTight_peak_legal :
    bjbLegal (bjbAbsRun ⟨[], 32⟩ (bjbPeelFrom 32 30 ++ [.push 1 1])) :=
  bjbLegal_run _ _ bjbLegal_init

/-- 排空见证：31 次循环后 31 次 pop，栈完全排空、掩码恢复 32（wr 回到 0）。 -/
theorem bjbTight_peel_drain :
    let s := bjbAbsRun ⟨[], 32⟩ (bjbPeelFrom 32 31 ++ List.replicate 31 .pop)
    bjbWr s.stk = 0 ∧ s.cur = 32 ∧ s.stk = [] := by
  native_decide

/- ========================================================================= -/
/- 4. 具体模型桥接（部分降级，见文件头 ★）                                     -/
/- ========================================================================= -/

/- ---- (a) wr 簿记引理（全证）：具体模型每步的 wr 效应 ---- -/

/-- nop 不改变 wr。 -/
theorem bjbWr_nop {depth nT : Nat} [NeZero depth] (s : BjSysState depth nT) :
    (bjSysStep s .nop).1.stack.wr = s.stack.wr := rfl

/-- 分化分支 wr + 2，非分化分支 wr 不变（:159 push = divOccur，:48-50）。 -/
theorem bjbWr_branch {depth nT : Nat} [NeZero depth] (s : BjSysState depth nT)
    (bi : BjBranchIn nT) :
    (bjSysStep s (.branch bi)).1.stack.wr =
      if bjDivOccur bi then s.stack.wr + 2 else s.stack.wr := by
  cases h : bjDivOccur bi <;>
    simp [bjSysStep, bjBranchStackIn, bjStackStep, bjStackJump, h]

/-- 有效 join（TOS 匹配且非下溢）wr − 1，否则不变（:42-45, :57-59）。 -/
theorem bjbWr_join {depth nT : Nat} [NeZero depth] (s : BjSysState depth nT) (pc : BitVec 32) :
    (bjSysStep s (.join pc)).1.stack.wr =
      if bjStackJump s.stack (bjJoinIn pc) then s.stack.wr - 1 else s.stack.wr := by
  have hpush : (bjJoinIn (nT := nT) pc).push = false := rfl
  cases h : bjStackJump s.stack (bjJoinIn pc) with
  | false =>
    have hs : bjStackStep s.stack (bjJoinIn pc) = s.stack := by
      simp [bjStackStep, hpush, h]
    show (bjStackStep s.stack (bjJoinIn pc)).wr = _
    rw [hs]
    simp [h]
  | true =>
    have hw := bjStackStep_pop_wr s.stack (bjJoinIn pc) hpush h
    show (bjStackStep s.stack (bjJoinIn pc)).wr = _
    rw [hw]
    simp [h]

/- ---- (b) 具体最坏轨迹：nT = depth = 6 的 5 级逐线程剥离 ---- -/
/-  每级：maskInit = 当前活跃掩码（掩码纪律，逐拍断言），valuMask 取 1 个线程。
    第 5 级 if/else 各 1 线程（计数相等 → takeif = false，走 else 侧）。
    峰值 wr = 6 = depth（与 32 线程时峰值 32 同构：k 级剥离峰值 = k + 1）。 -/

section BjbConcretePeel

def pcInit : BjSysState 6 6 := { stack := bjStackInit 6 6, tmask := 0b111111 }

def pcB1 : BjBranchIn 6 :=
  { valuMask := 0b000001, maskInit := 0b111111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }
def pcB2 : BjBranchIn 6 :=
  { valuMask := 0b000010, maskInit := 0b111110, PCbranch := 0x208, PCexecute := 0x108, PCreconv := 0x308 }
def pcB3 : BjBranchIn 6 :=
  { valuMask := 0b000100, maskInit := 0b111100, PCbranch := 0x210, PCexecute := 0x110, PCreconv := 0x310 }
def pcB4 : BjBranchIn 6 :=
  { valuMask := 0b001000, maskInit := 0b111000, PCbranch := 0x218, PCexecute := 0x118, PCreconv := 0x318 }
def pcB5 : BjBranchIn 6 :=
  { valuMask := 0b010000, maskInit := 0b110000, PCbranch := 0x220, PCexecute := 0x120, PCreconv := 0x320 }

def pcS1  := bjSysStep pcInit  (.branch pcB1)
def pcS2  := bjSysStep pcS1.1  (.join 0x300)
def pcS3  := bjSysStep pcS2.1  (.branch pcB2)
def pcS4  := bjSysStep pcS3.1  (.join 0x308)
def pcS5  := bjSysStep pcS4.1  (.branch pcB3)
def pcS6  := bjSysStep pcS5.1  (.join 0x310)
def pcS7  := bjSysStep pcS6.1  (.branch pcB4)
def pcS8  := bjSysStep pcS7.1  (.join 0x318)
def pcS9  := bjSysStep pcS8.1  (.branch pcB5)
def pcS10 := bjSysStep pcS9.1  (.join 0x320)
def pcS11 := bjSysStep pcS10.1 (.join 0x320)
def pcS12 := bjSysStep pcS11.1 (.join 0x318)
def pcS13 := bjSysStep pcS12.1 (.join 0x310)
def pcS14 := bjSysStep pcS13.1 (.join 0x308)
def pcS15 := bjSysStep pcS14.1 (.join 0x300)

-- 拍 1（B1）：分化 takeif，wr=2，走 if（1 线程）；掩码纪律：maskInit ⊆ tmask
theorem pcB1_beat :
    pcS1.1.stack.wr = 2 ∧ pcS1.1.tmask = 0b000001 ∧
    (pcB1.maskInit &&& pcInit.tmask) = pcB1.maskInit := by
  native_decide
-- 拍 2（J1）：弹 B1 路径项，wr=1，掩码换 sibling = 0b111110
theorem pcJ1_beat : pcS2.1.stack.wr = 1 ∧ pcS2.1.tmask = 0b111110 := by
  native_decide
-- 拍 3（B2）：wr=3，走 if；掩码纪律成立
theorem pcB2_beat :
    pcS3.1.stack.wr = 3 ∧ pcS3.1.tmask = 0b000010 ∧
    (pcB2.maskInit &&& pcS2.1.tmask) = pcB2.maskInit := by
  native_decide
theorem pcJ2_beat : pcS4.1.stack.wr = 2 ∧ pcS4.1.tmask = 0b111100 := by
  native_decide
theorem pcB3_beat :
    pcS5.1.stack.wr = 4 ∧ pcS5.1.tmask = 0b000100 ∧
    (pcB3.maskInit &&& pcS4.1.tmask) = pcB3.maskInit := by
  native_decide
theorem pcJ3_beat : pcS6.1.stack.wr = 3 ∧ pcS6.1.tmask = 0b111000 := by
  native_decide
theorem pcB4_beat :
    pcS7.1.stack.wr = 5 ∧ pcS7.1.tmask = 0b001000 ∧
    (pcB4.maskInit &&& pcS6.1.tmask) = pcB4.maskInit := by
  native_decide
theorem pcJ4_beat : pcS8.1.stack.wr = 4 ∧ pcS8.1.tmask = 0b110000 := by
  native_decide
-- 拍 9（B5，峰值）：wr = 6 = depth，恰好不溢出；掩码纪律成立
theorem pcB5_peak :
    pcS9.1.stack.wr = 6 ∧ pcS9.1.stack.wr.toNat = 6 ∧
    pcS9.1.tmask = 0b100000 ∧
    (pcB5.maskInit &&& pcS8.1.tmask) = pcB5.maskInit := by
  native_decide
-- 拍 10/11（J5×2）：先弹 B5 路径项（掩码换 if = 0b010000），再弹 B5 RPC 项（回 0b110000）
theorem pcJ5a_beat : pcS10.1.stack.wr = 5 ∧ pcS10.1.tmask = 0b010000 := by
  native_decide
theorem pcJ5b_beat : pcS11.1.stack.wr = 4 ∧ pcS11.1.tmask = 0b110000 := by
  native_decide
-- 拍 15（排空）：wr = 0，掩码恢复 0b111111
theorem pcDrain :
    pcS15.1.stack.wr = 0 ∧ pcS15.1.tmask = 0b111111 := by
  native_decide

end BjbConcretePeel

/- ---- (b') 具体最坏轨迹之二：nT = depth = 32 的 5 级对半嵌套 ---- -/
/-  每级 if/else 各半（计数相等 → takeif = false，走 else 侧），活跃掩码
    32→16→8→4→2→1，5 级分化 wr=10；第 6 级掩码只剩 1 线程，divOccur 不可能。 -/

section BjbConcreteHalve

def haInit : BjSysState 32 32 := { stack := bjStackInit 32 32, tmask := 0xFFFFFFFF }

def haB1 : BjBranchIn 32 :=
  { valuMask := 0x0000FFFF, maskInit := 0xFFFFFFFF, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }
def haB2 : BjBranchIn 32 :=
  { valuMask := 0x00FF0000, maskInit := 0xFFFF0000, PCbranch := 0x208, PCexecute := 0x108, PCreconv := 0x308 }
def haB3 : BjBranchIn 32 :=
  { valuMask := 0x0F000000, maskInit := 0xFF000000, PCbranch := 0x210, PCexecute := 0x110, PCreconv := 0x310 }
def haB4 : BjBranchIn 32 :=
  { valuMask := 0x30000000, maskInit := 0xF0000000, PCbranch := 0x218, PCexecute := 0x118, PCreconv := 0x318 }
def haB5 : BjBranchIn 32 :=
  { valuMask := 0x40000000, maskInit := 0xC0000000, PCbranch := 0x220, PCexecute := 0x120, PCreconv := 0x320 }
-- 第 6 级：活跃掩码仅 1 线程，valuMask 取它 → ifOnly → takeif、不分化、不 push
def haB6 : BjBranchIn 32 :=
  { valuMask := 0x80000000, maskInit := 0x80000000, PCbranch := 0x228, PCexecute := 0x128, PCreconv := 0x328 }

def haS1 := bjSysStep haInit (.branch haB1)
def haS2 := bjSysStep haS1.1 (.branch haB2)
def haS3 := bjSysStep haS2.1 (.branch haB3)
def haS4 := bjSysStep haS3.1 (.branch haB4)
def haS5 := bjSysStep haS4.1 (.branch haB5)
def haS6 := bjSysStep haS5.1 (.branch haB6)

theorem ha_halve_level1 : haS1.1.stack.wr = 2 ∧ haS1.1.tmask = 0xFFFF0000 := by
  native_decide
theorem ha_halve_level2 : haS2.1.stack.wr = 4 ∧ haS2.1.tmask = 0xFF000000 := by
  native_decide
theorem ha_halve_level3 : haS3.1.stack.wr = 6 ∧ haS3.1.tmask = 0xF0000000 := by
  native_decide
theorem ha_halve_level4 : haS4.1.stack.wr = 8 ∧ haS4.1.tmask = 0xC0000000 := by
  native_decide
-- 5 级对半嵌套 wr = 10 ≤ 32（taken 路径嵌套最多 5 级的定量证据）
theorem ha_halve_level5 : haS5.1.stack.wr = 10 ∧ haS5.1.tmask = 0x80000000 := by
  native_decide
-- 第 6 级：1 线程无法分化（divOccur = false），不 push，wr 不变
theorem ha_halve_level6_nodiv : haS6.1.stack.wr = 10 ∧ haS6.1.tmask = 0x80000000 := by
  native_decide

end BjbConcreteHalve

/- ---- 公理审计 ---- -/

#print axioms bjbPopcount_or_of_disjoint
#print axioms bjbPopcount_partition
#print axioms bjbTakeif_if_half
#print axioms bjbTakeif_else_half
#print axioms bjbLegal_step
#print axioms bjbWr_le_32
#print axioms bjbMain_no_overflow
#print axioms bjbWr_branch
#print axioms bjbWr_join
-- native_decide 测试定理的审计（预期含 Lean.ofReduceBool，见 AGENTS.md 已知踩坑）
#print axioms bjbTight_peel_peak
#print axioms bjbTight_peel_drain
#print axioms pcB5_peak
#print axioms ha_halve_level5

end Ventus.SIMT
