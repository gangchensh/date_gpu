/- QueueModel.lean —— FIFO 抽象规约模型
   * AQueue：基于 List 的抽象队列（队首 = list head），容量不变量内置于结构字段；
   * enq / deq / enqDeq：纯函数抽象操作，满入被拒（None）、空出被拒；
   * Hist：带历史（已入队/已出队序列）的幽灵状态，用于精确陈述顺序保持；
   * 精化框架 Simulates/Steps/aStep/aSteps：后续各具体 FIFO 只需给出 abs 与
     单步模拟证明，多步模拟由 simulates_steps 免费获得。
   注：本工程无 mathlib，用 Nat 而非 ℕ；"前缀"以 ∃ t, deqHist ++ t = enqHist
   陈述（即 List.IsPrefix 的展开），不依赖库记号。

   移植记录：2026-08-25 自 coralNPU/lean/CoralNPU/Base/QueueModel.lean 逐行移植，
   仅做 namespace 改名（CoralNPU.Base → Ventus.Base），未改任何定义/定理行为；
   按"移植即重审"纪律逐定义重审语义，结论：无实现与文档不符项，一处提示性疑点
   标注于 Hist.run_prefix 处。数值回归测试（源文件无）见文件末尾第 8 节。 -/

import Ventus.Base.Defs

namespace Ventus.Base

set_option linter.unusedVariables false

/- 1. 抽象队列状态与谓词 -/

/-- 抽象 FIFO 队列：内容为 `items`（队首 = list head，队尾 = list 末尾）。
    容量不变量 `bounded` 放结构字段而非独立谓词：所有抽象操作的结果自动
    满足不变量，规约定理无需反复携带长度前提。 -/
structure AQueue (α : Type) (cap : Nat) where
  items   : List α
  bounded : items.length ≤ cap

/-- 空队列 -/
def AQueue.empty {α : Type} {cap : Nat} : AQueue α cap :=
  ⟨[], Nat.zero_le _⟩

instance : Inhabited (AQueue α cap) := ⟨AQueue.empty⟩

/-- 队列中元素个数 -/
def AQueue.count {α : Type} {cap : Nat} (q : AQueue α cap) : Nat :=
  q.items.length

/-- 空（谓词，对 Nat 可判定） -/
def AQueue.isEmpty {α : Type} {cap : Nat} (q : AQueue α cap) : Prop :=
  q.count = 0

/-- 满（谓词，对 Nat 可判定） -/
def AQueue.isFull {α : Type} {cap : Nat} (q : AQueue α cap) : Prop :=
  q.count = cap

/-- 可入队（谓词，对 Nat 可判定） -/
def AQueue.canEnq {α : Type} {cap : Nat} (q : AQueue α cap) : Prop :=
  q.count < cap

/-- 可出队（谓词，对 Nat 可判定） -/
def AQueue.canDeq {α : Type} {cap : Nat} (q : AQueue α cap) : Prop :=
  0 < q.count

/-- 结构外延性：内容相同则队列相同（容量证明由证明不可知性抹平） -/
theorem AQueue.ext {α : Type} {cap : Nat} {q1 q2 : AQueue α cap}
    (h : q1.items = q2.items) : q1 = q2 := by
  cases q1; cases q2; subst h; rfl

/-- count 与 length 一致（定义即如此，列出以便重写） -/
theorem AQueue.count_eq_length {α : Type} {cap : Nat} (q : AQueue α cap) :
    q.count = q.items.length := rfl

theorem AQueue.isEmpty_iff {α : Type} {cap : Nat} (q : AQueue α cap) :
    q.isEmpty ↔ q.items = [] := by
  constructor
  · intro h
    exact List.eq_nil_of_length_eq_zero h
  · intro h
    simp only [AQueue.isEmpty, AQueue.count, h, List.length_nil]

/-- 可入队 ⟺ 非满（需用到容量不变量） -/
theorem AQueue.canEnq_iff_not_isFull {α : Type} {cap : Nat} (q : AQueue α cap) :
    q.canEnq ↔ ¬q.isFull := by
  simp only [AQueue.canEnq, AQueue.isFull, AQueue.count]
  have hb := q.bounded
  omega

/-- 可出队 ⟺ 非空 -/
theorem AQueue.canDeq_iff_not_isEmpty {α : Type} {cap : Nat} (q : AQueue α cap) :
    q.canDeq ↔ ¬q.isEmpty := by
  simp only [AQueue.canDeq, AQueue.isEmpty, AQueue.count]
  omega

theorem AQueue.empty_count {α : Type} {cap : Nat} : (AQueue.empty : AQueue α cap).count = 0 := rfl

theorem AQueue.empty_canEnq {α : Type} {cap : Nat} (h : 0 < cap) :
    (AQueue.empty : AQueue α cap).canEnq := h

/- 2. 抽象操作 enq / deq / enqDeq。
   语义选择：enq 满时返回 None（拒绝，不产生新状态）；deq 空时返回 None。 -/

/-- 入队：元素追加到队尾；满则返回 None -/
def AQueue.enq {α : Type} {cap : Nat} (q : AQueue α cap) (x : α) : Option (AQueue α cap) :=
  if h : q.count < cap then
    some ⟨q.items ++ [x], by
      have h' : q.items.length < cap := h
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  else
    none

/-- 出队：取队首；空则返回 None -/
def AQueue.deq {α : Type} {cap : Nat} (q : AQueue α cap) : Option (α × AQueue α cap) :=
  match hq : q.items with
  | [] => none
  | x :: xs =>
    some (x, ⟨xs, by
      have hb := q.bounded
      rw [hq] at hb
      simp only [List.length_cons] at hb
      omega⟩)

/-- 同拍出入队（满队列常见用法）：先出队再入队；空队列返回 None。
    与单独 enq 的区别：满队列上 enq 会被拒，但 enqDeq 可以成功。 -/
def AQueue.enqDeq {α : Type} {cap : Nat} (q : AQueue α cap) (x : α) : Option (α × AQueue α cap) :=
  match q.deq with
  | none => none
  | some (y, q') =>
    match q'.enq x with
    | none => none
    | some q'' => some (y, q'')

/- 3. enq 的规约定理 -/

/-- 不溢出：满时 enq 被拒 -/
theorem AQueue.enq_full {α : Type} {cap : Nat} (q : AQueue α cap) (x : α)
    (h : q.isFull) : q.enq x = none := by
  have hf : q.count = cap := h
  unfold AQueue.enq
  split
  · rename_i hc; omega
  · rfl

/-- enq 返回 none 当且仅当满 -/
theorem AQueue.enq_none_iff {α : Type} {cap : Nat} (q : AQueue α cap) (x : α) :
    q.enq x = none ↔ q.isFull := by
  constructor
  · intro h
    unfold AQueue.enq at h
    split at h
    · simp at h
    · rename_i hc; show q.count = cap
      have hb : q.count ≤ cap := q.bounded
      omega
  · intro h; exact q.enq_full x h

/-- enq 成功 ⟹ 原队列可入队 -/
theorem AQueue.canEnq_of_enq_some {α : Type} {cap : Nat} {q q' : AQueue α cap}
    {x : α} (h : q.enq x = some q') : q.canEnq := by
  unfold AQueue.enq at h
  split at h
  · rename_i hc; exact hc
  · simp at h

/-- enq 成功的完整刻画：内容 = 原内容 ++ [x]，count + 1 -/
theorem AQueue.enq_success {α : Type} {cap : Nat} (q : AQueue α cap) (x : α) (h : q.canEnq) :
    ∃ q', q.enq x = some q' ∧ q'.items = q.items ++ [x] ∧
      q'.count = q.count + 1 := by
  have h' : q.count < cap := h
  have h'' : q.items.length < cap := h
  refine ⟨⟨q.items ++ [x], ?_⟩, ?_, rfl, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · unfold AQueue.enq
    rw [dif_pos h']
  · simp [AQueue.count, List.length_append]

/-- enq 后内容 = 原内容末尾追加 -/
theorem AQueue.enq_items {α : Type} {cap : Nat} {q q' : AQueue α cap} {x : α}
    (h : q.enq x = some q') : q'.items = q.items ++ [x] := by
  obtain ⟨q'', hq, hitems, _⟩ := q.enq_success x (canEnq_of_enq_some h)
  rw [hq] at h
  have e := Option.some.inj h
  subst e
  exact hitems

/-- enq 后 count + 1 -/
theorem AQueue.enq_count {α : Type} {cap : Nat} {q q' : AQueue α cap} {x : α}
    (h : q.enq x = some q') : q'.count = q.count + 1 := by
  obtain ⟨q'', hq, _, hcnt⟩ := q.enq_success x (canEnq_of_enq_some h)
  rw [hq] at h
  have e := Option.some.inj h
  subst e
  exact hcnt

/- 4. deq 的规约定理 -/

/-- 不欠载：空时 deq 被拒 -/
theorem AQueue.deq_empty {α : Type} {cap : Nat} (q : AQueue α cap)
    (h : q.isEmpty) : q.deq = none := by
  have hem : q.items = [] := List.eq_nil_of_length_eq_zero h
  unfold AQueue.deq
  split
  · rfl
  · rename_i x xs hq; simp [hq] at hem

/-- deq 返回 none 当且仅当空 -/
theorem AQueue.deq_none_iff {α : Type} {cap : Nat} (q : AQueue α cap) :
    q.deq = none ↔ q.isEmpty := by
  constructor
  · intro h
    unfold AQueue.deq at h
    split at h
    · rename_i hq; simp only [AQueue.isEmpty, AQueue.count, hq, List.length_nil]
    · simp at h
  · intro h; exact q.deq_empty h

/-- deq 成功 ⟹ 原队列可出队 -/
theorem AQueue.canDeq_of_deq_some {α : Type} {cap : Nat} {q q' : AQueue α cap}
    {y : α} (h : q.deq = some (y, q')) : q.canDeq := by
  unfold AQueue.deq at h
  split at h
  · simp at h
  · rename_i x xs hq; simp only [AQueue.canDeq, AQueue.count, hq, List.length_cons]
    omega

/-- deq 成功的完整刻画：内容 = 队首 :: 剩余，count − 1 -/
theorem AQueue.deq_success {α : Type} {cap : Nat} (q : AQueue α cap) (h : q.canDeq) :
    ∃ y q', q.deq = some (y, q') ∧ q.items = y :: q'.items ∧
      q'.count + 1 = q.count := by
  have hne : q.items ≠ [] := by
    intro hz
    simp [AQueue.canDeq, AQueue.count, hz] at h
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨y, ⟨ys, by
    have hb := q.bounded
    rw [hys] at hb
    simp only [List.length_cons] at hb
    omega⟩, ?_, by exact hys, ?_⟩
  · unfold AQueue.deq
    split
    · rename_i hq; simp [hys] at hq
    · rename_i x xs hq; rw [hys] at hq
      obtain ⟨rfl, rfl⟩ := List.cons.inj hq
      rfl
  · simp [AQueue.count, hys]

/-- deq 后原内容 = 出队元素 :: 新内容 -/
theorem AQueue.deq_items {α : Type} {cap : Nat} {q q' : AQueue α cap} {y : α}
    (h : q.deq = some (y, q')) : q.items = y :: q'.items := by
  obtain ⟨y', q'', hdeq, hitems, _⟩ := q.deq_success (canDeq_of_deq_some h)
  rw [hdeq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact hitems

/-- deq 后 count − 1 -/
theorem AQueue.deq_count {α : Type} {cap : Nat} {q q' : AQueue α cap} {y : α}
    (h : q.deq = some (y, q')) :
    q'.count + 1 = q.count ∧ q'.count = q.count - 1 := by
  obtain ⟨y', q'', hdeq, _, hcnt⟩ := q.deq_success (canDeq_of_deq_some h)
  rw [hdeq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hcnt, by omega⟩

/-- 出队元素就是队首 -/
theorem AQueue.deq_head {α : Type} {cap : Nat} {q q' : AQueue α cap} {y : α}
    (h : q.deq = some (y, q')) : q.items.head? = some y := by
  rw [q.deq_items h]
  rfl

/- 5. 同拍出入队 enqDeq 的规约定理 -/

/-- enqDeq 成功（前提：可出队）：count 不变，原内容 = 队首 :: ys，
    新内容 = ys ++ [x] —— 即"出一个、进一个" -/
theorem AQueue.enqDeq_success {α : Type} {cap : Nat} (q : AQueue α cap) (x : α) (h : q.canDeq) :
    ∃ y q', q.enqDeq x = some (y, q') ∧ q'.count = q.count ∧
      ∃ ys, q.items = y :: ys ∧ q'.items = ys ++ [x] := by
  obtain ⟨y, qd, hdeq, hitems, hcnt⟩ := q.deq_success h
  have hb : q.count ≤ cap := q.bounded
  have hce : qd.canEnq := by
    show qd.count < cap
    omega
  obtain ⟨qe, henq, heitems, hecnt⟩ := qd.enq_success x hce
  refine ⟨y, qe, ?_, ?_, qd.items, hitems, heitems⟩
  · simp only [AQueue.enqDeq, hdeq, henq]
  · omega

/-- 满队列上的同拍出入队：成功且保持满。
    注意：cap = 0 时"满"与"空"同时成立，故需显式 canDeq 前提。 -/
theorem AQueue.enqDeq_full {α : Type} {cap : Nat} (q : AQueue α cap) (x : α)
    (hfull : q.isFull) (hcd : q.canDeq) :
    ∃ y q', q.enqDeq x = some (y, q') ∧ q'.isFull := by
  obtain ⟨y, q', hrun, hcnt, _⟩ := q.enqDeq_success x hcd
  have hf : q.count = cap := hfull
  exact ⟨y, q', hrun, by show q'.count = cap; omega⟩

/-- 空队列上 enqDeq 被拒 -/
theorem AQueue.enqDeq_empty {α : Type} {cap : Nat} (q : AQueue α cap) (x : α)
    (h : q.isEmpty) : q.enqDeq x = none := by
  simp only [AQueue.enqDeq, q.deq_empty h]

/-- enqDeq 成功 ⟹ 原队列可出队 -/
theorem AQueue.canDeq_of_enqDeq_some {α : Type} {cap : Nat} {q q' : AQueue α cap}
    {x y : α} (h : q.enqDeq x = some (y, q')) : q.canDeq := by
  show 0 < q.count
  apply Decidable.byContradiction
  intro hn
  have he : q.isEmpty := by
    show q.count = 0
    omega
  rw [q.enqDeq_empty x he] at h
  simp at h

/- ========================================================================= -/
/- 6. 顺序保持（带历史的幽灵状态）：精确形式为不变量
   enqHist = deqHist ++ q.items；直接推论：出队序列是入队序列的前缀。 -/

/-- 抽象操作标签：精化框架与历史运行共用。`enqDeq x` 为同拍出入（先出后入） -/
inductive AOp (α : Type) where
  | enq (x : α)
  | deq
  | enqDeq (x : α)
  | skip

/-- 带历史的队列：enqHist/deqHist 为幽灵变量，
    wf 为 FIFO 顺序不变量（enq 序列 = deq 序列 ++ 当前内容） -/
structure Hist (α : Type) (cap : Nat) where
  q       : AQueue α cap
  enqHist : List α
  deqHist : List α
  wf      : enqHist = deqHist ++ q.items

/-- 初始历史：空队列、空历史 -/
def Hist.empty {α : Type} {cap : Nat} : Hist α cap :=
  ⟨AQueue.empty, [], [], rfl⟩

/-- 单步执行一个抽象操作并更新历史；操作被拒（满入/空出）时返回 None。
    skip 不改变状态（对应具体实现中的气泡拍）。 -/
def Hist.step {α : Type} {cap : Nat} (h : Hist α cap) : AOp α → Option (Hist α cap)
  | .enq x =>
    match hq : h.q.enq x with
    | none => none
    | some q' =>
      some ⟨q', h.enqHist ++ [x], h.deqHist, by
        have e := AQueue.enq_items hq
        rw [e, ← List.append_assoc, ← h.wf]⟩
  | .deq =>
    match hq : h.q.deq with
    | none => none
    | some (y, q') =>
      some ⟨q', h.enqHist, h.deqHist ++ [y], by
        have e := AQueue.deq_items hq
        rw [h.wf, e]
        simp [List.append_assoc]⟩
  | .enqDeq x =>
    match hq : h.q.enqDeq x with
    | none => none
    | some (y, q') =>
      some ⟨q', h.enqHist ++ [x], h.deqHist ++ [y], by
        obtain ⟨y', q'', hrun, _, ys, h1, h2⟩ :=
          h.q.enqDeq_success x (AQueue.canDeq_of_enqDeq_some hq)
        rw [hrun] at hq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
        rw [h.wf, h1, h2]
        simp [List.append_assoc]⟩
  | .skip => some h

/-- 依次执行一串操作（任一被拒则整体 None） -/
def Hist.run {α : Type} {cap : Nat} (h : Hist α cap) (ops : List (AOp α)) : Option (Hist α cap) :=
  ops.foldlM Hist.step h

/-- 顺序保持（主定理）：任意操作序列跑完后，
    出队序列是入队序列的前缀，且 入队序列 = 出队序列 ++ 当前内容。
    审查疑点（提示性，非语义错误，保持与源一致未改）：前提 `_h : h0.run ops = some hf`
    实际未使用——不变量 wf 已内置于 Hist 结构字段，故结论对任意 hf（即使不可达）
    都成立，与 h0/ops 无关。定理语义仍正确且比文档措辞更强，但"跑完后"的表述
    易让人误以为结论依赖于 run 的可达性。 -/
theorem Hist.run_prefix {α : Type} {cap : Nat} (h0 : Hist α cap)
    (ops : List (AOp α)) (hf : Hist α cap)
    (_h : h0.run ops = some hf) :
    (∃ t, hf.deqHist ++ t = hf.enqHist) ∧
      hf.enqHist = hf.deqHist ++ hf.q.items :=
  ⟨⟨hf.q.items, hf.wf.symm⟩, hf.wf⟩

/-- 从空队列出发的特化：任何可达状态下出队序列都是入队序列的前缀 -/
theorem Hist.run_from_empty_prefix {α : Type} {cap : Nat} (ops : List (AOp α)) (hf : Hist α cap)
    (h : (Hist.empty : Hist α cap).run ops = some hf) :
    ∃ t, hf.deqHist ++ t = hf.enqHist :=
  (Hist.run_prefix _ _ _ h).1

/-- FIFO 语义 sanity check：空队列入队 x 再出队，得到 x 并回到空队列 -/
theorem AQueue.fifo_single {α : Type} {cap : Nat} (x : α) (hcap : 0 < cap) :
    ∃ q', (AQueue.empty : AQueue α cap).enq x = some q' ∧
      q'.deq = some (x, AQueue.empty) := by
  obtain ⟨q', henq, hitems, _⟩ :=
    AQueue.enq_success (AQueue.empty : AQueue α cap) x
      (by show 0 < cap; exact hcap)
  refine ⟨q', henq, ?_⟩
  have hi : q'.items = [x] := hitems
  obtain ⟨y, q'', hdeq, hqi, _⟩ := q'.deq_success (by
    show 0 < q'.count
    have h1 : q'.count = 1 := by simp [AQueue.count, hi]
    omega)
  rw [hdeq]
  rw [hi] at hqi
  obtain ⟨hy, ht⟩ := List.cons.inj hqi
  subst hy
  have hq'' : q'' = AQueue.empty := AQueue.ext (by exact ht.symm)
  rw [hq'']

/- ========================================================================= -/
/- 7. 精化关系框架：具体模型 → 抽象模型

   使用说明（供各 FIFO 模块作者照做）：
   ① 给出具体状态类型 S 与抽象函数 `abs : S → AQueue α cap`（即证明具体不变量
     ⟹ length ≤ cap，把缓冲内容按队首→队尾排成 list）；
   ② 定义具体单步关系 `step : S → Option α → S → Prop`，Option α 为该拍
     可观测的出队输出（无出队为 none）；
   ③ 证明单步模拟 `Simulates abs step`：每个具体 step 对应一个抽象标签
     （AOp.enq x / AOp.deq / AOp.enqDeq x / AOp.skip）且输出一致；通常对
     step 归纳，各分支用 aStep_enq / aStep_deq / aStep_enqDeq / aStep_skip 收尾；
   ④ 多步性质（任意有限拍的正确性）由 simulates_steps 免费获得。

   签名示例：
     def fifoAbs (s : FifoState α N) : AQueue α N := ...
     inductive fifoStep : FifoState α N → Option α → FifoState α N → Prop
     theorem fifo_simulates : Simulates fifoAbs fifoStep := by
       intro s s' out h; cases h with
       | enq hx  => exact ⟨.enq x, aStep_enq (by ...)⟩
       | deq hx  => exact ⟨.deq,   aStep_deq (by ...)⟩
       | bubble  => exact ⟨.skip,  aStep_skip _⟩                             -/

/-- 抽象单步语义：返回 (可观测输出, 后继抽象状态)；标签被拒（满入/空出）时返回 none。 -/
def aStep {α : Type} {cap : Nat} (q : AQueue α cap) : AOp α → Option (Option α × AQueue α cap)
  | .enq x => (q.enq x).map fun q' => (none, q')
  | .deq   => (q.deq).map fun p => (some p.1, p.2)
  | .enqDeq x => (q.enqDeq x).map fun p => (some p.1, p.2)
  | .skip  => some (none, q)

/-- 抽象多步语义：返回 (依次观测到的出队输出序列, 终态) -/
def aSteps {α : Type} {cap : Nat} (q : AQueue α cap) : List (AOp α) → Option (List α × AQueue α cap)
  | [] => some ([], q)
  | l :: ls =>
    match aStep q l with
    | none => none
    | some (o, q') =>
      match aSteps q' ls with
      | none => none
      | some (os, q'') => some (o.toList ++ os, q'')

theorem aStep_enq {α : Type} {cap : Nat} {q q' : AQueue α cap} {x : α} (h : q.enq x = some q') :
    aStep q (.enq x) = some (none, q') := by
  simp [aStep, h]

theorem aStep_deq {α : Type} {cap : Nat} {q q' : AQueue α cap} {y : α} (h : q.deq = some (y, q')) :
    aStep q .deq = some (some y, q') := by
  simp [aStep, h]

theorem aStep_enqDeq {α : Type} {cap : Nat} {q q' : AQueue α cap} {x y : α}
    (h : q.enqDeq x = some (y, q')) : aStep q (.enqDeq x) = some (some y, q') := by
  simp [aStep, h]

theorem aStep_skip {α : Type} {cap : Nat} (q : AQueue α cap) : aStep q .skip = some (none, q) := rfl

/-- 多步模拟的组合：两段执行可以拼接 -/
theorem aSteps_append {α : Type} {cap : Nat} (ls1 ls2 : List (AOp α)) :
    ∀ (q q1 q2 : AQueue α cap) (os1 os2 : List α),
      aSteps q ls1 = some (os1, q1) →
      aSteps q1 ls2 = some (os2, q2) →
      aSteps q (ls1 ++ ls2) = some (os1 ++ os2, q2) := by
  induction ls1 with
  | nil =>
    intro q q1 q2 os1 os2 h1 h2
    simp only [aSteps, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | cons l ls1 ih =>
    intro q q1 q2 os1 os2 h1 h2
    rw [List.cons_append]
    simp only [aSteps] at h1 ⊢
    cases hs : aStep q l with
    | none =>
      simp [hs] at h1
    | some p =>
      obtain ⟨o, qm⟩ := p
      simp only [hs] at h1 ⊢
      cases hs2 : aSteps qm ls1 with
      | none =>
        simp [hs2] at h1
      | some p2 =>
        obtain ⟨osm, qm2⟩ := p2
        simp only [hs2] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨r1, r2⟩ := h1
        subst r1
        subst r2
        simp only [ih qm qm2 q2 osm os2 hs2 h2]
        rw [List.append_assoc]

/-- 具体多步关系：单步关系的自反传递闭包（带输出累积，索引化归纳类型） -/
inductive Steps {S : Type} {α : Type} (step : S → Option α → S → Prop) : S → List α → S → Prop where
  | nil (s : S) : Steps step s [] s
  | cons {s t u : S} {o : Option α} {os : List α} :
      step s o t → Steps step t os u → Steps step s (o.toList ++ os) u

/-- 单步是多步的特例 -/
theorem Steps.single {S : Type} {α : Type} {step : S → Option α → S → Prop}
    {s s' : S} {o : Option α} (h : step s o s') :
    Steps step s o.toList s' := by
  simpa using Steps.cons h (Steps.nil s')

/-- 多步关系的传递性 -/
theorem Steps.trans {S : Type} {α : Type} {step : S → Option α → S → Prop}
    {s t u : S} {os1 os2 : List α}
    (h1 : Steps step s os1 t) (h2 : Steps step t os2 u) :
    Steps step s (os1 ++ os2) u := by
  revert h2
  induction h1 with
  | nil s =>
    intro h2
    simpa using h2
  | cons h htl ih =>
    intro h2
    simpa [List.append_assoc] using Steps.cons h (ih h2)

/-- 单步模拟：每个具体 step 都对应某抽象标签，且抽象执行后状态/输出一致 -/
def Simulates {S : Type} {α : Type} {cap : Nat}
    (abs : S → AQueue α cap) (step : S → Option α → S → Prop) : Prop :=
  ∀ {s s' : S} {out : Option α}, step s out s' →
    ∃ l : AOp α, aStep (abs s) l = some (out, abs s')

/-- 多步模拟 = 单步模拟的迭代（核心组合定理）：若 step 单步模拟于 abs，
    则任意有限具体执行序列都对应一段抽象标签序列，且输出与终态一致。 -/
theorem simulates_steps {S : Type} {α : Type} {cap : Nat}
    {abs : S → AQueue α cap} {step : S → Option α → S → Prop}
    (hsim : Simulates abs step) {s s' : S} {os : List α}
    (h : Steps step s os s') :
    ∃ ls : List (AOp α), aSteps (abs s) ls = some (os, abs s') := by
  induction h with
  | nil s => exact ⟨[], rfl⟩
  | cons hstep hsteps ih =>
    obtain ⟨l, hl⟩ := hsim hstep
    obtain ⟨ls, hls⟩ := ih
    exact ⟨l :: ls, by simp [aSteps, hl, hls]⟩

/- ========================================================================= -/
/- 8. 数值回归测试（移植重审的判收依据，全部 `by decide`；2026-08-25 移植时新增， -/
/-    源文件无此节。AQueue/Hist 含证明字段且未 deriving DecidableEq，故等值断言 -/
/-    一律比较 .items / 历史字段投影，拒绝情形用 .isNone 判定。）                -/

section QueueModelRegressionTests

/-- 测试辅助：由列表构造容量为 2 的具体队列 -/
def mkQ2 (l : List (BitVec 8)) (h : l.length ≤ 2 := by decide) : AQueue (BitVec 8) 2 := ⟨l, h⟩

-- 空队列基本谓词（isEmpty/isFull/canEnq/canDeq 是 Prop 定义、TC 无法穿透，
-- 故先 unfold 到 Nat 比较再 decide）
example : (AQueue.empty : AQueue (BitVec 8) 2).count = 0 := by decide
example : (AQueue.empty : AQueue (BitVec 8) 2).isEmpty := by
  unfold AQueue.isEmpty; decide
example : ¬(AQueue.empty : AQueue (BitVec 8) 2).isFull := by
  unfold AQueue.isFull; decide
example : (AQueue.empty : AQueue (BitVec 8) 2).canEnq := by
  unfold AQueue.canEnq; decide
example : ¬(AQueue.empty : AQueue (BitVec 8) 2).canDeq := by
  unfold AQueue.canDeq; decide

-- cap = 0 边界：空与满同时成立，enq 必被拒
example : (AQueue.empty : AQueue (BitVec 8) 0).isFull := by
  unfold AQueue.isFull; decide
example : ((AQueue.empty : AQueue (BitVec 8) 0).enq 7).isNone = true := by decide

-- enq：未满追加到队尾；满则拒绝；成功则 count + 1
example : ((AQueue.empty : AQueue (BitVec 8) 2).enq 5).map AQueue.items = some [5] := by decide
example : ((mkQ2 [1]).enq 5).map AQueue.items = some [1, 5] := by decide
example : ((mkQ2 [1, 2]).enq 5).isNone = true := by decide
example : ((mkQ2 [1]).enq 5).map AQueue.count = some 2 := by decide

-- deq：取队首；空则拒绝；成功则 count − 1
example : (mkQ2 [1, 2]).deq.map (fun p => (p.1, p.2.items)) = some (1, [2]) := by decide
example : (AQueue.empty : AQueue (BitVec 8) 2).deq.isNone = true := by decide
example : (mkQ2 [1, 2]).deq.map (fun p => p.2.count) = some 1 := by decide

-- enqDeq：满队列同拍出入成功（与 enq 的关键区别）；空队列被拒；count 不变
example : ((mkQ2 [1, 2]).enqDeq 9).map (fun p => (p.1, p.2.items)) = some (1, [2, 9]) := by decide
example : ((AQueue.empty : AQueue (BitVec 8) 2).enqDeq 9).isNone = true := by decide
example : ((mkQ2 [1]).enqDeq 9).map (fun p => (p.1, p.2.items, p.2.count)) = some (1, [9], 1) := by decide

-- aStep / aSteps：enq 无可观测输出、deq/enqDeq 输出队首、skip 不动；
-- 多步输出按时间顺序累积；任一操作被拒则整体 none
example : (aStep (mkQ2 [1, 2]) .deq).map (fun p => (p.1, p.2.items)) = some (some 1, [2]) := by decide
example : (aStep (mkQ2 [1]) (.enq 5)).map (fun p => (p.1, p.2.items)) = some (none, [1, 5]) := by decide
example : (aStep (mkQ2 [1, 2]) .skip).map (fun p => (p.1, p.2.items)) = some (none, [1, 2]) := by decide
example : (aSteps (AQueue.empty : AQueue (BitVec 8) 2) [.enq 1, .enq 2, .deq, .skip, .deq]).map
    (fun p => (p.1, p.2.items)) = some ([1, 2], []) := by decide
example : (aSteps (AQueue.empty : AQueue (BitVec 8) 2) [.enq 1, .enq 2, .enq 3]).isNone = true := by decide

-- Hist：FIFO 顺序保持的数值实例（历史精确记录入队/出队序列）
example : ((Hist.empty : Hist (BitVec 8) 2).run [.enq 1, .enq 2, .deq]).map
    (fun h => (h.enqHist, h.deqHist, h.q.items)) = some ([1, 2], [1], [2]) := by decide
example : ((Hist.empty : Hist (BitVec 8) 2).run [.deq]).isNone = true := by decide
example : ((Hist.empty : Hist (BitVec 8) 2).run [.enq 1, .enqDeq 2, .skip]).map
    (fun h => (h.enqHist, h.deqHist, h.q.items)) = some ([1, 2], [1], [2]) := by decide

end QueueModelRegressionTests

end Ventus.Base
