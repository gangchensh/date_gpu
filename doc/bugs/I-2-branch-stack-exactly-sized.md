> English translation of the Chinese master `doc/bugs/I-2-分支栈恰好定尺寸.md`. Translated 2026-09-13.

# I-2 Detailed Defect Report: `branch_join_stack` has no overflow protection, but the stack is sized exactly to the worst case

| Item | Content |
|---|---|
| ID | I-2 |
| Source location | `ventus/src/pipeline/branch_join.scala:24-63` (`branch_join_stack`, no full detection); instantiation `pipe.scala:129` (`depth_stack = num_thread = 32`); sources of the mask discipline `pipe.scala:366`, `branch_join.scala:145/:249-256/:57-59` |
| Type | Robustness risk (mechanism confirmed / unreachable under legal execution) |
| Severity | **Low** (reclassified as non-urgent: the stack is proven to be exactly sized) |
| Confirmation status | 【Mechanism confirmed / currently unreachable】 (doc/03 original verdict carried over verbatim) |
| Primary evidence | [Lean machine-checked proof] overflow-mechanism witnesses (`bjoT5_witness_lost_join`/`bjoT6_witness_ghost_pop`) + unreachability main theorem `bjbMain_no_overflow` + tight-bound witness `bjbTight_peel_peak`; [direct source reading] line-by-line checks of branch_join.scala / pipe.scala |
| Lean model | `lean/Ventus/SIMT/BranchJoinOverflow.lean` (mechanism witnesses, real parameters depth=32), `lean/Ventus/SIMT/BranchJoinBounds.lean` (tight-bound theorems), `lean/Ventus/SIMT/BranchJoin.lean` (base model) |
| Reproduction/patch | No RTL reproduction (unreachable under legal execution, see §5); no patch (the internal fix manifest: an overflow assertion is recommended, pending alignment with upstream style, low payoff; no VentusF fix variant) |
| Related entries | I-3 (complete-semantics check of the same module); III-3 (methodological lesson of reachability analysis; this entry is handled by the same procedure) |

---

## 0. Abstract

`branch_join_stack` (the SIMT divergence/reconvergence stack) is protected
against **underflow** (pop is allowed only when `wr_ptr ≠ 0`) but has no
protection at all against **overflow**: no full detection, no stall, no
exception. The overflow mechanism genuinely exists and has been nailed down in
the Lean model with real parameters (depth=32): after 17 consecutive levels of
push the write pointer reaches wr=34; write slots 32/33 alias via mod 32 onto
slots 0/1 of level 1, causing **lost reconvergence** (no pop, no jump, the mask
stuck at 1 thread) and **ghost re-entry** (an already-reconverged path popped
and jumped to again).

But the original analysis ("16 levels of nesting already overflow; the worst
case needs 62 entries") is **wrong**: it wrongly adds together two mutually
exclusive costs (2 entries per level × 31 levels of depth). The corrected
analysis (2026-08-25), fully proved by the main theorem `bjbMain_no_overflow`
(2026-08-27): under legal execution the mask is monotonically non-increasing
along nesting, takeif always picks the smaller side (the taken-path mask at
least halves per level ⇒ pure nesting ≤ 5 levels), and thread-by-thread peeling
can happen only on the larger-side path with a net occupancy of 1 entry per
level — at the deepest moment of 31 levels of peeling the stack occupancy is
exactly = 30 (outer RPC entries) + 2 (the deepest level) = **32 = depth_stack**.
The stack is **exactly sized**; 32 is a tight bound.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **Divergence/reconvergence stack**: on a vector branch, the warp's active mask
  is split in two by the if condition; the hardware first executes the side
  with fewer threads (takeif always picks the smaller side, a load-balancing
  intuition), while the other side's mask and reconvergence PC are pushed onto
  the stack; at join the stack is popped to resume. **One stack per warp**,
  depth parameter `depth_stack`.
- **Two entries per push**: on divergence two entries are pushed — the
  reconvergence RPC entry (reconPC, for reconvergence-point matching) and the
  path entry (the not-taken side's mask + jump PC). Hence the intuition "each
  nesting level costs 2 entries".
- **Pointer width**: the wr/rd pointers are `log2Ceil(depth+1)` = 6 bits wide
  (can represent 0..63, **do not wrap by themselves**), but the stack Mem has
  only 32 slots and indexing is implicitly mod 32 — the aliasing comes from
  exactly here.

### 1.2 Design intent

`depth_stack = num_thread = 32` (pipe.scala:129) looks conservative ("as deep
as the thread count must surely be enough"); this entry's conclusion is: this
size is not a conservative margin but is **exactly equal** to the worst-case
requirement.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: push two entries, pop decrements each by one, no overflow
protection** (`branch_join.scala:47-60`, ★ hazard):

```scala
when(io.push) {                          // divergence: push two entries
  stack_mem(wr_ptr)   := rpc entry       // slot wr: reconvergence RPC entry
  stack_mem(wr_ptr+1) := pushData        // slot wr+1: path entry (not-taken mask + jump PC)
  rd_ptr := wr_ptr + 1.U
  wr_ptr := wr_ptr + 2.U                 // ★ no full detection / stall / exception whatsoever
}.elsewhen(io.jump) {                    // pop
  wr_ptr := wr_ptr - 1.U
  rd_ptr := rd_ptr - 1.U
}
```

The only protection is on the underflow side (:42-44,
`is_pop = is_pop_pc && wr_ptr =/= 0`).

**Construct 2: the mask is monotonically non-increasing** (`pipe.scala:366`):
a vbranch's `mask_init = instruction mask ∧ out_mask` (a subset of the
currently active mask) — the deeper the nesting, the fewer threads available.

**Construct 3: takeif always picks the smaller side** (`branch_join.scala:145`):

```scala
takeif := ((ifCnt < elseCnt) && divOccur) || ifOnly
```

After divergence the taken side that executes first satisfies
|taken| ≤ |mask|/2: nesting continuously along the taken path halves the mask
at least per level, 32→16→8→4→2→1, **at most 5 levels**.

**Construct 4: peeling happens on the larger side; pops take the path entry
first** (`branch_join.scala:249-256` mask update + :57-59 pop order):
thread-by-thread peeling (extremely unbalanced divergence that peels only 1
thread per level) can happen only on the pushed **larger side**; the larger
side executes only after the taken side reaches join and the **path entry is
popped first** — each peeling level occupies a **net of 1 entry** (1 entry is
popped before 2 are pushed).

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

**Mechanism (confirmed)**: if 17 consecutive levels could be pushed (an illegal
trace with maskInit constantly all-ones), wr reaches 34, and level 17 writes
slots 32/33 → aliasing via mod 32 overwrites slots 0/1 of level 1. Observable
consequences (nailed down by Lean witnesses):

- A join for level 1's reconvergence: slot 1 has been overwritten, reconPC no
  longer matches → **no pop, no jump, reconvergence lost**, the mask stuck at
  1 thread (`bjoT5_witness_lost_join`);
- Issuing a join to level 17's reconPC: the leftover entry matches again →
  **ghost re-entry** into an already-reconverged path
  (`bjoT6_witness_ghost_pop`). Throughout: no full detection, no exception.

**Unreachable (under legal execution)**: the above trace has maskInit
constantly all-ones, **violating the mask discipline**. Under legal execution
three classes of constraints stack up: the mask is monotonically
non-increasing (construct 2) ⇒ pure taken-path nesting ≤ 5 levels (construct
3); deep peeling can happen only on the larger side with a net occupancy of 1
entry (construct 4) ⇒ the peak of 31 levels of peeling = 30 + 2 = 32. The
original analysis multiplied "2 entries/level" by "31 levels of depth", but
these two costs are mutually exclusive (deep nesting requires the mask to be
divisible; peeling requires the mask to be down to 2) and cannot be added.

### 3.2 Root cause

The absence of full detection is a design choice, not a coding mistake: the
author (or the refactorer) sized the stack with depth=num_thread, implicitly
relying on the conjunction of "mask discipline + takeif-smaller-side + LIFO"
to guarantee no overflow — this project's work turned that implicit argument
into a machine-checked theorem.

### 3.3 Harm and tolerability

- **Harm (if reachable)**: reconvergence bookkeeping corruption — a warp mask
  permanently incomplete (some threads never restored), or ghost re-entry into
  an already-reconverged path; silent, no trap.
- **Tolerability**: unreachable under legal execution (main-theorem-level
  guarantee, covering "arbitrary event sequences" and a tight-bound witness).
  The residual risk is **future changes breaking a premise** (any of mask
  discipline, takeif-smaller-side, LIFO pop order) — hence the recommendation
  to add an overflow assertion upstream as online detection, rather than
  changing the stack depth. Reclassified: non-urgent.

---

## 4. Lean Formal Evidence

All with zero sorry, full build passing (axiom audit archived in module report
doc/modules/15 §6).

**Mechanism witnesses** (`lean/Ventus/SIMT/BranchJoinOverflow.lean`, real
parameters depth=32, native_decide):

- `bjoT1_wr_unwrapped`: after 17 pushes wr=34 (the 6-bit pointer itself has
  not wrapped);
- `bjoT2_slot_alias` / `bjoT3a_slots_before` / `bjoT3b_slots_after`: level 17
  writes slots 32/33 ≡ mod 32 slots 0/1, with before/after snapshots of
  overwriting level 1;
- **`bjoT5_witness_lost_join`** (lost reconvergence) and
  **`bjoT6_witness_ghost_pop`** (ghost re-entry): the output divergence
  between the concrete model and an unbounded ideal stack (`bjoIdealStep`)
  nails down the harm. Note: the mod semantics is the "mildest concretization";
  real hardware Mem out-of-bounds behavior is undefined and can only be worse.

**Unreachability main theorem** (`lean/Ventus/SIMT/BranchJoinBounds.lean`,
abstract protocol layer):

- Supporting lemmas (fully proved):
  `bjbPopcount_or_of_disjoint`/`bjbPopcount_partition` (popcount form of mask
  partitioning), `bjbTakeif_if_half`/`bjbTakeif_else_half` (the taken side
  halves), `bjbLegal_step` (preservation of the legality invariant),
  `bjbWr_le_32` (occupancy ≤ 32 in legal states);
- Main theorem **`bjbMain_no_overflow`**: in a legal state (invariant
  `bjbLegal` encoding mask discipline / takeif-smaller-side / LIFO peeling),
  after executing **any event sequence** the stack occupancy ≤ 32 =
  depth_stack, and legality is preserved (can continue indefinitely);
- Tight-bound witness **`bjbTight_peel_peak`** (native_decide): a 31-level
  peeling trace reaches wr exactly = 32 — 32 is not a conservative margin but
  a tight bound;
- Concrete bridging: `bjbWr_nop/branch/join` (wr bookkeeping), `pcB5_peak`
  (5-level peeling peak with nT=depth=6),
  `ha_halve_level5`/`ha_halve_level6_nodiv` (32 threads halved for 5 levels of
  nesting gives wr=10; a 6th level with divOccur is impossible).

**Explicit downgrade**: the **full refinement from the concrete model to the
abstract model is unproved** — the bridging lemma aligning concrete traces to
abstract events is missing; the required assumptions (1)-(4) are listed item
by item in the header of BranchJoinBounds.lean, of which the popcount forms of
mask discipline and takeif-halving are fully proved, peeling's net occupancy
of 1 entry and LIFO pairing are direct source facts of
branch_join.scala:57-59/:48-56, plus a wid timing-consistency assumption
(pipe.scala:293). Residual premises at the [direct source reading] level are
faithfully registered.

---

## 5. Simulation Verification

**No RTL reproduction, and none is planned**: the overflow scenario requires
17 levels of nesting with maskInit constantly all-ones, which violates the
mask discipline (pipe.scala:366) and corresponds to no legal kernel trace —
it cannot be triggered by any legal program on RTL, only by breaking wires
(at which point what is being tested is no longer the original design). The
ChiselSim/Verilator channels of doc/22 have no test case for this entry.
**Not executed in this environment; the mechanism evidence rests on the Lean
witnesses** (§4).

---

## 6. Upstream Impact Analysis

- No functional impact under the current configuration (exactly sized);
- The fragility concentrates on three implicit premises: the mask is
  monotonically non-increasing (pipe.scala:366), takeif always picks the
  smaller side (branch_join.scala:145), push-two-entries/LIFO pop order
  (:47-60). If any premise is broken by a future change, overflow becomes
  reachable and undetected — silent bookkeeping corruption;
- Recommendation to upstream: add an overflow assertion (e.g.
  `assert(wr_ptr < depth_stack.U)` or `wr_ptr + 2.U <= depth_stack.U` on
  push), costing one line, turning the implicit argument into online
  detection.

---

## 7. Fix Plan and Fix Verification

**No patch** (the internal fix manifest: Defense-in-depth, "patch to be refined" — the
assertion form awaits alignment with upstream style; payoff is low because the
stack has been proven exactly sized). No VentusF fix variant (the internal fix manifest:
the original-side proof already covers it).

This entry's "fix verification" is borne by proofs: `bjbMain_no_overflow` is
the machine-checked proof that "no fix is needed", and `bjbTight_peel_peak`
is the machine-checked proof that "the margin is zero — it must not be made
smaller".

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | branch_join.scala:24-63 no overflow protection; :145 takeif-smaller-side; pipe.scala:366 mask discipline; :57-59 LIFO pop | line-by-line check |
| Lean mechanism witnesses | `bjoT1_wr_unwrapped`/`bjoT2_slot_alias`/`bjoT3a`/`bjoT3b`/`bjoT5_witness_lost_join`/`bjoT6_witness_ghost_pop` (real parameters depth=32, native_decide) | concrete-trace level |
| Lean unreachability proof | `bjbPopcount_partition`/`bjbTakeif_if_half`/`bjbTakeif_else_half`/`bjbLegal_step`/`bjbWr_le_32` → **`bjbMain_no_overflow`** (arbitrary event sequences, inductive full proof) | universal level (abstract layer) |
| Tight-bound witness | `bjbTight_peel_peak` (wr exactly = 32); `bjbTight_peel_drain` (drain and recover) | concrete-trace level |
| Downgrade registration | concrete→abstract full refinement unproved; assumptions (1)-(4) listed in the file header | explicit |

I-2 is a paradigmatic case of "the paper analysis was wrong; formalization
corrected it and closed the question": the initial verdict "16 levels already
overflow" was refuted by mask-chain tracing, and the final conclusion was
upgraded from an argument to a theorem — **the stack is exactly sized; 32 is a
tight bound; the overflow mechanism is real but unreachable under legal
execution**. Disposition: non-urgent; recommend an upstream overflow assertion
as defense-in-depth.
