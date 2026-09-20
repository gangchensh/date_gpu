> English translation of the Chinese master `doc/bugs/I-3-elseOnly死锁排除.md`. Translated 2026-09-13.

# I-3 Detailed Defect Report: an elseOnly branch does not raise `complete`, and the scoreboard beqReg might never be cleared 【Excluded】

| Item | Content |
|---|---|
| ID | I-3 |
| Source location | `ventus/src/pipeline/branch_join.scala:120` (the complete condition contains `takeif`), `:145` (takeif definition); contrast with the dead code `SIMT_STACK.scala:211` (complete condition `!elseOnly`); related `scoreboard.scala:113/:142`, `pipe.scala:252-254/:388`, `DecodeUnit.scala:473-479` |
| Type | Suspected functional bug (warp deadlock: the beqReg occupancy bit never cleared) → excluded after investigation |
| Severity | None (excluded); residual fragility see §3.4 |
| Confirmation status | 【Excluded】 (2026-08-25, decode evidence + clear-path analysis; doc/03 original verdict carried over verbatim) |
| Primary evidence | [Direct source reading] line-by-line check of the complementary fetch_ctl/complete chain; [Lean machine-checked proof] behavior pinning `tD_elseOnly` |
| Lean model | `lean/Ventus/SIMT/BranchJoin.lean` (test `tD_elseOnly` pins down the real behavior that complete is not raised under elseOnly) |
| Reproduction/patch | None (excluded entry); the internal fix manifest: No fix (excluded) |
| Related entries | I-1 (the complete-semantics divergence between the two versions is exactly an instance of that dead code's misdirection) |

---

## 0. Abstract

In `branch_join`, the condition for raising the vbranch completion signal
`complete` contains `takeif` (branch_join.scala:120), and `takeif` is
constantly false under elseOnly (the if-side mask is empty) (:145) — at first
glance a suspicion: an elseOnly branch never raises complete, while complete
is one of the ways the scoreboard clears beqReg (the branch-instruction
occupancy bit); if beqReg is never cleared, that warp is blocked by `delay`
and never issues again — **suspected warp deadlock**.

Investigation conclusion: **excluded**. beqReg has two **complementary** clear
paths (pipe.scala:252-254): `simt_stack.io.complete` and
`warp_sche.io.branch.fire` (the arbitration output of branch_back, whose in1
is exactly `simt_stack.io.fetch_ctl`, pipe.scala:388). In branch_join, the
fetch_ctl trigger condition for a vbranch is exactly `!takeif || elseOnly`,
**exactly complementary** to complete (= takeif): under elseOnly fetch_ctl
must fire (jumping to PC_branch) → beqReg is cleared via branch_back. At JOIN,
fetch_ctl always fires. Hence every vbranch/join takes at least one clear
path, and the deadlock suspicion is excluded (premise: warp_sche accepts
branch requests normally).

Residual observation: the complete semantics is inconsistent between the two
versions (SIMT_STACK's `!elseOnly` vs branch_join's `takeif`), and correctness
relies on the **implicit contract** that "fetch_ctl and complete are
complementary" — fragile but currently holding.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **Scoreboard**: a set of occupancy bits per warp, guarding against data
  hazards and structural conflicts. `beqReg` is the branch occupancy bit: it
  is set when a warp issues a branch/barrier-class instruction
  (scoreboard.scala:113); while set, that warp is blocked from issuing by the
  `delay` signal (:142), until the branch is resolved.
- **complete / fetch_ctl**: the SIMT stack's two kinds of reports for branch
  events. `complete` (Valid) tells the scoreboard "this warp's branch
  bookkeeping can be cleared"; `fetch_ctl` (Decoupled) tells the fetch side
  "jump/pop to a new PC". The two go to different consumers and have different
  semantics.
- **elseOnly / takeif**: on a vector branch, if the if-side mask is empty
  (elseOnly), all active threads take the else side.
  `takeif := ((ifCnt < elseCnt) && divOccur) || ifOnly` (:145) — under
  elseOnly, divOccur=false and ifOnly=false, hence takeif=false.

### 1.2 Design intent

complete is raised only when "the if side is chosen first" (takeif); going to
the else side or jump-class events instead rely on fetch_ctl to notify the
fetch side. Each of the two signals covers only half of the branch events —
the suspicion is precisely whether the scoreboard's beqReg can always be
cleared by one of them.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the complete condition contains takeif**
(`branch_join.scala:120`, ★ scene of the suspicion):

```scala
io.complete.valid := (if_mask_buf.fire & opcode === 0.U & branch_ctl_buf.valid & takeif)
```

elseOnly (if_mask==0) ⇒ takeif=false ⇒ complete is not raised. Contrast with
the dead code SIMT_STACK.scala:211, whose complete condition is `!elseOnly` —
**the two versions diverge semantically** (an instance of I-1's misdirection
risk).

**Construct 2: beqReg set and clear** (`scoreboard.scala:113/:142`,
`pipe.scala:252-254`):

```scala
beqReg.set(io.if_fire & ((io.if_ctrl.branch=/=0.U)|(io.if_ctrl.barrier)),0.U)  // :113 set
beqReg.clear(io.br_ctrl,0.U)                                                     // clear
io.delay := read1|read2|read3|readm|readw|readb|readf|read_op_colV|read_op_colX  // :142 includes beqReg
```

```scala
// pipe.scala:252-254: the three sources of br_ctrl
when(warp_sche.io.branch.fire && ...)          { scoreb(i).br_ctrl := true.B }.   // path A
  elsewhen(warp_sche.io.warp_control.fire && ...){ scoreb(i).br_ctrl := true.B }.
  elsewhen(simt_stack.io.complete.valid && ...)  { scoreb(i).br_ctrl := true.B }   // path B
```

`warp_sche.io.branch` is branch_back's arbitration output, and
`simt_stack.io.fetch_ctl` connects to its in1 (pipe.scala:388) — i.e.
**fetch_ctl firing also clears beqReg**.

**Construct 3: fetch_ctl and complete are complementary**: in branch_join, the
fetch_ctl trigger condition for a vbranch is `!takeif || elseOnly` (when
taking the else side one must jump to PC_branch); at JOIN (opcode=1),
fetch_ctl always fires. Disjoint from and exhaustive together with complete
(= takeif).

**Construct 4: decode evidence** (`DecodeUnit.scala:473-479`):
VBNE/VBEQ/VBLT/VBLTU/VBGE/VBGEU and JOIN all decode to `branch = B_B ≠ 0` —
so at issue beqReg is **indeed set**; the premise of the suspicion is real
(it is not "never set anyway so it doesn't matter").

---

## 3. Defect Analysis

### 3.1 Description of the suspicion and the exclusion argument

**Suspicion chain**: elseOnly vbranch → complete not raised (construct 1) →
if beqReg had only complete as its clear path → beqReg set forever → delay
blocks forever → warp deadlock.

**Exclusion**: beqReg has a second clear path (construct 2 path A:
branch.fire ← branch_back ← fetch_ctl). Case-by-case check:

| Branch event | takeif | complete | fetch_ctl | Clear path |
|---|---|---|---|---|
| Divergence choosing the if side | true | **raised** | does not fire | path B |
| Divergence choosing the else side (incl. elseOnly) | false | not raised | **fires** (jump to PC_branch) | path A |
| ifOnly / no divergence | true (ifOnly) | raised | conditional | ≥1 path |
| JOIN | — | — | **always fires** | path A |

Every vbranch/join takes at least one clear path — the deadlock suspicion is
excluded. Premise: warp_sche accepts branch requests normally (branch_back's
downstream does not deadlock by backpressure; that premise is warp_sche's own
responsibility).

### 3.2 Root cause (why the suspicion arose)

The semantic split between complete and fetch_ctl ("complete only when the if
side is chosen") looks like a coverage gap when viewed within a single module;
only by tracing to the scoreboard side's two clear paths and finding that the
two are **exactly complementary** does the suspicion dissolve. This kind of
"cross-module complementarity contract" is the form most easily misjudged by
paper review (contrast the methodological lesson of III-3: reachability /
exclusion arguments must cover the complete enable chain).

### 3.3 Harm and tolerability

No harm after exclusion. **Residual fragility**: correctness relies on the
implicit contract "fetch_ctl and complete are complementary" — if a future
change alters either condition (e.g. a tweak of the complete condition, or
narrowing the fetch_ctl trigger condition) without synchronizing the other
side, the beqReg clear chain truly breaks into a deadlock. Recommend upstream
fix the complementarity into an assertion or a comment.

### 3.4 Relationship with I-1

SIMT_STACK.scala:211's complete condition is `!elseOnly` (raised under
elseOnly), exactly opposite to branch_join's `takeif` (not raised under
elseOnly). A reviewer reading the dead code SIMT_STACK (I-1) would acquire a
completely different understanding of the complete semantics — this entry's
investigation experienced that divergence firsthand and is empirical evidence
of I-1's maintenance risk.

---

## 4. Lean Formal Evidence

- **Behavior pinning** [Lean machine-checked proof]: the test
  **`tD_elseOnly`** in `lean/Ventus/SIMT/BranchJoin.lean` (native_decide
  multi-cycle trace) pins down that the model behavior "complete is not raised
  under elseOnly" agrees with the source — the suspicion's premise (complete
  not raised) is faithfully present in the model, so the exclusion does not
  rest on the luck of "the model happened to get complete right".
- **Complementarity fact**: the complementary relation between the fetch_ctl /
  complete trigger conditions on the branch_join side has been modeled after
  the source in `bjSysStep` (module report doc/modules/15 §2.3); the clear
  path itself (pipe.scala wiring + scoreboard clear) is [direct source
  reading] evidence, with no whole-machine-level theorem built — the evidence
  layering of the exclusion conclusion is faithfully annotated.

---

## 5. Simulation Verification

Not applicable: an excluded entry, no reproduction needed (the exclusion rests
on source-chain checking + model behavior pinning). The ChiselSim/Verilator
channels of doc/22 have no test case for this entry. **Not executed in this
environment**.

---

## 6. Upstream Impact Analysis

- No functional issue under the current design (every branch event has at
  least one clear path);
- The recommendation to upstream is at documentation/assertion level: annotate
  near branch_join.scala:120 or scoreboard.scala:113 that "complete and
  fetch_ctl cover branch events complementarily, and beqReg clearing relies on
  this complementarity", guarding against future one-sided changes.

---

## 7. Fix Plan and Fix Verification

No fix (the internal fix manifest: No fix (excluded)). No corresponding variant in VentusF.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | line-by-line check of branch_join.scala:120/:145, scoreboard.scala:113/:142, pipe.scala:252-254/:388, DecodeUnit.scala:473-479; the clear-path complementarity table | line-by-line check |
| Lean machine-checked proof | `tD_elseOnly` (behavior pinning that complete is not raised under elseOnly); the fetch_ctl/complete complementary relation modeled after the source | concrete-trace level + modeling consistency |
| Simulation | none (excluded entry, not executed) | — |

I-3 is an exclusion case of the "cross-module complementarity contract" type
of suspicion: the coverage gap inside a single module (complete raised only
under takeif) is exactly filled by the scoreboard side's second clear path;
the exclusion holds but relies on an implicit contract. Residual
recommendation: upstream should fix the complementarity with a
comment/assertion. Status remains 【Excluded】.
