> English translation of the Chinese master `doc/bugs/I-4-记分板同拍置清竞态.md`. Translated 2026-09-13.

# I-4 Detailed Defect Report: on a same-cycle "dequeue + new occupancy" the OpColReg occupancy bit is wrongly cleared (mechanism confirmed / currently unreachable in the integration)

| Item | Content |
|---|---|
| ID | I-4 |
| Source location | `ventus/src/pipeline/scoreboard.scala:115-118` (OpColRegV/X set before clear); unreachability argument chain `pipe.scala:223` → `warp_schedule.scala:181` → `pipe.scala:161` → `scoreboard.scala:131,142`; corroborating evidence `operandCollector.scala:565-568` (instDemux widCmp dead code) |
| Type | Functional bug (occupancy bookkeeping race) — structurally-mutually-exclusive unreachable (doc/14 §1) |
| Severity | Medium-high at the mechanism level (when reachable = two instructions of the same warp in the collector + out-of-order issue); currently unreachable in the integration, rated latent/defense-in-depth |
| Confirmation status | 【Mechanism confirmed / currently unreachable in the integration】 — the mechanism has a machine-checked witness, the unreachability has an invariant-induction proof; this entry is also the subject of III-3 (the reachability analysis was once misjudged and later corrected) |
| Primary evidence | [Lean machine-checked proof] the full I4Fix.lean chain (mechanism pinning + gated-unreachability invariant + fixed-version verification); [direct source reading] line-by-line check of the four gating-chain sites |
| Lean model | `lean/Ventus/Schedule/Scoreboard.lean` (mechanism at bit level), `lean/Ventus/Schedule/I4Fix.lean` (719 lines, fixed version + gated system), `lean/Ventus/Schedule/OperandCollector.lean` (ungated witness `ocI4_C_issues_before_B`) |
| Reproduction/patch | Not reproducible under the current integration; a ChiselSim directed test for the broken-window scenario (adding a pipeline stage to the gating chain) is ready to be written. Patch `i04-scoreboard-set-clear.patch` (internal fix manifest; not released) (defense-in-depth, the internal fix manifest category "Defense-in-depth") |
| Related entries | III-3 (the misjudgment and correction of this entry's reachability analysis), I-12 (same module, doc/bugs/I-12), doc/14-不可达缺陷分析 §1, doc/modules/10-Schedule-Scoreboard与I4Fix.md |

---

## 0. Abstract

The issue scoreboard (Scoreboard) maintains a 1-bit OpColReg occupancy bit per
warp, meaning "this warp has an instruction inside the operand collector". The
occupancy bit is set when an instruction enters the collector
(`OpColRegV.set(op_colV_in_fire)`) and cleared when collection completes and
the instruction issues (`OpColRegV.clear(op_colV_out_fire)`). The source
writes set before clear (scoreboard.scala:115-118), and ScoreboardUtil's
chained semantics is "last write wins" — **when a dequeue and a new occupancy
happen in the same cycle, the occupancy bit is wrongly cleared**.

Consequence chain: occupancy bit wrongly cleared → the scoreboard thinks the
warp has no instruction in the collector → a second instruction of the same
warp is admitted into the collector (the collector layer has no same-warp
deduplication; instDemux's widCmp is dead code tied to 0) → an
all-immediate instruction can issue ahead of the stranded instruction —
**out-of-order**.

But this race is **unreachable from reset**: the issue gating chain is
combinational end to end; an enqueue event at cycle T requires the occupancy
bit to be 0 at the start of cycle T, while a dequeue event requires it to be 1
at the start of cycle T — two same-cycle events require the same register to
be both 0 and 1 in the same cycle, a contradiction. This unreachability is
machine-checked by the invariant-induction theorem `i4f_no_two_busy_orig`.
The fix (swapping the program order of set/clear to "set wins") is still
recommended as defense-in-depth, has been modeled and verified, and is in the
patch tree.

This entry's methodological value: it is this project's emblematic case of
"**structural possibility ≠ reachability**" — the earlier analysis looked only
at collector-side structural possibility and judged "reachability confirmed",
missing the gating side; it was caught and corrected by the Lean invariant
proof (recorded as III-3).

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **Scoreboard**: the hazard-blocking hub of the GPU issue path, one instance
  per warp (`scoreb(i)` in pipe.scala). It maintains several "occupancy bits":
  256 per-register occupancy bits each for vector/scalar registers, plus 1 bit
  each for beq/opColV/opColX/fence. When any relevant occupancy bit is set,
  the warp's next dependent instruction is blocked from issuing (the `delay`
  output is the OR of nine blocking sources, scoreboard.scala:142).
- **OpColReg occupancy bit**: opColV/opColX correspond to the vector/scalar
  channels respectively, with the semantics "this warp has an instruction
  collecting operands inside the operand collector". Its role is the
  **serialization of same-warp instructions inside the collector**: the
  collector has multiple collector units (CUs); without this occupancy-bit
  gating, multiple instructions of the same warp could occupy multiple CUs
  simultaneously, breaking program order.
- **ScoreboardUtil chained semantics**: occupancy-register updates are written
  as chained `set/clear` calls on a Scala var; multiple operations in the same
  cycle fold in program order — **last write wins** (proved on the Lean side
  as theorem `sb_clear_wins`).

### 1.2 Design intent

The occupancy bit is set when an instruction issues into the collector
(`op_colV_in_fire`); it is cleared when the collector has gathered the
operands and the instruction issues to an execution unit
(`op_colV_out_fire`). Normally the two events are many cycles apart
(collection takes at least several cycles of register-file reads/writes), so
the order of set and clear does not matter. The design did not consider the
race cycle of "same-cycle dequeue+enqueue" — which is exactly where the
defect lies.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: set before clear (★ hazard)** (scoreboard.scala:115-118):

```scala
OpColRegV.set(io.op_colV_in_fire, 0.U)    // :115  set first
OpColRegV.clear(io.op_colV_out_fire, 0.U) // :116  clear afterwards — with two same-cycle events the clear wins
OpColRegX.set(io.op_colX_in_fire, 0.U)    // :117
OpColRegX.clear(io.op_colX_out_fire, 0.U) // :118
```

ScoreboardUtil's chained semantics (the `_next` var folding at :90-97) makes
the result of same-cycle set+clear be clear — the occupancy bit is wrongly
zeroed (pinned at bit level in Lean: `sb_clear_wins`, `i4f_orig_race_loses`).

**Construct 2: the occupancy bit enters the issue gating (all-combinational
chain)**:

```scala
// scoreboard.scala:131,142
val read_op_colV=OpColRegV.read(0.U)                 // reads the register's current value (combinational)
io.delay:=read1|…|readf|read_op_colV|read_op_colX    // :142 OR of nine sources
```

```scala
// pipe.scala:161
warp_sche.io.scoreboard_busy:=(VecInit(scoreb.map(_.delay))).asUInt
```

```scala
// warp_schedule.scala:181
val warp_ready=(~(warp_bar_data | io.scoreboard_busy | io.exe_busy | (~warp_active).asUInt)).asUInt
```

```scala
// pipe.scala:223
ibuffer2issue.io.in(i).valid:=ibuffer.io.out(i).valid & warp_sche.io.warp_ready(i)
```

All four wirings are **purely combinational, without a single register
stage**: the occupancy bit's current register value participates in issue
gating in the very same cycle. This chain is the key fact for the
reachability denial (§3.2).

**Construct 3: no same-warp deduplication at the collector layer**
(operandCollector.scala:565-568):

```scala
//Since arbitration has finished in scoreboard, each instruction in this stage
//  should fetch operand unless there is no more collect unit.
(0 until num_collectorUnit).foreach( i => {
  //    widCmp(i) := io.control.bits.wid===collectorUnits(i).wid   // commented out
  widCmp(i) := 0.U                                                  // tied to 0
})
```

instDemux's same-warp comparison is commented out and widCmp is tied to all 0
— the comment itself says "arbitration has finished in scoreboard". That is,
the collector side **fully outsources** the invariant "at most one instruction
per warp is collecting" to the scoreboard occupancy bit. Once the occupancy
bit is wrongly cleared, the collector has no second line of defense inside.

---

## 3. Defect Analysis: Mechanism and Unreachability Argument

### 3.1 Precise description of the mechanism (confirmed)

When `op_colV_in_fire` (a new instruction of warp w entering the collector)
and `op_colV_out_fire` (an old instruction of warp w finishing collection and
issuing) hold in the same cycle:

1. Construct 1 causes OpColRegV(w) to be zeroed (it should be 1 — the new
   instruction has just entered the collector);
2. From cycle T+1 the scoreboard thinks w has no instruction in the
   collector, and a third instruction of w may enter the collector again —
   multiple same-warp instructions coexist in multiple CUs;
3. Construct 3 provides no deduplication backstop; an all-immediate
   instruction needs no register-file reads and can issue ahead of the
   stranded instruction still waiting for a bank response — **out-of-order
   issue**.

In the ungated model this out-of-order witness is machine-checked:
`ocI4_C_issues_before_B` in OperandCollector.lean (instruction C issues ahead
of B, which precedes it in program order).

### 3.2 Reachability denial (unreachable from reset, machine-checked)

The gating chain (construct 2) is fully combinational. Consider any cycle T:

- The **enqueue event** `op_colV_in_fire(w)` requires the instruction to be
  accepted by the collector in that cycle, i.e. `controlV.fire(w)`; and
  controlV's valid is gated by warp_ready (pipe.scala:223 ←
  warp_schedule.scala:181 ← pipe.scala:161 ← scoreboard.scala:142,131),
  which requires `read_op_colV = 0`, i.e. **occ(w) is 0 at the start of
  cycle T (the register's current value)**;
- The **dequeue event** `op_colV_out_fire(w)` requires w's instruction to
  already be inside some CU with collection complete, and when it entered
  the CU the occupancy bit was set, and the occupancy bit is cleared only by
  a dequeue event — hence **occ(w) is 1 at the start of cycle T**.

Two same-cycle events require the same register to be both 0 and 1 at the
start of cycle T — a contradiction. The race cannot bootstrap itself from
reset.

Formalization: `lean/Ventus/Schedule/I4Fix.lean` builds a gated 2-CU
single-warp scaled system (`I4fSysState`, gating
`controlV.valid = offer ∧ occ=0`), with the inductive invariant `i4fSysInv`
(including "occ ⟺ the warp has an instruction in the collector" and "at most
one CU busy"), preserved from reset for arbitrary input sequences:

- **`i4f_no_two_busy_orig`**: under the original version's gating, after any
  input sequence there do not exist two CUs simultaneously holding
  instructions of that warp — the mechanism premise of out-of-order does not
  hold;
- **`i4f_witness_shape_unreachable`**: the concrete shape of the I-4 witness
  (CU0 in s_add ∧ CU1 in s_out) is unreachable under the gating;
- **`i4fSys_run_eq_orig`**: under the gating the fixed version and the
  original are stepwise equivalent — the fix does not change any reachable
  behavior.

### 3.3 Misjudgment-correction record (III-3)

The earlier reachability analysis (2026-08-25, wave 3) argued only
collector-side structural possibility (in and out can happen in the same
cycle in different CUs), **missing the gating side**, and judged
"reachability confirmed". agent-21 discovered and proved the contradiction
while modeling I4Fix (`i4f_no_two_busy_orig`); on 2026-08-27 the main session
re-checked the four line numbers of the source chain and confirmed the
correction, recorded as III-3. The lesson has been written into doc/03
§III-3: **a reachability argument must cover the complete enable chain
(including upstream gating)**.

### 3.4 Harm and tolerability

- **If reachable**: same-warp instructions issue out of order, with
  all-immediate instructions jumping the gun — silent-wrong-data level
  (depending on the concrete program).
- **Current integration**: unreachable (§3.2 machine-checked), no realistic
  harm.
- **Broken-window condition**: inserting any pipeline register into the
  gating chain (e.g. adding a register between ibuffer2issue and the
  scoreboard for timing optimization) makes occ read a stale value, and the
  race becomes reachable. The consequences then fully materialize along the
  §3.1 chain.
- **Conclusion**: mechanism confirmed / currently unreachable in the
  integration; the fix is treated as defense-in-depth (§5).

---

## 4. Lean Formal Evidence

All machine-checked (zero sorry, full build passing; audit see
doc/modules/10 §6).

**Mechanism pinning (bit level, bv_decide)**:

- `sb_clear_wins` (Scoreboard.lean): ScoreboardUtil chained semantics last
  write wins — for same-cycle set+clear the address reads back 0, for
  arbitrary prior state;
- `i4f_orig_race_loses` vs `i4f_race_gone` (I4Fix.lean): after same-cycle
  in+out the original occupancy bit ends at 0, the fixed version stays at 1
  (arbitrary prior state r);
- `i4f_occOrig_spec` / `i4f_occFix_spec`: event specifications of the two
  versions' occupancy bits — original `occ' = (in || occ) && !out`, fixed
  `occ' = in || (occ && !out)`.

**Ungated witness (mechanism reachability, control group)**:

- `ocI4_C_issues_before_B` (OperandCollector.lean:1437): a concrete trace in
  which, without gating, C issues ahead of B;
- `i4fT_race_orig` vs `i4fT_race_fix` (I4Fix.lean, native_decide): in the
  ungated race cycle the original's occ wrongly ends at 0 while the fixed
  version stays at 1 — the broken-window control.

**Gated unreachability (invariant induction, arbitrary input sequences)**:

- `i4fSys_run_inv_fix`: invariant-induction preservation of the fixed gated
  system (the heaviest proof in this file);
- **`i4f_no_two_busy_orig`**: under the original version's gating, ≤1 CU busy
  — the main unreachability theorem;
- `i4f_witness_shape_unreachable`: exclusion of the witness shape;
- `i4fSys_run_eq_orig`: under the gating the fixed version ≡ the original
  (stepwise equivalence).

**Fixed-version verification**:

- `i4f_race_gone`, `i4f_set_wins` (set wins in general form),
  `i4f_occ_tracks_busy` (the fixed occ precisely tracks collector occupancy);
- `i4f_sbRun_equiv`: for race-free input sequences the fixed and original
  versions are stepwise equivalent over whole traces — regression safety;
- `i4f_no_two_busy_fix` (under the fixed version's gating, likewise no double
  occupancy);
- Numeric traces: `i4fT_gated_C_blocked` (the gating blocks C),
  `i4fT_B_issues_first`/`i4fT_C_after_B` (program order restored under
  gating), `i4fT_ungated_fix_still_oob` (ungated, even with the occupancy bit
  fixed, the absence of widCmp deduplication still yields out-of-order —
  confirming that the scoreboard fix and collector deduplication are two
  complementary lines of defense).

---

## 5. Simulation Verification

【Ready-to-run (not executed in this environment)】Under the current
integration this race is unreachable (§3.2), **there is no baseline to
reproduce**; a ChiselSim directed test for the broken-window scenario
(same-cycle in+out after inserting a pipeline stage into the gating chain) is
ready to be written (doc/03 I-4 reproduction-method entry).
doc/22-复现执行结果.md has no simulation record for this entry — consistent
with the "unreachable" verdict (simulation can only falsify unreachability,
not confirm it; confirmation rests on the invariant theorems of §4).

The patch `i04-scoreboard-set-clear.patch` has been regression-verified with
no side effects in the 38-patch combined tree (2026-09-10, doc/22 §"38-patch
combined tree regression") [simulation run].

---

## 6. Fix Plan and Fix Verification (Defense-in-Depth)

**Patch** (`i04-scoreboard-set-clear.patch` (internal fix manifest; not released), two edit
points at scoreboard.scala:115-118): swap the program order of set/clear for
OpColRegV/X — `clear` first, then `set`; the same-cycle merge semantics
changes from "clear wins" to "**set wins**". The in-patch comment states the
positioning: "under the current integration this race is masked by the gating
structure; this is defense-in-depth".

**Fix verification** [Lean machine-checked proof]: effectiveness
(`i4f_race_gone` — the occupancy bit stays 1 in the race cycle,
`i4f_occ_tracks_busy`), regression safety (`i4f_sbRun_equiv` — stepwise
equivalence on race-free sequences, `i4fSys_run_eq_orig` — stepwise
equivalence with the original under gating).

**Second line of defense (not implemented, recommended to keep)**: restore
instDemux's wid deduplication (uncomment widCmp at
operandCollector.scala:566) — a collector-side line of defense independent
of the gating; `i4fT_ungated_fix_still_oob` proves the two are complementary,
and neither alone prevents the "post-broken-window" out-of-order.

---

## 7. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Mechanism (Lean machine-checked proof) | `sb_clear_wins` + `i4f_orig_race_loses`: same-cycle in+out wrongly clears the occupancy bit | bit level, fully symbolic |
| Mechanism-reachability control (Lean) | `ocI4_C_issues_before_B`, `i4fT_race_orig/fix`: out-of-order really happens ungated | concrete-trace witness |
| Unreachability (Lean machine-checked proof) | `i4f_no_two_busy_orig` + `i4f_witness_shape_unreachable` + `i4fSys_run_eq_orig` | invariant induction, arbitrary input sequences |
| Direct source reading | line-by-line check of scoreboard.scala:115-118/131/142, pipe.scala:223/161, warp_schedule.scala:181, operandCollector.scala:565-568 | four files consistent |
| Simulation | baseline not reproducible (consistent with the unreachability verdict); the patch passes the 38-patch combined-tree regression with no side effects | ready-to-run + actually measured (regression) |
| Fix verification | i04 patch (2 edit points); Lean fixed-version effectiveness + regression safety | machine-checked |

I-4's final characterization is **mechanism confirmed, currently excluded in
the integration by the structural fact that "the issue gating chain is
all-combinational"**. Together with this series' other exclusion case I-9, it
forms the core methodological argument of doc/14: **the strong meaning of
"cannot reproduce" is that unreachability has an invariant theorem**, not that
testing has not covered it; every exclusion conclusion comes with a precise
broken-window condition (inserting a pipeline stage into the gating chain),
attributing safety to monitorable engineering contracts. At the same time it
is the carrier of III-3 — formal methods caught and corrected an error in the
manual reachability analysis, a direct demonstration of this project's thesis
"proof beats paper review".
