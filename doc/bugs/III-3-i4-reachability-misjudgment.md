> English translation of the Chinese master `doc/bugs/III-3-I4可达性误判.md`. Translated 2026-09-13.

# III-3 Lessons Record: The I-4 reachability analysis error (wave-3 main-session conclusion, corrected in wave 11)

| Item | Content |
|---|---|
| ID | III-3 (Class III: specification/proof-side error — a **reachability argument** that missed upstream gating) |
| Location | Related to I-4 (`scoreboard.scala:115-118`, the OpColReg same-cycle "dequeue + new occupancy" race); corrective evidence `lean/Ventus/Schedule/I4Fix.lean`; gating source chain pipe.scala:223 → warp_schedule.scala:181 → pipe.scala:161 → scoreboard.scala:131,142 |
| When found | The wrong conclusion was made in wave 3; discovered and corrected by agent-21 during wave-11 modeling, and confirmed by the main session re-checking the source chain |
| Status | Corrected: I-4 reclassified as 【Mechanism confirmed / currently unreachable in the current integration】; same-kind risk sweep completed (on record in doc/03) |

---

## Background

I-4's mechanism (real, undisputed): in scoreboard.scala:115-118, `OpColRegV.set(...)` is followed by `OpColRegV.clear(...)`; ScoreboardUtil's same-cycle chained semantics is last-write-wins (proven on the Lean side as `sb_clear_wins`) — when in_fire (a new instruction issues into the collector) and out_fire (an instruction leaves the collector) occur on the same cycle, the occupancy bit is wrongly cleared, which can leave multiple instructions of the same warp stranded in the collector and cause out-of-order issue.

The dispute was only about **reachability**: the wave-3 main session adjudicated "reachability confirmed"; wave 11 overturned it.

## The problem

Wave 3's reachability conclusion only argued for **structural possibility on the collector side** — in_fire and out_fire belong to different collectorUnits, so they can structurally occur on the same cycle. But this **missed the gating side**: OpColReg is a register, and the warp issue gating chain combinationally reads its current value, along the chain [direct source reading, re-confirmed by the main session]:

- `pipe.scala:223`: `ibuffer2issue.in(i).valid = ibuffer.out(i).valid & warp_sche.warp_ready(i)`;
- `warp_schedule.scala:181`: `warp_ready = ~(… | scoreboard_busy | …)`;
- `pipe.scala:161`: `scoreboard_busy = VecInit(scoreb.map(_.delay))`;
- `scoreboard.scala:131,142`: `delay` includes `read_op_colV` — the OpColRegV **register's current value** read out combinationally.

Hence the constraints at cycle T are:

- in_fire(w) (a new instruction enters the CU) requires the gate to pass ⇒ at the **start** of T, occ(w)=0 (the register value at the start of T);
- out_fire(w) requires w's instruction to already be inside the CU — and when it entered the CU, occ was set, and it is only cleared by out_fire ⇒ at the **start** of T, occ(w)=1.

Same-cycle occurrence of both events requires occ to be both 0 and 1 on that cycle — a **contradiction**. Same-cycle in+out is unreachable from reset; the correct adjudication of I-4 is "mechanism confirmed, unreachable in the current integration" (broken-window scenario = inserting a pipeline stage into the gating chain so that occ reads a stale value; the fixed version swaps set/clear as defense in depth, modeled and verified in I4Fix.lean).

## Evidence

- [Lean machine-checked proof] Discovered and proven by agent-21 during I4Fix modeling:
  - **`i4f_no_two_busy_orig`** (I4Fix.lean:600) — under the original gating system, the "≤1 CU busy" invariant holds (out-of-order is unreachable);
  - `i4f_witness_shape_unreachable` (I4Fix.lean:536) — I-4's witness shape is unreachable under the gating system;
  - the companion `i4fSys_run_eq_orig` (under the gating system, the fixed and original versions are step-by-step equivalent) — the fix is regression-safe.
- [Direct source reading] The four gating-chain source locations (pipe.scala:223, warp_schedule.scala:181, pipe.scala:161, scoreboard.scala:131,142) were re-checked by the main session; the combinational chain closes and the correction is genuine.
- The wrong original conclusion and the correction process are fully recorded in the "reachability negation" section of doc/03's I-4 entry (the earlier 2026-08-25 analysis only looked at the collector side's structural possibility and missed the gating side — hereby corrected; III-3 is the archival of that correction).

## Lessons

1. **A "reachability" argument must cover the complete enablement chain (including upstream gating); structural possibility ≠ reachability.** Wave 3 only looked at the individual frequency of the two events (both in and out are common), missing the four-file combinational gating upstream of the events — this kind of omission is almost inevitable in paper review, because the gating chain spans multiple files across the scheduler, scoreboard, and top-level wiring.
2. **This is exactly where formalization beats paper review**: a combinational-level invariant (`i4f_no_two_busy_orig`) turns the gating constraint that paper review missed into a theorem — the proof obligation forces the modeler to write the whole enablement chain into the model, and the omission is exposed at the modeling stage (agent-21 discovered the contradiction precisely while building the gating-system model).
3. **Same-kind risk sweep conclusion** (on record in doc/03): I-2 (BranchJoin overflow) was already handled as "mechanism confirmed / unreachable under legal execution", with a consistent process; all other 【Confirmed】 entries have reachability supported by witness traces and are unaffected by this error.
4. **Another instance of the same lesson**: I-8 (ibuffer's warp_end flush crowded out by a same-cycle branch jump) was likewise excluded due to the structural mutual exclusion of `warp_control.ready := !branch.fire & !flushCache.valid` (warp_schedule.scala:52) — "two events are each individually frequent" never implies "they can co-occur on the same cycle"; an enablement-chain mutual-exclusion check should be a standard move in reachability review.

## Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Gating chain pipe.scala:223 → warp_schedule.scala:181 → pipe.scala:161 → scoreboard.scala:131,142 | Re-checked by the main session |
| Lean machine-checked proof | i4f_no_two_busy_orig (I4Fix.lean:600) + i4f_witness_shape_unreachable (:536) — I-4 is unreachable under gating | Invariant-level |

III-3 is this project's first complete case of "a paper reachability analysis corrected by machine-checked proof": the wrong "reachability confirmed" conclusion survived for one wave and was ultimately overturned by gating-system modeling. It directly gave rise to the review discipline that "a reachability argument must cover the complete enablement chain", and together with I-8's exclusion it established the precedent "structural possibility ≠ reachability".
