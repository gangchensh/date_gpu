> English translation of the Chinese master `doc/bugs/I-8-flush挤占排除.md`. Translated 2026-09-13.

# I-8 Defect Analysis Report: the ibuffer warp_end flush is preempted by a same-cycle branch jump — 【Excluded】 (the two events are structurally mutually exclusive)

| Item | Content |
|---|---|
| ID | I-8 |
| Source location | `ventus/src/pipeline/warp_schedule.scala:73-74` (flush single-wid Mux); **exclusion basis `:52`** (`warp_control.ready := !io.branch.fire & !io.flushCache.valid`) |
| Type | Formerly suspected functional bug (flush lost → residual instructions leak into execution); ruled unreachable |
| Status | **【Excluded】** (2026-08-27: agent-30 discovered the mutual exclusion while constructing the reproduction + main session source re-check; 2026-09-06/07 ChiselSim premise-check test confirmed empirically, doc/22) |
| Primary evidence | [Direct source reading] the :52 enable-chain mutual exclusion; [simulation run] ChiselSim premise-check test — flushes of the two wids arrive on separate cycles (test passing = mutual exclusion in effect) |
| Lean model | `lean/Ventus/Schedule/WarpScheduler.lean` (wsOut.flushValid etc. modeled after the source; this exclusion is a source-level argument with no machine-checked theorem) |
| Reproduction | `repro/WarpSchedulerBugRepro.scala` I-8 case (rewritten as a **premise-check test**) |

---

## 0. Abstract

The original analysis suspected: on the same cycle that warp b executes endprg
(a single-cycle warp_end pulse), a taken branch of warp a triggers an ibuffer
flush, and since the flush channel is a single-wid Mux (branch has priority),
b's flush is permanently lost and residual instructions leak into execution
after the wid is reused.

**Exclusion**: the premise of warp_end is warp_control.fire, and :52 writes
`warp_control.ready` as `!io.branch.fire & !io.flushCache.valid` — **on any
cycle where branch.fire is true, warp_control cannot fire**, i.e. warp_end and
branch jump are structurally mutually exclusive, the two flush sources never
occur in the same cycle, and the Mux preemption is unreachable. The ChiselSim
premise-check test measured: on the branch cycle only wid0's flush is issued,
on the next cycle wid1's flush is issued, and both arrive — the mutual
exclusion holds on RTL.

## 1. Mechanism and Exclusion Argument

**Original mechanism hypothesis** (the wrong premise is highlighted):

```scala
io.flush.valid := (io.branch.fire & io.branch.bits.jump) | warp_end            // :73
io.flush.bits := Mux((io.branch.fire & io.branch.bits.jump), io.branch.bits.wid, warp_end_id)  // :74
```

The flush channel can carry only one wid per cycle, with branch jump having
priority. The original analysis hypothesized "warp b's endprg in the same
cycle as warp a's branch jump" ⇒ b's flush preempted and lost.

**Exclusion basis** (:52, enable-chain mutual exclusion):

```scala
io.warp_control.ready := !io.branch.fire & !io.flushCache.valid                // :52
```

warp_end := warp_control.fire & simt_stack_op (:47), and fire requires
ready=1; branch.fire true ⇒ ready=0 ⇒ warp_control does not fire ⇒ warp_end
is false. The two flush sources (branch jump / warp_end) are **structurally
impossible in the same cycle**; the two priority branches of the :74 Mux are
never simultaneously valid, and the preemption is unreachable.

**Lesson recorded**: the original analysis looked only at the individual
frequency of the two events (branch is common, endprg is common ⇒ "they will
collide eventually"), missing the enable chain's mutual exclusion — same type
as I-4's first misjudgment (doc/03 III-3: "structural possibility ≠
reachability; a reachability argument must cover the complete enable chain"),
recorded as of the same kind as III-3.

## 2. Evidence

- [Direct source reading] warp_schedule.scala:47/:52/:73-74 checked line by
  line; the mutual-exclusion chain is purely combinational with no register
  staging — the same-cycle mutual exclusion is unconditional.
- [Simulation run] ChiselSim (`repro/WarpSchedulerBugRepro.scala` I-8
  premise-check test, actually run 2026-09-06/07, doc/22): construct a
  "same-cycle attempt" of branch jump and endprg; measured
  warp_control.ready=0 with the mutual exclusion in effect — on the branch
  cycle only wid0's flush is issued, on the next cycle wid1's flush is issued,
  and both arrive. Verdict: **the precondition is falsified (test passing =
  mutual exclusion in effect)**.
- [Simulation run] 38-patch combined-tree regression (2026-09-10, doc/22):
  WarpSchedulerBugRepro 5/5 green; the I-8 premise-falsification conclusion
  agrees with the baseline (after the i46 patch adds fence_end gating to
  warp_control.ready, the mutual exclusion still holds).

## 3. Residual Observations (note level)

- The preemption **mechanism** of the single-wid flush Mux **is still there**
  — if the mutual-exclusion condition of warp_control.ready is relaxed in the
  future (e.g. a rework of the flushCache path, or endprg rerouted to an
  independent channel), this entry needs re-evaluation.
- The fix suggestion (making flush a per-warp vector, eliminating the
  single-wid bottleneck) still stands as **defense-in-depth**, but is not
  currently necessary.

## 4. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | the :52 mutual-exclusion chain checked line by line; purely combinational, unconditionally holds | certain |
| ChiselSim premise check | flushes of the two wids arrive on separate cycles; the same-cycle premise does not hold | actually measured |

I-8 closed as 【Excluded】. Its value is methodological: this entry's
exclusion path (the premise turned out not to hold while constructing the
reproduction) and III-3's lesson corroborate each other — "writing a
reproduction test" is not only a means to confirm a bug, but also a means to
falsify an unreachability suspicion.
