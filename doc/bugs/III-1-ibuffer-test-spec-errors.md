> English translation of the Chinese master `doc/bugs/III-1-IBuffer测试规约错误.md`. Translated 2026-09-13.

# III-1 Lessons Record: IBuffer test/specification written wrong (found during the wave-4 breakpoint repair; all fixed)

| Item | Content |
|---|---|
| ID | III-1 (Class III: specification/proof-side error) |
| Location | The IbLane test block in `lean/Ventus/Schedule/IBuffer.lean` and the statement of the `ibTop_warp_prefix` specification; the real hardware semantics involved is at `ventus/src/pipeline/ibuffer.scala:170` (SlowDown's in.ready) |
| When found | During wave 4 (IBuffer modeling, WP2) breakpoint repair |
| How found | decide / native_decide counterexamples (the specification/test errors were directly refuted by kernel reduction) |
| Status | All fixed; the model itself was verified line by line to match the source, **no Class II (translation) issues** |

---

## Background

IBuffer (InstrBufferV2, ibuffer.scala:105-203) is a per-warp instruction buffer: the upstream fetches groups of num_fetch=2 instructions per cycle (a group queue, Queue depth 2), which SlowDown (:137-177) decomposes and issues to the issue stage one instruction at a time. Wave 4 built a Lean model for it (`Ventus/Schedule/IBuffer.lean`: IbQ circular buffer + IbGrp group + SlowDown + IbLane single-warp lane + IbTop 8-warp top level), following the "test before proving" process: write numeric trace tests first, then prove refinement theorems.

## The problems (two, both on the verification side)

**Error 1: wrong trace timing assumptions in the IbLane test block and `ibT_no_flush_ok`.** The original test trace assumed that "after enqueueing into an empty lane, issue can happen the next cycle; loading does not require out.ready". But the real hardware's SlowDown load condition is [direct source reading, ibuffer.scala:170]:

```scala
io.in.ready := mask_next === 0.U && io.out.ready   // even with an empty group (mask_next==0), out.ready is required
```

That is: SlowDown requires the downstream ready even in the empty state before accepting a new group (conservative bubble, IBuffer.lean open question Q3). Therefore an empty lane has a **2-cycle latency** from enqueue to first issue: cycle 0 enqueue (the group queue's deq.valid is still low), cycle 1 load into SlowDown, issue starts at cycle 2. The original trace was one cycle early, misaligning all subsequent cycles.

**Error 2: the `ibTop_warp_prefix` specification was written in the wrong form.** The original conclusion form was

```
run.2 ++ tl = run.1.abs ++ accepted
```

(issued sequence ++ remainder = final-state residual ++ accepted sequence) — the right-hand side mixes the "final-state residual" with the "accepted sequence"; it was a **half-refactored artifact** left over from interrupted work and is unprovable in itself. Following the comment's original intent, it was changed to the prefix form

```
∃ tl, run.2 ++ tl = accepted     -- the issued sequence is a prefix of the accepted sequence
```

which was then proven.

## Evidence

- [Lean machine-checked proof] Both errors were caught directly by decide/native_decide counterexamples — that is exactly how they were found: the wrongly written test/specification was quickly refuted by kernel reduction, rather than being found by manual review.
- [Direct source reading] The conservative-bubble condition at ibuffer.scala:170 verified verbatim (the code block above in this report).
- The corrected forms are on record [Lean machine-checked proof]:
  - the test trace of `ibT_no_flush_ok` (IBuffer.lean:781) was rewritten per the real timing, with a comment stating "empty lane has 2-cycle load latency; issue on cycles 3 and 4" (a same-family comment at IBuffer.lean:465-466);
  - `ibTop_warp_prefix` (IBuffer.lean:709-723) is now in the prefix form; the proof goes through `ibLane_run_abs` (the lane-level refinement main theorem) + the locality lift `ibTopRun_get`.
- The model itself (IbQ.step / ibSdInRdy / flush-drop semantics) was verified line by line to match the source — the errors were only on the test/specification side, **no Class II issues** (conclusion copied verbatim from doc/03).

## Lessons

1. **The "test before proving" process works**: specification/test errors are quickly caught by decide-family counterexamples (a lesson consistent with coralNPU). The value of testing first is not "the tests pass" but "wrongly written tests get slapped down immediately" — if we had skipped tests and gone straight into proofs, Error 1's 2-cycle latency would have contaminated the premises of the entire refinement chain.
2. **Multi-cycle timing tests must be aligned cycle by cycle with the real handshake semantics.** Boundary latencies like "when does an empty structure first issue after enqueue" are high-frequency error points; the trap in this case was SlowDown's conservative bubble (requiring out.ready even when empty), which is easy to misread as "loadable whenever empty" when deriving traces on paper.
3. **A specification you cannot prove is most likely a specification written wrong.** Error 2's half-refactored artifact was exposed by proof failure — when a lemma just will not go through, first go back and audit the specification statement (against the comment's original intent), and only then grind at the proof.
4. Half-finished products from interrupted sessions (a theorem statement half-edited at the interruption) must be checked first when resuming — both errors in this case occurred in the breakpoint-repair stage.

## Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | ibuffer.scala:170 (SlowDown conservative bubble) | Verified verbatim |
| Lean machine-checked proof | Errors caught by decide/native_decide counterexamples; corrected ibT_no_flush_ok (:781) and ibTop_warp_prefix (:709, prefix form) on record | All green |

III-1 is a positive case for the "test first" process: both verification-side errors were intercepted by numeric counterexamples before entering the main proof chain, and the model body has no Class II issues. The lessons have been merged into wave practice (align multi-cycle traces cycle by cycle with handshake semantics; when resuming interrupted work, first check half-finished statements).
