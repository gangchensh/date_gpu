> English translation of the Chinese master `doc/bugs/I-41-MSHR同拍优先级族.md`. Translated 2026-09-13.

# I-41 Detailed Defect Analysis Report: L2 MSHR Same-Cycle Priority Family — allocate×sinkd, merge×sinkd

| Item | Content |
|---|---|
| ID | I-41 |
| Source location | `ventus/src/L2cache/MSHR.scala:67-72` (allocate branch `sink_d_reg := false.B`) vs `:143-147` (`when(io.sinkd.valid){ sink_d_reg := true.B }`, later write wins); `:81-87` (`data_reg` priority allocate>merge>sinkd) |
| Type | Functional bug (bookkeeping corruption / data loss) — a same-cycle event priority design error inside the MSHR (same family as I-39) |
| Severity | **High at the mechanism level** ((a) a new entry gains d-response eligibility before receiving its memory response; (b) on a merge×sinkd same-cycle collision the Grant data is discarded); **conditionally unreachable** — predicated on environment contract E1, and the residual premise of E1's proof includes per-cycle E3, which has been falsified by I-44 |
| Confirmation status | 【Mechanism confirmed / machine-proven unreachable (under condition E1), conditional】 (Wave-27 revised qualification, see §3.3) |
| Primary evidence | 【Lean machine-checked proof】MSHR-level dual witness + Scheduler-side dual unreachability discharge + E1 discharge theorem + I-44 corner re-reachability argument; 【direct source reading】line-by-line check of MSHR.scala:67-72/81-87/143-147 |
| Lean model | `lean/Ventus/L2/L2MSHR.lean` (mechanism and witness), `lean/Ventus/L2/Scheduler.lean` (discharge), `lean/Ventus/L2/Discharge.lean` (E1 discharge and E3 falsification); fixed version `lean/VentusF/MemL2.lean` |
| Reproduction/patch | No ChiselSim/Verilator reproduction suite (ready-to-run, not executed in this environment, see §5); patch `i41-l2-mshr-mutex-assert.patch` (internal fix manifest; not released) (defense-in-depth: two mutual-exclusion assertions) |
| Related entries | **I-44** (E3's falsification makes this collision reachable again in the pool-exhaustion corner), I-39 (same module, same family: sche_a_valid priority inversion), I-40 (same wave) |

---

## 0. Abstract

The L2 MSHR contains two same-cycle priority defects (filed as a single "same-cycle priority family" entry):

- **(a) allocate×sinkd**: the clear of `sink_d_reg` (the "this entry has received its memory D response" flag) is written in the allocate branch (:67-72), while the set is written in an independent `when` later in the file (:143-147). Chisel last-connect-wins: when allocate and sinkd occur in the same cycle, the set takes effect — **the newly allocated entry, before receiving the memory response that belongs to it, already has `schedule.d` response eligibility** (`d.valid = io.valid && sink_d_reg && !sche_a_valid`, :89), and would send the previous transaction's stale response to L1 as if it were this transaction's response.
- **(b) merge×sinkd**: the update chain for `data_reg` has priority allocate>merge>sinkd (:81-87) — when merge (merging same-block Put data) and sinkd (Grant data arrival) occur in the same cycle, the sinkd branch is swallowed, **the Grant data returned from memory is discarded**, and the entry keeps only the merge result.

Each mechanism has a single-cycle machine-checked witness. Wave 25 provided the Scheduler-side unreachability discharge: under environment contract E1 ("an AccessAckData response on sinkD only targets an active entry, and is the first response for that entry"), the entry being allocated is inactive that cycle (valids=0) and the entry being merged has sinkDReg=1, each contradicting E1. **Wave-27 revised qualification**: although E1 has been discharged as a theorem (`l2dc_e1_step/run`), its proof's residual premise includes per-cycle E3; in the corner where E3 is falsified by I-44 (ListBuffer pool exhaustion), a duplicate A on the same source ⇒ the outer layer returns a double AccessAckData ⇒ the allocate×sinkd / merge×sinkd collision **becomes reachable again**. Outside the scope where E3 holds, the conclusion remains valid. The fix is positioned as defense-in-depth (in-module mutual-exclusion assertions); after the I-44 root fix, this entry returns to unreachable.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **MSHR response bookkeeping**: each L2 MSHR entry uses `sink_d_reg` to record "this transaction's D-channel response (AccessAckData etc.) has arrived". Once complete, the entry sends the data/completion signal back to L1 via `schedule.d`, and is then popped by the Scheduler for reuse.
- **merge**: when a subsequent Put (write) to the same block arrives, it need not occupy a new entry; instead its data is merged byte-mask-wise into the existing entry's `data_reg` (`merge_data`), joining the memory response.
- **TileLink discipline (the source of E1)**: the outer memory returns exactly one D response, on the same source, per A request; source = the MSHR entry number at allocation time. Therefore, under normal discipline, a sinkD AccessAckData necessarily hits an entry that "has issued A but not yet received D" — active and with `sink_d_reg=0`.
- **Semantics of allocate**: the Scheduler loads the miss result into a free entry and resets all transaction flags (`request` overwritten, `sink_d_reg` cleared, `sche_a_valid` set).

### 1.2 Design Intent

The three events allocate, merge, sinkd are designed to occur **mutually exclusively**: allocate only targets free entries, sinkd only targets active entries that have issued A, merge only targets entries that have received or are awaiting data. The code does not fix this contract with assertions; instead, the arbitration result is implied by the priority chain / write order — once the contract is violated upstream (the I-44 corner), the implicit arbitration produces the wrong answer.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the clear and set of `sink_d_reg` are separated; the later write wins** (★ hazard a, `MSHR.scala:67-72` and `:143-147`, verified by direct source reading):

```scala
when(io.allocate.valid) {       // :67
  request := io.allocate.bits   // :68
  sink_d_reg := false.B         // :69  allocate clears
}
...
when (io.sinkd.valid ) {        // :143  ★ independent when at the tail of the file
  sink_d_reg := true.B          // :145  later write wins — overrides the :69 clear on a same-cycle collision
}
```

allocate×sinkd in the same cycle ⇒ `sink_d_reg := true.B` (last-connect-wins). The new entry's `request` has been overwritten with the new transaction, but the response flag is set — `schedule.d.valid` (:89 `io.valid && sink_d_reg && !sche_a_valid`) can become true as soon as the new transaction's A is issued (sche_a_valid cleared to 0), carrying the new `request` + the old `data_reg`.

**Construct 2: the three-level priority chain of `data_reg`** (★ hazard b, `MSHR.scala:81-87`):

```scala
when(io.allocate.valid) {
  data_reg := io.allocate.bits.data    // :82  allocate has top priority
}.elsewhen(io.merge.valid) {
  data_reg := merge_data               // :84  merge second
}.elsewhen(io.sinkd.valid){
  data_reg := io.sinkd.bits.data       // :86  ★ sinkd lowest — swallowed on a same-cycle collision
}
```

merge×sinkd in the same cycle ⇒ `data_reg := merge_data` — `merge_data` is "the byte-wise merge of the later-arriving same-block Put data with the old data_reg" (:60) and does **not** include the Grant data arriving this cycle (`io.sinkd.bits.data`). The memory response is silently discarded: entry data = merge of old data and the Put, missing the memory portion.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

- **(a) allocate×sinkd**: same cycle ⇒ the new entry has `sink_d_reg=1`. Consequence chain: after the new transaction's Get is issued (a.fire clears `sche_a_valid`), `schedule.d.valid` can become true immediately — responding early to L1 with the **old data_reg** (or even the initial data loaded by allocate); when the real memory response arrives later, `sink_d_reg` is already set, and the entry's bookkeeping is misaligned with the actual response stream (response-pairing corruption).
- **(b) merge×sinkd**: same cycle ⇒ Grant data discarded, `data_reg` keeps only the merge result. Consequence: the refill data L1 receives is missing the memory bytes — a silent data error.

### 3.2 Root Cause

Same root as I-39: the MSHR treats "event mutual exclusion" as an implicit contract, using a priority chain / write order in place of explicit arbitration. The two sites are even written differently — (a) is a later-write-wins across separate `when` blocks, (b) is an earlier-write-wins in an elsewhen chain — indicating the author had no uniform design for same-cycle combinations. The module contains no mutual-exclusion assertion whatsoever.

### 3.3 Harm and Tolerability (including the Wave-27 revised qualification)

- **Harm** (when triggered): (a) premature response / response-pairing corruption (liveness + correctness); (b) refill data missing bytes (correctness, silent).
- **Reachability (conditional, qualification copied verbatim from doc/03)**:
  - 【Lean machine-checked proof】Machine-proven unreachable under E1: `l2sc_i41a_no_alloc_sinkd` (alloc ⇒ valids=0, and E1 "sinkD responses only target active entries" ⇒ contradiction) and `l2sc_i41b_no_merge_sinkd` (merge ⇒ sinkDReg=1, and E1 "first response" ⇒ sinkDReg=0, contradiction).
  - 【Lean machine-checked proof】E1 has been discharged as a theorem (`l2dc_e1_step`/`l2dc_e1_run`, the joint invariant `l2dcInvE1` is maintained cycle by cycle), but the **residual premise includes per-cycle E3** (the honest-boundary statement in the Discharge.lean file header: the outer-layer TL discipline E1b is a black-box residual premise, plus per-cycle E3).
  - **In the corner where E3 is falsified (I-44), a duplicate A on the same source ⇒ double AccessAckData ⇒ the allocate×sinkd / merge×sinkd collision becomes reachable again. Outside the scope where E3 holds, the conclusion remains valid.**
- **Tolerability**: same as I-39 — the trigger surface = the I-44 pool-exhaustion corner; after the I-44 root fix restores E3 by construction, this entry returns to unreachable. Rating: latent defect, handled as defense-in-depth (the internal fix manifest: Defense-in-depth).

---

## 4. Lean Formal Evidence

**MSHR-level mechanism witness** (`lean/Ventus/L2/L2MSHR.lean`, 【Lean machine-checked proof】, native_decide single cycle):

- `l2mT_alloc_sinkd_collision` (:510): allocate×sinkd in the same cycle ⇒ `sinkDReg'=true` — the new entry gains d-response eligibility before receiving its memory response;
- `l2mT_merge_sinkd_priority` (:532): merge×sinkd in the same cycle ⇒ `dataReg'` takes only the merge result; the Grant data is discarded.

**Scheduler-side unreachability discharge** (`lean/Ventus/L2/Scheduler.lean`, Wave 25, 【Lean machine-checked proof】, symbolic single cycle, arbitrary state):

- `l2sc_i41a_no_alloc_sinkd` (:833): under `l2scEnv` (which includes E1), `l2scAllocValid st inp i = true ⇒ l2scSinkdV st inp i = false`;
- `l2sc_i41b_no_merge_sinkd` (:846): under `l2scEnv`, `l2scMergeValid st inp i = true ⇒ l2scSinkdV st inp i = false`.

**E1 discharge and qualification** (`lean/Ventus/L2/Discharge.lean`, Wave 27, 【Lean machine-checked proof】):

- `l2dc_e1_step` (:424) / `l2dc_e1_run` (:694): the joint invariant `l2dcInvE1` (the I-39 invariant + the in-flight-A bit property + armed entries have not received responses) + this-cycle E3 + this-cycle E1b ⇒ this-cycle E1 holds and the invariant is maintained, by induction over arbitrary traces;
- Residual premises (honest boundary): ① E1b itself (outer memory/TL fabric is a black box); ② per-cycle E3 — already falsified by `l2dc_e3_falsified`; the E3-failure corner (duplicate A ⇒ double AccessAckData) also breaks E1b, and this entry's discharge fails in that corner.

**Fixed-version verification** (`lean/VentusF/MemL2.lean`, 【Lean machine-checked proof】):

- `fmem_i41a_alloc_sinkd_mutex` (:744) / `fmem_i41b_merge_sinkd_mutex` (:763): in the fixed version (with the E1-only environment premise — E3 having been restored by construction by the I-44 fix, `fmem_i44_e3_by_construction`), the mutual exclusion of allocate×sinkd / merge×sinkd is proven; symbolic, arbitrary state.

---

## 5. Simulation Verification

**【Ready-to-run / not executed in this environment】** — this entry has no ChiselSim/Verilator reproduction suite (doc/22's 11 suites + 10 kernels do not cover L2 MSHR same-cycle injection). Moreover, per §3.3, directly reproducing on the current design requires first constructing the I-44 pool-exhaustion corner (a duplicate A on the same source triggering a double AccessAckData from the outer layer). The targeted test shapes are: module-level — drive allocate×sinkd / merge×sinkd in the same cycle at the MSHR and observe `sink_d_reg`/`data_reg` (mechanism-level, directly writable); or Scheduler-level — replay the I-44 scenario and observe the bookkeeping corruption (system-level, depends on cooperation from the outer memory model). The test code is yet to be written (ready-to-run, not executed in this environment).

On the patch side: the i41 patch (two mutual-exclusion assertions) passed mill compilation and whole-chip elaboration as part of the 35/38 combined patch tree (doc/22, MILL_EXIT=0); the assertions are simulation-time detectors that do not exist after synthesis — their protective value complements the Lean-side `fmem_i41a/b_*_mutex` mutual-exclusion theorems.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: unreachable within the scope where E1/E3 hold; reachable again inside the I-44 pool-exhaustion corner (the double AccessAckData in that corner is filed under I-44). doc/14 classifies I-39/I-41 as "environment-contract-type" unreachability: the blocking mechanism = the TileLink one-D-per-A discipline; the broken-window condition = relaxation of the outer interconnect/memory response discipline (to which I-44's pool exhaustion now adds a proven broken-window path).
- **How to state it to upstream**: same as I-39 — one must not claim "proved unreachable" without qualification; the statement must carry the condition "under the E1/E3 premises, except the I-44 corner" (the review framing of doc/20 §W2).
- **Rationale for the fix positioning**: a mechanism fix (changing the priority / adding mutual-exclusion logic) has low payoff — after the I-44 root fix this entry is structurally unreachable; but the implicit contract deserves to be fixed with assertions, so the patch takes the form of "in-module mutual-exclusion assertions", turning the contract from paper into simulation-time-monitorable engineering discipline (doc/14 methodology point 2).

---

## 7. Fix and Fix Verification

**Patch** (`i41-l2-mshr-mutex-assert.patch` (internal fix manifest; not released), defense-in-depth, registered in the internal fix manifest): two simulation-time assertions appended at the tail of MSHR.scala:

```scala
assert(!(io.allocate.valid && io.sinkd.valid), "L2 MSHR: allocate and sinkd in the same cycle")
assert(!(io.merge.valid && io.sinkd.valid), "L2 MSHR: merge and sinkd in the same cycle")
```

(Patch header note: unreachable via E1/E3 after the I-44 fix; the assertions here defend against future integration changes.)

**Fix verification**:

- 【Lean machine-checked proof】`fmem_i41a_alloc_sinkd_mutex`/`fmem_i41b_merge_sinkd_mutex` — in the fixed-version environment (E1-only, E3 restored by construction via the I-44 fix), both same-cycle combinations are proven mutually exclusive; note these two are **symbolic theorems under a contract premise**, not unconditional theorems (honest annotation in MemL2.lean §4);
- 【simulation run】the patch passed mill compilation + whole-chip elaboration as part of the 35/38 combined patch tree (doc/22);
- Upstream handling recommendation (copied verbatim from doc/03): add mutual-exclusion asserts inside the module; when upstream fixes, handle together with I-39 (same module, same family).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | MSHR.scala:67-72 (allocate clears sink_d_reg), :143-147 (sinkd sets it later), :81-87 (data_reg priority chain), :89 (d.valid gating), line-by-line check | Four sites consistent |
| Lean machine-checked proof (mechanism) | `l2mT_alloc_sinkd_collision`, `l2mT_merge_sinkd_priority` dual witness | Concrete traces |
| Lean machine-checked proof (unreachability discharge) | `l2sc_i41a_no_alloc_sinkd`, `l2sc_i41b_no_merge_sinkd` (premise E1) | Symbolic single cycle |
| Lean machine-checked proof (E1 discharge and qualification) | `l2dc_e1_step`/`l2dc_e1_run` (residual premises E1b + per-cycle E3); E3 falsified by `l2dc_e3_falsified` ⇒ reachable again in the I-44 corner | Arbitrary-trace induction + counterexample |
| Simulation | No targeted suite (ready-to-run, not executed in this environment); patch tree compile/elaboration passed | Patch-tree measurement |
| Fix verification | i41 patch (dual mutual-exclusion assertions); `fmem_i41a_alloc_sinkd_mutex`/`fmem_i41b_merge_sinkd_mutex` (proven under E1-only) | Machine proof + compile measurement |

I-41 and I-39 together form the L2 MSHR "same-cycle priority family": the module treats event mutual exclusion as an implicit contract, the contract is carried by E1 (the outer TL discipline), and E1's proof in turn residually depends on E3 (the ListBuffer pool discipline) — both layers of premise have been precisely characterized by this project's subsequent machine-proof work, with E3 falsified by I-44. The final form of this entry is "conditionally unreachable + assertions fixing the contract": the mechanism is real, the corner is reachable, the root fix lives in I-44, and the assertions defend the future.
