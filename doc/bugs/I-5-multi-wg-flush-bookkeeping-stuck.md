> English translation of the Chinese master `doc/bugs/I-5-多WG完成簿记卡死.md`. Translated 2026-09-13.

# I-5 Detailed Defect Report: endprg/flush bookkeeping stuck when multiple WGs complete simultaneously (OHToUInt misused on non-one-hot input)

| Item | Content |
|---|---|
| ID | I-5 |
| Source location | `ventus/src/pipeline/warp_schedule.scala:164-173` (mask_0/need_flush/flush_entry/clear block); core hazard at `:168` (`flush_entry = OHToUInt(mask_0)`) |
| Type | Functional bug (bookkeeping stuck) — misuse of a single-bit-vector encoder's semantics |
| Severity | **Medium** (flushDCache requested permanently: performance/power loss + wg valid-bit leak; no data corruption; a self-healing path exists but is blocked by I-6) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + ChiselSim reproduction successful + 38-patch merged tree regression 5/5 green |
| Primary evidence | [Lean machine-checked proof] WS4 theorem family + T6 concrete-trace witness; [simulation run] ChiselSim reproduction successful (after calibration); [direct source reading] line-by-line check against line numbers |
| Lean model | `lean/Ventus/Schedule/WarpScheduler.lean` (original); fixed version `lean/VentusF/Schedule.lean` |
| Reproduction/patch | `repro/WarpSchedulerBugRepro.scala` (ChiselSim, I-5 case); patch `i05-warp-schedule-flush-entry.patch` (internal fix manifest; not released) |
| Related entries | I-6 (warpRsp handshake violation, blocks this entry's self-healing path), I-7 (same-cycle bookkeeping bit lost), I-46 (endprg does not wait for in-flight memory accesses) |

---

## 0. Summary

warp_scheduler records, per WG (workgroup), "which warps in the group have not yet executed endprg" in the `warp_endprg_cnt` bitmap: when a WG's cnt is cleared and its valid bit is set, the corresponding bit of `warp_endprg_mask_0` is set, meaning "all warps of this WG have finished; a flush to the DCache is pending". Multiple WGs pending flush must be processed one at a time, and the selector uses `flush_entry = OHToUInt(mask_0)` (warp_schedule.scala:168) to pick one out of mask_0.

**OHToUInt acts as an "index encoder" only when its input is exactly one-hot (exactly one bit set)**; for an input with multiple bits set, it outputs the **bitwise OR** of all set indices (e.g. bits 1 and 2 both set ⇒ output 1|2=3). When multiple WGs complete in succession within the flush-consumption window, mask_0 is not one-hot, and flush_entry lands on an index that is **not set** in mask_0 ⇒ `warp_endprg_mask_0(flush_entry)=false` ⇒ the clear condition is permanently false ⇒ `warp_wg_valid` can never be cleared, `need_flush` is permanently true, and flushDCache.valid is stuck high forever. Triggering does not require the same cycle — adjacent cycles suffice.

The Lean evidence chain for this entry is complete (combinational bit-level theorems → single-cycle invariant → arbitrary-length-trace stuck theorem + concrete witness), ChiselSim reproduction succeeded (flushDCache.valid stuck at 1 for 6/6 cycles), and the fix (replacing OHToUInt with PriorityEncoder) went green in the patch-tree regression.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **WG (workgroup) and warp**: In Ventus, a WG (CUDA's thread block / OpenCL's work-group) consists of several warps and is assigned to a WG slot on an SM for execution. There are `num_block=8` WG slots and `num_warp=8` warp slots; per-WG bookkeeping is an 8-entry register vector.
- **endprg**: after a warp executes its last instruction, it reports the completion event to warp_scheduler via the `warp_control` channel (a warp_control.fire with `simt_stack_op=1`).
- **WG completion bookkeeping**: each WG slot maintains `warp_endprg_cnt` (bitmap of warps in the group that have not yet endprg'd) and `warp_wg_valid` (whether a WG resides in the slot). When cnt is cleared while valid is set, the WG has completed and needs: (a) a flush sent to the DCache (writing the WG's dirty data back to L2); (b) valid cleared to release the slot.
- **flushDCache consumption**: `flushDCache` is a Decoupled channel; the scheduler issues at most one WG's flush request per cycle, and when the DCache is ready (ready=1) that WG's valid bit is cleared in the same cycle. When multiple WGs complete simultaneously they must be consumed **one at a time** — this is why the flush_entry selector exists.
- **OHToUInt vs PriorityEncoder**: Chisel's `OHToUInt` assumes a one-hot input; its implementation is "for each output bit, OR together all input bits whose index has that bit set". With a non-one-hot input the output is the bitwise OR of the set indices, which may point to an unset index. `PriorityEncoder` has no such assumption and always returns the lowest set index. This is a contract difference explicitly documented in Chisel.

### 1.2 Design intent

WG completion is processed at a "one per cycle" pace: the WGs set in mask_0 queue up, flush_entry selects the one currently being processed, its valid bit is cleared when flushDCache.ready arrives, mask_0 shrinks accordingly, and the next one is handled the next cycle. The designer evidently anticipated that mask_0 could have multiple bits set when multiple WGs complete, and expected OHToUInt to "pick one" out of it — that expectation holds for one-hot inputs, but not for non-one-hot inputs.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: the set logic of mask_0** (warp_schedule.scala:164-166):

```scala
for(i<-0 until num_block){
  warp_endprg_mask_0(i) := (warp_endprg_cnt(i).orR === false.B) && warp_wg_valid(i)  // :165
}
val need_flush = warp_endprg_mask_0.asUInt.orR                                        // :167
```

All warps of WG i have endprg'd (cnt empty) and the slot is valid ⇒ mask_0(i)=1. When multiple WGs complete in succession (cnt clearing does not have to happen in the same cycle; adjacent cycles suffice), mask_0 having multiple bits set is **normal operating condition**.

**Construct 2: the selector and the clear block** (warp_schedule.scala:168-170, ★ hazard):

```scala
val flush_entry = OHToUInt(warp_endprg_mask_0.asUInt)                  // :168 ★
when(warp_endprg_mask_0(flush_entry) && io.flushDCache.ready){         // :169
  warp_wg_valid(flush_entry) := false.B                                // :170
}
io.flushDCache.valid := need_flush                                     // :172
```

`flush_entry` is used as a dynamic index to read mask_0 itself back: the clear happens only when "the selected index is indeed set". For a one-hot input, OHToUInt returns exactly the set index, the read-back is 1, and the clear proceeds normally; for a non-one-hot input the output is the bitwise OR (e.g. {1,2}→3), and if mask_0(3)=0 (WG3 is not in the pending-flush set), the read-back is 0 and the clear condition is permanently false. Since mask_0 changes only with valid/cnt, and the clear never happens, mask_0 stays unchanged and so does flush_entry — **state self-lock**: need_flush permanently true (:172 flushDCache.valid stuck high), valid(1) and valid(2) permanently residual.

**Counterexample (when it does not trigger)**: everything works when a single WG completes (mask_0 one-hot); two WGs completing in the same cycle whose indices' bitwise OR happens to land on one of them (e.g. {0,1}→1) also survive by luck — this is the numerical detail behind why the first version of the reproduction test with wg0+wg1 did not trigger, and why calibrating it to wg1+wg2 (0b110→3) made it trigger (doc/22).

---

## 3. Defect analysis

### 3.1 Precise description of the defect

The stuck chain (every link backed by a Lean theorem or direct source reading):

1. The warps of wg1 and wg2 endprg in succession (adjacent cycles suffice; same cycle not required) ⇒ mask_0=0b110;
2. flush_entry = OHToUInt(0b110) = 1|2 = 3 (bitwise-OR semantics);
3. mask_0(3)=0 ⇒ the clear condition at :169 is permanently false ⇒ valid(1), valid(2) are never cleared;
4. cnt(1), cnt(2) are already 0 and, with no new warp dispatched, never change again ⇒ mask_0 stays 0b110 forever;
5. Back to 2: flush_entry is 3 forever, the state self-locks; need_flush permanently true ⇒ flushDCache.valid stuck high forever (a continuous storm of flush requests to the DCache).

**Self-healing path and its blockage**: the only escape path is the CTA dispatching a new warp to the stuck wg1/wg2 — the req set bit raises cnt first, mask_0 falls back to a singleton, and flush_entry lands back on a correct index (the premise `hnr` of the Lean theorem `ws4_step_stuck` is precisely "no new warpReq", and this escape path is called out in the comments). But I-6 (warpRsp response loss) makes cnt never clear and corrupts the bookkeeping, blocking this path — the two defects must be read together.

### 3.2 Root cause

**Misuse of a library function's semantics**: OHToUInt's name (One-Hot to UInt) carries a one-hot premise, and the input here (the union mask of multiple completed WGs) can structurally be non-one-hot. The correct primitive is PriorityEncoder (no one-hot assumption; takes the lowest set entry each cycle). This is not a timing race or an interface mismatch, but an unsatisfied premise of a single combinational function — a "didn't read the library documentation carefully" kind of defect, and the most typical hunting ground for formal bit-level reasoning (bv_decide): two lines of theorem pin down "non-one-hot ⇒ must miss a set entry".

### 3.3 Harm and tolerability

- **Harm**: (a) flushDCache.valid stuck high permanently — the DCache receives an endless stream of flush requests, and continuous whole-cache flushing costs performance/power; (b) wg valid-bit leak — the stuck WG slots are never reclaimed (`warp_wg_valid` is scheduler-side bookkeeping; slot reclamation also needs the warpRsp/CTA2warp link working); (c) combined with I-6, the flush may never actually happen while the completion report is still sent (see I-47).
- **No data corruption**: the flush itself keeps being executed, so dirty data is eventually written back; the defect shape is "flushing nonstop" rather than "not flushing".
- **Tolerability**: the trigger condition is multiple WGs completing in succession within the flush-consumption window — reachable under dense CTA scheduling (multiple WGs resident concurrently, completions concentrated at kernel boundaries); a normal operating condition, not a corner case. Rating: **Medium**.
- **Fix recommendation**: switch flush_entry to PriorityEncoder (or scan bit by bit and clear one at a time). Adopted and verified (§7).

---

## 4. Lean formal evidence

All in `lean/Ventus/Schedule/WarpScheduler.lean`, zero sorry, full build passes:

**Combinational bit-level core** (bv_decide, universal over arbitrary 8-bit inputs):

- `wsOHToUInt` (modeling item M6): models Chisel OHToUInt's true semantics strictly — bit j of the result = the OR of all set entries whose index has bit j set, not "the lowest set bit";
- **`ws4_flush_entry_avoids`**: mask_0 containing both bit1 and bit2 ⇒ OHToUInt output ≠1 and ≠2 — the clear target necessarily misses these two set WGs (the bit-level root of the stuck state).

**Sequential stuck chain** (manual case analysis + list induction):

- `wsStuck` (definition of the stuck state): cnt(1)=cnt(2)=0 and valid(1)=valid(2)=true;
- `ws4_step_stuck` (single-cycle invariant): under inputs with no warpReq dispatch, the stuck state is preserved across one step;
- `ws4_run_stuck`: the stuck state is preserved after an **arbitrarily long** input sequence without warpReq;
- **`ws4_stuck_forever`** (verdict form): in the stuck state, mask_0 is forever nonzero (need_flush permanently true, flushDCache continuously requested) and valid(1), valid(2) leak permanently.

**Numerical witness (T6, native_decide)**: wg1 (warp1) and wg2 (warp2) endprg in succession → mask_0=0b110, flush_entry=3; after 3 more cycles with flushDCache.ready=true, valid(1) and valid(2) are still true and flushDCacheValid stays high (`wsF7` series examples).

**Fixed-version verification** (`lean/VentusF/Schedule.lean`): `fschWs_priEnc_hit` (after the fix, flush_entry always lands on a set entry of mask_0), `fschWs_step_clears_selected` (the selected entry is always cleared), `fschWsT_i5_drains` (the original witness scenario drains cycle by cycle on the fixed version — after multiple WGs complete in succession, mask_0 converges to 0).

Evidence layering: the ws4 formal theorems rely only on Lean's standard axioms plus bv_decide's per-theorem private LRAT trust axioms; the native_decide witness additionally introduces `Lean.ofReduceBool` (archived in module report §6).

---

## 5. Simulation verification (ChiselSim measurements + patch-tree regression)

**ChiselSim module-level reproduction** (`repro/WarpSchedulerBugRepro.scala` I-5 case, actually run 2026-09-06/07, doc/22): two WGs endprg in succession + flushDCache.ready held high; measured **flushDCache.valid stuck at 1 for 6/6 cycles**. Verdict: **reproduction successful**.

- **Test calibration record** (doc/22): the first version's trigger pair wg0+wg1 did not trigger — OHToUInt(0b011)=0|1=1, which lands on a set entry by luck; after calibrating to wg1+wg2 (0b110→3 lands on a WG with mask_0=0), it reproduced. This calibration itself is independent empirical evidence of the "bitwise-OR semantics".

**Patch-tree regression**: on the 35-patch tree (2026-09-07), WarpSchedulerBugRepro passed 4/4 after adaptation (adaptation content: the i46 patch adds a fence_end input; the test must add pokes or all endprgs get back-pressured, producing an idle-spin false green — doc/22 detected and corrected this); on the 38-patch merged tree (2026-09-10) **5/5 green**, and the fixed behavior of I-5/6/7 genuinely passes end to end.

---

## 6. Upstream impact analysis

- **Trigger surface**: any kernel boundary with "multiple WGs completing in succession" — multiple concurrent WGs are a normal capability of the CTA scheduler (NUM_WG_SLOT=8), not dependent on special configuration or rare timing.
- **Why upstream did not find it**: the observable symptoms are flushDCache.valid stuck high and slot leakage, manifesting as performance degradation and resource occupation rather than wrong results or deadlock halt; no assertion covers this bookkeeping (the OHToUInt premise is not pinned by an assert); test kernels are mostly small single-WG cases.
- **Defect-family positioning**: this entry belongs with I-6, I-7, and I-46 in the warp scheduler's endprg/wid lifecycle bookkeeping family — the four defects share the same register-update code (:47/:55/:123-134/:157-163/:180) and are mutually coupled through self-healing paths / the response channel (I-6 blocks I-5's self-healing path; one i06-i07-i46 patch fixes three entries at once).
- **Residual observation**: while need_flush is permanently true, flushDCache.bits is constantly true (:173), and the DCache side treats every flush as a full invalidation — when this entry is combined with I-47 (completion report does not wait for flush completion), the combined consequence of "report still sent but flush never truly completes per-WG" has been recorded in the I-47 entry of doc/03.

---

## 7. Fix and fix verification

**Patch** (`i05-warp-schedule-flush-entry.patch` (internal fix manifest; not released), single edit point):

```scala
-  val flush_entry = OHToUInt(warp_endprg_mask_0.asUInt)
+  val flush_entry = PriorityEncoder(warp_endprg_mask_0.asUInt)   // :168
```

PriorityEncoder has no one-hot assumption: each cycle it takes the lowest set WG, clears it when ready, and mask_0 shrinks cycle by cycle until drained. Fix footprint = one line.

**Fix verification trio**:

- Effectiveness: Lean fixed-version theorems `fschWs_priEnc_hit`/`fschWs_step_clears_selected`/`fschWsT_i5_drains` (the original stuck witness drains normally on the fixed version);
- Regression safety: 38-patch merged tree ChiselSim regression 5/5 green (doc/22); the fixed version is behaviorally equivalent to the original in the non-trigger domain (VentusF/Schedule.lean regression-equivalence theorem family `fschWs_*_equiv`);
- No follow-up items: this fix introduces no new design points (PriorityEncoder is the primitive that should have been used all along).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | warp_schedule.scala:164-173 checked line by line; OHToUInt semantics cross-checked against Chisel library conventions | Consistent |
| Lean machine-checked proof | `ws4_flush_entry_avoids` (bit-level root) → `ws4_step_stuck`/`ws4_run_stuck` → `ws4_stuck_forever` (arbitrary-length-trace verdict) + T6 witness | Universal / arbitrary-length trace |
| ChiselSim reproduction | flushDCache.valid stuck at 1 for 6/6 cycles (after wg1+wg2 calibration); wg0+wg1 surviving by luck confirms the bitwise-OR semantics from the opposite side | Measured |
| Fix verification | i05 patch (1 line); Lean fixed-version drain theorems + 38-patch tree regression 5/5 green | Measured + machine-checked |

I-5 is a textbook sample of the "library-function premise misuse" defect class: one line of OHToUInt with an unsatisfied premise turns the normal multi-WG completion condition into a bookkeeping self-lock. Formal methods (bv_decide's bit-level universal reasoning) hit this class deterministically, whereas simulation needs to construct exactly the right index combination — non-one-hot with the bitwise OR landing on an unset index. This project's first ChiselSim test (wg0+wg1) happened to miss it and only reproduced after calibration, which confirms from both directions the necessity of the "mechanism proof first, simulation calibration follows" workflow.
