> English translation of the Chinese master `doc/bugs/I-43-drb满丢脏写回.md`. Translated 2026-09-13.

# I-43 Detailed Defect Analysis Report: L2 Scheduler's miss-dirty result.ready Missing drb.enq.ready — Dirty Victim Writeback Lost

| Item | Content |
|---|---|
| ID | I-43 |
| Source location | `ventus/src/L2cache/Scheduler.scala:252` (★ hazard: the miss branch of `result.ready` does not include `drb.enq.ready`); linked points `:246` (drb.enq.valid includes the dirty condition), `:244` (drb = 1-deep Queue), `:249` (drb.deq.ready requires sourceD.req.ready) |
| Type | Functional bug — **correctness-level** (dirty victim writeback lost ⇒ memory holds stale data) |
| Severity | **High** (data correctness compromised: subsequent reads of the victim block return stale data; the trigger condition is a common interleaving) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified (VentusF/MemL2.lean) + i43 patch included in the 38-patch combined-tree regression |
| Primary evidence | 【Lean machine-checked proof】three-leg machine-proven reachability: `l2dc_i43_witness` (Scheduler leg) + `l2dc_i43_dir_results` (Directory leg) + `l2dc_i43_sourced_busy` (SourceD leg), with two cycles' environment legality machine-checked per cycle; 【direct source reading】line-by-line check of Scheduler.scala:244-252 |
| Lean model | `lean/Ventus/L2/Scheduler.lean` (`l2sc*`), `lean/Ventus/L2/Discharge.lean` (`l2dc*`); fixed version `lean/VentusF/MemL2.lean` (`fmem_i43*`) |
| Reproduction/patch | No ChiselSim suite (doc/22 does not cover the L2 Scheduler; ready-to-run); patch `i43-l2-scheduler-drb-ready.patch` (internal fix manifest; not released) |
| Related entries | I-42 (same file, the mixed guard), I-44 (same file, the allocate gating), I-38 (SourceD-side handshake defect, the same-family background providing the drb backpressure window) |

---

## 0. Abstract

The L2 Scheduler pushes the victim writeback information of the directory's miss-dirty results (miss with a dirty victim line) into a 1-entry-deep dir_result_buffer (drb); SourceD dequeues it from drb and writes the dirty victim back to the outer memory. The defect is an asymmetry between the two ends of the handshake: the **enqueue enable** (Scheduler.scala:246, `enq.valid` includes the dirty condition) and the **result consumption condition** (:252, the miss branch of `result.ready` = `push.ready`, without `drb.enq.ready`) disagree. When drb is full, the miss-dirty result is consumed normally (the request is still allocated an MSHR entry and still lands in the requests queue), but the enqueue of its victim writeback information is silently discarded — **the dirty victim's writeback is permanently lost**. After the refill overwrites the victim way, the outer memory holds stale data; subsequent reads of the victim block return the old value. A data-correctness-level defect.

The evidence chain is three-leg machine-proven reachability: the Directory leg proves that miss-dirty results can be produced on two consecutive cycles; the SourceD leg proves that under a-channel backpressure drb's dequeue window is blocked for ≥3 cycles (drb stays full); the Scheduler leg proves that when "drb full × miss-dirty result" coincide on the same cycle, the enq is dropped while allocate/push still fire. The fix (i43 patch): add `drb.enq.ready` to result.ready for miss-dirty; fixed-version theorems `fmem_i43s_no_leak` (symbolic no-leak) + `fmem_i43_witness_green` + the regression `fmem_i43s_regress`.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **Victim and writeback**: when a cache miss needs to install a new block and the target set is full, an old line (victim) must be selected to make way. If the victim is **dirty** (written, inconsistent with the outer memory), it must be written back to memory first, otherwise data is lost.
- **miss-dirty result**: one cycle after the L2's directory lookup it produces a result: hit/miss, the victim's set/way, whether the victim is dirty. miss with dirty=1 means "install a new block and the victim is dirty" — this miss carries a writeback obligation.
- **dir_result_buffer (drb)**: a **1-entry-deep** queue inside the Scheduler (Scheduler.scala:244) that receives every directory result needing SourceD processing (hit, miss-dirty, flush last item). SourceD takes victim information from drb (the group of Muxes at :257-272: when there is no schedule.d, the sourceD request comes entirely from drb), issues a read of the victim line, and then writes it back to the outer memory via the writeback channel.
- **Handshake discipline (Decoupled)**: under the valid/ready protocol, a datum counts as consumed only when `valid && ready` hold in the same cycle; if "the consumer believes it consumed" while "the receiver did not actually take it", the data is lost. This entry's defect is exactly two "consumption judgments" disagreeing.

### 1.2 Design Intent

When a directory result emerges: a hit result goes into drb (SourceD needs to read data back to L1); a miss-dirty result must both push the request into the requests queue (for the subsequent outer-memory fetch) and push the victim writeback information into drb. Both consumption paths must succeed before the result can be consumed — result.ready should reflect both.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: drb's enqueue enable includes dirty** (`Scheduler.scala:244-247`):

```scala
val dir_result_buffer=Module(new Queue(new DirectoryResult_lite_victim(params),1))   // :244, depth 1

dir_result_buffer.io.enq.valid:= directory.io.result.valid && (directory.io.result.bits.hit || directory.io.result.bits.dirty || directory.io.result.bits.last_flush) //hit or miss dirty, sourceD don't care if dirty when hit   // :246
dir_result_buffer.io.enq.bits:=directory.io.result.bits                                 // :247
```

A miss-dirty result (hit=0 and dirty=1) satisfies the dirty branch of enq.valid — **the intent to enqueue clearly exists**. drb has only 1 entry of depth: when full, enq.ready=0 and the enqueue is dropped.

**Construct 2: drb's dequeue depends on SourceD being ready** (`Scheduler.scala:249`):

```scala
dir_result_buffer.io.deq.ready:= !schedule.d.valid && sourceD.io.req.ready
```

When SourceD is busy (e.g. a-channel backpressure, the writeback cannot go out), deq is blocked — drb staying full is a reachable, routine window (machine proof in §4 leg B).

**Construct 3: the miss branch of result.ready only looks at push.ready (★ hazard)** (`Scheduler.scala:252`):

```scala
directory.io.result.ready:= Mux(directory.io.result.bits.hit,dir_result_buffer.io.enq.ready,requests.io.push.ready)
```

The hit branch correctly carries `drb.enq.ready`; **the miss branch (including miss-dirty) has only `requests.io.push.ready`**. So when drb is full:

- from the directory's perspective ready=1 ⇒ the result is consumed and the pipeline advances;
- allocate still fires (the allocate gating at Scheduler.scala:190 only looks at result.valid), the MSHR entry is allocated;
- push still lands (push.ready=1), the request enters the requests queue;
- only the :246 enq is dropped because drb is full — **the victim writeback information is lost**.

**Construct 4: the consumption consequence — SourceD takes the victim only from drb** (`Scheduler.scala:257-272`):

```scala
sourceD.io.req.bits.way := Mux(!schedule.d.valid, dir_result_buffer.io.deq.bits.way, ...)
sourceD.io.req.valid  := Mux(!schedule.d.valid, dir_result_buffer.io.deq.valid, ...)
...
```

drb is the sole source of SourceD's victim writeback requests. Writeback information never enqueued ⇒ SourceD never issues a writeback for that victim ⇒ after the refill data lands and overwrites the victim way, the block's old data in memory becomes a permanently stale value.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

The defect chain (three-leg machine-proven reachability, see §4):

1. drb full (the previous miss-dirty's victim writeback has not yet been taken by SourceD — under a-channel backpressure SourceD's deq is blocked, window ≥3 cycles);
2. the directory produces a second miss-dirty result (consecutive miss-dirty results can be produced, Directory-leg machine proof);
3. `result.ready = push.ready = 1` (the miss branch does not look at drb) ⇒ the directory consumes the result, allocate still fires, push still lands;
4. drb.enq.valid=1 but enq.ready=0 ⇒ **the victim (set/way/data) writeback information is never enqueued**;
5. SourceD takes the victim only from drb ⇒ the writeback of that victim never happens;
6. after that entry's refill arrives and overwrites the victim way ⇒ the outer memory holds stale data ⇒ subsequent reads of the victim block return **stale data (correctness-level)**.

### 3.2 Root Cause

The Mux at :252 splits the "result consumption condition" two ways by hit/miss, but drb's enqueue intent (:246) is three-way (hit ‖ dirty ‖ last_flush) — **the two expressions' conditional structures are asymmetric**. The hit branch remembers to carry drb.enq.ready; the miss-dirty branch forgets. This is a "two ends of a handshake with asymmetric conditions" omission: the enqueue side declares "I want to accept dirty", while the consumption side does not wait for "was it accepted".

### 3.3 Harm and Tolerability

- **Harm**: memory data goes stale — the latest write to the victim block is lost, and any subsequent read (this SM's refill, another SM, host direct read) gets the old value. This is **silent data corruption**: no trap, no assertion, no error report. The consequence is persistent (not a transient race — the data is simply wrong).
- **Trigger condition**: drb full (the SourceD backpressure window, routine) × consecutive miss-dirty results (routine for workloads with lots of dirty data). No anomalous configuration is needed.
- **Tolerability**: intolerable (correctness-level). Rating: high.
- **Amplifying surface**: the L2 is the last-level cache shared by all SMs (before the consistency point on the host-side memory); its writeback loss affects every user.

---

## 4. Lean Formal Evidence

Three-leg machine-proven reachability (all zero sorry; file `lean/Ventus/L2/Discharge.lean` §2, :133-269). Methodology: instead of jointly instantiating all submodules, the Scheduler side replays a hand-constructed input trace, while the Directory/SourceD sides each independently machine-prove "the input signals can be produced", and the legs are connected signal-by-signal per signal semantics (the alignment notes at Discharge.lean:140-143).

**Leg C (Scheduler side, core witness)**: `l2dc_i43_witness` (Discharge.lean:171, native_decide) —

- Cycle 0: miss-dirty result1 (Get, tag 0x111, set 9, way 2) enqueues normally (drb empty → full: drbValid=1, drbBits.tag=0x111); SourceD busy ⇒ deq blocked;
- Cycle 1: miss-dirty result2 (Get, tag 0x222, set 10, way 5) arrives with drb full: the enq enable condition is false, but `l2scPushValid = true` (push still fires);
- consumption evidence: entry 1 is allocated (request.tag=0x222, set=10, way=5, scheAValid=1), valids=0b11;
- discard evidence: drb still holds result1's victim (tag 0x111, set 9, way 2) — **result2's victim (set 10/way 5) is never enqueued**.

Per-cycle machine proof of environment legality: `l2dc_i43_env0` / `l2dc_i43_env1` (both cycles satisfy `l2scEnv`).

**Leg A (Directory side: producibility of the inputs)**: `l2dc_i43_dir_results` (Discharge:238, native_decide) — the Directory model (hand-constructed prior state: wipe complete, all lines dirty) produces miss-dirty results on two consecutive cycles (cycle 1: set 9; cycle 2: set 10), and the second read is accepted on the very cycle the first result is consumed (readFire=1) — the two results of leg C's cycle 0/cycle 1 can indeed be produced on a real Directory pipeline. Auxiliary probe theorems `l2dc_probe_o1`/`l2dc_probe_o2`/`l2dc_probe_fire` pin down the output shape conjunct by conjunct.

**Leg B (SourceD side: producibility of the backpressure window)**: `l2dc_i43_sourced_busy` (Discharge:260, native_decide) — after SourceD accepts a miss-dirty Get request, under a-channel backpressure `reqReady` stays 0 for ≥3 consecutive cycles (o0=1, o1=o2=o3=0) — drb's deq (:249 requires sourceD.req.ready) is blocked across a window covering leg C's cycle 0/cycle 1.

**Axiom audit**: `#print axioms` at the end of Discharge.lean — the three witness theorems carry the `_native.native_decide.ax_*` trust axioms (the expected form under the 4.31 toolchain); the environment-legality theorems are at the propext/Quot.sound level only.

---

## 5. Simulation Verification

**Ready-to-run, not executed in this environment.** Neither doc/22's ChiselSim channel (11 suites) nor its Verilator channel (10 kernels) contains an L2 Scheduler-level suite; I-43 has no RTL reproduction case.

Indirect evidence: the **38-patch combined-tree regression** (2026-09-10, doc/22) — the combined tree including the i43 patch passed mill compilation, and all regression suites were judged identical to the 35-patch tree (no collateral damage). This is patch regression-safety evidence, not an RTL reproduction of the bug.

Suggested reproduction (ready to be written): targeted ChiselSim — at the L2 Scheduler level: first fill drb with one miss-dirty (SourceD backpressured), then feed a second miss-dirty directory result, and observe drb.enq.fire=0 while directory.result.fire=1 in the same cycle; the end-to-end version then lets the refill through, reads the victim address, and compares against memory data.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: any workload with "L2 has dirty lines + high miss density + occasional backpressure on SourceD/the writeback channel". Writeback-channel backpressure is routine when the outer memory is busy; dirty victims are routine in write-intensive workloads. The combination of the two conditions is not an anomalous scenario.
- **Observable consequence**: the victim address's data reverts to its old value. For GPU workloads this manifests as silently wrong computation results (no error report); host-side comparison can detect it.
- **Why upstream didn't find it**: it needs the one-cycle window where "drb happens to be full" to collide with a miss-dirty result; upstream test workloads (vecadd etc.) put low pressure on the L2 and drb almost never fills. A blind spot of low-pressure testing.
- **Shared background with I-38**: I-38 (SourceD stage_8 payload overwritten under backpressure) and I-43 share the SourceD backpressure window — SourceD being busy is a routine L2 event, and multiple defects cluster in the same weak-handshake region.

---

## 7. Fix and Fix Verification

**Patch** (`i43-l2-scheduler-drb-ready.patch` (internal fix manifest; not released), a single edit point):

```scala
// :252 after the fix (adds drb.enq.ready for miss-dirty)
directory.io.result.ready:= Mux(directory.io.result.bits.hit,dir_result_buffer.io.enq.ready,
  requests.io.push.ready && (!directory.io.result.bits.dirty || dir_result_buffer.io.enq.ready))
```

A dirty=1 miss result must now wait for space in drb before being consumed — the writeback information and the request advance live and die together; dropping is impossible. Non-dirty misses are unaffected (drb does not accept them anyway).

**Fixed-version modeling verification** (`lean/VentusF/MemL2.lean`, 【Lean machine-checked proof】):

- `fmem_i43s_no_leak`: the fixed version does not leak miss-dirty results (symbolic theorem — result consumed ⇒ drb enq succeeded);
- `fmem_i43_witness_green`: the original witness trace goes green on the fixed version (result2 is backpressured while drb is full, and enqueues normally once drb drains);
- `fmem_i43s_regress`: regression safety — outside the trigger domain the fixed version behaves identically to the original;
- residual case honestly registered: `fmem_i43_push_leak_residual` (a boundary case that persists after the fix; see the theorem's comment in VentusF/MemL2.lean and the table in doc/modules/24 §5).

**Patch-tree regression**: i43 is in the 35/38 combined patch tree (doc/22); all combined-tree regression suites judged identical, no collateral damage 【simulation run · regression level】.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Scheduler.scala:244-252 / :257-272 line-by-line check (the asymmetry between the three-way enq and the two-way ready) | Single construct point |
| Lean machine-checked proof | Three legs: `l2dc_i43_witness` (Scheduler consumption/discard in the same cycle) + `l2dc_i43_dir_results` (Directory can produce consecutive miss-dirty) + `l2dc_i43_sourced_busy` (SourceD backpressure window ≥3 cycles); environment legality `l2dc_i43_env0`/`l2dc_i43_env1` | Three-leg machine-proven reachability |
| Fix verification | `fmem_i43s_no_leak` (symbolic no-leak) + `fmem_i43_witness_green` + `fmem_i43s_regress`; i43 patch in the 38-patch combined-tree regression with no collateral damage | Machine proof + regression |
| RTL reproduction | None (ready-to-run; doc/22 does not cover an L2 Scheduler suite) | Gap, honestly noted |

I-43 is a "two ends of a handshake with asymmetric conditions" defect: the enqueue enable declares a three-way receive intent (hit‖dirty‖flush), while the consumption condition lets results through on a two-way split (hit/else) — miss-dirty falls exactly into the crack between the two expressions. The consequence is loss of the L2's dirty victim writeback and persistent memory staleness; the rating is high (correctness-level). The three-leg machine proof pins down every link of "the trigger window is reachable" (production, backpressure, same-cycle) as a theorem.
