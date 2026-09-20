> English translation of the Chinese master `doc/bugs/I-35-L2-flushCount卡死.md`. Translated 2026-09-13.

# I-35 Detailed Defect Analysis Report: L2 Directory flushCount stuck at 1024 — second flush scans out of range

| Item | Content |
|---|---|
| ID | I-35 |
| Source location | `ventus/src/L2cache/Directory_test.scala:144-148` (the increment branch takes priority over the flushDone reset branch); related points `:135-136` (flushCount width and flushDone definition), `:139-140` (flush_set/flush_way derivation), `:151-159` (flush_issue_reg clearing), `:271` (io.ready) |
| Type | Functional bug (state-machine counter priority error) — coherence-maintenance path failure |
| Severity | **High** (an all-clean cache's first flush always triggers it; from the second flush on, 1024 cycles of out-of-range scanning with dirty lines not written back) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + patch exists (this entry not covered by RTL regression) |
| Primary evidence | 【Lean machine-checked proof】`l2dT_flush_count_stuck` / `l2dT_flush_second_outofrange` (+ `l2dT_flush_first_completes`); 【direct source reading】line-by-line check of Directory_test.scala :135-159 |
| Lean model | Original `lean/Ventus/L2/Directory.lean`; fixed version `lean/VentusF/MemL2.lean` (`fmem_i35_*`) |
| Reproduction/patch | ChiselSim ready-to-run (not executed in this environment, see §5); patch `i35-l2-directory-flushcount.patch` (internal fix manifest; not released) |
| Related entries | I-36 (status pollution on the flush path in the same file), I-38 (flush response chain, SourceD side), Q4 (victim LFSR period 31, same-file review point) |

---

## 0. Abstract

The Ventus L2 Cache directory (Directory_test) uses the `flushCount` counter
during flush/invalidate operations to scan the 64×16 = 1024 directory entries
one set×way at a time. The update logic for `flushCount` is written as
"increment branch takes priority over reset branch" (Directory_test.scala:144-148):
when the scan reaches the last entry (flushCount=1023, flushDone asserted),
the increment condition `(flush_issue_reg && (io.result.fire
|| !RegNext(...dirty...)))` still holds on the same cycle — either the last
entry's result being consumed (result.fire) or the last entry being clean
(!dirty) makes the increment branch hit — and Chisel's when/elsewhen priority
makes the **increment override the reset**, so flushCount stops at 1024 and
never resets (the source itself carries a `//todo not sure` comment at :149).

The first flush appears to complete normally (the last_flush response is sent
normally, `io.ready` recovers), and the fault is completely masked; **the
second flush starts scanning from flushCount=1024**: flush_set = 1024/16 = 64
is out of range (legal sets are only 0–63), the status array is indexed
dynamically out of bounds, the SRAM address is truncated, and the counter must
run another 1024 cycles to wrap back to 1023 before flushDone appears again —
during the out-of-range period dirty lines are not written back. Any scenario
that relies on flush for coherence maintenance (kernel boundaries, coherence
windows) silently fails from the second flush onward.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **L2 Cache and Directory**: Ventus's L2 is the chip-wide shared last-level
  cache (inclusive-cache lineage, a trimmed-down adaptation of the SiFive
  inclusive-cache). The **Directory** stores the tag of every cache block
  (in the `cc_dir` SRAM, 64 sets × 16 ways) and the valid/dirty state bits
  (the `status_reg` register array); it is responsible for hit determination
  on each request, victim-way selection on a miss, and responding to
  flush/invalidate.
- **flush / invalidate**: coherence-maintenance operations. flush = write all
  dirty lines back to memory; invalidate = additionally clear the valid bits.
  The initiator (Scheduler) raises `io.flush`/`io.invalidate` for one cycle;
  the Directory then scans all 1024 entries at a pace of **one entry per
  cycle**, handing dirty entries to SourceD via the result channel for
  writeback.
- **flushCount and flushDone**: `flushCount` is the scan cursor (11 bits,
  setBits(6)+wayBits(4)+1); `flush_set = flushCount/16` and `flush_way =
  flushCount%16` locate the current entry; `flushDone = (flushCount === 1023)`
  flags that the last entry has been reached.
- **io.ready**: `wipeDone && !flush_issue_reg`, indicating that the directory
  can serve requests normally; it is 0 during flush.

### 1.2 Design intent

A flush pulse arrives → `flush_issue_reg` is set and flushCount scans entry by
entry starting from 0 → each dirty entry issues a result (SourceD takes it for
writeback), clean entries are skipped directly → the scan reaches
flushCount=1023 (flushDone) → `flush_issue_reg` is cleared and **flushCount is
reset to zero**; the directory returns to standby, waiting for the next flush.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: definition of flushCount and the scan cursor** (`:135-140`):

```scala
val flushCount = RegInit(0.U((params.setBits+params.wayBits+1).W))   // :135, 11 bits
val flushDone  = flushCount===((params.cache.sets*params.cache.ways).asUInt-1.U)  // :136, ===1023
val flush_set  = flushCount/params.cache.ways.asUInt                  // :139
val flush_way  = flushCount%params.cache.ways.asUInt                  // :140
```

**Construct 2: the update logic — increment branch takes priority over reset branch** (`:144-148`, ★ the hazard):

```scala
when(io.flush || io.invalidate ||
     (flush_issue_reg && (io.result.fire || !RegNext(status_reg(flush_set).dirty(flush_way), false.B)))) {
  flushCount := flushCount + 1.U          // :145 increment
}.elsewhen(flushDone) {
  flushCount := 0.U                        // :147 reset — never reached
}
//todo not sure                            // :149 the source's own doubtful comment
```

The hazard lies in the when/elsewhen priority: on the flushDone cycle
(flushCount=1023), `flush_issue_reg` is still 1 (it is only cleared by the
`elsewhen(flushDone)` at :155-159 on the **same cycle**), and the last entry
either has result.fire (a dirty entry / last_flush being consumed) or
`!RegNext(dirty)` (a clean entry) — the increment condition necessarily holds,
the increment branch wins, and **the reset branch becomes dead code**.
flushCount increments from 1023 and stops at 1024.

**Construct 3: how the fault is masked — the first flush appears to complete** (`:151-159`, `:271`, `:305`):

```scala
}.elsewhen(flushDone) {           // :155-159: flush_issue_reg cleared normally
  flush_issue_reg := false.B
  ...
}
val io.ready = wipeDone && !flush_issue_reg                        // :271 recovers
io.result.bits.last_flush := Mux(flush_issue_regnext, RegNext(flushDone, ...), false.B)  // :305
```

The clearing of flush_issue_reg does **not** go through the flushCount logic
and happens normally; the last_flush response is sent normally; io.ready
recovers high. An external observer sees nothing abnormal — this is why the
bug remained latent in upstream simulation for a long time.

**Construct 4: the out-of-range second flush** (`:139-140` + truncation/dynamic-index semantics):

When the second flush pulse arrives, scanning starts from flushCount=1024:
`flush_set = 64`, while legal sets are only 0–63. `status_reg(flush_set)` is a
dynamic out-of-bounds index into the register array (read-out undefined), and
the `cc_dir` SRAM address (setIdx at :246) is truncated. The counter must run
another 1024 steps (the 11-bit counter wraps past 0 and climbs back to 1023)
before it meets flushDone again — meanwhile the dirty determination for every
entry is based on out-of-range/truncated data, and **writebacks of genuinely
dirty lines are skipped or misplaced**.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

1. flush/invalidate triggers; flush_issue_reg is set; flushCount scans entry
   by entry from 0;
2. On the cycle where the scan reaches the 1024th entry (flushCount=1023,
   flushDone=1): the increment condition
   `flush_issue_reg && (io.result.fire || !RegNext(dirty))` still holds
   (either the last entry's result.fire or the last entry being clean — one of
   the two must hold);
3. when priority ⇒ flushCount := 1024; the elsewhen(flushDone) reset branch is
   dead code;
4. flush_issue_reg is cleared normally and io.ready recovers — **the first
   flush appears to succeed**;
5. Second flush: flush_issue_reg is set again; flushCount keeps incrementing
   from 1024; flush_set ∈ {64, …, 127} (before the 11-bit counter wraps) —
   all out of range;
6. The out-of-range scan lasts 1024 cycles; during it the status read-out is
   undefined / the SRAM address is truncated, and dirty-line writeback is
   skipped — the coherence semantics that depend on flush are silently broken.

Trigger surface: **the first flush of an all-clean cache always triggers the
stuck state** (the Lean witness is exactly this scenario); any second
flush/invalidate enters the out-of-range scan. This is a "low-frequency but
certain-hit" defect — flush happens at kernel boundaries, so the second kernel
onward steps on it.

### 3.2 Root cause

A branch-ordering design error in the when/elsewhen chain: the designer's
intent was clearly "reset when the scan completes", but the reset was placed
in the lower-priority branch, without considering that the increment condition
still holds on the flushDone cycle (the clearing of flush_issue_reg and the
clearing of flushCount race on the same cycle, and the consumption of the
last_flush entry / its clean nature makes the increment condition true on that
cycle). The `//todo not sure` at :149 of the source shows the author had
doubts about this logic but never resolved them.

### 3.3 Harm and tolerability

- **Harm**: during the 1024 cycles of the second and subsequent
  flush/invalidate, dirty lines are not written back (under invalidate
  semantics, the valid-bit clearing is also based on out-of-range indices and
  may clear the wrong entries). Upper-level flows that rely on "after flush,
  memory holds the latest data" (result collection at kernel boundaries, host
  reading result buffers — same family as I-47's "completion reported before
  flush completes" but further downstream) read stale data. Data-correctness
  level.
- **Tolerability**: if the workload flushes only once per kernel and the host
  does not depend on the effect of a second flush, the first flush happens to
  be normal — strong masking; but multi-kernel scenarios (against the
  background of the same class of boundary problem where I-34 already ruled
  the AXI top-level ICache invalidate is tied to false) will certainly trigger
  it. Rating: **High**.

---

## 4. Lean Formal Evidence

`lean/Ventus/L2/Directory.lean` (the model covers Directory_test.scala
:111-311 line by line; `L2dState.flushCount` is an 11-bit field; the update
logic at :438-441 faithfully translates :144-148). All are `native_decide`
multi-cycle-trace witnesses 【Lean machine-checked proof】:

- **`l2dT_flush_count_stuck`**: after `l2dAfterFlush` (wiped state + 1 cycle of
  flush pulse + 1100 idle cycles), `flushCount = 1024#11` — the stuck value
  pinned down exactly;
- **`l2dT_flush_first_completes`**: ready recovers after the first flush —
  proves the fault is masked until the second flush, explaining why upstream
  simulation did not see it;
- **`l2dT_flush_second_outofrange`**: issuing another flush pulse on
  `l2dAfterFlush`, within 6 cycles `flushIssueReg = true` and
  `flushCount.toNat >>> 4 ≥ 64` — machine-checked proof that the second
  flush's scan cursor is out of range.

**Fixed version** (`lean/VentusF/MemL2.lean`):

- `fmem_i35_fix_vs_orig` / `fmem_i35_flushCount_def` /
  `fmem_i35_orig_flushCount_def`: comparison of flushCount update semantics
  before and after the fix;
- **`fmem_i35_count_returns_zero`**: after a fixed-version flush completes,
  flushCount returns to zero;
- **`fmem_i35_second_flush_in_range`**: the fixed version's second flush scans
  entirely in range;
- `fmem_i35_regress` / `fmem_i35_flushCount_regress` /
  `fmem_i3536_step_regress_others`: regression equivalence — step-by-step
  agreement with the original outside the trigger domain.

Model idealization statement (Directory.lean D2/Q8, evidence boundary stated
honestly): on an out-of-range flush, the status array is modeled as
"out-of-range read returns false, write is a no-op", and the SRAM address as
truncated (the most conservative interpretation); **the flushCount-stuck-at-
1024 fact itself is independent of this semantic choice** (pure counter
logic); the concrete read-path behavior of the out-of-range scan could differ
if FIRRTL semantics differ — this is a registered class-II risk boundary.

---

## 5. Simulation Verification

**Status: ready-to-run, not executed in this environment** (the
ChiselSim/Verilator dual-channel runs recorded in doc/22 cover entries in the
I-5…I-33 range, not the L2 Directory/SourceD group I-35–I-38).

Directed test design (ChiselSim, Directory_test module level): after wipe
completes, issue a flush pulse and wait for io.ready to recover; then issue a
second flush pulse and observe cycle by cycle the effect on the flush_set
output side (or directly observe the internal flushCount — if not visible,
observe whether the set field of the result sequence starts at 64) and the
absence of dirty-line writebacks. Expected: the first flush completes
normally; the second flush's result stream has set ≥ 64. The Lean witness
scenario of this entry (all-clean cache) is the configuration easiest to
rebuild on RTL.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: any run containing ≥2 flush/invalidate operations.
  flush is initiated by the Scheduler, driven by flush requests from the L1
  DCache (the kernel-boundary path); multi-kernel, multi-CU alternating
  flushes are the normal deployment form.
- **Why upstream did not find it**: the first flush is completely normal
  (§3.1 point 4); single-kernel tests/demos never trigger the second flush's
  out-of-range segment; and during the out-of-range period there is no
  assertion, no exception — silent.
- **Same-family entries**: I-36 (same file, same flush path, status pollution)
  and I-38 (flush completion signal's payload clobbered in SourceD) — when the
  three stack together, the flush coherence path is unreliable at three
  stages simultaneously: counting, directory state, and response.

---

## 7. Fix and Fix Verification

**Patch**: `i35-l2-directory-flushcount.patch` (internal fix manifest; not released) —
swap the two when branches (flushDone reset takes priority):

```scala
// I-35 fix: flushDone reset takes priority over increment
when(flushDone){
  flushCount := 0.U
}.elsewhen(io.flush || io.invalidate || (flush_issue_reg && (io.result.fire || !RegNext(...)))){
  flushCount := flushCount + 1.U
}
```

(An equivalent alternative: add `&& !flushDone` to the increment condition;
the patch uses the branch swap.)

**Fix verification**:

- Effectiveness 【Lean machine-checked proof】: `fmem_i35_count_returns_zero`
  (returns to zero), `fmem_i35_second_flush_in_range` (second flush in range);
- Regression safety 【Lean machine-checked proof】: `fmem_i35_regress` /
  `fmem_i35_flushCount_regress` / `fmem_i3536_step_regress_others`
  (step-by-step equivalence on non-trigger paths);
- RTL-level patch regression: not run (same as §5; this entry is not in the
  suite executed in doc/22).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Directory_test.scala :144-148 branch priority, :135-140 counter/cursor definitions, :151-159 clearing logic, :149 author's own `//todo not sure` note | Line-by-line check |
| Lean machine-checked proof | `l2dT_flush_count_stuck` / `l2dT_flush_second_outofrange` / `l2dT_flush_first_completes` | native_decide trace witnesses |
| Simulation reproduction | Ready-to-run (not executed in this environment; no record of this entry in doc/22) | Ready-to-run |
| Fix verification | i35 patch (branch swap); fixed version `fmem_i35_*` all green + regression equivalence | Machine-checked |

I-35 is a textbook case of the "branch priority" defect class: an ordering
error in two when branches turns the reset branch into dead code; the first
operation is completely normal, and from the second on the coherence path
silently fails — exactly the class of defect that simulation finds hardest to
expose (it needs the low-frequency sequence prefix "second flush") while
state-machine-level formal modeling hits directly.
