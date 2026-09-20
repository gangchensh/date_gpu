> English translation of the Chinese master `doc/bugs/I-42-mixed缺守卫插入失败.md`. Translated 2026-09-13.

# I-42 Detailed Defect Analysis Report: L2 Scheduler's mixed Flag Missing the tagMatches.orR Guard — Silent Cache Insertion Failure

| Item | Content |
|---|---|
| ID | I-42 |
| Source location | `ventus/src/L2cache/Scheduler.scala:214` (★ hazard: `m.io.mixed` missing the `tagMatches.orR` guard); linked points `MSHR.scala:118-124` (sche_dir_valid set condition includes `!(io.mixed‖mixed_reg)`), `MSHR.scala:128-131` (mixed_reg can only be cleared by allocate), `Scheduler.scala:227`/`:276` (directory/bankedStore write enable = schedule.dir.valid) |
| Type | Functional bug — performance-level (silent cache insertion failure; data correctness is not compromised) |
| Severity | **Medium** (the consequence is the performance loss of repeated misses; the refill datapath itself is correct, no data error) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified (VentusF/MemL2.lean) + i42 patch included in the 38-patch combined-tree regression |
| Primary evidence | 【Lean machine-checked proof】`l2dc_i42_witness` (buggy/control dual trace) + per-cycle machine proof of the five cycles' environment legality; 【direct source reading】line-by-line check of Scheduler.scala:214 and MSHR.scala:110-134 |
| Lean model | `lean/Ventus/L2/Scheduler.lean` (combinational logic + invariants, `l2sc*`), `lean/Ventus/L2/Discharge.lean` (joint temporal discharge, `l2dc*`); fixed version `lean/VentusF/MemL2.lean` (`fmem_i42_*`) |
| Reproduction/patch | No ChiselSim suite (doc/22's 11 suites do not cover the L2 Scheduler; ready-to-run); patch `i42-l2-scheduler-mixed-guard.patch` (internal fix manifest; not released) |
| Related entries | I-43/I-44 (same file, discovered in the same wave), I-39/I-41 (reachability discharges on the same Scheduler), I-40 (witness on the same Scheduler) |

---

## 0. Abstract

The L2 Cache's central scheduler (Scheduler) computes a `mixed` flag for each MSHR entry, intended to mark the special case where "the opcode of the entry's miss result differs from the opcode of its request" (the MSHR.scala:132 comment says: "this MSHR has read miss and write miss"). The computation (Scheduler.scala:214) uses `OHToUInt(tagMatches)===i` to locate "the entry on the same block as this directory result", but **omits the `tagMatches.orR` guard**: when `tagMatches=0` (no match, i.e. an ordinary miss), `OHToUInt(0)=0`, so any directory result whose opcode differs from entry 0's will falsely tag **entry 0** with mixed.

Once set, mixed_reg can only be cleared by the next allocate (MSHR.scala:128-131), while the set condition of sche_dir_valid includes `!(io.mixed‖mixed_reg)` (MSHR.scala:123) — after that entry's refill data arrives it **never obtains directory-write eligibility**, so the refill writes neither the directory (Scheduler.scala:227) nor the bankedStore (:276): **the cache insertion silently fails**. The data is not corrupted (refill data reaches L1 directly via the sinkd path; the data_reg path is correct; the directory and data array still hold the victim's old contents, consistently with each other), but subsequent accesses to the same block miss repeatedly — functional correctness is not compromised; performance is.

Evidence: Lean machine-checked witness (3-cycle buggy/control dual trace, environment legality machine-checked per cycle) + fixed-version modeling verification (`fmem_i42_guard`/`fmem_i42_witness_green`/`fmem_i42_regress`) + the i42 patch (:214 adds `tagMatches.orR &&`) in the 38-patch combined-tree regression.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **L2 Cache and MSHR**: the L2 is the second-level cache shared by the L1s of all SMs. A Miss Status Holding Register (MSHR) registers an in-flight miss request: while a block's miss is unresolved, subsequent requests to the same block do not re-access memory; they merge into the existing MSHR entry (secondary miss). Ventus's L2 Scheduler holds 32 MSHR entries and a requests ListBuffer (32 queues × 32-entry pool).
- **directory**: records the tag and state of the block currently resident in each set/way. An access first queries the directory (read); the result (hit/miss, victim way, dirty bit, etc.) emerges one cycle later, and the Scheduler uses it to allocate the request to a free MSHR entry (allocate) or merge it into an existing entry (merge/secondary push).
- **TileLink-style channels**: fetch requests to the outer memory go on the A channel (Get/Put), responses on the D channel (AccessAckData etc.); each request carries a source number (here = the MSHR entry number), and responses are routed back by source.
- **refill and directory refill**: after the miss's data is fetched back from the outer memory (received via sinkD), the entry must launch a schedule.dir transaction: write the new block's tag into the directory and the data into the bankedStore — only when this step completes is the block truly "inserted" into the L2.
- **The `mixed` flag**: a one-bit register inside the MSHR entry (mixed_reg). Design intent (MSHR.scala:132 comment): marks the case "read miss and write miss mixed on the same entry" — in this case the refill should not write the directory via the ordinary flow (the directory state is maintained separately by the write path).

### 1.2 Design Intent

The intent of Scheduler.scala:214 is: when a directory result emerges, find the entry that is on the **same block** as it (bit i of tagMatches is 1); if the result's opcode differs from that entry's request opcode, tag it with mixed. The premise is "at least one bit of tagMatches is 1" (the result really did hit some in-flight entry) — `OHToUInt(tagMatches)` only has meaning in that case.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the computation of mixed (★ hazard)** (`Scheduler.scala:213-215`):

```scala
mshrs.zipWithIndex.foreach { case (m, i) =>
  m.io.mixed:= directory.io.result.valid&& (OHToUInt(tagMatches)===i.asUInt) && (directory.io.result.bits.opcode=/= m.io.status.opcode)   // :214
}
```

`OHToUInt` converts a one-hot vector to an index; for an **all-zero input** (no match), Chisel's OHToUInt semantics degenerates to 0 (`l2scOtu` models this hardware semantics). Thus when tagMatches=0, `OHToUInt(tagMatches)===i.asUInt` is constantly true for i=0 — **any valid directory result** (whether a hit or a no-match miss), as long as its opcode differs from entry 0's request opcode, falsely tags entry 0 with mixed.

**Construct 2: the consequence chain of mixed — sche_dir_valid is never set** (`MSHR.scala:118-124`):

```scala
when(io.allocate.valid){
  sche_dir_valid :=false.B
}.elsewhen(io.schedule.dir.fire) {
  sche_dir_valid := false.B
}.elsewhen(io.mixed){
  sche_dir_valid:=false.B        // :122-123 area: mixed forces 0 that cycle
}.elsewhen(io.sinkd.valid && !(io.mixed||mixed_reg)){
  sche_dir_valid:=true.B         // :123-124: the directory write is armed only when the refill arrives and it is not mixed
}
```

**Construct 3: mixed_reg is cleared only by allocate** (`MSHR.scala:128-131`):

```scala
when(io.allocate.valid) {
  mixed_reg:=false.B
}.elsewhen(io.mixed){
  mixed_reg:=true.B
} //this MSHR has read miss and write miss
```

The falsely-tagged mixed leaves mixed_reg stuck set; while the entry awaits its refill it will not be allocated again (it is occupied), so mixed_reg persists for the rest of the entry's lifetime.

**Construct 4: directory/data-array write enables are gated on schedule.dir.valid**:

```scala
// Scheduler.scala:227
directory.io.write.valid := schedule.dir.valid
// Scheduler.scala:276
bankedStore.io.sinkD_adr.valid := schedule.dir.valid     //now managed by MSHR
```

And MSHR.scala:134 `io.schedule.dir.valid := sche_dir_valid && (request.opcode===Get)` — sche_dir_valid stuck at 0 ⇒ schedule.dir never fires ⇒ the refill writes neither the directory nor the bankedStore.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

The defect chain (every link has machine proof or direct source-reading evidence):

1. entry 0 holds a Get miss request, awaiting the outer-memory refill;
2. in the meantime, any directory result with opcode≠Get emerges (either a Put hit or a Put miss — a common interleaving scenario), whose tag does not match entry 0 (tagMatches=0);
3. OHToUInt(0)=0 ⇒ Scheduler.scala:214 falsely tags entry 0 with mixed;
4. mixed_reg sticks set (MSHR.scala:128-131); when the refill arrives (sinkd.valid), the :123 condition `!(io.mixed‖mixed_reg)` fails ⇒ sche_dir_valid is not set;
5. schedule.dir.valid stays 0 ⇒ neither the directory nor the bankedStore is written (Scheduler.scala:227/:276) — **the block is never inserted into the L2**;
6. subsequent accesses to the same block keep missing (the directory still holds the old contents), repeatedly going to the outer memory — a silent performance loss.

### 3.2 Root Cause

`OHToUInt`'s degenerate value (0) on an all-zero input is treated as a legitimate index. The correct pattern is right there in the same file, in the `is_pending` computation at `Scheduler.scala:180-182` (`tagMatches.orR && alloc` is decided first; OHToUInt only has meaning when orR is true) — :214 omits the same guard. This is a typical "one-hot decoder input not checked for emptiness" omission. Chisel's OHToUInt documented semantics is defined only for one-hot inputs; the caller bears the obligation to check.

### 3.3 Harm and Tolerability

- **Harm classification**: data correctness is not compromised. Refill data reaches L1 directly via the sinkd → data_reg path (independent of the directory write); the directory and the bankedStore keep the victim's old contents, and the two are self-consistent (the tag array and the data array point to the same old block), so no "tag says A, data is B" misalignment arises. The consequence is purely a **cache insertion failure**: every access to that block misses, increasing outer-memory traffic and latency.
- **Trigger surface**: requires "entry 0 in flight + a different-opcode directory result emerging in the meantime". entry 0 is insertOH's preferred free slot (lowest-bit first), so under high load entry 0 is used frequently; Put/Get interleaving is the norm for multi-SM workloads. The trigger frequency is non-trivial.
- **Tolerability**: functionally tolerable (no wrong data); if any upper layer relied on "L2 hit" for a coherence decision, that would need re-auditing (no such dependency seen so far). Rating: medium (performance-level).

---

## 4. Lean Formal Evidence

All machine-checked (zero sorry; the witness family uses native_decide, environment legality uses symbolic theorems), in file `lean/Ventus/L2/Discharge.lean` (§1, :48-131).

**Main witness** (`l2dc_i42_witness`, Discharge.lean:90, native_decide) — a 3-cycle buggy/control dual trace:

- Cycle 0: the directory result of a Get miss (tag 0xAB, set 5, way 3) allocates entry 0;
- Cycle 1 (buggy): a Put miss result (tag 0xCD, no match with entry 0) — that cycle `l2scMixedI ... 0 = true` (OHToUInt(0)=0 and Put≠Get); cycle 1 (control): the same trace with only the result opcode changed to Get ⇒ no mixed tag;
- Cycle 2: entry 0's refill response (AccessAckData, source=0);
- buggy final state: refill data received (sinkDReg=1), mixedReg=1, scheDirValid=0, and on the observation cycle (dir write port ready) `l2scSchedDirValid = false`, `l2scSinkDAdrValid = false` — neither the directory write nor the bankedStore address write is launched;
- control final state: scheDirValid=1, schedule.dir fires normally, and the directory write and bankedStore write point to set=5/way=3 (correct insertion).

**Per-cycle machine proof of environment legality** (symbolic theorems, not numeric enumeration):
`l2dc_i42_env0` / `l2dc_i42_env1_put` / `l2dc_i42_env1_get` / `l2dc_i42_env2_bug` / `l2dc_i42_env2_ok` — all five cycles satisfy `l2scEnv` (E1: sinkd only targets active entries; E3: at allocate time the push is accepted). That is, every cycle of the witness's inputs can arise in a legal environment.

**Supporting definitions**: `l2scMixedI` (Scheduler.lean, the line-by-line model of :214; OHToUInt's hardware semantics includes `OHToUInt(0)=0`); OHToUInt's semantics is modeled by `l2scOtu` and noted in the file header D5.

**Axiom audit**: `#print axioms l2dc_i42_witness` at the end of Discharge.lean — the native_decide witness carries the `_native.native_decide.ax_*` trust axioms (the expected form under this project's Lean 4.31 toolchain, noted for the archive); the environment-legality theorems are at the propext/Quot.sound level only.

---

## 5. Simulation Verification

**Ready-to-run, not executed in this environment.** Neither doc/22's ChiselSim channel (11 suites, 18 cases, actually run 2026-09-06/07) nor its Verilator channel (10 kernels) contains an L2 Scheduler-level suite — all three L2 entries I-42/I-43/I-44 lack RTL reproduction cases.

Available indirect evidence: the **38-patch combined-tree regression** (2026-09-10, doc/22 §"38-patch combined-tree regression") — the combined tree including the i42 patch passed mill compilation (MILL_EXIT=0), and all 11 regression suites were judged identical to the 35-patch tree (no collateral damage). This is regression-safety evidence for the patch; it does not constitute an RTL reproduction of the bug itself.

Suggested reproduction (ready to be written): targeted ChiselSim — apply to the L2 Scheduler the sequence "Get miss allocates entry 0 → a no-match Put result emerges in the same window → refill arrives", and observe directory.io.write.valid and bankedStore.io.sinkD_adr.valid staying 0 on the buggy trace and behaving normally on the control trace.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: an L2 Get miss interleaved with any Put traffic. A single-SM pure-read workload does not trigger; under multi-SM mixed read/write workloads (the GPU norm), entry 0 is in flight with high frequency, so the trigger probability is non-trivial.
- **Observable consequence**: repeated Gets to the same block address are visible on the outer-memory (AXI/DRAM) side — detectable at the performance-counter level (repeated misses on the same address); nothing is reported at the functional level.
- **Why upstream didn't find it**: the effect is performance, not correctness, and it only affects misses that "happen to use entry 0 + interleave with a Put"; no assertion covers it (a directory non-write violates no online check).
- **Necessity of the fix**: the patch is a one-line guard, minimal risk, and the benefit is restoring the L2's normal insertion behavior for this class of interleaved traffic.

---

## 7. Fix and Fix Verification

**Patch** (`i42-l2-scheduler-mixed-guard.patch` (internal fix manifest; not released), a single edit point):

```scala
// :214 after the fix (adds the tagMatches.orR guard)
m.io.mixed:= directory.io.result.valid && tagMatches.orR && (OHToUInt(tagMatches)===i.asUInt) && (directory.io.result.bits.opcode=/= m.io.status.opcode)
```

On no match (tagMatches=0), orR=0, so every entry's mixed is 0 — the source of the false tagging is sealed; when there is a match, behavior matches the original design intent.

**Fixed-version modeling verification** (`lean/VentusF/MemL2.lean`, 【Lean machine-checked proof】):

- `fmem_i42_guard`: the fixed version's mixed includes the tagMatches.orR guard (no match ⇒ no tag);
- `fmem_i42_witness_green`: the original witness trace goes green on the fixed version (after the refill the dir write fires normally);
- `fmem_i42_regress`: regression safety — outside the trigger domain (match present, or same opcode) the fixed version behaves identically to the original.

**Patch-tree regression**: i42 is in the 35/38 combined patch tree (doc/22); all combined-tree regression suites judged identical, no collateral damage 【simulation run · regression level】.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Scheduler.scala:214 / :227 / :276, MSHR.scala:118-124 / :128-131 / :134 line-by-line check | Two source files consistent |
| Lean machine-checked proof | `l2dc_i42_witness` (buggy/control dual trace) + five environment-legality theorems (`l2dc_i42_env0`/`env1_put`/`env1_get`/`env2_bug`/`env2_ok`) | Witness level (trace reachable and consequence occurs) |
| Fix verification | `fmem_i42_guard`/`fmem_i42_witness_green`/`fmem_i42_regress` (fixed-version modeling); i42 patch in the 38-patch combined-tree regression with no collateral damage | Machine proof + regression |
| RTL reproduction | None (ready-to-run; doc/22 does not cover an L2 Scheduler suite) | Gap, honestly noted |

I-42 is an instance of the "one-hot decoder empty input unguarded" class of omission: a single missing line of `tagMatches.orR` makes the L2 silently lose cache insertions under common read/write interleaving. Data correctness is not compromised; the rating is medium (performance-level). The evidence chain closes with a machine-checked witness plus fixed-version verification; the RTL reproduction is left as a to-do.
