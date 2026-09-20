> English translation of the Chinese master `doc/bugs/I-23-ICache假命中垃圾指令.md`. Translated 2026-09-13.

# I-23 Detailed Defect Analysis Report: No Mutual Exclusion Between ICache probe × refill on the Same Cycle and Same Set — tag/data Reads Return LFSR Random Values (False miss / False hit Executing Garbage Instructions)

| Item | Content |
|---|---|
| ID | I-23 |
| Source location | `ventus/src/L1Cache/ICache/ICache.scala:262` (`coreReq.ready := true.B`, probe has zero backpressure, ★ structural root cause); `:145`/`:152`/`:175`/`:179` (the refill path `memRsp_Q.deq.fire` has no mutual exclusion with probe; the commented-out old code at the end of `:262` once contained the mutual exclusion); the carrying mechanism lives in SRAMTemplate: `L1TagAccess.scala:451` (tag instantiation, bypassWrite=false), `ICache.scala:84` (data instantiation, bypassWrite=false) |
| Type | Functional bug (instruction data corruption) — unguarded same-cycle read/write conflict |
| Severity | **High**: in the false-hit branch a warp receives an LFSR garbage instruction word and executes it (data/instruction-stream corruption); in the false-miss branch, MSHRs are allocated redundantly and memory is re-fetched (performance loss). Triggerable under the existing configuration |
| Confirmation status | 【Confirmed】 — ChiselSim reproduction successful (doc/22) + the fix turns green in patch-tree regression |
| Main evidence | 【Lean machine-checked proof】 structural absence of mutual exclusion + mechanism theorems + reachability witness + the two consequence chains false miss / false hit + a control group; 【simulation runs】 ChiselSim reproduction successful (after calibration); 【direct source reading】 ICache.scala/L1TagAccess.scala checked line by line |
| Lean model | `lean/Ventus/Mem/ICache.lean` (including the LFSR-semantics hookup of SRAMTemplate); fixed version `lean/VentusF/Mem.lean` |
| Reproduction/patch | `repro/L1CacheBugRepro.scala` (the I-23 case, ChiselSim); patch `i23-icache-probe-refill-mutex.patch` (internal fix manifest; not released) |
| Related entries | I-29 (the DCache-side member of the same family: victim writeback data polluted by LFSR), I-34 (AXI top-level icache_invalidate tied to false, further tightening the fetch-correctness boundary), I-24 (same module), the SRAMTemplate review note (doc/03) |

---

## 0. Summary

The ICache's fetch-request (probe) channel is hardwired to never backpressure (`io.coreReq.ready := true.B`,
ICache.scala:262 — the trailing comment shows the old code once had a `!memRsp_Q.io.deq.valid` mutual exclusion, which was removed),
while the L2 refill path's write enables into the same tag/data SRAM
(`tagAccess.io.w.req.valid := memRsp_Q.io.deq.fire`, :152; likewise for data at :175) and the probe's
read enables (:145/:179) have **no mutual exclusion whatsoever**. Both SRAMTemplate instances are
instantiated with bypassWrite=false, so a same-cycle same-address (same-set) read/write returns an LFSR64 random
value (the NutShell-lineage X-probing convention).

Because a missed warp recovers via "status=01 followed by scheduler replay" (warp_schedule.scala:194-198),
a retry probe landing on a refill cycle is **normal timing**, not a corner case — the collision scenario is structurally reachable.
The consequences split in two:

- **False miss** (the likely branch): the tag has actually been written, but the colliding cycle's readout is an LFSR value, so the verdict is miss →
  an MSHR entry is allocated redundantly for the same block, and the block is re-fetched from L2. In this configuration the refill writes identical data,
  so no data error results — it is purely a performance loss.
- **False hit** (data error): when the probe's tag happens to match the low 17 bits of the LFSR value, a HIT plus an LFSR garbage instruction word is returned for an address
  **that has never entered the cache** — the warp executes a garbage instruction.
  The LFSR sequence is deterministic, and so is the collision.

Evidence chain: on the Lean side, everything closes from the structural theorem (`ic_coreReq_ready_true`, rfl-level) to the mechanism theorems
(`ic_tag_collision_lfsr`/`ic_data_collision_lfsr`) to the reachability and consequence witnesses
(`icTA_*`/`icTB_false_hit`/`ic_false_hit_st1`) and finally the control group (`icTC_clean_hit`);
the ChiselSim reproduction succeeded (the same block fetched twice, the retry receiving the garbage data
0xce2468acf10eca86); the i23 patch (restoring coreReq backpressure on refill cycles) is verified both by Lean fixed-version
theorems and by patch-tree regression.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **Instruction cache (ICache)**: the first-level cache on the fetch path of a CPU/GPU. This design is 256 sets ×
  2 ways set-associative, with 32-word (1024-bit) blocks and 17-bit tags. On a hit, a two-stage pipeline (st1 checks tags,
  st2 returns data) sends 64 bits (2 instructions) to the ibuffer via `coreRsp`.
- **MSHR (Miss Status Holding Register)**: on a miss, records "which block is currently being fetched from L2"
  to avoid duplicate memory traffic for the same block; when the L2 response returns, the tag/data SRAM is refilled and the entry is released.
- **Warp replay**: this design's ICache does **not** buffer "who missed". A missed warp
  receives a status=01 response, and the warp scheduler later **re-issues the same fetch request**
  (warp_schedule.scala:194-198) — retries are a normal part of the protocol.
- **SRAMTemplate and bypassWrite**: when an SRAM macro is read and written at the same address in the same cycle, the read
  value is physically undefined. Chisel's SRAMTemplate (NutShell lineage), in a dual-port instantiation with
  bypassWrite=false, simulates this case by returning an **LFSR64
  pseudo-random value** (the X-probing convention; after synthesis it is real logic with an indeterminate readout). bypassWrite=true
  would forward the correct write data.
- **probe × refill mutual exclusion**: a standard discipline of cache design — on the cycle when a refill is writing a set,
  no probe read of the same set is allowed, otherwise the readout is meaningless.

### 1.2 Design Intent

The probe (coreReq) reads the tag/data SRAM to determine hit/miss; the refill (memRsp_Q dequeue) writes the block returned
from L2 into the tag/data SRAM. The two paths share the same physical SRAM array and must be mutually exclusive in time —
the commented-out old code at the end of `:262`, `!memRsp_Q.io.deq.valid && !mshrAccess.io.missRspOut.valid`,
is precisely the vestige of that mutual exclusion.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: probe with zero backpressure** (`ICache.scala:262`, ★ fault point):

```scala
io.coreReq.ready := true.B//!memRsp_Q.io.deq.valid && !mshrAccess.io.missRspOut.valid//mshrAccess.io.missReq.ready //&& !coreRsp_QAlmstFull
```

`coreReq.ready` is constant true — fetch requests are accepted at any time. The three trailing comments are historical
ready expressions, the first of which contains exactly the refill mutual exclusion (`!memRsp_Q.io.deq.valid`). After the mutual exclusion
was removed, no other structure took its place.

**Construct 2: probe read enables** (`ICache.scala:145`, `:179`):

```scala
tagAccess.io.r.req.valid := io.coreReq.fire && !ShouldFlushCoreRsp_st0   // :145 read tag
...
dataAccess.io.r.req.valid := io.coreReq.fire && !ShouldFlushCoreRsp_st0  // :179 read data
```

**Construct 3: refill write enables** (`ICache.scala:152`, `:175`):

```scala
tagAccess.io.w.req.valid := memRsp_Q.io.deq.fire   // :152 write tag
...
dataAccess.io.w.req.valid := memRsp_Q.io.deq.fire  // :175 write data
```

The refill depends only on memRsp_Q and MSHR busy, and on no field of coreReq whatsoever — the two paths
colliding on the same cycle and same set is structurally bound to be reachable.

**Construct 4: both SRAM instantiations have bypassWrite=false** (`L1TagAccess.scala:451`,
`ICache.scala:84`):

```scala
// L1TagAccess.scala:451 (the ICache-version tag array; shouldReset=F, holdRead=T,
//   singlePort=F, bypassWrite=F)
val tagBodyAccess = Module(new SRAMTemplate(UInt(tagBits.W), set=set, way=way,
  shouldReset = false, holdRead = true, singlePort = false, bypassWrite = false))

// ICache.scala:84 (the data array; shouldReset=F, holdRead=F, singlePort=F,
//   bypassWrite defaults to F)
val dataAccess = Module(new SRAMTemplate(gen=UInt(BlockBits.W), set=NSets,
  way=NWays, shouldReset = false, holdRead = false, singlePort = false))
```

bypassWrite=false ⇒ a same-cycle same-(set,way) read/write returns an LFSR64 value (unrelated to the
data being written and to the array's previous contents). The tag instantiation additionally has holdRead=true — the LFSR readout is held until
the next read, lengthening the observation window of the pollution.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

Trigger scenario (normal timing, not a corner case):

1. A warp's fetch misses → the ICache returns status=01, and the scheduler later **replays** the same address;
2. The retry probe lands on the same cycle as some refill (memRsp_Q.deq.fire), in the same set —
   after a miss, the L2 response's return and the warp's retry are naturally adjacent; no deliberate construction is needed;
3. On that cycle, st1's tag/data readout = an LFSR value (unrelated to the real contents);
4. Branch one (**false miss**): the refilled block's tag has been written, but the probe reads an LFSR
   value and judges miss → an MSHR entry is allocated redundantly for the same block and a duplicate memReq fetch is issued (performance loss);
5. Branch two (**false hit**): when the probe's tag happens to equal the low 17 bits of the LFSR readout, a HIT is declared for an address
   never allocated, and st2 sends the LFSR garbage word as an instruction via coreRsp to
   the ibuffer → **the warp executes a garbage instruction**.

The LFSR is a deterministic recurrence; whether a collision occurs is determined by the tag-value distribution, not by probabilistic noise.

### 3.2 Root Cause

`coreReq.ready := true.B` adopts "probe is always accepted" as a simplification, removing the refill mutual exclusion
(the trailing comment proves the mutual exclusion once existed). This is a **structural omission**, not a local typo: the refill
path (Construct 3) and the probe path (Construct 2) are each individually correct; what is missing is the timing arbitration between them.
The SRAMTemplate bypassWrite=false instantiation (Construct 4) then determines that the collision's consequence takes the form of
"reading a random value" rather than "reading the old/new value".

### 3.3 Harm and Tolerability

- **Harm**: the false-hit branch is **instruction-stream corruption** — a warp executes an "instruction" never written to memory,
  with completely unpredictable behavior (and since the LFSR value is deterministic in simulation but indeterminate after synthesis, debug
  reproduction of the scene is extremely difficult). The false-miss branch is a deterministic performance loss (redundant MSHR allocations + duplicate fetches).
- **Trigger surface**: any scenario where a post-miss retry coincides with a refill on the same cycle and same set; genuinely reachable under the existing configuration (256 sets
  × 2 ways, MMU off).
- **Tolerability**: intolerable (data-correctness level). Rating: **High**. When combined with I-34 (AXI top-level
  icache_invalidate tied to false), the boundary of this entry tightens further under
  multi-kernel same-address reuse.
- **Control confirmation**: `icTC_clean_hit` proves that "after a clean refill (no probe conflict), the hit verdict
  and the data path are completely correct" — the collision is the necessary condition, not a systematic model bias.

---

## 4. Lean Formal Evidence

All located in `lean/Ventus/Mem/ICache.lean`, zero sorries, full build passing. In four layers:

**Structural absence of mutual exclusion (combinational level / rfl level)**:

- `ic_coreReq_ready_true` (:1342): `coreReq.ready ≡ true`, rfl — probe has zero backpressure;
- `ic_deqFire_indep_probe` (:1346): the refill (deq.fire) depends only on the queue and MSHR busy,
  on no field of coreReq whatsoever (arbitrary state/input);
- `ic_probe_read_indep_refill` (:1353): the probe read enable is not conditioned on the refill.
  The three together: a same-cycle same-set collision is structurally bound to be reachable.

**Mechanism theorems (single cycle over arbitrary states, symbolic level)**:

- `ic_tag_collision_lfsr` (:1363): after a collision cycle (probe × refill same cycle, same set; the victim
  mask hits way j), way j's tag readout = the low 17 bits of the LFSR64 next value, independent of the tag
  being written and of the array's previous contents;
- `ic_data_collision_lfsr` (:1378): the same form for the data array (1024 bits, and with no
  invalidate precondition — the data read is not gated by invalidate);
- `ic_false_hit_st1` (:1402): the symbolic false-hit criterion — when the probe's tag happens to equal the LFSR value about to be read out,
  st1 "hits" on the victim way a ghost tag never written into the array.

**Reachability and consequence witnesses (native_decide, 3–5 cycles from reset)**:

- `icTA_collision_reachable` (:1458): constructs "probe and refill same cycle, same set" in 3 cycles from reset; `icTA_miss_accepted` (:1451), `icTA_tag_readout_lfsr` (:1465)
  pin down the accompanying trace shape;
- **False-miss chain**: `icTA_false_miss` (:1473, the tag has been written yet the verdict is miss) +
  `icTA_duplicate_alloc` (:1480, redundant MSHR entry allocation for the same block, duplicate fetch);
- **False-hit chain**: `icTB_false_hit` (:1503, a 5-cycle trace: miss A → refill B ∥
  probe a ghost address X; the array contains only tagB and empties, yet the probe of X hits, and st2 returns
  status=00 HIT + an LFSR garbage instruction word, which is ≠ the 0xDEADBEEF written that cycle).

**Control group**: `icTC_clean_hit` (:1524) — after a clean refill, the hit verdict and the data path
are completely correct (status=00, the real written data returned), ruling out a systematic model bias.

**Fixed-version verification** (`lean/VentusF/Mem.lean`): `fmem_i23_stall_mechanism` (:236,
after the fix coreReq is backpressured on refill cycles), `fmem_i23_no_false_verdict` (:249, false verdicts
eliminated), `fmem_i23_step_regress` (:257, step-by-step equivalence outside the trigger domain),
`fmem_i23_false_hit_gone` (:325, the original false-hit witness turns green),
`fmem_i23_retry_hit_correct` (:334, the retry hits correctly).

**Axiom audit** (archived in module report 20): the symbolic theorems depend only on
`[propext, Classical.choice, Quot.sound]`; `ic_false_hit_st1` additionally carries 2
bv_decide native LRAT trust axioms (`_native.bv_decide.ax_*`); each native_decide
witness carries 1 `_native.native_decide.ax_1_1` (the ofReduceBool family) — all
expected under the v4.31 toolchain, no sorryAx.

---

## 5. Simulation Verification (ChiselSim Measurement + Patch-Tree Regression)

**ChiselSim module-level** (`repro/L1CacheBugRepro.scala`, the I-23 case, actually run 2026-09-06/07,
doc/22): construct a single warp whose post-miss retry lands on the same cycle and same set as a refill. Measured: **the same
block is fetched twice** (redundant MSHR allocation — the false-miss consequence materializes); the retry receives a status=1
coreRsp with garbage data **0xce2468acf10eca86**. Verdict: **reproduction successful** (after calibration).

Calibration record (doc/22 test-change list): memRsp_Q is actually consumed on the cycle after the poke, so the retry
coreReq had to be shifted 1 cycle later to make "the read and the write coincide"; event-trace printing was also added.

**Patch-tree regression** (doc/22, two actual runs: the 35-patch tree 2026-09-07 and the 38-patch merged tree 2026-09-10):
L1CacheBugRepro (the three cases I-23/24/27) **3/3 green** — after the i23 fix, the retry
is backpressured on the refill cycle and hits cleanly on the next cycle.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: all fetch traffic. Post-miss replay is protocol-normal (warp_schedule.scala:194-198),
  and any miss-heavy kernel (cold start, large code footprint, many warps contending for the ICache) operates
  within the collision window.
- **Why upstream did not find it**: it requires the precise timing of probe and refill on the same cycle and same set + (for the false-hit
  branch) a collision of the tag's low 17 bits with the LFSR value; functional tests care about result correctness — a false miss merely shows as
  one extra memory access, and a false hit appears in simulation as a deterministic "weird instruction stream" easily blamed on the test itself.
- **Upstream corroboration**: the trailing comment at `:262` proves the maintainers once wrote the mutual exclusion and later removed it — this entry
  is a regression-type defect introduced by "optimizing away the backpressure".
- **Same-family entries**: I-29 (the same kind of collision on the DCache data array, where what gets polluted is the victim writeback data),
  and the SRAMTemplate review note (doc/03), which records the full inventory of this semantics.

---

## 7. Fix and Fix Verification

**Patch** (`i23-icache-probe-refill-mutex.patch` (internal fix manifest; not released),
single edit point):

```scala
// ICache.scala:262
-  io.coreReq.ready := true.B
+  // I-23 fix: when a refill (memRsp_Q dequeue writing the tag/data SRAM) collides with a probe
+  // on the same cycle and same set, the SRAM (bypassWrite=false) reads out an LFSR random value —
+  // false misses allocate MSHRs redundantly, false hits execute garbage instructions.
+  // Backpressure coreReq while a refill is pending, restoring probe×refill mutual exclusion.
+  io.coreReq.ready := !memRsp_Q.io.deq.valid
```

That is, restore the first mutual-exclusion term from the commented-out old code (backpressuring the probe on refill cycles). Alternative (not adopted):
change both SRAM instantiations to bypassWrite=true, forwarding the correct write data on same-cycle conflicts — a larger change
that also alters the SRAM macro's timing assumptions; the internal fix manifest classifies i23 as a Functional fix (required).

**Fix-verification trio**:

- Effectiveness: the Lean fixed-version theorems `fmem_i23_false_hit_gone`/`fmem_i23_retry_hit_correct`
  (in the original false-hit witness scenario, the fixed version's verdict and data are both correct);
- Regression safety: `fmem_i23_step_regress` (step-by-step equivalent to the original on non-refill cycles);
- RTL level: patch-tree regression L1CacheBugRepro 3/3 green (two rounds: the 35-patch tree and the 38-patch merged tree).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | ICache.scala:262 (ready constant true + the commented-out mutual exclusion), :145/:152/:175/:179 (no mutual exclusion between the two paths), L1TagAccess.scala:451 and ICache.scala:84 (bypassWrite=false instantiations) | Checked line by line at the cited line numbers |
| Lean machine-checked proof | `ic_coreReq_ready_true` (rfl) + `ic_deqFire_indep_probe` + `ic_probe_read_indep_refill` (structural); `ic_tag_collision_lfsr`/`ic_data_collision_lfsr`/`ic_false_hit_st1` (mechanism, symbolic level); `icTA_collision_reachable`/`icTA_false_miss`/`icTA_duplicate_alloc`/`icTB_false_hit` (reachability and consequence witnesses); `icTC_clean_hit` (control group) | Symbolic level + concrete traces |
| ChiselSim reproduction | the same block fetched twice + the retry receives garbage 0xce2468acf10eca86 (reproduction successful after calibration) | Measured |
| Fix verification | i23 patch (1 edit point); five Lean fixed-version `fmem_i23_*` theorems + patch-tree regression 3/3 green ×2 rounds | Machine-checked + measured |

I-23 is a "structural mutual exclusion removed" defect: two individually correct data paths share one
bypassWrite=false SRAM array, and all that is missing is same-cycle arbitration. Its false-hit branch (executing garbage
instructions) is among the highest-severity defect forms found in this project, while the false-miss branch was directly observed in RTL simulation
(redundant allocations, garbage data); the evidence chain is a complete closed loop.
