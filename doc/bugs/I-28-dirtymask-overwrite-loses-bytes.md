> English translation of the Chinese master `doc/bugs/I-28-脏掩码同字覆盖丢字节.md`. Translated 2026-09-13.

# I-28 Defect Detailed Analysis Report: dirtyMaskPerCL_init — multiple lanes with the same blockOffset overwrite each other, losing earlier lanes' bytes (L2 data loss)

| Item | Content |
|---|---|
| ID | I-28 |
| Source location | `ventus/src/L1Cache/L1TagAccess.scala:241-245` (dirtyMaskPerCL_init is written lane-by-lane in ascending order with overwrites; for the same blockOffset a later lane overwrites an earlier lane); feed point `ventus/src/L1Cache/DCache/DCache.scala:267` (TagAccess's perLaneAddr_st1 is connected to the **non-remapped** coreReq_st1.perLaneAddr); correct comparison path `DCache.scala:104-134` (genDataMapSameWord merges multiple lanes of the same word; the data path at :410/:375-378 uses the remapped value); upstream `LSU.scala:273-279` (perLaneAddr is emitted directly from addresses with no same-word merging, recorded in doc/03) |
| Type | Functional bug (silent data loss: the dirty bitmap comes out too small → bytes are missed when writing back to L2) |
| Severity | **High** (correctness level: L2 retains stale bytes; vector SB/SH stores with adjacent addresses trigger it — a common memory-access pattern) |
| Confirmation status | 【Confirmed】, ChiselSim reproduction succeeded (0x212 vs expected 0x213) + patch-tree regression turned green (i28 v2) |
| Main evidence | [Lean machine-checked proof] mechanism witness `l1taT_dmBuild_overwrite_real` (at the actual 32-lane × 32-block scale) + reachability machine proof `dcT_i28_asymmetry` (under the same input the data path has all bytes while the dirty-bit path misses bytes) + the positive theorem `dcWriteMissMask_complete` (the data path merges completely); [simulation run] ChiselSim L1TagAccessDirtyMaskRepro reproduction; [direct source reading] TA:241-245 / DCache.scala:267 / :104-134 checked line by line |
| Lean model | `lean/Ventus/Mem/L1TagAccess.lean` (§7 dirtyMask construction), `lean/Ventus/Mem/DCache.lean` (§3 data path and the I-28 witness); fixed version `lean/VentusF/Mem.lean` (§3, `fmemDmBuild`) |
| Repro/patch | `repro/L1TagAccessDirtyMaskRepro.scala` (ChiselSim); patch `i28-dirtymask-merge.patch` (internal fix manifest; not released) (**v2** — v1 had a combinational-loop incident, see §7) |
| Related entries | I-27 (same-module bit-order/merge family), I-24 (same family); the doc/22 patch-tree regression record "i28 v1 combinational-loop incident" |

---

## 0. Abstract

The DCache's writeback uses a **byte-level dirty bitmap**: each cacheline (32 words
× 4 bytes = 128 bits) is paired with a dirtyMask, and when writing back to L2 only
the bytes whose dirty bit is 1 are written — this exists to support coherence when
multiple SMs write to different parts of the same cacheline (the comment at
L1TagAccess.scala:206-207 states this design intent itself).

The defect lies in the construction of the dirty bitmap: L1TagAccess receives the
32 lanes' access descriptors (activeMask, blockOffset, wordOffset1H) sent by the
DCache and executes, lane by lane in ascending order,
`dirtyMaskPerCL_init(blockOffset) := wordOffset1H` (:241-245) — **overwrite writes
instead of an or-merge**. When two active lanes of the same vector memory
instruction fall in the same word (same blockOffset) but on different bytes
(adjacent-address SB/SH stores produce exactly this shape), the later lane's byte
mask overwrites the earlier lane's wholesale, and the earlier lane's dirty byte
bits are lost.

The key point is that **the data path does not have this problem**: the DCache's
data/write-mask path goes through genDataMapSameWord (:104-134), which bitwise-OR-
merges (remaps) multiple lanes of the same word, whereas the dirtyMask path sent to
TagAccess uses the **non-remapped raw perLaneAddr** (DCache.scala:267) — the two
paths give inconsistent results for the same input. The Lean reachability machine
proof `dcT_i28_asymmetry` pins this asymmetry down on the same actual-scale input:
the data-path mask is 0b0011 (both bytes present), while the dirtyMask keeps only
0b0010. Consequence: when the line is replaced or flushed, the mask used to write
back to L2 misses bytes — **L2 retains stale bytes: silent data loss**. The
ChiselSim reproduction hits the predicted value exactly (dirtyMask=0x212, expected
0x213).

The fix (i28 patch v2): for multiple lanes with the same blockOffset, write the
or-reduction of their wordOffset1H values, aligning with the data path's remap
semantics. The fix process itself recorded this project's first "defect in the
patch itself" case: v1's self-read-self-or formulation formed a combinational loop
and was rejected by firrtl CheckCombLoops at elaboration (see §7).

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **SIMT vector memory access and per-lane addresses**: one vector store
  instruction carries 32 lanes, each with its own byte address. On the DCache side
  each lane's address is decomposed into `(activeMask, blockOffset, wordOffset1H)`
  (L1Interfaces.scala:29-33): blockOffset indicates which 32-bit word of the
  cacheline it falls in (1 of 32); wordOffset1H is a 4-bit byte enable (SB=single
  byte, SH=two bytes, SW=four bytes). **Different lanes can fall on different
  bytes of the same word** — e.g., lane5 writes byte0 of some word while lane27
  writes byte1 (adjacent-address SB).
- **The dirtyMask array**: an SRAM inside L1TagAccess (:209-217) storing a 128-bit
  dirty bitmap per (set,way). On a write hit, "the bytes written this time" are
  **or-merged** with the array's old value and written back (:246's
  `dirtyMaskPerCL := dirtyMaskPerCL_init.asUInt | array old value`); on replacement
  (needReplace) and flush, the dirty bitmap is read out as the byte enable for the
  writeback to L2 (DCache.scala:501/:605). A dirty bitmap that comes out too small
  = writeback misses bytes = stale data in L2.
- **genDataMapSameWord (remap)**: a combinational module at DCache.scala:104-134
  that exists precisely for "multiple lanes on the same word": for each lane, it
  bitwise-OR-reduces the wordOffset1H (and data) of all active lanes sharing its
  blockOffset. The data write paths (write hit :410, write miss :375-378) both
  consume the remapped values.

### 1.2 Design Intent

On a write hit, the dirtyMask array should record "the union of all bytes written
by this request." The design intent (:219 comment) is explicit: the array update
on a hit write = old value | this write's mask. This write's mask ought to undergo
the same same-word multi-lane merging as the data path — but the implementation
omitted it.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: dirtyMaskPerCL_init is written lane-by-lane in ascending order with
overwrites** (`L1TagAccess.scala:239-245`, ★ hazard point):

```scala
val dirtyMaskPerCL_init = WireInit(VecInit(Seq.fill(dcache_BlockWords)(0.U(BytesOfWord.W))))
...
for (i <- 0 until num_lane) {
  when(io.perLaneAddr_st1(i).activeMask) {
    dirtyMaskPerCL_init(io.perLaneAddr_st1(i).blockOffset) := io.perLaneAddr_st1(i).wordOffset1H
    // ★ :243 dynamic-index overwrite write: for the same blockOffset, a later lane overwrites an earlier lane
  }
}
dirtyMaskPerCL := (dirtyMaskPerCL_init.asUInt | dirtyMaskAccess.io.r.resp.data(...))...
// :246 the or-merge with the array's old value is correct; what is wrong is that inside init, multiple lanes of the same word overwrite each other
```

The comment at source :236-238 even states WireInit's overwrite semantics itself
("every clock cycle the Wire is reset to its initial value ... condition satisfied
? new value : 0"), showing the author knew this was an overwrite assignment chain
but did not realize the same-word multi-lane case.

**Construct 2: the feed path is not remapped** (`DCache.scala:267`, ★ hazard
point):

```scala
TagAccess.io.perLaneAddr_st1 := coreReq_st1.perLaneAddr   // ★ the raw perLaneAddr
```

Compare with the data path (:353-356):

```scala
remapDataPerWord.io.perLaneAddr := coreReq_st1.perLaneAddr
coreReq_st1_PerLaneAddr_Remap := remapDataPerWord.io.perLaneAddrRemap
```

The data path consumes the remapped value (the write-hit :410's
`coreReq_st1_PerLaneAddr_Remap(...).wordOffset1H`; the write-miss :377-378's
`WordOffsetConv`), while the dirtyMask path consumes the raw value — **the two
paths are inconsistent**.

**Construct 3 (control, the correct path)**: genDataMapSameWord
(`DCache.scala:111-133`):

```scala
blockOffsetMatch(i)(j) := both-active && blockOffset equal          // :116-120
io.perLaneAddrRemap(i).wordOffset1H := wordOffsetRemap(i).reduce(_|_)  // :126 same-word or-merge
```

**Construct 4 (the legitimacy of upstream producing same-word multi-lane
patterns)**: on the LSU side, perLaneAddr is emitted directly from addresses with
no same-word merging (LSU.scala:273-279, recorded in doc/03) — an adjacent-address
SB vector store produces two active lanes with the "same blockOffset, different
bytes" pattern; this is a common memory-access form requiring no special
construction.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

For a write request containing multiple active lanes on the same word (the
write-hit path; :257-258 writes dirtyMaskPerCL back into the array):

1. Ascending-lane overwrites ⇒ dirtyMaskPerCL_init(block) keeps only the byte mask
   of the **highest lane number**;
2. The or-merge with the array's old value at :246 cannot recover the earlier
   lane's bytes (already lost inside init);
3. The dirty bit for that byte is missing in the array;
4. When the line is later replaced (needReplace; read out at :254-255 and fed via
   :605 into dirtyReplace_st1.a_mask) or flushed (:501
   InvOrFluMemReq.a_mask), the byte enable for the writeback to L2 misses that
   byte;
5. **L2 keeps the stale value for the corresponding byte, while the data itself
   has already been correctly merged and written inside L1** (the data path is
   complete) — once the L1 line is evicted, the stale byte becomes the only
   surviving copy; the data loss is established.

### 3.2 Root Cause

**Drift between two implementations of the same semantics**: the requirement
"merge multiple lanes of the same word" is correctly implemented on the data path
by genDataMapSameWord, but the dirtyMask path uses an independent construction loop
that does no merging. The two sites should have shared the same merge logic (or at
least the same remapped input); in fact they are two parallel paths that evolved
independently. The root cause belongs, together with I-12, to the type
"locally self-consistent, broken in combination": TA:241-245's overwrite write is
perfectly correct for inputs with "at most one active lane per word," while the
legitimacy of "multiple lanes on the same word" inputs is guaranteed by LSU-side
behavior — the error lies in the inconsistent implicit assumptions on the two sides
of the interface.

### 3.3 Harm and Tolerability

- **Harm**: correctness level, silent. Any vector kernel containing adjacent
  byte/halfword stores (kernels that sweep data byte by byte, such as image and
  character processing, are typical) leaves stale bytes in L2/memory when a
  cacheline is replaced or flushed. No assertion, no error.
- **Trigger surface**: write hit + multiple active lanes on the same word (on
  different bytes) + the line is later replaced or flushed. All three conditions
  are the norm.
- **Tolerability**: intolerable (the direction is data corruption). Note: the
  write-miss path's a_mask (:377-378) uses the remapped value and is unaffected;
  the defect is precisely confined to the dirtyMask array path.

---

## 4. Lean Formal Evidence

**Mechanism** (`lean/Ventus/Mem/L1TagAccess.lean` §7; `l1taDmBuild` models the
ascending-lane overwrite fold of :239-245):

- **`l1taT_dmBuild_overwrite_real`** (L1TagAccess.lean:610, native_decide): a
  witness at the **actual scale** (num_lane=32 × BlockWords=32 × 4 bytes) — lane5
  writes block3 byte0, lane27 writes block3 byte1; the result keeps only 0b0010
  (lane27's byte1); lane5's byte0 dirty bit is lost. A small-scale symbolic version
  `l1taT_dmBuild_overwrite` (:602, arbitrary off/m0/m1, m0 disappears wholesale).

**Reachability** (`lean/Ventus/Mem/DCache.lean` §3):

- **`dcT_i28_asymmetry`** (DCache.lean:484, native_decide): under the same
  actual-scale input, the data path (`dcWriteMissMaskWord`/`dcRemapMask`,
  corresponding to :377-378/:410) has mask = 0b0011 (both bytes present), while the
  dirtyMask path (`l1taDmBuild`) keeps only 0b0010 — the data/dirty-bit path
  inconsistency is pinned down inside the machine;
- The positive theorem **`dcWriteMissMask_complete`** (DCache.lean:413, for
  arbitrary lane configurations, a hand-written or-fold induction lemma, not
  enumeration): the data path's byte mask is complete for any active lanes — an
  exact contrast with the dirtyMask defect (**the data path merges correctly; the
  dirty-bit path does not merge**).

**Fixed-version verification** (`lean/VentusF/Mem.lean` §3, `fmemDmBuild` =
or-merge for the same blockOffset):

- **`fmem_i28_witness_fixed`** (VentusF/Mem.lean:383): under the original witness
  input, the fixed version's mask = 0b0011, both bytes present;
- **`fmem_i28_two_lane_merge`** (:392): the two same-word lanes' masks are
  bitwise-ORed (small-scale exhaustive enumeration);
- **`fmem_i28_step_regress`** (:402) / **`fmem_i28_regress`** (:409): when there
  are no multiple active lanes on the same word, the fixed version and the original
  agree step by step / overall (regression safety).

---

## 5. Simulation Verification

**ChiselSim module-level** (`repro/L1TagAccessDirtyMaskRepro.scala`, actually run
2026-09-06/07, doc/22; treadle backend): two lanes write adjacent bytes of the same
blockOffset; measured **dirtyMask=0x212 (expected 0x213)** — lane0's byte is
overwritten and lost by lane1, numerically matching the Lean witness
`l1taT_dmBuild_overwrite_real` exactly; the control group (different blockOffset)
passes at 0x210. Verdict: **reproduction succeeded**.

**Patch-tree regression** (actually run 2026-09-07, doc/22): the first run on the
35-patch tree triggered the i28 v1 combinational-loop incident (see §7); after the
v2 correction, **1/1 green** (0x213 achieved); L1CacheBugRepro (I-23/24/27) stays
3/3 green, and the DCache suite (DCacheBugRepro) regained elaboratable simulation.
The 38-patch merged-tree regression re-check of 2026-09-10 remains 1/1 green
(EXIT=0).

---

## 6. Upstream Impact Analysis

- **Trigger surface**: all vector byte/halfword stores going through the DCache
  (the LSU emits perLaneAddr directly, unmerged) + a subsequent replacement/flush.
  It affects the final data of L2 and global memory.
- **Why upstream did not find it**: the full chain "same-word multi-lane byte
  writes + the line being evicted later + software reading that byte back" is
  needed to observe the wrong data; upstream test kernels mostly use whole-word
  (SW) accesses, where wordOffset1H=0b1111 and same-word multi-lane overwrites lose
  no information (0b1111 overwriting 0b1111), which happens to mask the defect
  throughout.
- **Design-intent corroboration**: the comment at L1TagAccess.scala:206-207 states
  that the dirtyMask array exists precisely for the coherence of "multiple SMs
  writing to different parts of the same cacheline" — the defect occurs exactly in
  the core scenario of that design goal.

---

## 7. Fix Plan and Fix Verification

**Patch** (`i28-dirtymask-merge.patch` (internal fix manifest; not released), one edit point,
L1TagAccess.scala:243): for multiple lanes with the same blockOffset, write the
or-reduction of their wordOffset1H:

```scala
for (i <- 0 until num_lane) {
  when(io.perLaneAddr_st1(i).activeMask) {
-   dirtyMaskPerCL_init(io.perLaneAddr_st1(i).blockOffset) := io.perLaneAddr_st1(i).wordOffset1H
+   dirtyMaskPerCL_init(io.perLaneAddr_st1(i).blockOffset) := (0 until num_lane).map { j =>
+     Mux(io.perLaneAddr_st1(j).activeMask && io.perLaneAddr_st1(j).blockOffset === io.perLaneAddr_st1(i).blockOffset,
+       io.perLaneAddr_st1(j).wordOffset1H, 0.U)
+   }.reduce(_ | _)
  }
}
```

Lanes of the same group compute the same reduced value, so the multiple assignments
agree and there is no multi-driver conflict.

### 7.1 The v1 combinational-loop incident (a defect in the patch itself, as recorded in doc/22)

The i28 patch's **v1** was written as a self-read-self-or:

```scala
dirtyMaskPerCL_init(idx) := dirtyMaskPerCL_init(idx) | wordOffset1H   // v1, wrong
```

A self-read-self-or through a dynamic index forms a **combinational loop**, which
firrtl `CheckCombLoops` rejects at elaboration — L1TagAccessDirtyMaskRepro and
DCacheBugRepro were both wiped out (under v1, no design containing a DCache could
be elaborated; the earlier "whole-tree mill compile passes" covered only Scala
compilation, not elaboration — an empirical lesson that "compile-green ≠
elaborate-green"). v2 changes to the reduction formulation above: for each active
lane, the or-reduction of the wordOffset1H of all lanes in the same group is
written, **without reading back the target Wire** — no combinational loop;
semantically aligned with the data path's remapDataPerWord (DCache.scala:111-133).
The patch file was updated in sync across our internal working trees, with matching md5 (the
original file is CRLF; applying requires `patch --binary` or `git apply`).

### 7.2 Fix Verification

- Effectiveness: Lean fixed version `fmem_i28_witness_fixed` (the witness turns
  green, 0b0011) + ChiselSim patch-tree regression 1/1 green (0x213);
- Regression safety: `fmem_i28_step_regress`/`fmem_i28_regress` (with no same-word
  multi-lane, step-by-step / overall equivalence with the original) + 38-patch
  merged-tree regression with no collateral damage (doc/22);
- Elaboration verification: under v2, all DCache-related suites are elaboratable
  and simulatable (the negative control of the v1 incident).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | L1TagAccess.scala:241-245 (overwrite write) / :246 (or-merge with old value) / DCache.scala:267 (not remapped) / :104-134 (remap merge) / :410,:375-378 (the data path uses the remapped value) | Four source locations consistent |
| Lean machine-checked proof | `l1taT_dmBuild_overwrite_real` (mechanism, actual scale) + `dcT_i28_asymmetry` (reachability, data/dirty-bit asymmetry) + `dcWriteMissMask_complete` (positive: the data path is complete) | Witness + arbitrary-configuration theorem |
| ChiselSim reproduction | dirtyMask=0x212 vs expected 0x213, numerically matching the Lean witness; the control group passes | Actually run |
| Fix verification | i28 patch v2 (the v1 combinational-loop incident fixed); `fmem_i28_witness_fixed` / `fmem_i28_two_lane_merge` / `fmem_i28_step_regress` / `fmem_i28_regress` + patch-tree regression 1/1 green | Machine proof + actual run |

I-28 is a defect of the "two implementations of the same semantics drifting apart"
type: the data path implements the same-word multi-lane or-merge specifically, while
the dirty-bit path omits it. The data path writes correctly while the dirty bitmap
under-records; at replacement/flush, L2 receives a writeback with missing bytes —
correctness-level silent data loss. The fix process also contributed the process
lesson of "a patch trapping itself in a combinational loop" (compile-green ≠
elaborate-green), which has been codified into doc/22 and the patch file's header
note.
