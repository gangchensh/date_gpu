> English translation of the Chinese master `doc/bugs/I-27-满组驱逐MRU.md`. Translated 2026-09-13.

# I-27 Defect Detailed Analysis Report: DCache ReplacementUnit evicts MRU instead of LRU when the set is full

| Item | Content |
|---|---|
| ID | I-27 |
| Source location | `ventus/src/L1Cache/L1TagAccess.scala:424-428` (minIdxTree candidate assembly in reversed order), `:430` (reduceTree output indexed in the reversed coordinate), `:364` (`victimIdx := minTimeChooser.io.idxOfMin`, not mapped back to natural coordinates), `:367` (the full-set branch uses victimIdx to produce waymask); correct comparison point `:297` (the validOfSet assembly has a `Reverse`) |
| Type | Performance bug (the LRU intent is systematically inverted; no data corruption) |
| Severity | **Medium** (hot sets ping-pong-evict the just-used line, collapsing the hit rate; triggerable by any full-set allocate under the current configuration; functional correctness unaffected) |
| Confirmation status | 【Confirmed】, ChiselSim reproduction succeeded + patch-tree regression turned green |
| Main evidence | [Lean machine-checked proof] fully symbolic bv_decide theorems `l1ta_replD2_full_evicts_mru`/`l1ta_replD2_full_ne_lru` + numeric witness `l1taT_replD2_full_witness`; [simulation run] ChiselSim (L1CacheBugRepro) measured the MRU being selected on full-set replacement; [direct source reading] minIdxTree/ReplacementUnit checked line by line |
| Lean model | `lean/Ventus/Mem/L1TagAccess.lean` (§3 ReplacementUnit); fixed version `lean/VentusF/Mem.lean` (§3, `fmemReplD2`) |
| Repro/patch | `repro/L1CacheBugRepro.scala` (ChiselSim, the same suite as I-23/24/27); patch `i27-dcache-replacement-lru.patch` (internal fix manifest; not released) |
| Related entries | I-24 (the ICache version of the same kind of bit-order defect, missing a Reverse), I-29 (I-27 enlarges its trigger surface — any way can be chosen as victim), L1TagAccess note Q5 (the accessCount Counter(1000) wraparound breaks LRU ordering, note-level) |

---

## 0. Abstract

The DCache's replacement unit (ReplacementUnit) intends to implement LRU: each way
records a last-access timestamp (10 bits), and on a full set it evicts the way with
the smallest (least recently used) timestamp. But in the implementation, the
combinational unit minIdxTree that finds the minimum timestamp assembles its
candidates **in reversed order** (`candVec(i).candidate :=
io.candidateIn(numInput-1-i)`, L1TagAccess.scala:426), so its output `idxOfMin` is
an index in the **reversed coordinate**; the consumer ReplacementUnit at :364 uses
this reversed index directly as a way number, without the `way = (way-1) - idx`
mapping. The combined consequence of the two sites: on a full set the selected
victim is exactly the **complementary way** of the argmin — i.e., the way with the
largest timestamp (most recently used, MRU).

This is not an occasional deviation but a **systematic inversion**: the Lean
fully-symbolic machine proof (bv_decide, for arbitrary 10-bit timestamps) shows
that whenever the two ways' timestamps differ, the actual eviction target is
**always the opposite** of the LRU specification (`l1ta_replD2_full_ne_lru`).
ChiselSim reproduction (L1CacheBugRepro, doc/22): after filling the set, triggering
a replacement selects the MRU (waymask=0b10; the LRU way0 should have been
evicted). Patch i27 (`victimIdx := (way-1).U - idxOfMin`) is verified twice over:
by the Lean fixed-version theorems (`fmem_i27_fix_eq_lru` etc.) and by the
patch-tree regression (L1CacheBugRepro 3/3 green).

The harm is limited to performance: the victim writeback path is correct for any
legal victim, so no data corruption occurs; but hot sets repeatedly evict
just-allocated/just-hit lines, the hit rate collapses, and the trigger surface of
I-29 (victim-writeback data LFSR pollution) is enlarged.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **Set-associative cache and replacement policy**: the DCache is organized in
  sets, each with 2 ways. When a new block is filled into a full set, one old block
  must be chosen for eviction (the victim). The **LRU (least recently used)**
  policy evicts the way not accessed for the longest time, exploiting the
  program's temporal locality; if the most recently used way (MRU) is wrongly
  chosen, the just-accessed hot data is evicted immediately and the next access
  necessarily misses — in performance terms the set degenerates.
- **Timestamp implementation**: L1TagAccess uses a `Counter(accessFire, 1000)`
  (:77) to produce a monotonically increasing access count, and writes the current
  count into that way's timeAccess SRAM (:168-176) on every hit (:188-193) or
  allocation (:195-200). A larger timestamp means more recent use.
- **minIdxTree**: a combinational reduction tree that finds "the minimum value and
  its index" (:412-431); `reduceTree` compares pairwise and takes the smaller,
  outputting the winner's index.

### 1.2 Design Intent

On miss refill (allocateWrite), the ReplacementUnit looks at the set's way_valid:
for a non-full set it picks the lowest free way (the
`PriorityEncoder(~validOfSet)` of :367); for a full set it uses minIdxTree to find
the way with the smallest timestamp as the victim — i.e., LRU. With way=2 the
reduction tree degenerates to a single comparison.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: candidates assembled in reversed order** (`L1TagAccess.scala:424-428`,
inside minIdxTree, ★ hazard point one):

```scala
val candVec = Wire(Vec(numInput,new candWithIdx))
for(i <- 0 until numInput){
  candVec(i).candidate := io.candidateIn(numInput-1-i)   // ★ :426 reversed: slot i loads input numInput-1-i
  candVec(i).index := i.asUInt                           // index i is in the "reversed coordinate"
}

io.idxOfMin := candVec.reduceTree(minWithIdx(_,_)).index // :430 outputs the winner's index in the reversed coordinate
```

`candVec(0)` holds `candidateIn(way-1)` (the last way); `candVec(1)` holds
`candidateIn(0)`. `minWithIdx` (:422, takes a on strict less-than, otherwise b) with
way=2 is equivalent to "if way1's timestamp is strictly smaller than way0's, pick
slot 0, otherwise slot 1." Thus an output of 0 actually means "way1 is the minimum"
and an output of 1 actually means "way0 is the minimum" — **the coordinate system
is flipped**.

**Construct 2: the reversed index used directly as a way number**
(`L1TagAccess.scala:362-364`, ★ hazard point two):

```scala
val minTimeChooser = Module(new minIdxTree(width=timeLength,numInput=way))
minTimeChooser.io.candidateIn := timeOfSetAfterValid
victimIdx := minTimeChooser.io.idxOfMin                  // ★ :364 no (way-1)-idx mapping
```

With way=2: way0 is older (t0 < t1) → minWithIdx picks slot 1 → victimIdx=1 →
evicts **way1** (the newer one, MRU). Exactly opposite to the LRU intent.

**Construct 3: the full-set branch consumes victimIdx** (`L1TagAccess.scala:356-367`):

```scala
io.Set_is_full := io.validOfSet === Fill(way,1.U)                       // :356
...
io.waymask_st1 := UIntToOH(Mux(io.Set_is_full, victimIdx,
  PriorityEncoder(~io.validOfSet)))                                     // :367 the full set takes victimIdx
```

The non-full branch (PriorityEncoder for the lowest free way) is **correct** —
pinned down by the machine proof `l1ta_replD2_mapping`; the defect is only in the
full-set branch.

**Correct comparison point**: the same file's :297
`Replacement.io.validOfSet := Reverse(Cat(...))` explicitly performs the coordinate
correction (bit j = way j's valid); the ICache version at :496 lacks this Reverse —
that is I-24. The same file contains three Cat/Reverse bit-order sites with two
different treatments — precisely the common breeding ground of this defect family
(I-24/I-27).

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

On a full-set (`Set_is_full`) allocate:

1. timeAccess reads out the two ways' last-access timestamps (t0, t1); the larger
   is more recent;
2. minIdxTree assembles the candidates in reversed order and outputs "the index of
   the minimum-timestamp candidate in the reversed coordinate";
3. :364 does not map it back to the natural coordinate, so victimIdx points at the
   **largest-timestamp** way;
4. The MRU line is evicted: the hot line whose timestamp was just refreshed by a
   hit is thrown out.

Lean characterization (way=2, arbitrary 10-bit timestamps t0≠t1):
`l1taReplD2 0b11 t0 t1 = (if t0 < t1 then 0b10 else 0b01)` — when t0 is smaller
(way0 is older), way1 is evicted: always the MRU.

### 3.2 Root Cause

**Coordinate-system convention drift between modules**: minIdxTree's output
coordinate system (reversed) is inconsistent with ReplacementUnit's consumption
convention (natural way number). Viewed alone, minIdxTree is "self-consistent" (it
does return the argmin's index in its own coordinate system); viewed alone,
ReplacementUnit is also "self-consistent" (it takes idxOfMin as a way number). The
error is the interface-semantics mismatch. It is of the same family as I-24 (the
ICache version's validbits missing a Reverse): bit-order/coordinate-system
conventions repeatedly go wrong in this file.

### 3.3 Harm and Tolerability

- **Harm**: hot-set ping-pong — the two active blocks of the same set are
  alternately evicted (each time the just-used way is evicted); the miss rate
  approaches 100%, and fetch bandwidth and latency degrade across the board. **No
  data corruption**: the victim writeback path (dirtyReplace etc.) is correct for
  any legal victim. This is a performance bug.
- **Trigger surface**: under the current configuration (NSets=256, NWays=2) any
  full-set allocate triggers it — no special timing is needed. With num_lane=32
  vector memory accesses, full sets are the norm.
- **Amplification effect**: I-29 (victim-writeback data LFSR pollution) requires
  "the lingering write's hit way = the victim way" to trigger; this bug biases
  victim selection toward the MRU, and combined with timestamps being refreshed on
  every hit (:188-193), both the trigger surface and the frequency are amplified.
- **Tolerability**: functional correctness is unaffected; if upstream performance
  testing is not hit-rate-sensitive, it is unobservable. Rating: medium
  (performance level). When stacked with note Q5 (the accessCount Counter(1000)
  wraparound periodically inverts the timestamps' old/new order), the LRU semantics
  degrade further, but this still affects only performance.

---

## 4. Lean Formal Evidence

All in `lean/Ventus/Mem/L1TagAccess.lean` (§3), modeled specialized to way=2 (the
only actual configuration; file-header note D1):

- `l1taMinIdx2` (:190): the way=2 unfolding of minIdxTree —
  `if t1 < t0 then 0 else 1`, faithfully preserving the reversed-coordinate
  semantics;
- `l1taReplD2` (:194): modeling of the ReplacementUnit full/non-full branches;
- `l1taLruSpec2` (:229): the LRU specification (the ought-to-be) — evict the
  smallest-timestamp way, ties going to way0.

Mechanism theorems ([Lean machine-checked proof], bv_decide fully symbolic, for
arbitrary 10-bit timestamps):

- **`l1ta_replD2_full_evicts_mru`** (L1TagAccess.lean:224): on a full set, the way
  evicted is the one with the larger timestamp (MRU) —
  `l1taReplD2 0b11 t0 t1 = (if t0 < t1 then 0b10 else 0b01)` (t0≠t1);
- **`l1ta_replD2_full_ne_lru`** (:232): the actual behavior and the LRU
  specification `l1taLruSpec2` are **never equal** when t0≠t1 — a systematic
  inversion, not an occasional deviation.

Numeric witness (native_decide):

- **`l1taT_replD2_full_witness`** (:244): with (t0,t1)=(5,3), way0 (0b01) is
  evicted, while the LRU specification requires evicting way1 (0b10; 3<5 is older);
  the reverse (3,5) is likewise inverted;
- Controls `l1taT_replD2_notfull` (:238) and `l1ta_replD2_mapping` (:216): the
  non-full branch behaves correctly — the defect is precisely delimited to the
  full-set branch.

Fixed-version verification (`lean/VentusF/Mem.lean` §3, `fmemReplD2` changes
victimIdx to `(1#1) - l1taMinIdx2 t0 t1`):

- **`fmem_i27_fix_eq_lru`** (VentusF/Mem.lean:353): the fixed version's full-set
  choice **= the LRU specification** (bv_decide fully symbolic);
- **`fmem_i27_witness_gone`** (:360): under both input groups of the original
  witness, the fixed version evicts per LRU while the original evicts per MRU —
  value-by-value comparison;
- **`fmem_i27_regress`** (:368): the fixed and original versions are value-by-value
  equal on non-full sets (regression safety; the fix touches only the full-set
  branch).

The other half of fix verification, `l1ta_i24_fix_correct` (L1TagAccess.lean:326),
verifies I-24's "add a Reverse" plan (the ICache version), a different fix path
from this entry — do not confuse them.

---

## 5. Simulation Verification

**ChiselSim module-level** (`repro/L1CacheBugRepro.scala`, actually run
2026-09-06/07, doc/22; treadle backend): after filling both ways of the same set,
accessing them in a known LRU order, and then triggering an allocation, the
measurement shows the **full-set replacement selecting the MRU (waymask=0b10; the
LRU way0 should have been evicted)**. Verdict: **reproduction succeeded** (same
suite as I-23/I-24, 3/3 all reproduced).

**Patch-tree regression** (actually run 2026-09-07, doc/22): on the 35-patch tree
(including i27), L1CacheBugRepro is **3/3 green**; the 38-patch merged-tree
regression re-check of 2026-09-10 remains green (EXIT=0).

There is no Verilator whole-machine-level case (a performance bug is not suited to
a whole-machine witness; the mechanism is already closed by the ChiselSim
module-level test + the Lean fully-symbolic theorems).

---

## 6. Upstream Impact Analysis

- **Trigger surface**: the sole instantiation point DCache.scala:184 (NSets=256,
  NWays=2); any kernel whose working set fills some set enters "evict MRU" mode.
  The ICache uses an independent ReplacementUnit_ICache (:510-522, round-robin),
  which does not go through minIdxTree and is unaffected by this entry (its
  bit-order defect is I-24).
- **Why upstream did not find it**: a pure performance defect with all functional
  tests green; no upstream benchmark report targeting the L1 DCache hit rate has
  been seen. It falls in a "test-coverage blind spot."
- **Relationship with I-24**: same root (bit-order convention), different fruit —
  I-24 degenerates the ICache to direct-mapped (way1 permanently invalid), while
  this entry inverts the DCache's full-set eviction. The two fixes do not cover
  each other; both the i24 and i27 patches have entered the tree.

---

## 7. Fix Plan and Fix Verification

**Patch** (`i27-dcache-replacement-lru.patch` (internal fix manifest; not released), one edit
point):

```scala
// L1TagAccess.scala:364
-    victimIdx := minTimeChooser.io.idxOfMin
+    // I-27 fix: minIdxTree's candidates are assembled in the reversed coordinate (candidateIn(numInput-1-i)),
+    // so idxOfMin is in the reversed coordinate and must be mapped back to natural order — otherwise a full set evicts MRU instead of LRU.
+    victimIdx := (way-1).U - minTimeChooser.io.idxOfMin
```

(The alternative "remove the reversed assembly from minIdxTree" was not adopted —
keeping the minIdxTree interface unchanged and mapping at the consumption point
minimizes the change surface.)

**Fix verification triad**:

- Effectiveness: Lean fixed version `fmem_i27_fix_eq_lru` (fixed version ≡ LRU
  specification, fully symbolic) + `fmem_i27_witness_gone` (the original witness
  turns green); ChiselSim patch-tree regression 3/3 green;
- Regression safety: `fmem_i27_regress` (value-by-value equivalence on non-full
  sets) + 38-patch merged-tree regression with no collateral damage (doc/22,
  2026-09-10);
- Note: the timestamp Counter(1000) wraparound (Q5) is an independent note-level
  performance issue and is outside this patch's scope.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | L1TagAccess.scala:424-428 / :430 / :364 / :367, checked line by line against :297 | Both hazard points consistent |
| Lean machine-checked proof | `l1ta_replD2_full_evicts_mru` / `l1ta_replD2_full_ne_lru` (bv_decide fully symbolic) + `l1taT_replD2_full_witness` (numeric) | Fully symbolic + witness |
| ChiselSim reproduction | Full-set replacement selects the MRU (waymask=0b10; way0 should have been evicted) | Actually run |
| Fix verification | i27 patch (1 edit point); `fmem_i27_fix_eq_lru` / `fmem_i27_witness_gone` / `fmem_i27_regress` + patch-tree regression 3/3 green | Machine proof + actual run |

I-27 is the DCache-side instance of the "coordinate-system convention drift"
defect family: minIdxTree's reversed output is consumed by ReplacementUnit in
natural order, systematically inverting full-set eviction (LRU→MRU).
Performance-level harm, with the evidence chain (fully-symbolic machine proof +
module-level reproduction + fix regression) fully closed.
