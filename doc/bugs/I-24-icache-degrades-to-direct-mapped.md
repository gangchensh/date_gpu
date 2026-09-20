> English translation of the Chinese master `doc/bugs/I-24-ICache退化直接映射.md`. Translated 2026-09-13.

# I-24 Detailed Defect Analysis Report: ICache ReplacementUnit Input Missing a Reverse — Two-Way Set-Associative Degrades to Direct-Mapped

| Item | Content |
|---|---|
| ID | I-24 |
| Source location | `ventus/src/L1Cache/L1TagAccess.scala:496` (the ICache version's `Replacement.io.validbits_of_set := Cat(way_valid(...))` lacks a `Reverse`); the consuming site `ReplacementUnit_ICache` `:517-518` (`indexWhere` scans from bit0); compare `L1TagAccess.scala:297` (the DCache version has `Reverse`, correct) |
| Type | Performance bug (functional correctness is not impaired — the ICache is read-only; the hit rate collapses) |
| Severity | **Medium**: the two-way set-associative cache de facto degrades to direct-mapped; two blocks in the same set ping-pong with guaranteed misses, degrading fetch performance; no data errors |
| Confirmation status | 【Confirmed】 — ChiselSim reproduction successful (doc/22) + the fix turns green in patch-tree regression |
| Main evidence | 【Lean machine-checked proof】 symbolic mis-selection theorem + an invariant over arbitrary inputs (way1 always invalid) + a ping-pong witness + an independent re-proof chain on the L1TagAccess side; 【simulation runs】 ChiselSim reproduction successful; 【direct source reading】 line-by-line comparison of the ICache/DCache versions of the ReplacementUnit input |
| Lean model | `lean/Ventus/Mem/ICache.lean` (`icVictimMask_*`/`ic_way1_never_valid`/`icTD_victim_thrash`); `lean/Ventus/Mem/L1TagAccess.lean` (independent re-proof `l1ta_i24_*`); fixed version `lean/VentusF/Mem.lean` |
| Reproduction/patch | `repro/L1CacheBugRepro.scala` (the I-24 case, ChiselSim); patch `i24-icache-replacement-reverse.patch` (internal fix manifest; not released) |
| Related entries | I-27 (the coordinate reversal of the DCache version's ReplacementUnit — another kind of bit-order error in the same file), I-23 (same module) |

---

## 0. Summary

When L1TagAccess_ICache feeds the way_valid register array into ReplacementUnit_ICache it writes
`Cat(way_valid(...))` (L1TagAccess.scala:496), whereas the DCache version of the same action writes
`Reverse(Cat(...))` (:297). Chisel's `Cat` places the first element at the MSB: with way=2,
bit0 of `Cat(way_valid)` is **way1**'s valid bit; while ReplacementUnit_ICache's
free-way search `indexWhere(_===false.B)` scans from bit0. The result of the bit-order mismatch: when
way0 is occupied and way1 is free, the victim still selects the occupied **way0** — the second block of a set
always evicts the first, and **way1 is always invalid**.

Consequence: the ICache's two-way set associativity de facto degrades to direct-mapped (each set's effective capacity is constantly 1); alternating fetches of two
blocks in the same set miss every time (ping-pong thrash). On the Lean side this is nailed down with three layers of evidence: the symbolic mis-selection
theorem (`icVictimMask_way0_valid_only`), an invariant over arbitrary input sequences
(`ic_way1_never_valid`: way1 is never valid, starting from reset), and an 8-cycle thrash witness
(`icTD_victim_thrash`); L1TagAccess.lean additionally has an independent re-proof chain (`l1ta_i24_*`).
The ChiselSim reproduction succeeded (the second allocation in the same set has waymask=0b01, should be 0b10); the i24 patch
(adding `Reverse`) was verified green both by the fixed-version theorems and by patch-tree regression.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **Set-associative caches and victim selection**: each set of an N-way set-associative cache has N ways. When a new block
  is installed, a free way is chosen first; when the set is full, a victim is chosen by the replacement policy (this design uses round-robin
  victim for full sets). Two-way (N=2) is the smallest scale — precisely the scale
  at which "choosing the wrong way" is most directly exposed as direct-mapped behavior.
- **The way_valid array**: one valid bit per set per way (`RegInit` all zeros). The ReplacementUnit's
  input `validbits_of_set` is exactly the current set's way-valid-bit vector.
- **The bit order of Chisel's `Cat` and `Reverse`**: `Cat(a, b)` places `a` in the high bits —
  `Cat(way_valid(s))` (where `way_valid(s)` is a `Vec(way0, way1)`) yields bit1=way0,
  bit0=way1. The `indexWhere` / `PriorityEncoder` family scans from **bit0 (the least significant bit)**.
  To make "the j-th bit found by the scan" correspond to "way j", a `Reverse` is required first.
- **`indexWhere(_===false.B)`**: finds the index of the first free way; `UIntToOH` converts it to a one-hot
  waymask for the SRAMTemplate write port.

### 1.2 Design Intent

For a non-full set: install into the first free way; for a full set: use the round-robin victim. The DCache version (:297)'s
`Reverse(Cat(...))` is exactly the correct bit-order alignment — the ICache version (:496) omits the
`Reverse`.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the ICache version's input lacks Reverse** (`L1TagAccess.scala:496`, ★ fault point):

```scala
Replacement.io.validbits_of_set := Cat(way_valid(io.w.req.bits.setIdx))
```

**Control: the DCache version of the same action has Reverse** (`L1TagAccess.scala:297`):

```scala
Replacement.io.validOfSet := Reverse(Cat(way_valid(allocateWrite_st1.setIdx)))
```

Two versions coexist in the same file; the bit-order difference is visible at a glance.

**Construct 2: the selection logic of ReplacementUnit_ICache** (`L1TagAccess.scala:517-518`):

```scala
io.Set_is_full := io.validbits_of_set === Fill(way,1.U)
io.waymask := Mux(io.Set_is_full, victim_1Hidx,
  UIntToOH(VecInit(io.validbits_of_set.asBools).indexWhere(_===false.B)))
```

`indexWhere` scans from bit0 for the first 0 (a free bit).

**Bit-order mismatch analysis** (way=2): when way0 is occupied and way1 is free, `Cat(way_valid(s))` yields
bit1=1 (way0), bit0=0 (way1). `indexWhere(_===false)` scans from bit0, hits
bit0 → `UIntToOH(0) = 0b01` → the waymask selects **way0** (the occupied one). The correct behavior would select
way1 (waymask=0b10).

**Construct 3: the full-set branch never activates**: way1 is always invalid ⇒ `Set_is_full` (which requires both ways to be 1)
is always false ⇒ the round-robin victim (`victim_1Hidx`) is dead logic — each set's effective capacity is constantly 1.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

- The first block of a set is installed into way0 (for an empty set, indexWhere hits bit0 = way1's free bit……
  note that for an empty set both ways are free, bit0=0 selects way0 — which happens to be correct;
  `icVictimMask_empty` pins down this boundary);
- The second block of the same set arrives: way0 occupied / way1 free ⇒ way0 is wrongly selected ⇒ **the second block evicts the first**,
  and way1 can never be installed into;
- From then on, that set has only way0 rotating: alternating accesses to two blocks = a guaranteed miss every time
  (ping-pong thrash).

### 3.2 Root Cause

An asymmetric bit-order convention: between the producing side's `Cat` (first element at the MSB) and the consuming side's `indexWhere` (scanning from
bit0 / the least significant bit), one `Reverse` alignment is needed, and the ICache version omitted it. The
DCache version in the same file got it right — a typical "one edit missed after copy-paste".

### 3.3 Harm and Tolerability

- **Harm**: purely performance. The ICache is read-only; what gets evicted are instruction blocks, which can simply be re-fetched — no data-correctness
  issue; but the degradation from two-way to direct-mapped causes a structural hit-rate drop (any spatial locality slightly worse than perfect
  in the instruction stream causes thrash).
- **Tolerability**: functionally tolerable (correctness unaffected), performance-wise unacceptable (half the
  ICache silicon area wasted). Rating: **Medium**.
- **Delimitation**: the bug appears only in the "half-full with way1 free" case — an empty set correctly selects way0
  (`icVictimMask_empty`), and a full set takes the round-robin path (`icVictimMask_full`, and a full set is in fact
  unreachable).

---

## 4. Lean Formal Evidence

**Main evidence** (`lean/Ventus/Mem/ICache.lean`):

- `icVictimMask_way0_valid_only` (:1079, fully proved symbolically): with wayValid=0b01 (way0 occupied,
  way1 free), `icVictimMask` still returns 0b01 (selecting way0) — the mis-selection is nailed down, over arbitrary states;
- Boundary delimitation: `icVictimMask_empty` (:1068, an empty set selects way0 — correct),
  `icVictimMask_full` (:1073, a full set takes the round-robin victim — correct);
- `icTD_victim_thrash` (:1548, native_decide, an 8-cycle witness): two blocks of the same set
  are cleanly refilled in sequence; the second block overwrites way0, way1 stays empty forever, and re-fetching the first block is a guaranteed miss —
  the ping-pong guaranteed-miss behavior is established;
- **`ic_way1_never_valid`** (:1557, fully proved by invariant induction): the invariant
  `icTagInv` = (for every set, wayValid ∈ {00, 01}, i.e., way1 is always invalid) ∧ the victim
  is constantly 0b01, is preserved by induction over **arbitrary input sequences** (`induction` + the preservation lemma
  `icTagStep_preserves_inv`, :1124). This is the strongest evidence level: starting from reset, over arbitrarily many cycles and
  arbitrary inputs, the ICache de facto degrades to direct-mapped.

**Independent re-proof chain** (`lean/Ventus/Mem/L1TagAccess.lean`, modeling the bit order directly):

- `l1ta_i24_mapping` (:271): the selection looks only at bit0 (= way1's valid bit);
- `l1ta_i24_way0_occupied` (:278): the mis-selection in the way0-occupied case is nailed down;
- `l1ta_i24_way1_never_valid` (:297): the invariant that way1 is always invalid;
- `l1taT_two_refill_contrast` (:321): a two-refill contrast witness;
- `l1ta_i24_fix_correct` (:326): the selection is correct after adding `Reverse` (a formal
  pre-verification of the fix).

**Fixed-version verification** (`lean/VentusF/Mem.lean`): `fmem_i24_victim_correct` (:202),
`fmem_i24_way1_reachable` (:286, way1 reachable after the fix), `fmem_i24_way1_used`
(:302, way1 actually installed into), `fmem_i24_regress` (:209)/
`fmem_i24_regress_state` (:218)/`fmem_i24_tagStep_regress` (:224, regression equivalence
outside the trigger domain).

---

## 5. Simulation Verification (ChiselSim Measurement + Patch-Tree Regression)

**ChiselSim module-level** (`repro/L1CacheBugRepro.scala`, the I-24 case, actually run 2026-09-06/07,
doc/22): two addresses in the same set miss and refill in sequence; observe the waymask of the second allocation.
Measured: **the second allocation in the same set has waymask=0b01 (should be 0b10)** — way1 never takes effect; the two-way set-associative
cache degrades to direct-mapped. Verdict: **reproduction successful**.

**Patch-tree regression** (doc/22, two actual runs: the 35-patch tree 2026-09-07 and the 38-patch merged tree 2026-09-10):
L1CacheBugRepro (the three cases I-23/24/27) **3/3 green** — after the i24 fix, the second
allocation correctly selects way1.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: any second-block installation into an ICache set — i.e., all kernels whose "fetch footprint exceeds the direct-mapped
  capacity". The trigger is structural; no special timing is needed.
- **Why upstream did not find it**: functionality is completely correct (read-only cache + the warp-replay protocol as a safety net); it only manifests
  as a low hit rate; upstream tests are mainly functional-verdict-based, with no ICache hit-rate regression.
- **Same-family entry**: I-27 (the DCache version's ReplacementUnit evicting the MRU on a full set) is the same file, the same
  class of "bit-order / coordinate-system" error — the minIdxTree candidates assembled in reversed order without being mapped back. The two entries corroborate each other:
  this file's bit-order conventions are a systematic error-prone point.

---

## 7. Fix and Fix Verification

**Patch** (`i24-icache-replacement-reverse.patch` (internal fix manifest; not released),
single edit point):

```scala
// L1TagAccess.scala:496
-  Replacement.io.validbits_of_set := Cat(way_valid(io.w.req.bits.setIdx))
+  // I-24 fix: add Reverse (aligning with the DCache version at :297) — otherwise bit0=way1,
+  // and ReplacementUnit_ICache's indexWhere, scanning from bit0, mis-selects way0,
+  // degrading the two-way set-associative cache to direct-mapped (way1 always empty).
+  Replacement.io.validbits_of_set := Reverse(Cat(way_valid(io.w.req.bits.setIdx)))
```

the internal fix manifest classification: Functional fix (required), performance level ("No (performance
only)" — no wrong results are produced).

**Fix-verification trio**:

- Effectiveness: `l1ta_i24_fix_correct` (the post-fix selection logic is correct, symbolic level) +
  `fmem_i24_way1_reachable`/`fmem_i24_way1_used` (way1 reachable and actually used);
- Regression safety: `fmem_i24_regress`/`fmem_i24_regress_state`/
  `fmem_i24_tagStep_regress` (step-by-step equivalence outside the trigger domain);
- RTL level: patch-tree regression L1CacheBugRepro 3/3 green ×2 rounds (the 35-patch tree and the 38-patch merged tree).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | L1TagAccess.scala:496 (missing Reverse) vs :297 (the DCache version has it); ReplacementUnit_ICache :517-518 (indexWhere scans from bit0) | Line-by-line comparison of the two versions |
| Lean machine-checked proof | `icVictimMask_way0_valid_only` (symbolic mis-selection) + `icVictimMask_empty`/`icVictimMask_full` (boundary delimitation) + `ic_way1_never_valid` (invariant over arbitrary inputs: way1 always invalid) + `icTD_victim_thrash` (thrash witness); independent re-proof `l1ta_i24_mapping`/`l1ta_i24_way0_occupied`/`l1ta_i24_way1_never_valid`/`l1taT_two_refill_contrast` | Invariant level (arbitrary inputs, arbitrary cycles) |
| ChiselSim reproduction | the second allocation in the same set has waymask=0b01 (should be 0b10); way1 never takes effect | Measured |
| Fix verification | i24 patch (1 edit point); `l1ta_i24_fix_correct` + five `fmem_i24_*` theorems + patch-tree regression 3/3 green ×2 rounds | Machine-checked + measured |

I-24 is a structural performance defect caused by a one-line bit-order omission (`Reverse`): the evidence reaches the invariant level of "way1
is always invalid under arbitrary input sequences", making it a model example of the "one edit missed after copy-paste" class of defects,
and together with I-27 it exposes the systematic error-proneness of L1TagAccess.scala's bit-order conventions.
