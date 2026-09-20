> English translation of the Chinese master `doc/bugs/I-29-victim写回LFSR污染.md`. Translated 2026-09-13.

# I-29 Detailed Defect Analysis Report: DCache victim writeback data can be polluted by SRAM LFSR random values

| Item | Content |
|---|---|
| ID | I-29 |
| Source location | `ventus/src/L1Cache/DCache/DCache.scala:623` (`probereadAllocateWriteConflict` only blocks a `coreReq.fire` on the **same cycle** as allocateWrite); `:445` (the st1 hit-branch ready contains `!(missRspOut.valid && !secondaryFullReturn)` — the source of stranding); collision site `:646-648` (writeHit_st1 write port) × `:579-583` (dataReplaceReadValid read port) on the same cycle and same (set,way); data landing point `:764` (`dirtyReplace_st1.a_data := DataAccessReadSRAMRRsp`) → `:786` (MemReqArb.in(0) → victim writeback to L2); SRAM instantiation `:637-659` (bypassWrite=false) |
| Type | Functional bug (silent data corruption: victim writeback data to L2 polluted with garbage) |
| Severity | **High (mechanism-level)**: if triggered, silent data corruption; however neither simulation track observed LFSR pollution (see §5), leaving residual doubt about observability |
| Confirmation status | 【Confirmed】 (mechanism, machine-checked Lean proof closed); **not reproduced in simulation (residual doubt)** — doc/22 ruled "the Lean-side mechanism proof is authoritative" |
| Primary evidence | 【Machine-checked Lean proof】 `dc_fire_excludes_allocWrite` (precise characterization of the sole interlock's coverage) + `dcT_w1_collision_reachable` (three-cycle reachable witness) + `dcT_w1_sram_lfsr` (read-out = LFSR value 0x43B2A190, connected to `sram_lfsr_bypass`); 【simulation runs】 ChiselSim (Verilator backend) on both trees: LFSR pollution not observed; 【direct source reading】 line-by-line verification of the above line numbers |
| Lean model | `lean/Ventus/Mem/DCache.lean` (§5 sequential core `dcCollision` + §6 witness); conflicting read-out semantics connected to `sram_lfsr_bypass` in `lean/Ventus/Mem/SRAMTemplate.lean`; fixed version `lean/VentusF/Mem.lean` (§4, `fmemDcSt1Ready` guard) |
| Reproduction/patch | `repro/DCacheBugRepro.scala` (ChiselSim, Verilator backend); patch `i29-dcache-victim-read-guard.patch` (internal fix manifest; not released) |
| Related entries | I-23 (same-family LFSR pollution in ICache, reproduced), I-40 (same family in L2 BankedStore), I-27 (full-set eviction inversion widens this entry's trigger surface), SRAMTemplate note (bypassWrite=false same-cycle same-address read-write returns LFSR64 — X-propagation semantics) |

---

## 0. Summary

The DCache data SRAM (32 banks, each `SRAMTemplate(UInt(8), set=512, way=4)`,
:637-659) is instantiated with bypassWrite=false — **on a same-cycle same-address
read-write pair, the read port returns an LFSR64 pseudo-random value rather than
the old or new value** (SRAMTemplate's X-propagation convention; this project's
SRAMTemplate.lean has pinned this semantics down with `sram_lfsr_bypass`).

The DCache's only interlock against such conflicts is
`probereadAllocateWriteConflict` (:623), which only blocks a `coreReq.fire` on the
**same cycle** as allocateWrite (tag allocation for miss refill). But a write
request may have **already entered st1 on the previous cycle** and become stranded
because missRspOut occupies the response channel (the
`!(missRspOut.valid && !secondaryFullReturn)` term at :445), launching its SRAM
write port on the cycle **after** allocateWrite — exactly colliding, on the same
cycle and same (set,way), with the victim eviction read triggered by memRsp
(dataReplaceReadValid at :579-583). The SRAM reads out LFSR garbage, which is
loaded into `dirtyReplace_st1.a_data` at :764 and sent to L2 as the victim's
**writeback data** — silent data corruption.

Same family as I-23 (ICache LFSR), but here what is corrupted is **writeback
data** (I-23 is fetch-side read data). I-27 (full-set eviction MRU) widens this
entry's trigger surface: victim selection is biased toward the most recently used
way, increasing the probability of overlap with the way hit by the stranded write.

The simulation status must be recorded faithfully: under two rounds of
orchestration on ChiselSim (Verilator backend), **neither tree (baseline nor
patched) showed LFSR pollution** — the collision configuration genuinely occurred
on baseline (victim=A), but the writeback data was the store's new value rather
than an LFSR value; doc/22 maintains the "not reproduced (residual doubt)"
verdict, with conclusions based on the Lean mechanism proof (see §5).

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **DCache two-stage pipeline**: coreReq enters st1 via coreReq_Q (hit
  determination in st1 is provided by L1TagAccess); when st1 completes (fires), it
  launches the SRAM read/write. The st1 launch condition (coreReq_st1_ready,
  :442-478) includes "the response channel is not occupied by missRspOut" — while
  occupied, the request **stays stranded in st1** (does not fire, does not leave),
  and launches once the channel frees up.
- **Miss refill and victim eviction**: when memRsp (read-data return) arrives it
  triggers allocateWrite (tag allocation, :620); if the replaced victim line is
  dirty (needReplace), on the next cycle a **dataReplaceReadValid read** is issued
  against the data SRAM (:579-583), and the read-out victim data is sent via
  dirtyReplace_st1/st2 to L2 for writeback.
- **SRAMTemplate bypassWrite semantics**: when a dual-port SRAM is instantiated
  with bypassWrite=false, the read-out value of a same-cycle same-address
  read-write pair is **undefined** — the model implementation chooses to output an
  LFSR64 pseudo-random value (the X-propagation convention, used to expose
  unhandled conflicts in simulation; after synthesis it is real but unpredictable
  logic). This project's SRAMTemplate.lean pins this semantics down as the theorem
  `sram_lfsr_bypass`.

### 1.2 Design intent

Every "write port and read port on the same cycle and same address" combination
must be excluded by the control logic. `probereadAllocateWriteConflict` (:623,
feeding into coreReq.ready at :218) is exactly that interlock: a new coreReq must
not enter on the same cycle as allocateWrite. The designer's field of view covered
only the "new request" entry point and missed the "request already stranded in
st1" path.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the only interlock covers only same-cycle new requests**
(`DCache.scala:623` + `:218`, ★ trouble spot):

```scala
probereadAllocateWriteConflict := io.coreReq.valid && TagAccess.io.allocateWrite.valid
// :623 —— only blocks "coreReq.valid on the same cycle as allocateWrite.valid"
...
io.coreReq.ready := coreReq_Q.io.enq.ready && !probereadAllocateWriteConflict && ...
// :218 —— the interlock acts at the moment of "entry"; it has no force on requests already in st1
```

**Construct 2: the st1 stranding mechanism** (`DCache.scala:445`):

```scala
when(TagAccess.io.hit_st1) {
  when(coreRsp_st2.io.enq.ready && coreRsp_st2_valid_from_coreReq_Reg.io.enq.ready
       && !(MshrAccess.io.missRspOut.valid && !secondaryFullReturn)) {  // ★ source of stranding
    coreReq_st1_ready := true.B
  }
}
```

When missRspOut occupies the response channel (and the secondaryFullReturn
exception does not apply), a hit write request stays in st1 without firing.

**Construct 3: the victim eviction read port** (`DCache.scala:579-583`):

```scala
val dataReplaceReadValid = RegNext(TagAccess.io.allocateWrite.valid, false.B) &&
  tagReplaceStatus === false.B && TagAccess.io.needReplace.get
DataAccessReplaceReadSRAMRReq.foreach(_.setIdx :=
  Cat(missRspSetIdx_st1, OHToUInt(TagAccess.io.waymaskReplacement_st1)))
```

On the cycle after allocateWrite, a data SRAM read is issued against the victim
(set,way).

**Construct 4: the write-hit write port and the read-out landing point**
(`DCache.scala:646-649`, `:764`):

```scala
DataAccess.io.w.req.valid := Mux(dataFillVaild, true.B,
  writeHit_st1 & getBankEn.io.perBankValid(i))      // :646-648 write port (when the stranded write launches)
...
dirtyReplace_st1.a_data := DataAccessReadSRAMRRsp   // :764 —— read port output directly becomes victim writeback data
```

The conflict occurs when the write port address
`Cat(coreReq_st1.setIdx, OHToUInt(waymaskHit_st1))` (same style as :408/:416)
shares the same (set,way) as the read port address; the read-out value one cycle
later becomes the victim's a_data and is written back to L2 via MemReqArb.in(0)
(:785-786).

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

Trigger sequence (Lean witness dcW1, three cycles, reachability machine-checked by
native_decide):

1. **T0**: a write request (isWrite, set5, hitting way0) fires into st1 (no
   allocateWrite that cycle; all terms of :218 hold);
2. **T1**: missRspOut occupies the response channel → the write request is
   **stranded in st1**; on the same cycle memRsp arrives → allocateWrite.valid=1
   (RegNext plants prevAllocWriteV);
3. **T2**: missRspOut departs → the write hit is released (writeHit_st1=1, write
   port launches); on the same cycle needReplace=1 → dataReplaceReadValid=1, the
   victim read port launches. The two ports hit the same (set5, way0) on the same
   cycle — **SRAM same-address read-write conflict**;
4. **T3**: the read port output = LFSR value (`dcT_w1_sram_lfsr`: 0x43B2A190,
   neither the written value 0xAAAA0000 nor the original value) →
   `dirtyReplace_st1.a_data` → the victim's writeback data to L2 is polluted with
   garbage. The write itself still takes effect (data inside L1 is correct), but
   what is written back to L2 is garbage — the L2 copy of the victim block is
   corrupted.

### 3.2 Root cause

**Incomplete field of view of the interlock**: the conflict-prevention logic
considers only the "entry moment" (a new coreReq on the same cycle as
allocateWrite) and does not account for the cycle offset introduced by st1
stranding — stranding slides the write request's SRAM write port from "entry
cycle + 1" to an arbitrarily later cycle, where it can exactly collide with the
victim read on the cycle after allocateWrite. This is the classic "interlock
designed around events, accident caused by timing": two individually legal events
(stranding, eviction read) can superpose in time into a conflict.

### 3.3 Impact and tolerability

- **Impact**: when replacing a dirty line, L2 receives random data — silent data
  corruption, with no assertion to catch it. The direction is correctness-level:
  the contents of that block in L2 (and memory beyond) are no longer the true data
  at any point in time.
- **Trigger conditions**: a hit write stranded in st1 (missRspOut occupying the
  channel) + an allocateWrite in the same window with a dirty victim + the
  write-hit way = the victim way + same set. The condition chain is long, but
  every link is a routine event; I-27 biases the victim toward the most recently
  used way, and the stranded write hits exactly a hot way, amplifying the overlap
  probability.
- **Tolerability**: the mechanism holds (machine-checked in Lean), but
  **simulation observability is in doubt** (§5: two orchestration rounds on the
  Verilator backend did not observe LFSR pollution) — if real silicon/other
  simulators likewise do not exhibit random read-out for SRAM (e.g. read-out =
  the newly written value; read-during-write behavior varies by process/macro
  cell), the actual impact shape changes accordingly. The rating stays high
  (mechanism-level); the degree to which the impact materializes depends on the
  process library's SRAM behavior.

---

## 4. Lean Formal Evidence

All in `lean/Ventus/Mem/DCache.lean` (§5/§6; conflicting read-out semantics
connected to SRAMTemplate.lean):

- **`dc_fire_excludes_allocWrite`** (DCache.lean:927, full enumeration of 10
  Bools, native_decide): the only same-cycle mutual exclusion at :218/:623 —
  `coreReq.fire` and `allocateWrite.valid` cannot occur on the same cycle. **But**
  this imposes no constraint whatsoever on "write requests already stranded in
  st1"; this theorem is simultaneously a precise characterization of the
  interlock's coverage (the gap lies exactly outside it);
- **`dcT_w1_collision_reachable`** (:979, three-cycle trace native_decide
  witness): the same-cycle same-(set,way) collision of stranded write × eviction
  read is **reachable** in time — at the end of T1 the write request is stranded
  in st1 (`dcW1S2.st1 = some dcW1Req`) and prevAllocWriteV=1; under the T2 input,
  `dcCollision` (:823, write hit ∧ dataReplaceReadValid ∧ same setIdx ∧
  waymaskHit=waymaskRepl) = true;
- **`dcT_w1_sram_lfsr`** (:992, native_decide): connects to the SRAMTemplate model
  (`sramCfgDCacheData` = bypassWrite=false configuration, :637-659) and pins down
  the consequence — the same-address read-write cycle outputs the LFSR value
  0x43B2A190 (neither the written value nor the original value), while the write
  itself takes effect. The mechanism theorem is `sram_lfsr_bypass` in
  SRAMTemplate.lean (:543).

**Fixed-version verification** (`lean/VentusF/Mem.lean` §4, where
`fmemDcSt1Ready` adds a "no in-flight victim read" guard to the hit branch):

- **`fmem_i29_guard`** (VentusF/Mem.lean:538, symbolic): st1-stranded write + hit
  + in-flight victim read ⇒ the fixed version does not release (the original has
  ready=true in this situation);
- **`fmem_i29_collision_blocked`** (:550, replay of the original dcW1 trace): the
  write is held, the victim read proceeds normally, and **the collision does not
  occur**;
- **`fmem_i29_write_proceeds`** (:563, liveness): after the victim-read window
  passes, the stranded write is released normally — the guard introduces no
  deadlock;
- **`fmem_i29_ready_regress`** (:568): with no in-flight victim read, the fixed
  version's ready agrees with the original (regression-safe).

---

## 5. Simulation Verification (not reproduced — recorded faithfully)

**ChiselSim track** (`repro/DCacheBugRepro.scala`, actually run 2026-09-06/07,
doc/22; **Verilator 5.020 backend** — under treadle, dirtyMaskAccess's 256-entry
reset clearing back-pressures coreReq.ready for about 256 cycles and the test
precondition fails, so the whole DCache suite runs on the Verilator backend):

- **First round**: verdict **not reproduced** — under the current timing
  orchestration, victim(B)'s writeback data ∈ {0xBBBB2222, 0xDDDD4444}, no LFSR
  pollution observed; the collision cycle order of stranded-store × allocateWrite
  needs recalibration against actual Verilator timing (residual doubt).
- **After dedicated calibration on the patched tree** (doc/22 "I-29/I-30 special
  session"): with the test stub fixed and calibration done, both trees pass but
  with different semantics — **on baseline the collision genuinely occurs**
  (victim=A=the store line, addr=0x8000), but the writeback data is the **store's
  new value 0xDDDD4444** (Verilator's SRAM same-cycle read-write does not exhibit
  LFSR pollution); on the patched tree victim=B (way1), no collision, clean data
  0xBBBB2222.
- **38-patch merged tree** (2026-09-10, doc/22): the I-29 test case was re-aimed
  (touch-A removed, expecting victim=A addr=0x8000 data=0xAAAA1111) — actual
  measurement found that after the i27 fix, the LRU dynamics (hit updates
  accessCount, L1TagAccess.scala:188-193) make the way hit by the stranded write
  always the MRU, so the "stranded write and victim read on the same way"
  collision configuration is **structurally unreachable** under this
  orchestration, and the i29 guard eliminates the residual timing window; the test
  case degenerates into a clean-writeback regression, re-run 2/2 green.

**Conclusion (doc/22 ruling, verbatim)**: **maintain "not reproduced (residual
doubt)"** — LFSR pollution was not observed on either tree under the Verilator
backend; the Lean-side mechanism proof (the `dcT_w1_*` chain +
`sram_lfsr_bypass`) is authoritative. Two candidate explanations for the residual
doubt: (a) Verilator's evaluation behavior of the $random branch for
read-during-write in the generated code differs from the model assumption; (b) the
collision cycle order is still not precisely aligned. Distinguishing them requires
waveform-level debugging or a different simulator (e.g. VCS/xrun or a timing-aware
FPGA prototype), which this environment does not have.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: the window in which a hit write runs concurrently with
  miss-refill eviction. When vector kernels have high miss rates
  (missRspOut/allocateWrite frequent), the window appears more often; the presence
  of I-27 biases the victim toward hot ways, amplifying it further.
- **Why upstream did not find it**: twofold — (a) the conflict window is narrow
  and depends on specific timing superposition; (b) even when hit, the read-out
  behavior of SRAM same-address read-write in a simulator may not exhibit random
  values (empirical evidence from this reproduction attempt), and behavior on
  silicon in turn depends on the SRAM macro cell — a deep-water defect of the
  "behaves differently across simulators/processes" kind, exactly where the value
  of a formal mechanism proof lies.
- **Same family**: I-23 (ICache probe×refill, reproduced in ChiselSim), I-40 (L2
  BankedStore) — the X-propagation semantics of SRAMTemplate bypassWrite=false is
  being checked off one by one at all four instantiation points in the design;
  this entry is the DCache data array one.

---

## 7. Fix Plan and Fix Verification

**Patch** (`i29-dcache-victim-read-guard.patch` (internal fix manifest; not released), one edit
point, adding a guard to the hit-branch ready at DCache.scala:445):

```scala
-      when(coreRsp_st2.io.enq.ready && coreRsp_st2_valid_from_coreReq_Reg.io.enq.ready && !(MshrAccess.io.missRspOut.valid && !secondaryFullReturn)) {
+      // I-29 fix: an st1-stranded write (not launched because missRspOut occupies
+      // the response channel) that launches on the cycle after allocateWrite
+      // collides on the same SRAM row (bypassWrite=false) with the victim read of
+      // dataReplaceReadValid → the victim writeback data to L2 is polluted by
+      // LFSR. Add a "no in-flight victim read" guard to the release of hit writes.
+      when(coreRsp_st2.io.enq.ready && coreRsp_st2_valid_from_coreReq_Reg.io.enq.ready && !(MshrAccess.io.missRspOut.valid && !secondaryFullReturn) &&
+        !(coreReqControl_st1_Q.io.deq.bits.isWrite && RegNext(TagAccess.io.allocateWrite.valid, false.B) && (tagReplaceStatus === false.B) && TagAccess.io.needReplace.get)) {
```

(The definition of dataReplaceReadValid is inlined because its textual position at
:579 is after this edit point.) The alternative "instantiate DataAccess with
bypassWrite=true" was not adopted — changing the guard only affects the write
release on the conflicting cycle (one bubble) without touching the SRAM behavior
assumption, which is semantically more conservative.

**Fix verification**:

- Effectiveness: Lean fixed version `fmem_i29_guard` /
  `fmem_i29_collision_blocked` / `fmem_i29_write_proceeds` (collision eliminated +
  no deadlock); patched-tree DCache suite regression green (doc/22);
- Regression safety: `fmem_i29_ready_regress` (step-by-step equivalence when no
  in-flight victim read); no collateral damage in the 38-patch merged tree
  regression;
- Incidental benefit (measured on the 38-patch tree, doc/22): the i29 guard plus
  the post-i27-fix LRU dynamics make the original collision configuration
  structurally unreachable under the test orchestration — defense-in-depth effect
  of the fixes.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Line-by-line verification of DCache.scala:623 / :218 / :445 / :579-583 / :646-649 / :764 / :637-659 | Six locations consistent |
| Machine-checked Lean proof | `dc_fire_excludes_allocWrite` (interlock coverage) + `dcT_w1_collision_reachable` (three-cycle reachable) + `dcT_w1_sram_lfsr` (read-out = LFSR 0x43B2A190, connected to `sram_lfsr_bypass`) | Machine-checked closed loop |
| Simulation verification | ChiselSim (Verilator backend): no LFSR pollution observed on either tree; on baseline the collision configuration genuinely occurs but the writeback data is the store's new value | **Not reproduced (residual doubt)**; doc/22 ruled the Lean mechanism proof authoritative |
| Fix verification | i29 patch (st1 guard); `fmem_i29_guard` / `fmem_i29_collision_blocked` / `fmem_i29_write_proceeds` / `fmem_i29_ready_regress` + patched-tree regression green | Machine-checked + measured (regression side) |

The entire I-29 mechanism chain (interlock gap → timing reachable → SRAM
semantics → writeback pollution) is closed by machine-checked proofs, but the
LFSR pollution shape was not observed on the simulation side — this entry is a
typical case of "machine-checked mechanism stronger than simulation evidence": the
layered credibility of conclusions must be maintained, and the residual doubt
(Verilator's read-during-write behavior) has been faithfully recorded in doc/22
and §5 of this report, pending waveform-level debugging or another simulator to
settle it.
