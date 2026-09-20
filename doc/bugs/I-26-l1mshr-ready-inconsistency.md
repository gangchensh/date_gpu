> English translation of the Chinese master `doc/bugs/I-26-L1MSHR反压不一致.md`. Translated 2026-09-13.

# I-26 Defect Detailed Analysis Report: L1MSHR's missReq.ready inconsistent with st0 backpressure; a secondary miss can lose the request and pollute targetInfo

| Item | Content |
|---|---|
| ID | I-26 |
| Source location | `ventus/src/L1Cache/L1MSHR.scala:295` (`missReq.ready` looks only at `mshrStatus_st1_w`) vs `:247-265` (`mshrStatus_st0` predictive backpressure); ★ lesion `:274-282` (the st1_w recompute condition covers only st1_r∈{0,1}, missing the case st1_r=SECONDARY_AVAIL(2) with the secondary-matched line's subentries already full); `:354` (the elsewhen that sets the secondary-merge bit hooks only se=1; a full line's indexWhere defaults to seIdx=0); `:299-301` (targetInfo write has no state gating); assertion `:196` (`assert(PopCount(entryMatchProbe) <= 1.U)`) |
| Type | Handshake protocol violation (Decoupled ready inconsistent with internal backpressure) → request loss + response-routing-information pollution |
| Severity | **Medium**: the mechanism is confirmed and reachable from the initial state in three cycles on the Lean side; under DCache's current integration it is most likely masked by st0-side interception; the ChiselSim reproduction trips the RTL's own assertion (:196), so the actual failure manifestation is stronger than the predicted "request loss" |
| Confirmation status | 【Confirmed (mechanism) / most likely masked under current integration】; ChiselSim reproduction succeeded (doc/22); the i26 patch was adjudicated in a dedicated review as a **harmless identity** (doc/22 I-26 special review), retained as defense in depth |
| Main evidence | [Lean machine-checked proof] symbolic inconsistency theorem + three-cycle-reachable witness triple + handshake-compliance control theorems; [simulation run] ChiselSim reproduction succeeded (ready/st0 inconsistency hit exactly + RTL assertion tripped); [direct source reading] L1MSHR.scala and the DCache-side interception chain (DCache.scala:212-219) checked line by line |
| Lean model | `lean/Ventus/Mem/L1MSHR.lean`; fixed version `lean/VentusF/Schedule.lean` |
| Repro/patch | `repro/L1MSHRReadyBugRepro.scala` (ChiselSim); patch `i26-l1mshr-missreq-ready.patch` (internal fix manifest; not released) |
| Related entries | I-22 (MSHRv2 handshake violation — the control case: this module's missRspOut is compliant), DCache-side masking chain (DCache.scala:212-219) |

---

## 0. Abstract

L1MSHR (the DCache's miss information table, 4 entries × 2 subentries) exposes a
standard Decoupled `missReq` interface, but its ready signal is **inconsistent**
with the internal st0 backpressure state: the st1_w recompute condition (:274)
covers only st1_r∈{PRIMARY_AVAIL(0), PRIMARY_FULL(1)} and misses the case where
st1_r=SECONDARY_AVAIL(2) and the secondary-matched line's subentries are already
full — in that case `missReq.ready=1` (the consumer trusts ready and fires), while
in the same cycle `mshrStatus_st0=3` (SECONDARY_FULL, backpressure). Two
consequences fire together: the secondary merge's subentry set-bit does not take
effect (:354's elsewhen hooks only se=1, and a full line's indexWhere defaults to
seIdx=0 — **the request never gets a response; it is lost**), while the targetInfo
write at :299-301 has no state gating and overwrites the existing subentry0's
response routing information (**bookkeeping pollution**).

The Lean side gives a symbolic core theorem (`l1m_q1_ready_inconsistent`) and a
witness triple reachable from the initial state in three cycles
(`l1mT7_ready_inconsistent`/`l1mT7_reqLost`/`l1mT7_tiCorrupt`). The ChiselSim
reproduction hits the ready/st0 inconsistency exactly, and in the response phase it
**trips the RTL's own assertion** `L1MSHR.scala:196` (PopCount(entryMatchProbe)<=1;
duplicate entries appear for the same block) — a failure manifestation stronger
than the predicted "request loss."

Tolerability conclusion: under DCache's current integration it is most likely
masked (st0 is predictive backpressure; the third same-block request is always
intercepted first at the st0 side by DCache.scala:212-219). The i26 patch (ready
ANDed with `!(secondaryMiss && subEntryFull)`) was adjudicated in the doc/22
special review as a **harmless identity** (it changes no behavior on any measured
trace) and is retained as defense in depth; the fixed-version behavior is pinned by
the Lean theorems `fschL1m_*`.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **L1MSHR**: the DCache's Miss Status Holding Register — on a miss it registers
  "which block is being fetched from L2." 4 entries (each holding one block
  address), each entry with 2 subentries (each holding one request waiting for that
  block). A **primary miss** (the block is requested for the first time) allocates
  a new entry and issues a memReq to L2; a **secondary miss** (an entry for the
  same block is already in flight) only merges into a free subentry of that entry,
  without repeating the memory access. When the L2 response returns, coreRsp is
  replayed subentry by subentry.
- **targetInfo**: the response routing information carried by each subentry (warp
  id, lane mask, byte offset, etc.; tIWidth=323 bits) — when the response arrives,
  this tells "whom to return the data to."
- **Two state levels st0/st1**: `mshrStatus_st0` is a **predictive** same-cycle
  combinational state (it also counts the current cycle's missReq.valid into
  occupancy, :248/:256), used by the DCache's coreReq acceptance logic for early
  backpressure; `mshrStatus_st1_r/_w` are pipeline-stage registered/recomputed
  values, and `missReq.ready` is derived from the latter.
- **Decoupled handshake discipline**: under the ready/valid protocol, a consumer
  seeing ready=1 regards the fire as effective and the information as recorded by
  the receiver. ready being inconsistent with the internal true acceptability =
  protocol violation.
- **State encoding**: 0=PRIMARY_AVAIL, 1=PRIMARY_FULL, 2=SECONDARY_AVAIL,
  3=SECONDARY_FULL, 4=SECONDARY_FULL_RETURN.

### 1.2 Design Intent

The intent of the st1_w recompute (:274-282): when a secondary request arrives, if
the state registered in the previous cycle is PRIMARY_* (0/1), it must be
recomputed against the current actual subentry occupancy as SECONDARY_AVAIL(2) or
SECONDARY_FULL(3); in all other cases the registered value is kept. ready and st0
should be of one source — in any situation where "st0 says backpressure," ready
should be 0.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the omission in the st1_w recompute condition**
(`L1MSHR.scala:274-282`, ★ the lesion):

```scala
when(secondaryMiss && (mshrStatus_st1_r === 0.U || mshrStatus_st1_r === 1.U)
     && io.stage2_ready) {
  when(subEntryFull) {
    mshrStatus_st1_w := 3.U //SECONDARY_FULL
  }.otherwise {
    mshrStatus_st1_w := 2.U //SECONDARY_AVAIL
  }
}.otherwise {
  mshrStatus_st1_w := mshrStatus_st1_r   // ★ when st1_r=2 it is kept unchanged
}
```

The recompute happens only when st1_r∈{0,1}. If st1_r=SECONDARY_AVAIL(2) (last
time it was judged that a free subentry remained) while this time the
secondary-matched line's subentries are **already full**, st1_w stays 2 — it does
not reflect "full."

**Construct 2: missReq.ready looks only at st1_w** (`L1MSHR.scala:295`, ★ hazard
point):

```scala
io.missReq.ready := !(mshrStatus_st1_w === 1.U || mshrStatus_st1_w === 3.U )
```

st1_w=2 ⇒ ready=1. Meanwhile in the same cycle st0 (construct 3) has already
computed SECONDARY_FULL(3).

**Construct 3: st0's predictive backpressure** (`L1MSHR.scala:247-265`):

```scala
when(primaryMiss_st0) {
  when(mainEntryFull || io.missReq.valid && mainEntryAlmFull) {
    mshrStatus_st0 := 1.U //PRIMARY_FULL        // :249, missReq.valid counted into occupancy
  }.otherwise { mshrStatus_st0 := 0.U }
}.otherwise {
  when(subEntryFull || io.missReq.valid && subEntryAlmFull) {
    mshrStatus_st0 := 3.U //SECONDARY_FULL      // :257, same as above: almost-full backpressures
  }.elsewhen(...) { mshrStatus_st0 := 4.U
  }.otherwise { mshrStatus_st0 := 2.U }
}
```

**Construct 4: the targetInfo write has no state gating**
(`L1MSHR.scala:299-301`, ★ the second victim surface):

```scala
when(io.missReq.fire && MSHR_st1.io.deq.ready) {
  targetInfo_Accesss(real_SRAMAddrUp)(real_SRAMAddrDown) := io.missReq.bits.targetInfo
}
```

It looks only at fire, not at st1_w — even when the secondary fire with ready=1
fails to set the subentry bit, targetInfo is overwritten all the same
(real_SRAMAddrDown for a full line takes the default seIdx=0, overwriting
subentry0's routing information).

**Construct 5: the elsewhen hook-up of the secondary-merge set-bit** (around
`L1MSHR.scala:354`):

```scala
}.elsewhen(iofSubEn.asUInt === subEntryIdx_st1 &&
  io.missReq.fire && secondaryMiss && MSHR_st1.io.deq.fire && ...) {
  subentry_valid(iofEn)(iofSubEn) := true.B
}
```

For a full line, indexWhere defaults to seIdx=0, while this branch hooks only se=1 —
which happens to be correct under the fixed parameter S=2 (doc/03 L1MSHR note), but
stacked on construct 1's omission, the subentry set-bit of a "full-line secondary
fire" falls through.

**Construct 6: the built-in assertion** (`L1MSHR.scala:196`):

```scala
assert(PopCount(entryMatchProbe) <= 1.U)
```

A runtime assertion that at most one entry matches the same block — it was tripped
during reproduction (see §5), showing that the downstream effects of the ready/st0
inconsistency can push the module into a state even the developers considered
impossible.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

Trigger sequence (corresponding to the Lean witness three-cycle trace,
blockAddr=0x10, NMshrSubEntry=2):

1. C1: primary miss (instrId=5, ti=0xBEEF) → allocates entry0 sub0;
2. C2: secondary miss (instrId=6, ti=0xCAFE) → merges into entry0 sub1 (subentries
   full from here on);
3. C3: another secondary miss (instrId=7, ti=0xDEAD) → **st0=3 (SECONDARY_FULL,
   backpressure) but missReq.ready=1 (fire takes effect)**:
   - the subentry set-bit does not take effect (:354 hooks only se=1; a full line
     defaults to seIdx=0) — instrId=7's request **never gets a response; it is
     lost**;
   - targetInfo(0,0) is overwritten by 0xDEAD (it should still be 0xBEEF) —
     entry0 sub0's response routing information is **polluted**.

### 3.2 Root Cause

The whitelist `{0,1}` of the st1_w recompute condition (:274) misses the case
st1_r=2 — the author considered "last time it was a primary-miss judgment and this
time it must be recomputed against the actual secondary situation," but missed
"last time it was already judged secondary-available, yet this time the matched
line is full." From then on the two judgments — ready (construct 2) and st0
(construct 3) — diverge: st0 looks at the actual situation (predictively), while
ready looks at st1_w (lagging, with an incomplete condition). This is a defect of
the class **two judgment logics for the same fact falling out of sync**.

### 3.3 Harm and Tolerability

- **Harm**: under Decoupled semantics the consumer trusts ready and fires — the
  secondary request is lost (the corresponding warp's memory access never gets a
  response; the direction is a hang) + targetInfo pollution (response routing goes
  wrong; the direction is wrong data / wrong bookkeeping).
- **Masking under the current integration** (the tolerability conclusion of doc/03,
  reproduced verbatim): st0 is predictive (:248/:256 count missReq.valid into
  full); coreReq acceptance is intercepted when st0∈{1,3}
  (DCache.scala:212-219); coreReq_Q is 1 deep — the third same-block request is
  always blocked first at the st0 side and never reaches missReq. But **any
  consumer that "trusts missReq.ready"** (perfectly legal under Decoupled) would
  trigger it — the masking relies on one-sided gatekeeping, which is fragile
  correctness.
- **Unexpected finding during reproduction**: the ChiselSim reproduction trips the
  RTL's own assertion `L1MSHR.scala:196` (PopCount(entryMatchProbe)<=1) in the
  response phase — duplicate entries appear for the same block, a failure
  manifestation stronger than the predicted "request loss"; the targetInfo
  pollution observation was preempted by this assertion (residual doubt, recorded
  verbatim in doc/22).
- Rating: **medium** (mechanism confirmed, reachable from the initial state in
  three cycles, but most likely masked under the current integration).

### 3.4 Control Conclusion (Good News)

The same module's missRspOut channel is buffered by a 1-deep pipe queue, and
**NoWithdraw and Stable both hold unconditionally**
(`l1m_rspOut_noWithdraw`/`l1m_rspOut_stable`, for any state and any two cycles of
input) — unlike I-22 (MSHRv2's valid withdrawal), this module's output-side
handshake is compliant; the defect is concentrated on the input-side ready.

---

## 4. Lean Formal Evidence

All located in `lean/Ventus/Mem/L1MSHR.lean`, zero sorry.

**Symbolic core** (combinational level, any state satisfying the premises):

- `l1m_q1_ready_inconsistent` (:908): when st1_r=SECONDARY_AVAIL(2) and the
  secondary-matched line's subentries are full, `missReq.ready=1` while in the same
  cycle `st0=3` — the ready/st0 inconsistency is pinned down.

**Reachability witness triple** (native_decide, reachable from the initial state in
three cycles):

- `l1mT7_ready_inconsistent` (:531): st0=3 yet missReq.fire takes effect;
- `l1mT7_reqLost` (:538): the secondary-merge set-bit does not take effect (seIdx=0
  while :354 hooks only se=1) — the request never gets a response; it is lost;
- `l1mT7_tiCorrupt` (:545): the targetInfo write has no state gating; reqTI=0xDEAD
  overwrites subentry0's 0xBEEF — response routing information polluted.

**Handshake-compliance control**: `l1m_rspOut_noWithdraw` (:674) /
`l1m_rspOut_stable` (:684) — missRspOut satisfies NoWithdraw and Stable
unconditionally (a structural property of the 1-deep pipe queue).

**Fixed-version verification** (`lean/VentusF/Schedule.lean`):
`fschL1m_q1_ready_consistent` (:2160, ready consistent with st0 after the fix),
`fschL1m_fire_eq_iff` (:2168), `fschL1m_noFire_ti_preserved` (:2178, no fire ⇒
targetInfo not polluted), `fschL1mStep_eq_orig` (:2185)/`fschL1mRun_eq_orig`
(:2198, step-by-step equivalence on the non-trigger domain), `fschL1mT_i26_noFire`
(:2232, in the original witness scenario after the fix ready=0, no fire, and ti
stays 0xBEEF).

---

## 5. Simulation Verification (ChiselSim Run)

**Reproduction succeeded (evidence 1 hit exactly)**
(`repro/L1MSHRReadyBugRepro.scala`, actually run 2026-09-06/07, doc/22):

- Driven by the C1/C2/C3 sequence of §3.1. **At C3, measured st0=3
  (SECONDARY_FULL) and missReq.ready=1** — the ready/st0 inconsistency holds;
  evidence 1 hit exactly;
- In the response phase the **RTL's own assertion** `L1MSHR.scala:196` is tripped
  (PopCount(entryMatchProbe)<=1; duplicate entries appear for the same block) —
  this is a failure manifestation stronger than the predicted "request loss"
  (doc/22 verbatim; its special-review section elsewhere cites :200 — the same
  assertion with a different line-number reference; direct source reading confirms
  :196);
- the targetInfo pollution observation was preempted by this assertion (residual
  doubt);
- test adaptation record (doc/22 change list): the C3 evidence assertion was moved
  ahead of the response phase; the response phase is wrapped in Try so the
  hardware assertion is recorded as evidence (otherwise the RTL's own assertion
  would preempt the observation).

**Patch-tree regression (key finding: i26 is a harmless identity)** (doc/22 "I-26
special review," actually run 2026-09-07 + re-confirmed identically on the 38-patch
merged tree 2026-09-10): L1MSHRReadyBugRepro on the patched tree is **0/1 red,
cycle-by-cycle identical to baseline** — the patch has no effect on this witness.
The dedicated analysis is in §7.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: the DCache's L1MSHR sole instantiation point
  (DCache.scala:178). Under the current integration it is most likely masked (the
  st0-side interception chain of §3.3); the broken-window condition = any
  consumption style that bypasses DCache's st0 interception and trusts missReq.ready
  directly per Decoupled semantics (refactoring, parameter changes, deepening
  coreReq_Q, etc.).
- **Why upstream did not find it**: the masking chain (predictive st0 + 1-deep
  coreReq_Q) always blocks the third same-block request at the door in normal
  simulation; and once triggered (in a synthesized environment without assertions)
  the manifestation is request loss / routing pollution, which is hard to
  attribute.
- **Upstream corroboration**: the built-in assertion at `:196` was tripped by the
  reproduction — the developers foresaw that "duplicate entries for the same
  block" is unacceptable, yet the ready/st0 inconsistency happens to be able to
  push it into exactly that state.

---

## 7. Fix Plan and Fix Verification

**Patch** (`i26-l1mshr-missreq-ready.patch` (internal fix manifest; not released), single edit
point):

```scala
// L1MSHR.scala:295
-  io.missReq.ready := !(mshrStatus_st1_w === 1.U || mshrStatus_st1_w === 3.U )
+  // I-26 fix (defense in depth): when the secondary miss's matched line has its subentries full, st0 backpressures (=3)
+  // but the st1_w recompute condition (:274) misses this case, leaving ready=1 — a consumer trusts ready and
+  // fires; the request is lost and targetInfo is polluted. ready is ANDed with the negation of this case.
+  io.missReq.ready := !(mshrStatus_st1_w === 1.U || mshrStatus_st1_w === 3.U ) && !(secondaryMiss && subEntryFull)
```

the internal fix manifest positioning: Defense-in-depth (not functional fix required).

**The special adjudication that the i26 patch is a harmless identity** (doc/22
"I-26 special review," key points reproduced):

- The diagnostic test `I26DiagRepro.scala` (run on both trees, pure IO observation;
  a diagnostic artifact located under tests/src/L1Cache/ of both trees, not synced
  to /mnt/d) located the cause: in the patch condition
  `!(secondaryMiss && subEntryFull)`, `secondaryMiss` is taken from the st1 stage
  (`MSHR_st1.io.deq.bits`, a depth-1 queue whose deq lags one cycle), while
  `subEntryFull` is taken from the st0 stage (the line matched by the same-cycle
  probe) — under the witness test's same-cycle probe+missReq driving, the two
  signals are misaligned at C3 (diag A/B: at C3, secondaryMiss(st1)=false,
  subEntryFull=false).
- Replaying with DCache's real timing (probe@N, missReq@N+1 gated by probestatus,
  DCache.scala:275/319) (diag C): both trees are again cycle-by-cycle identical,
  and **the unpatched code already backpressures correctly on this trace** (st1_r
  is updated to 3 via the probe cycle); I-26's ready/st0 inconsistency under real
  timing is additionally masked by DCache coreReq gating (:212/:217/:219 block
  st0=3).
- **Adjudication: the i26 patch is a harmless identity** (it changes no behavior on
  any measured trace); no signal name was written wrongly; the witness test's
  timing model is not DCache's real timing. Recommendation: keep the patch
  (defense in depth), and write a new witness case per the diag C timing to pin the
  behavior; the original test is retained to pin the baseline behavior.
- 38-patch merged-tree re-check (2026-09-10): the judgment is consistent (same
  witness: C3 ready=1 + PopCount assertion).

**Lean fixed-version verification** (independent of the patch timing issue, modeled
per the semantics of "ready ANDed with `!(secondaryMiss && subEntryFull)`"):
`fschL1m_q1_ready_consistent` (consistent after the fix), `fschL1mT_i26_noFire`
(in the original witness scenario after the fix there is no fire and targetInfo is
preserved), `fschL1mRun_eq_orig` (regression equivalence).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | L1MSHR.scala:274-282 (recompute-condition omission)/:295 (ready)/:247-265 (st0 predictive)/:299-301 (targetInfo ungated)/:354 (elsewhen hook-up)/:196 (built-in assertion); masking chain DCache.scala:212-219 | Line numbers checked one by one |
| Lean machine-checked proof | `l1m_q1_ready_inconsistent` (symbolic) + `l1mT7_ready_inconsistent`/`l1mT7_reqLost`/`l1mT7_tiCorrupt` (witnesses reachable from the initial state in three cycles) + controls `l1m_rspOut_noWithdraw`/`l1m_rspOut_stable` | Symbolic level + concrete traces |
| ChiselSim reproduction | C3 measured ready=1/st0=3, hit exactly; the response phase trips the RTL's own assertion :196 (stronger than predicted); the targetInfo observation was preempted by the assertion (residual doubt recorded verbatim) | Actually run |
| Fix verification | i26 patch (1 edit point); patch-tree regression 0/1 red (cycle-by-cycle identical to baseline) → special adjudication: **harmless identity** (doc/22); Lean fixed version `fschL1m_*` six theorems | Actual run + machine proof |

I-26 is a defect of the "two judgment logics for the same fact falling out of sync"
type: the whitelist omission in the st1_w recompute makes ready and st0 diverge,
and a secondary miss can lose the request and pollute targetInfo. The mechanism is
triply confirmed by Lean symbolization + three-cycle-reachable witnesses +
ChiselSim (including the RTL's own assertion being tripped); under the current
integration it is most likely masked by st0's predictive backpressure, so the fix
is positioned as defense in depth. This entry also contributed this project's first
complete special adjudication of "a patch being a harmless identity on the witness"
(doc/22) — the difference between the reproduction test's timing model and the
integrated timing of the system under test itself became an object of analysis.
