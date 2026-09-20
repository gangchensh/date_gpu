> English translation of the Chinese master `doc/bugs/I-39-MSHR分配优先级反转.md`. Translated 2026-09-13.

# I-39 Detailed Defect Analysis Report: L2 MSHR allocate×a.fire priority inversion — a new request's Get is never sent

| Item | Content |
|---|---|
| ID | I-39 |
| Source location | `ventus/src/L2cache/MSHR.scala:110-115` (the `when(a.fire).elsewhen(allocate.valid)` priority inversion of `sche_a_valid`); related point `L2cache/Scheduler.scala:190` (allocate gated by the `result.valid` level rather than fire, I-44) |
| Type | Functional bug (hang) — same-cycle event priority design error inside the MSHR |
| Severity | **Mechanism-level high** (when triggered, that MSHR entry hangs: the outgoing Get is never sent and the request is never answered); **machine-checked unreachable under most current configurations** — reachable again only in the ListBuffer-pool-exhaustion corner of I-44 |
| Confirmation status | 【Mechanism confirmed / machine-checked unreachable (Scheduler side), conditional】 — the unreachability discharge is premised on environment assumption E3, which I-44 has falsified (wave-27 revision qualification, see §3.3) |
| Primary evidence | 【Lean machine-checked proof】MSHR-level witness + Scheduler-side invariant induction discharge + machine-checked invariant breakage in the I-44 corner; 【direct source reading】line-by-line check of MSHR.scala:110-115, Scheduler.scala:190 |
| Lean model | `lean/Ventus/L2/L2MSHR.lean` (MSHR mechanism and witness), `lean/Ventus/L2/Scheduler.lean` (reachability discharge), `lean/Ventus/L2/Discharge.lean` (E3 falsification); fixed version `lean/VentusF/MemL2.lean` |
| Reproduction/patch | No ChiselSim/Verilator reproduction suite (ready-to-run, not executed in this environment, see §5); patch `i39-l2-mshr-alloc-priority.patch` (internal fix manifest; not released) (defense in depth) |
| Related entries | **I-44** (E3 falsified — the qualifying condition of this entry's unreachability conclusion; in the corner where E3 fails, this entry becomes reachable again), I-41 (same-module same-cycle priority family), I-40 (same-wave L2 finding), I-37 (mshr_wait failure widens the same kind of timing surface) |

---

## 0. Abstract

Each MSHR entry of the L2 Cache uses a flag bit `sche_a_valid` to record "this
entry has a Get request pending to be sent to the outer memory". The priority
chain that updates this flag at MSHR.scala:110-115 orders **a-channel
handshake success (a.fire) before reallocation (allocate)**: when the
Scheduler reallocates an entry whose `sche_a_valid` is still 1, and the old
request's a.fire happens to succeed on the same cycle, the `when(a.fire)`
branch hits first and clears the flag to 0, while the
`elsewhen(allocate.valid)` branch is swallowed — **the new request's
pending-send flag is never set, and its outgoing Get can never be sent**: the
entry stays occupied, the memory request is missing, the response never
arrives, and the MSHR hangs.

The mechanism is pinned down by the MSHR-level witness
`l2mT_alloc_fire_collision`. Wave 25 established an unreachability discharge
on the Scheduler side: the invariant `l2scInv1` ("an MSHR corresponding to a
free ListBuffer slot has no pending A") holds inductively from reset
(`l2sc_inv1_init/preserved/run`) under environment assumption E3 ("allocate
hits ⇒ the push is accepted"), and under the invariant an entry being
allocated cannot a.fire on that cycle (`l2sc_i39_no_alloc_afire`). **But the
wave-27 discovery of I-44 falsified E3** (the ListBuffer-pool-exhaustion
corner; `l2dc_e3_falsified`/`l2dc_e3_inv1_broken`) — in that corner this entry
becomes reachable again. Final characterization: **the mechanism is real;
machine-checked unreachable within the range where E3 holds (pool not
exhausted); reachable in the I-44 corner**; the fix is positioned as defense
in depth (branch swap), and once I-44's root fix (allocate changed to fire
semantics) lands, this entry returns to structural unreachability.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **L2 Cache and MSHR**: Ventus's L2Cache sits between each SM's L1 and the
  outer memory. An MSHR (Miss Status Holding Register; 32 entries in this
  design) records the metadata of every miss/write transaction (`request`:
  opcode/tag/set/way/source etc.) and its data (`data_reg`), and drives three
  kinds of pending transactions: fetch requests to the outer memory
  (`schedule.a`, TileLink A channel), responses to the L1 (`schedule.d`), and
  directory/data-array backfill (`schedule.dir`).
- **TileLink A/D channel discipline**: the A channel carries requests
  (Get=read, Put=write), the D channel carries responses (AccessAckData etc.).
  Every A request carries a `source` field (here = the MSHR entry number), and
  the outer memory returns exactly one D response with the same source for
  every A.
- **Scheduler allocation**: the directory result of a miss is loaded into a
  free MSHR entry via `m.io.allocate`; `sche_a_valid=1` means "this entry's
  Get has not been sent yet"; the Scheduler's round-robin arbiter picks one
  entry with `sche_a_valid` set to send an A.
- **Entry reuse**: once an entry's D response completes, the entry can be
  reallocated by a later miss. At the reuse moment, the handover of the old
  and new transactions' flag bits is decided by the when/elsewhen chain inside
  the MSHR — this defect lies in the priority of that handover.

### 1.2 Design intent

The semantics of `sche_a_valid` should be: **set to 1 on allocate (new request
pending), cleared to 0 on a.fire (sent)**. When the two events coincide on the
same cycle, the correct composite semantics is "the old request is sent, the
new request is pending", i.e. the flag should stay 1 (or equivalently: clear
first then set; the set wins).

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the update chain of `sche_a_valid` — a.fire takes priority over allocate** (★ the hazard, `MSHR.scala:110-115`, confirmed consistent by direct source reading):

```scala
when(io.schedule.a.fire) {          // :110  ★ checked first: did the old request's A go out
  sche_a_valid := false.B           // :111
}.elsewhen(io.allocate.valid) {     // :112  ★ checked second: is the entry reallocated this cycle
  sche_a_valid := true.B            // :113
}.otherwise {
  sche_a_valid := sche_a_valid      // :115  hold
}
```

Chisel's `when/elsewhen` is a priority chain: when both conditions are true on
the same cycle, only the first branch takes effect. So allocate×a.fire on the
same cycle ⇒ `sche_a_valid := false.B` — allocate's set is **swallowed whole**
(not "clear then set", but "cleared and never set").

**Construct 2: the output gating of a.valid** (`MSHR.scala:97`):

```scala
io.schedule.a.valid := sche_a_valid && !io.mshr_wait
```

The outgoing Get's valid is driven directly by `sche_a_valid`. Once the flag
is wrongly cleared to 0, the new request's Get has no other path to be sent.

**Construct 3: how allocate is produced on the Scheduler side** (`Scheduler.scala:190`):

```scala
when (directory.io.result.valid && alloc && s && !directory.io.result.bits.hit
      && !directory.io.result.bits.flush){
  m.io.allocate.valid := true.B     // :191
  ...                               // :192-195 loads the result's set/tag/way/opcode
}
```

The allocate gating uses the `result.valid` **level** rather than the
`result.fire` event — this is where I-44 lands, and also the source of the
conditionality of this entry's reachability conclusion: when result is stuck
(not consumed), allocate.valid repeats every cycle and the MSHR is re-armed
repeatedly (see §3.3).

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

Trigger form: MSHR entry i satisfies
1. `sche_a_valid(i)=1` (the old request's Get is pending or in flight);
2. on that cycle `allocate.valid(i)=1` (the Scheduler allocates a new miss to
   entry i);
3. on that cycle `schedule.a.fire(i)=1` (the old request's Get happens to go
   out this cycle).

All three on the same cycle ⇒ the :110 branch hits first,
`sche_a_valid(i)'=false`, and the :112 set is swallowed. The consequence
chain: the new request's `request`/`data_reg` are loaded correctly
(allocate's other branches are independent), but `schedule.a.valid` is never
true (construct 2) ⇒ the outer memory never receives this Get ⇒ the D
response never arrives ⇒ `sink_d_reg` is never set ⇒ the entry is occupied
permanently (occupying an MSHR slot and a ListBuffer queue item), and the L1
requester waiting on that block hangs.

### 3.2 Root cause

A single-point priority design error: the author of the when/elsewhen chain
put "a.fire clears the flag" before "allocate sets the flag", which implicitly
assumes the contract "allocate and a.fire never coincide on the same cycle"
without enforcing it inside the module (no assertion). The same module's
`sink_d_reg` (:67-72 allocate clears + :143-147 sinkd sets, last write wins)
and `data_reg` (:81-87) have same-cycle priority problems of the same family;
see I-41.

Why upstream did not find it: under a normal scheduling rhythm the Scheduler
reuses an entry only after it is fully drained (D response complete, the
ListBuffer item popped), by which time `sche_a_valid` has long been cleared to
0 — the same-cycle collision needs the tight timing of "old A and
reallocation on the same cycle", which functional simulation very rarely hits.

### 3.3 Harm and tolerability (including the wave-27 revision qualification)

- **Harm** (when triggered): the entry hangs, the requester hangs — an
  L2-level progress failure, and silent (no assertion, no timeout).
- **Reachability (conditional, must be stated precisely)**:
  - 【Lean machine-checked proof】When E3 ("allocate hits ⇒ the push is
    accepted") holds, the invariant `l2scInv1` is preserved inductively, and
    an entry being allocated cannot a.fire on that cycle — **machine-checked
    unreachable** (`l2sc_i39_no_alloc_afire`, wave 25).
  - 【Lean machine-checked proof】**E3 has been falsified by I-44** (wave 27):
    in the ListBuffer-pool-exhaustion corner, allocate.valid repeats while the
    push is rejected, and `l2scInv1` is machine-checkably broken
    (`l2dc_e3_inv1_broken`) — in that corner, allocate×a.fire on the same
    cycle is **reachable again**.
  - Conclusion copied verbatim from doc/03: **outside the range where E3
    holds (pool not exhausted) the conclusion still stands; in the
    pool-exhaustion corner this discharge does not hold**.
- **Tolerability**: under the current design the trigger surface = I-44's
  pool-exhaustion corner (31 primary + 1 secondary pushes exhausting the
  freelist, machine-checkably reachable via `l2dc_lb_pool_exhausted`). Once
  I-44's root fix lands, E3 is restored by construction
  (`fmem_i44_e3_by_construction`) and this entry returns to unreachability;
  until then it is rated a **latent correctness/liveness defect**, with the
  fix positioned as defense in depth.

---

## 4. Lean Formal Evidence

All zero-sorry; the evidence comes in three layers (all 【Lean machine-checked
proof】):

**MSHR-level mechanism witness** (`lean/Ventus/L2/L2MSHR.lean`):

- `l2mT_alloc_fire_collision` (L2MSHR.lean:501, native_decide single-cycle
  witness): in the allocated state (scheAValid=1), allocate + aReady on the
  same cycle ⇒ `l2mAFire=true` and `scheAValid'=false`, and on the next cycle
  `aValid=false` — the new request's Get cannot be sent; the mechanism is
  pinned down.
- Control side: the premise of `l2m_step_alloc` (the full effect of an
  allocate cycle) happens to exclude the collision cycle — the premise itself
  is a mirror image of the defect's trigger condition;
  `l2m_scheA_noWithdraw`/`l2m_aBits_stable` characterize the a-channel
  compliance when there is no collision.

**Scheduler-side unreachability discharge** (`lean/Ventus/L2/Scheduler.lean`, wave 25):

- Invariant `l2scInv1`: a free ListBuffer slot ⇒ the corresponding MSHR has
  `scheAValid=0`.
- `l2sc_inv1_init` (:703, holds at reset), `l2sc_inv1_preserved` (:717,
  single-cycle preservation, premise `l2scEnv` includes E3), `l2sc_inv1_run`
  (:805, induction over arbitrary traces).
- Main theorem `l2sc_i39_no_alloc_afire` (:708): under `l2scInv1`,
  `l2scAllocValid st inp i = true ⇒ l2scAFire st inp i = false` — an entry
  being allocated cannot a.fire on that cycle; I-39 is machine-checked
  unreachable.

**The qualification of this entry by E3's falsification** (`lean/Ventus/L2/Discharge.lean`, wave 27):

- `l2dc_e3_falsified` (:367): E3 is falsified as a proposition (the
  counterexample `l2dc_e3_counterexample` with allocValid ∧ ¬pushReady on the
  same cycle);
- `l2dc_e3_inv1_broken` (:377): `¬ l2scInv1 l2dcE3St33` — I-39's invariant is
  machine-checkably broken in the I-44 corner;
- `l2dc_lb_pool_exhausted` (:291): pool exhaustion itself is machine-checkably
  reachable.

**Fixed-version verification** (`lean/VentusF/MemL2.lean`):

- `fmem_i39_witness_green` (:454): when allocate×a.fire coincide, the original
  swallows the new request while the fixed version (allocate takes priority)
  keeps the pending-send flag — the original witness goes green on the fixed
  version;
- `fmem_i39_regress` (:465): when `allocValid=false ∨ a.fire=false`, the fixed
  version is step-by-step equivalent to the original (regression-safe outside
  the trigger domain);
- Root-fix linkage: `fmem_i44_e3_by_construction` (:576) — under the I-44
  fixed version, E3 is restored by construction, and this entry is
  structurally unreachable under the fixed Scheduler.

Axiom audit: Scheduler.lean archives `#print axioms` for 10 theorems
including `l2sc_i39_no_alloc_afire`, `l2sc_inv1_preserved`, `l2sc_inv1_run` —
the symbolic theorems depend only on standard axioms of the
propext/Quot.sound level; native_decide witnesses carry `Lean.ofReduceBool`
(the expected trust axiom in v4.31, noted in the archive).

---

## 5. Simulation Verification

**【Ready-to-run / not executed in this environment】** — this entry has no
ChiselSim/Verilator reproduction suite. The 11 ChiselSim suites and 10
Verilator kernels actually run in doc/22 do not cover the L2 MSHR (no
corresponding file under repro/). And per the reachability analysis of §3.3,
**directly reproducing this entry on the unfixed current design requires first
constructing I-44's pool-exhaustion scenario** (after 31+1 pushes exhaust the
freelist, make a stuck allocate coincide with a.fire); a reasonable form for a
directed ChiselSim test is: at the Scheduler level, drive consecutive misses
to fill the requests pool, inject a secondary push on the same cycle to
exhaust the pool, and observe the `schedule.a.valid` of the repeatedly
re-armed entry. That test code is yet to be written (ready-to-run, not
executed in this environment).

Patch side: the i39 patch has been merged into the tree together with the
35/38 patches and passed mill compilation and elaboration (doc/22 patch-tree
regression, MILL_EXIT=0), but there is no directed behavioral test case for
this entry — its regression safety is carried by the Lean-side
`fmem_i39_regress` machine-checked proof.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: unreachable within the range where E3 holds; reachable
  inside I-44's pool-exhaustion corner (that corner's own harm — repeated
  refill A's with the same source — is already filed as I-44; this entry is
  its downstream MSHR-hang form).
- **Coupling with I-44 (an accurate statement for upstream)**: the premise of
  this entry's unreachability proof is E3, and E3 is broken by I-44 in the
  current (unfixed) design — **on the current design one cannot
  unconditionally claim this entry is "proved unreachable"** (the project's
  internal review W2 targets exactly this wording; doc/20 §W2); the accurate
  statement is "machine-checked unreachable under `l2scInv1`; that invariant's
  premise E3 is falsified exactly in I-44's pool-exhaustion corner; after
  fixing I-44, E3 is restored by construction and this entry returns to
  unreachability".
- **Broken-window conditions (independent of I-44)**: any scheduling change
  that makes "an entry reallocated before being drained" possible (e.g. the
  ListBuffer pop timing moved earlier, or an allocation path bypassing the
  pool check) directly activates this entry — the defense-in-depth fix (branch
  swap) eliminates the entire same-cycle combination and does not rely on any
  scheduling discipline.

---

## 7. Fix and Fix Verification

**Patch** (`i39-l2-mshr-alloc-priority.patch` (internal fix manifest; not released),
defense-in-depth class, registered in the internal fix manifest): swap the two branches at
`MSHR.scala:110-115` so allocate takes priority — on a same-cycle collision
`sche_a_valid := true.B` (the new request is pending) and a.fire falls into
the elsewhen:

```scala
when(io.allocate.valid) {            // after fix: allocate takes priority
  sche_a_valid := true.B
}.elsewhen(io.schedule.a.fire) {
  sche_a_valid := false.B
}.otherwise {
  sche_a_valid := sche_a_valid
}
```

**Fix verification**:

- 【Lean machine-checked proof】`fmem_i39_witness_green` (the collision trace
  no longer swallows the flag on the fixed version), `fmem_i39_regress`
  (step-by-step equivalence outside the trigger domain — regression-safe);
- 【Lean machine-checked proof】root-fix linkage: under the I-44 fixed version
  E3 holds by construction (`fmem_i44_e3_by_construction`), and this entry
  returns to structural unreachability — verbatim from the internal fix manifest:
  "`l2sc_i39_no_alloc_afire` holds under E3; E3 is restored by the
  I-44 fix";
- 【Simulation run】the patch was merged into the tree together with the 35/38
  patches and passed mill compilation + full-chip elaboration (doc/22,
  MILL_EXIT=0); the directed behavioral test case is ready-to-run (§5).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | MSHR.scala:110-115 priority inversion, :97 a.valid gating, Scheduler.scala:190 level-based allocate, line-by-line checked | Three points consistent |
| Lean machine-checked proof (mechanism) | `l2mT_alloc_fire_collision` single-cycle witness: allocate×a.fire on the same cycle swallows the new request | Concrete trace |
| Lean machine-checked proof (unreachability discharge) | `l2sc_i39_no_alloc_afire` + `l2sc_inv1_init/preserved/run` — unreachable over arbitrary traces under E3 | Invariant induction (premise E3) |
| Lean machine-checked proof (qualification) | `l2dc_e3_falsified`/`l2dc_e3_inv1_broken`/`l2dc_lb_pool_exhausted` — E3 falsified by I-44; the discharge fails in the pool-exhaustion corner | Counterexample + invariant breakage |
| Simulation | No directed suite (ready-to-run, not executed in this environment); patch tree compiles/elaborates | Patch-tree run |
| Fix verification | i39 patch (branch swap); `fmem_i39_witness_green`/`fmem_i39_regress`; E3 restored by construction after the I-44 fix (`fmem_i44_e3_by_construction`) | Machine-checked + compile run |

I-39 is a textbook case of the "same-cycle event priority" defect family: the
mechanism is real (one cycle hangs the entry), and its unreachability is a
**conditional theorem**, not an unconditional conclusion — the premise E3 is
falsified by another finding of the same project (I-44), and the coupling
between the two layers of conclusions is itself machine-checked (the
invariant-breakage theorem). This makes it a methodological case study in
"reachability conclusions must carry their premises, and premises can be
overturned by later discoveries".
