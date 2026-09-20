> English translation of the Chinese master `doc/bugs/I-37-L2-putput恒假mshrwait失效.md`. Translated 2026-09-13.

# I-37 Detailed Defect Analysis Report: L2 SourceD `PutFullData && PutPartialData` always false — mshr_wait disabled

| Item | Content |
|---|---|
| ID | I-37 |
| Source location | `ventus/src/L2cache/SourceD.scala:142` (`s1_req.opcode === PutFullData && s1_req.opcode === PutPartialData` is always false); related points `:137` (the miss-dirty branch correctly sets mshr_wait), `Scheduler.scala:133` (mshr_wait broadcast to all MSHRs) |
| Type | Functional bug (logical operator miswritten: && should be \|\|) — protection barrier disabled |
| Severity | **Medium-high** (the write-miss-no-allocate path loses the blocking protection on the victim way, a data race; the harm surface depends on concrete scheduling timing, to be quantified by Scheduler modeling — conclusion recorded verbatim from doc/03) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + patch exists (this entry not covered by RTL regression) |
| Primary evidence | 【Lean machine-checked proof】`l2s_putput_and_false` (exhaustive over all 3-bit opcodes, always false) + `l2sT_mshr_wait_put_miss` (scenario witness); 【direct source reading】line-by-line check of SourceD.scala :135-145, cross-checked against :103/:218 where the same condition is correctly written with \|\| |
| Lean model | Original `lean/Ventus/L2/SourceD.lean`; fixed version `lean/VentusF/MemL2.lean` (`fmem_i37_*`) |
| Reproduction/patch | ChiselSim ready-to-run (not executed in this environment, see §5); patch `i37-l2-sourced-putput.patch` (internal fix manifest; not released) |
| Related entries | I-40 (BankedStore same-cycle read-write conflict, also a gap in victim-eviction protection), I-39/I-41 (L2 MSHR same-cycle priority family) |

---

## 0. Abstract

When the stage_1 state machine of the L2 SourceD handles "write miss no
allocate" (PutFullData/PutPartialData miss, non-dirty victim, from an MSHR),
it should set `mshr_wait_reg` as a blocking barrier on the victim way (the
comment at SourceD.scala:142 states this itself: `//wait write miss no
allocate`). But the condition is written as `s1_req.opcode === PutFullData &&
s1_req.opcode === PutPartialData` — the same 3-bit field equal to two
different constants at the same time (PutFullData=0, PutPartialData=1), which
is **always false; the branch is dead code**. Consequence: on the
write-miss-no-allocate path mshr_wait is never set, and the way-occupancy
barrier that the Scheduler broadcasts to all MSHRs (Scheduler.scala:133) is
ineffective in this scenario — an MSHR can initiate a new allocation on a way
currently being evicted — a data race. In the same file, the same-kind
conditions at :103 and :218 are correctly written with `||`; :142 is an
isolated typo.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **SourceD**: the L2's "D-channel response source". It consumes the
  Directory's lookup results (hit/miss/dirty/way etc.), drives BankedStore
  reads and writes, generates TileLink D-channel responses
  (AccessAck/AccessAckData/HintAck), and, when a dirty victim line needs
  eviction, issues the writeback to memory via the a channel. Internally it is
  an 8-state FSM, stage_1…stage_8.
- **Write miss no allocate**: when a Put request misses and the victim line is
  not dirty, the L2 does not allocate a new line — the write data is passed
  through directly to memory via the a channel (SourceD.scala :274-278; for a
  Put, the a-channel data takes `s_final_req.data` rather than the BankedStore
  read-out).
- **mshr_wait**: a blocking signal output by SourceD and broadcast to all
  MSHRs at `Scheduler.scala:133`. Design intent (:137 comment): "used for
  kicking out victim way, to block premature potential miss request of victim
  way" — while a victim way is being evicted / passed through, block MSHRs
  from prematurely making new allocations on that way, preventing a new
  allocation and an in-flight eviction from trampling the same way.
- **TileLink opcodes**: PutFullData=0, PutPartialData=1, Get=4, Hint=5, etc. —
  3-bit encodings, all mutually distinct.

### 1.2 Design intent

stage_1 receives a request → miss and dirty: set mshr_wait and take the
dirty-line eviction path (:136-137, correct) → miss and not dirty (from MSHR):
enter stage_4, set busy, **and likewise set mshr_wait** (the design intent of
:138-144) to block the victim way — but the always-false condition at :142
means the latter never happens.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the miss branch of stage_1** (`:135-145`, ★ the hazard is at :142):

```scala
when(!s1_req.hit) {
  when(s1_req.dirty) {
    mshr_wait_reg := true.B //used for kicking out victim way, to block premature
                            //potential miss request of victim way    // :137 correct
  }.otherwise { //miss but not dirty?? from mshr
    stateReg := stage_4
    busy := true.B
    tobedone := false.B
    when(s1_req.opcode === PutFullData && s1_req.opcode === PutPartialData) { // ★ always false
      mshr_wait_reg := true.B                     // :143 dead code
    }                                             // :142 comment: //wait write miss no allocate
  }
}
```

**Construct 2: the arithmetic fact of always-falseness**: `s1_req.opcode` is a
3-bit UInt; PutFullData=0, PutPartialData=1. `x === 0.U && x === 1.U` is false
for every x. On the Lean side, `l2s_putput_and_false` confirms it by
exhaustion over all eight 3-bit values.

**Construct 3: cross-check points — the correct writing elsewhere in the same file** (`:103`, `:218`):

```scala
// :103 about_to_not_busy:
... Mux((!s_final_req.hit && (s_final_req.opcode === PutFullData ||
       s_final_req.opcode === PutPartialData)), io.a.fire && io.d.fire, io.d.fire) ...
// :218 stage_4:
when((!s_final_req.hit && (s_final_req.opcode===PutFullData ||
     s_final_req.opcode===PutPartialData)) || s_final_req.opcode===Hint) { ... }
```

The same-semantics "is PutFull or PutPartial" test is correctly written with
`||` at both :103 and :218 — the `&&` at :142 is not design intent; it is a
typo.

**Construct 4: the consumer side of mshr_wait** (`Scheduler.scala:133`):

```scala
m.io.mshr_wait := sourceD.io.mshr_wait   // broadcast to every MSHR as the way-occupancy barrier
```

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

1. A PutFullData/PutPartialData request misses in the L2, the victim is not
   dirty, and the request comes from an MSHR (write miss no allocate) →
   stage_1 takes the otherwise branch at :138-145;
2. The :142 condition is always false ⇒ `mshr_wait_reg` is not set (stays
   false);
3. SourceD enters stage_4 and waits for d/a fire to pass the write data
   through to memory (several cycles);
4. During this period the Scheduler broadcasts mshr_wait=false ⇒ the MSHRs
   have no barrier and can initiate a new allocation / new request on the same
   victim way;
5. The new allocation and the in-flight pass-through write operate on the
   same way concurrently — a data race (which wins, and how the directory and
   BankedStore states interleave, depends on concrete scheduling timing).

Control group: the miss-and-dirty path (:137) sets mshr_wait correctly — **of
the two sibling branches, one has the protection and the other does not**; the
barrier coverage has a hole.

### 3.2 Root cause

A logical-operator typo: `&&` should be `||`. The two opcode constants are
mutually exclusive, so the conjunction is always false — a classic case of
"the type system cannot catch it, review easily misses it, and simulation
needs a specific scenario to expose it". The two correct cross-checks in the
same file (:103/:218) prove this is an isolated typo, not a semantic
misunderstanding.

### 3.3 Harm and tolerability

- **Harm**: when a write miss runs concurrently with a victim eviction, an
  MSHR can initiate a new allocation on the way being evicted — a data race.
  Conclusion recorded verbatim from doc/03: it depends on concrete scheduling
  timing; the harm surface awaits quantification by Scheduler modeling.
- **Tolerability**: triggering requires the time windows of "write miss no
  allocate" and "a new allocation on the same way" to overlap; the window
  width = the number of cycles SourceD waits in stage_4 for d/a fire. Upstream
  simulation has not reported a corresponding failure, but the missing barrier
  is a structural fact (the always-false proof does not depend on timing).
  Rating: medium-high.

---

## 4. Lean Formal Evidence

`lean/Ventus/L2/SourceD.lean` (`l2sFsmNext` :218-268 faithfully translates
:129-255; :142 is modeled as `(op == l2opPutFull) && (op == l2opPutPartial)`)
【Lean machine-checked proof】:

- **`l2s_putput_and_false`**: `∀ op : BitVec 3, ((op == l2opPutFull) &&
  (op == l2opPutPartial)) = false` — a combinational-level fact by exhaustion
  over all 3-bit opcodes (native_decide); the always-falseness depends on no
  scenario assumption;
- **`l2sT_mshr_wait_put_miss`**: scenario witness — construct a "write miss no
  allocate" request (PutFull + !hit + !dirty + fromMem=true) into stage_1;
  one step later:
  (a) `mshrWaitReg = false` (the actual buggy behavior: not set);
  (b) `stateReg = stage_4` (the rest of the state transition is normal);
  (c) the fixed-semantic condition `(op==PutFull) || (op==PutPartial) = true`
  (cross-check: in this scenario it should have been set).

**Fixed version** (`lean/VentusF/MemL2.lean`):

- **`fmem_i37_fix_faithful`**: the fixed version's step semantics correspond
  exactly to the intent of "change && to ||";
- **`fmem_i37_witness_green`**: in the original witness scenario, mshr_wait is
  correctly set in the fixed version;
- `fmem_i3738_regress` / `fmem_i3738_step_regress`: regression equivalence
  (non-trigger paths agree step by step with the original).

---

## 5. Simulation Verification

**Status: ready-to-run, not executed in this environment** (the
ChiselSim/Verilator runs in doc/22 cover the I-5…I-33 range, not the L2
Directory/SourceD group I-35–I-38).

Directed test design (ChiselSim, SourceD module level): inject into the req
port a PutFullData-miss, dirty=false, from_mem=true request and observe the
`io.mshr_wait` output one cycle later — the original is expected to be
constantly 0, the fixed version is expected to be 1. To observe the downstream
harm (the race), a Scheduler+MSHR-level joint run is needed: while SourceD
waits in stage_4, issue an allocation on the same way via another MSHR and
observe the BankedStore/directory state interleaving.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: all write-miss-no-allocate transactions (Put miss,
  clean victim). This path is common in write-through/streaming-write
  workloads.
- **Why upstream did not find it**: mshr_wait is the conservative layer of a
  combined performance/correctness protection; the consequence of the missing
  barrier is an open race window rather than a guaranteed error — it only
  becomes visible when concurrent scheduling happens to trample, extremely
  hard for simulation coverage to hit.
- **Same-family entries**: I-40 (BankedStore same-cycle same-row read-write
  with no protection — likewise exposing the theme "insufficient protection
  during victim eviction"); I-39/I-41 (MSHR same-cycle priority family, whose
  reachability discharge depends on Scheduler-side invariants and shares the
  same modeling object as this entry's harm quantification).

---

## 7. Fix and Fix Verification

**Patch**: `i37-l2-sourced-putput.patch` (internal fix manifest; not released) — a
single-point change:

```scala
// :142
- when(s1_req.opcode === PutFullData && s1_req.opcode === PutPartialData) {
+ when(s1_req.opcode === PutFullData || s1_req.opcode === PutPartialData) { //wait write miss no allocate
+   // I-37 fix: was && (a conjunction of equalities to two different opcodes, always false),
+   // so mshr_wait_reg was never set → the blocking protection on the victim way was lost
    mshr_wait_reg := true.B
  }
```

**Fix verification**:

- Effectiveness 【Lean machine-checked proof】: `fmem_i37_fix_faithful` +
  `fmem_i37_witness_green` (mshr_wait correctly set in the write-miss-
  no-allocate scenario);
- Regression safety 【Lean machine-checked proof】: `fmem_i3738_regress` /
  `fmem_i3738_step_regress` — the fix only changes the reachability of the
  originally always-false branch; behavior on all other paths is step-by-step
  equivalent (the original branch was dead code, so the regression surface is
  naturally minimal);
- RTL-level patch regression: not run (same as §5; this entry is not in the
  suite executed in doc/22).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | SourceD.scala :142 (always-false conjunction), :137 (correct cross-check), :103/:218 (same condition correctly written with \|\|); Scheduler.scala:133 (mshr_wait broadcast) | Line-by-line check |
| Lean machine-checked proof | `l2s_putput_and_false` (exhaustive always-false over all opcodes) + `l2sT_mshr_wait_put_miss` (scenario witness) | Combinational universal + native_decide witness |
| Simulation reproduction | Ready-to-run (not executed in this environment; no record of this entry in doc/22) | Ready-to-run |
| Fix verification | i37 patch (single-point &&→\|\|); fixed version `fmem_i37_*` all green + regression equivalence | Machine-checked |

I-37 is an "always-false conjunction" typo: one 3-bit field equated to two
different constants simultaneously, turning the branch into dead code and
leaving the design-intent victim-way blocking barrier entirely absent on the
write-miss-no-allocate path. The always-falseness is pinned down by a
combinational-level exhaustive theorem (depending on no timing assumption);
the scenario witness pins down the concrete behavioral difference of "should
have been set but was not"; the fix is a single-character change with a
minimal regression surface.
