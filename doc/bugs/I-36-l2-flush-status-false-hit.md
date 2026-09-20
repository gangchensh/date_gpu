> English translation of the Chinese master `doc/bugs/I-36-L2-flush期status污染假命中.md`. Translated 2026-09-13.

# I-36 Detailed Defect Analysis Report: L2 Directory write.valid pollutes status during flush — false hit

| Item | Content |
|---|---|
| ID | I-36 |
| Source location | `ventus/src/L2cache/Directory_test.scala:192` (the status write branch uses `io.write.valid` instead of `io.write.fire`); related points `:169/:264` (tag SRAM write enable uses fire), `:272` (write.ready is 0 during flush), `Scheduler.scala:227` (write.valid held high by the MSHR waiting for ready) |
| Type | Functional bug (handshake-semantics misuse: valid/fire confusion) — false-hit family |
| Severity | **High** (when flush and a miss allocation run concurrently, the status and tag arrays desynchronize, producing false hits on never-allocated lines and Get returning wrong data) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + patch exists (this entry not covered by RTL regression) |
| Primary evidence | 【Lean machine-checked proof】`l2dT_write_during_flush_corrupts` / `l2dT_flush_false_hit`; 【direct source reading】line-by-line check of Directory_test.scala :187-195, :264-272, Scheduler.scala:227-231 |
| Lean model | Original `lean/Ventus/L2/Directory.lean`; fixed version `lean/VentusF/MemL2.lean` (`fmem_i36_*`) |
| Reproduction/patch | ChiselSim ready-to-run (not executed in this environment, see §5); patch `i36-l2-directory-write-fire.patch` (internal fix manifest; not released) |
| Related entries | I-23 (ICache false hit, same family), I-35 (flushCount stuck, same file), I-29 (DCache-side same-kind array desynchronization) |

---

## 0. Abstract

In the update logic of the L2 Directory's status array (valid/dirty bits), the
enable condition of the refill write branch is `io.write.valid`
(Directory_test.scala:192), while the write enable of the tag SRAM (cc_dir) is
`io.write.fire` (:169, :264). Under Decoupled handshake semantics, valid can be
held high while ready=0 — during flush, `io.write.ready := wipeDone &&
!flush_issue_reg` (:272) is 0, and the upstream Scheduler holds the MSHR's
directory write request with valid high waiting for ready
(Scheduler.scala:227). As a result, during flush every pending directory write
request causes **status to be set valid while the tag array is not written** —
the two arrays desynchronize. After the flush ends, a hit determination on the
polluted way reads the wipe-residual tag=0, so a read of a tag=0 address (a
line that was never allocated) **false-hits** and Get returns wrong data. This
belongs to the same "false hit" family as I-23 (ICache false hit): the
directory claims a line is valid and its tag matches, when in fact the line
was never allocated.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **The Directory's two stores**: the tag array `cc_dir` (SRAM, 64 sets × 16
  ways, holding 19-bit tags) and the status array `status_reg` (registers,
  holding per-way valid/dirty). Hit determination (:239-242) = some way's tag
  matches **and** status.valid is true — **the two arrays must be updated in
  sync**, otherwise the basis of the determination is broken.
- **Decoupled handshake**: `fire = valid && ready`. Data actually transfers
  only on a fire cycle; valid may legitimately be held high while ready=0
  (the source waits) — this is legal and common.
- **The io.write channel**: after an MSHR completes a refill (data fetched
  back from memory), it writes a directory entry into the Directory via the
  Scheduler (Scheduler.scala:227-231: `directory.io.write.valid :=
  schedule.dir.valid`, bits being way/set/tag).
- **Directory refuses writes during flush**: :272 `io.write.ready := wipeDone
  && !flush_issue_reg` — while flush is in progress ready=0; directory write
  requests stay pending and land only after the flush ends.

### 1.2 Design intent

Refill completes → Scheduler raises write.valid → Directory accepts the write
(fire) → **on the same cycle** the tag SRAM is written with the new tag and
status is set valid — the two arrays stay in sync, and accesses to that tag
hit from then on.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the status write branch uses valid** (`:187-195`, ★ the hazard is at :192):

```scala
}.elsewhen(io.result.valid && io.result.bits.hit && ...) {      // :187 hit sets dirty
  status_reg(i).dirty(j) := true.B
}.elsewhen(io.result.valid && !io.result.bits.hit && ... ) {    // :189 replacement clears valid
  status_reg(i).valid(j) := false.B
  status_reg(i).dirty(j) := false.B
}.elsewhen(io.write.valid && io.write.bits.set===i.asUInt &&    // :192 ★ should be fire
           io.write.bits.way===j.asUInt) {
  status_reg(i).valid(j) := true.B                               // :193 sets valid
  status_reg(i).dirty(j) := false.B                              // :194
}
```

**Construct 2: the tag SRAM write enable uses fire** (`:169`, `:264-268`):

```scala
val wen = io.write.fire                                          // :169
...
cc_dir.io.w.req.valid := wen_new                                 // :264, wen_new = ... || io.write.fire
```

The tag array is **written only on a fire cycle** — while valid is held high
with ready=0, the tag is not written. Of the two arrays' write conditions, one
is valid and the other is fire; during flush the two conditions diverge.

**Construct 3: during flush ready=0 while valid stays high** (`:272` + `Scheduler.scala:227`):

```scala
// Directory_test.scala:
io.write.ready := wipeDone && !flush_issue_reg                   // :272 refuses during flush

// Scheduler.scala:
directory.io.write.valid := schedule.dir.valid                   // :227 MSHR holds it waiting for ready
```

After an MSHR completes a refill, it holds the directory write request with
valid high (the Scheduler side has no withdrawal mechanism); during flush
ready=0 and the request legitimately stays pending — for every cycle it stays
pending, the :192 branch hits for one cycle and status is set valid.

**Construct 4: hit determination and the wipe-residual tag=0** (`:239-242`, `:122-124`, `:266-267`):

The reset wipe phase writes 0 to the entire tag SRAM (:267 `data=...0.U`) and
clears status to invalid. The polluted way's tag is still 0 while valid is
erroneously set to 1 ⇒ a read of a tag=0 address makes the hit determination
(tag equal ∧ valid) hold — **false hit**.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

1. An MSHR refill completes; the Scheduler raises `directory.io.write.valid`
   (waiting to commit);
2. flush starts; `flush_issue_reg=1` ⇒ write.ready=0; the request stays
   pending;
3. On every cycle of the pending period the :192 branch hits:
   `status_reg(set).valid(way) := true.B` — **status pollution**, while cc_dir
   is not written because fire does not hold (the tag keeps its old value /
   wipe-residual 0);
4. When flush ends and the write finally fires, the tag is written — but if
   the write request is overwritten / its timing is missed, or if an access
   arrives before the fire, the two arrays are in a desynchronization window;
5. After flush, an access to tag=0 / set = the polluted set: the hit
   determination hits the polluted way (valid=1 ∧ tag=0 equal) → the
   Directory reports hit → Get takes the hit path and reads that way's data
   from BankedStore — **a never-allocated line returns garbage/stale data**.

Trigger condition: a flush concurrent with an MSHR refill directory write —
flush occurs when multiple warps complete and the L1 DCache flushes; refill is
normal traffic; the overlap window genuinely exists.

### 3.2 Root cause

valid/fire confusion: the status write branch should use `io.write.fire` like
every other consumer (state updated only when the transaction actually
completes), but it was written as `io.write.valid` (updated as soon as the
request intent exists). Elsewhere in the same file, `about_replace` at :284
and `timely_hit` at :286 both correctly use `io.write.fire` — :192 is an
isolated miswrite. This kind of error looks "reasonable in intent" when
reading the module in isolation (you do want to write when valid is high); it
only becomes visible when combined with the value domain of ready (0 during
flush).

### 3.3 Harm and tolerability

- **Harm**: a false hit is a data-correctness-level defect — returning hit +
  stale/garbage data for an address that was never allocated, with no error
  reported whatsoever. Same family as I-23 (ICache LFSR false hit), but I-36's
  pollution is **deterministic** (a held-high valid necessarily pollutes); it
  does not need LFSR collision probability.
- **Tolerability**: requires a flush concurrent with a refill directory write
  plus a subsequent access to the tag=0 address range. tag=0 corresponds to
  the low range of physical addresses (depending on the address map); whether
  it is frequently accessed depends on the workload; but once hit, the wrong
  data is silent. Rating: **High**.

---

## 4. Lean Formal Evidence

`lean/Ventus/L2/Directory.lean` (around `l2dStatusNext` :391, the b5 branch
faithfully models :192's valid semantics via `inp.writeValid` — the bug enters
the model as-is). All `native_decide` witnesses 【Lean machine-checked proof】:

- **`l2dT_write_during_flush_corrupts`**: wiped state + flush pulse + 1 idle
  cycle + a write request held during flush (way=7, set=9, tag=0x77) → three
  components pinned down simultaneously:
  (a) `status(9,7).valid = true` (status polluted);
  (b) `cc_dir.mem(9,7) = 0` (tag array not written, keeps the wipe residual);
  (c) on that cycle `writeFire = false` (indeed no fire) — the mechanism chain
  is complete;
- **`l2dT_flush_false_hit`**: on the polluted end state `l2dCorrupt`, reading
  tag=0/set=9 (a never-allocated address) → `resultValid = true ∧ resultHit =
  true ∧ resultWay = 7` — the false hit lands on the polluted way7. For a Get
  request this returns wrong data.

**Fixed version** (`lean/VentusF/MemL2.lean`):

- **`fmem_i36_no_corrupt`**: in the same scenario, the fixed version's status
  is not polluted;
- **`fmem_i36_false_hit_gone`**: in the same access, the false hit disappears
  in the fixed version;
- `fmem_i36_regress` / `fmem_i36_status_regress` /
  `fmem_i3536_step_regress_others`: regression equivalence (behavior on fire
  cycles agrees with the original; step-by-step equivalence on non-trigger
  paths).

---

## 5. Simulation Verification

**Status: ready-to-run, not executed in this environment** (the
ChiselSim/Verilator runs in doc/22 cover the I-5…I-33 range, not the L2
Directory/SourceD group I-35–I-38).

Directed test design (ChiselSim, Directory_test module level): after the reset
wipe completes, trigger a flush (while flush_issue_reg is up, write.ready=0);
during it hold one write.valid (way=w, set=s, tag=T≠0) for several cycles then
deassert it; after flush ends and ready recovers, issue a read request for
tag=0/set=s and observe result.hit — the original is expected to give hit=true
(false hit), the fixed version is expected to give miss. Additionally, compare
with a read of tag=T/set=s: if the write request eventually fires and commits,
it hits normally, distinguishing "pollution already healed" from the
"desynchronization window".

---

## 6. Upstream Impact Analysis

- **Trigger surface**: overlap of flush (kernel boundary) with an MSHR refill
  directory write. The L2 is shared chip-wide; during flush the other SMs'
  memory refills proceed as usual — the overlap is not a corner case.
- **Why upstream did not find it**: the pollution itself is silent (the status
  array has no observer); the harm only becomes visible when "a later access
  happens to hit the polluted way with tag=0"; and if the write request
  fires and commits normally after flush ends, part of the pollution is healed
  — a window-type fault, hard for simulation coverage to hit.
- **Same-family entries**: I-23 (ICache false hit, LFSR collision,
  probabilistic); I-29 (DCache victim writeback data pollution); I-35
  (flushCount stuck in the same file — shares with this entry the scenario
  prefix "directory unavailable during flush"; the two can stack in the same
  window).

---

## 7. Fix and Fix Verification

**Patch**: `i36-l2-directory-write-fire.patch` (internal fix manifest; not released) — a
single-point change:

```scala
// :192
- }.elsewhen(io.write.valid && io.write.bits.set===i.asUInt && io.write.bits.way===j.asUInt) {
+ }.elsewhen(io.write.fire  && io.write.bits.set===i.asUInt && io.write.bits.way===j.asUInt) { // I-36 fix
```

valid → fire; the status and tag arrays resume same-cycle synchronized
updates.

**Fix verification**:

- Effectiveness 【Lean machine-checked proof】: `fmem_i36_no_corrupt` /
  `fmem_i36_false_hit_gone` (the original witness scenario goes green on the
  fixed version);
- Regression safety 【Lean machine-checked proof】: `fmem_i36_regress` /
  `fmem_i36_status_regress` / `fmem_i3536_step_regress_others` (under fire
  semantics the difference from the original is confined exactly to cycles
  where "valid is held but no fire"; normal paths are step-by-step
  equivalent);
- RTL-level patch regression: not run (same as §5; this entry is not in the
  suite executed in doc/22).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Directory_test.scala :192 (valid misused), :169/:264 (tag uses fire), :272 (ready=0 during flush); Scheduler.scala:227 (valid held high) | Line-by-line check |
| Lean machine-checked proof | `l2dT_write_during_flush_corrupts` (three-component mechanism) + `l2dT_flush_false_hit` (false hit end-to-end) | native_decide witnesses |
| Simulation reproduction | Ready-to-run (not executed in this environment; no record of this entry in doc/22) | Ready-to-run |
| Fix verification | i36 patch (single-point valid→fire); fixed version `fmem_i36_*` all green + regression equivalence | Machine-checked |

I-36 is a textbook case of handshake-semantics misuse (valid/fire confusion):
two arrays that must be updated in sync use valid and fire respectively as
their write enables, desynchronizing inside the window where "valid is
legitimately held while ready=0", and manufacturing a deterministic false hit
on never-allocated lines. The value of the formal model is turning the
"window" into a concrete trace — the three pollution components and the false
hit are each pinned down by a native_decide witness.
