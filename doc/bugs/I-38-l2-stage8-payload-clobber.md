> English translation of the Chinese master `doc/bugs/I-38-L2-stage8响应payload覆盖.md`. Translated 2026-09-13.

# I-38 Detailed Defect Analysis Report: L2 SourceD stage_8 response payload clobbered under backpressure (decoupled violation)

| Item | Content |
|---|---|
| ID | I-38 |
| Source location | `ventus/src/L2cache/SourceD.scala:82` (`s_final_req = RegNext(s1_req)` with no enable), `:193-196` (a last-entry clean flush enters stage_8 and clears `busy := false.B` on the same cycle), `:105` (`io.req.ready := !busy`), `:264-269` (the d-channel payload is taken combinationally from s_final_req) |
| Type | Functional bug (Decoupled handshake violation: bits unstable while valid && !ready) — dual failure mode of dropped/duplicated responses |
| Severity | **High** (when d-channel backpressure genuinely exists, the flush completion signal HintAck is lost; the upper-level waiter hangs or its bookkeeping is corrupted) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + patch exists (this entry not covered by RTL regression) |
| Primary evidence | 【Lean machine-checked proof】`l2sT_stage8_accepts_req` / `l2sT_stage8_payload_clobber`; 【direct source reading】line-by-line check of the wiring chain SourceD.scala :82/:105/:193-196/:247-254/:264-269 (re-reviewed and confirmed by the main session, doc/03) |
| Lean model | Original `lean/Ventus/L2/SourceD.lean`; fixed version `lean/VentusF/MemL2.lean` (`fmem_i38_*`) |
| Reproduction/patch | ChiselSim ready-to-run (not executed in this environment, see §5); patch `i38-l2-sourced-stage8.patch` (internal fix manifest; not released) |
| Related entries | I-35 (Directory side of the same flush chain), I-52 (fudian output-side bits switching under backpressure, same family of decoupled violation), I-22 (MSHRv2 NoWithdraw violation) |

---

## 0. Abstract

A last-entry clean flush (Hint && last_flush && !dirty) in the L2 SourceD
goes directly from stage_1 into stage_8 (waiting for d-channel ready to send
the HintAck), but on the very cycle of entry it clears `busy := false.B`
(SourceD.scala:193-196). `io.req.ready := !busy` (:105) therefore goes high,
and a new request can fire in; meanwhile `s_final_req = RegNext(s1_req)` (:82)
is a register with **no enable**, following s1_req every cycle — one cycle
after the new request fires, s_final_req is overwritten with the new request's
contents. The d-channel payload (source/opcode/size/data/address at :264-269)
is taken combinationally from s_final_req — **the payload of the pending
HintAck (d.valid=1 and d.ready=0) is clobbered by the new request**, directly
violating the Decoupled contract "bits remain stable while valid". The
consequence has two forms: the HintAck is lost (the flush completion signal
never reaches the upper level) + the new request's response is sent early and
will be sent again later (dropped and duplicated responses coexisting). Losing
the flush completion signal means the upper level waiting for flush completion
(the DCache's waitforL2flush flow) hangs or its bookkeeping is corrupted.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **SourceD and its 8-state FSM**: see §1.1 of the I-37 report. What matters
  here: stage_4 is responsible for sending responses/writebacks (waiting for
  d.fire/a.fire); **stage_8 = the "wait for d ready" parking state** — entered
  when a response has been decided upon but the d channel is backpressured;
  returns to stage_1 after d.fire.
- **HintAck and flush completion**: if the last entry (last_flush) of the
  Directory's flush scan is not dirty, no writeback is produced, but a HintAck
  response must still be given to the flush initiator as the "flush complete"
  signal — this is what the upper level (the L1 DCache's waitforL2flush) uses
  to decide that the flush has finished.
- **The Decoupled contract**: once valid is raised, until fire (valid &&
  ready), bits must remain stable and valid must not be withdrawn (NoWithdraw
  + Stable). The consumer may rely on this property to sample across multiple
  cycles.
- **busy and req.ready**: `io.req.ready := !busy` (:105) — busy is SourceD's
  "currently processing a request" flag; while busy=1 new requests are
  rejected. The `about_to_not_busy` comment at :103 shows the designer
  considered the boundary-cycle semantics of exiting.

### 1.2 Design intent

A last-entry clean flush → stage_1 determination (Hint && last_flush) → enter
stage_8 to send the HintAck → if d is backpressured, wait in stage_8
(**during which it should stay busy and reject new requests**) → after d.fire,
return to stage_1 and clear busy. This is consistent with the design in :103's
`about_to_not_busy` of `(stateReg === stage_8) && io.d.fire`: stage_8 is
exited by d.fire **and** busy is cleared there — i.e. "busy should stay 1
while waiting for d".

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the enable-less s_final_req** (`:81-82`, ★ hazard one):

```scala
val s1_req = Mux(io.req.fire, io.req.bits, s1_req_reg)  // stall if busy   // :81
val s_final_req = RegNext(s1_req)  ///                                      // :82 ★
```

s_final_req latches s1_req unconditionally every cycle — **there is no enable
of any kind to "hold while pending"**. The d-channel payload is taken
combinationally from it (construct 4); its stability is the payload's
stability.

**Construct 2: a last-entry clean flush enters stage_8 and clears busy on the same cycle** (`:192-196`, ★ hazard two):

```scala
}.elsewhen(s1_req.opcode===Hint && s1_req.last_flush){ //last flush but not dirty.
  stateReg:= stage_8
  busy := false.B          // ★ :194 — not busy while waiting for d
  tobedone := false.B
  mshr_wait_reg := false.B
}
```

Compare with stage_8's exit (`:247-254`): `when(io.d.fire){ stateReg :=
stage_1; busy := false.B; ...}` — busy is cleared at exit, consistent with the
:103 `about_to_not_busy` design. **Clearing busy at entry coexists with
clearing busy at exit**: the entry-side clearing is the wrong one.

**Construct 3: req.ready wired straight to busy** (`:105`):

```scala
io.req.ready := !busy   // || about_to_not_busy
```

busy=0 ⇒ req.ready=1 ⇒ during the stage_8 wait, new requests are accepted.

**Construct 4: the d payload taken combinationally from s_final_req** (`:264-269`):

```scala
io.d.valid  := ((stateReg===stage_4 || stateReg===stage_8) &&
               !(s_final_req.opcode===Hint && !s_final_req.last_flush))   // :264
io.d.bits.source := s_final_req.source                                     // :265
io.d.bits.opcode := Mux(s_final_req.opcode===Get, AccessAckData,
                    Mux(s_final_req.last_flush, HintAck, AccessAck))      // :266
io.d.bits.size    := s_final_req.size                                      // :267
io.d.bits.data    := Mux(s_final_req.opcode===Get, ..., 0.U...)            // :268
io.d.bits.address := params.expandAddress(s_final_req.tag, ...)            // :269
```

d.valid stays high throughout stage_8 (until d.fire); if s_final_req is
overwritten during that time, every payload field changes on that cycle — a
decoupled violation.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

1. A last-entry clean flush arrives at stage_1 → enters stage_8, `busy :=
   false` (:193-196);
2. During stage_8, d.valid=1 (:264), payload = this flush request's HintAck
   (source = the flush initiator);
3. While d.ready=0 (backpressure): `req.ready = !busy = 1` (:105) → a new
   request fires;
4. One cycle after the fire: s1_req = the new request's bits (:81), and
   s_final_req is overwritten accordingly (:82);
5. **d.valid is still 1 and d.ready still 0, but the payload has become the
   new request's response** (e.g. if the new request is a Get hit, the payload
   becomes AccessAckData + the new source) — the HintAck disappears from the
   bus (the loss form);
6. When the d channel recovers, the consumer receives the new request's
   response (sent early); and the new request itself will go through the
   response flow again in the FSM (the duplication form) — **one loss and one
   duplication**;
7. The flush initiator (the L1 DCache's waitforL2flush) never receives the
   HintAck → it hangs, or it mistakes someone else's response for the HintAck
   → bookkeeping corrupted.

Trigger condition: flush completion coincides with d-channel backpressure + a
new request arriving in the same window. Downstream of the d channel is shared
arbitration (multiple masters contending for the D channel); the backpressure
genuinely exists.

### 3.2 Root cause

The superposition of two independent choices: (a) :194 clears busy when
entering stage_8 (inconsistent with the exit-side design at :103/:248 — the
designer's own `about_to_not_busy` says stage_8 should be exited by d.fire
with busy cleared there; clearing busy at entry breaks the "stay busy while
waiting" invariant); (b) :82's enable-less s_final_req (implicitly assuming
"no new request can come in while pending", which (a) breaks). Fixing either
one plugs the hole (§7 takes (a)).

### 3.3 Harm and tolerability

- **Harm**: loss of the flush completion signal → the upper level hangs (the
  DCache invalidate flow waiting for flush completion stalls, which can
  indirectly block warp scheduling); meanwhile the new request's response is
  dropped/duplicated, so consumers that keep accounts by source (the L1
  MSHR/Coalscer family) get bookkeeping mismatches. Both correctness and
  liveness level.
- **Tolerability**: triggering needs the three-way overlap of "last-entry
  clean flush + d backpressure + new request in the same window". A
  last-entry clean flush is the common case (most lines are not dirty); d
  backpressure depends on downstream arbitration load. A genuinely reachable
  timing window. Rating: **High**.

---

## 4. Lean Formal Evidence

`lean/Ventus/L2/SourceD.lean` (`L2sState.sFinalReq` modeled per :82 as an
enable-less RegNext; the FSM's :193-196 entry into stage_8 clearing busy is
modeled as-is). All native_decide witnesses 【Lean machine-checked proof】:

- **`l2sT_stage8_accepts_req`**: machine-checked proof that during stage_8
  `reqReady = true` and a new request is captured — the premise fact "new
  requests are still accepted while waiting" is pinned down;
- **`l2sT_stage8_payload_clobber`**: a three-cycle end-to-end witness —
  in0: a flush request (Hint, last_flush, source=0xF1) enters;
  cycle 1 (stage_8, d.ready=0): `dValid = true ∧ dOpcode = HintAck ∧
  dSource = 0xF1` (the pending HintAck, not fired);
  on the same cycle a new Get request (source=0xA5) fires in;
  cycle 2: `dValid = true ∧ dOpcode = AccessAckData ∧ dSource = 0xA5` —
  **while valid stays high, the payload is rewritten from HintAck(0xF1) to
  AccessAckData(0xA5)** — the decoupled violation and the dual form of
  "HintAck lost + response sent early" pinned down in one stroke.

Normal-path baselines (control group, proving the violation comes from this
mechanism and not from model noise):
`l2sT_trace_read_hit` / `l2sT_trace_write_hit` / `l2sT_trace_miss_clean` /
`l2sT_trace_miss_dirty` / `l2sT_trace_write_miss_noalloc` /
`l2sT_trace_flush_last_dirty` — for each form, "responses neither dropped nor
duplicated".

**Fixed version** (`lean/VentusF/MemL2.lean`):

- **`fmem_i38_fix_faithful`**: the fixed version (entering stage_8 keeps
  busy=true) corresponds exactly to the design intent (the :103
  about_to_not_busy semantics);
- **`fmem_i38_witness_green`**: in the original witness scenario, the HintAck
  stays stable until fire in the fixed version;
- `fmem_i3738_regress` / `fmem_i3738_step_regress`: regression equivalence
  (backpressure-free normal paths agree step by step with the original).

---

## 5. Simulation Verification

**Status: ready-to-run, not executed in this environment** (the
ChiselSim/Verilator runs in doc/22 cover the I-5…I-33 range, not the L2
Directory/SourceD group I-35–I-38).

Directed test design (ChiselSim, SourceD module level): inject a
Hint+last_flush request (source=S1); from the next cycle pull d.ready low for
2+ cycles, and during that window inject one Get hit request (source=S2);
record d.valid/d.bits cycle by cycle. Original expectation: d.valid stays high
but d.bits flips from HintAck/S1 to AccessAckData/S2 (the violation is
observable); fixed-version expectation: req.ready is 0 during stage_8 (new
requests rejected), and d.bits stays stable at HintAck/S1 until d.ready goes
high and fires.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: flush completion signals (a last-entry clean flush is
  the most common finishing form of a flush — most lines are not dirty) ×
  d-channel backpressure (downstream shared arbitration) × concurrent new
  requests. The three genuinely overlap under multi-SM high load + kernel-
  boundary flush.
- **Why upstream did not find it**: it requires d backpressure to land exactly
  on the stage_8 window; the d-channel consumer in upstream test environments
  may be constantly ready (consuming immediately), so the backpressure branch
  is never exercised.
- **Same-family entries**: I-52 (the fudian ScalarFPU output side switches
  bits under backpressure — an instance of the same decoupled-violation
  pattern in the FPU wrapper layer); I-22 (MSHRv2 to_pipe NoWithdraw violation
  — valid withdrawal rather than bits flipping); I-35 (Directory side of the
  same flush chain — when the two stack, the flush path is broken at both
  ends).

---

## 7. Fix and Fix Verification

**Patch**: `i38-l2-sourced-stage8.patch` (internal fix manifest; not released) — keep busy
when entering stage_8:

```scala
}.elsewhen(s1_req.opcode===Hint && s1_req.last_flush){ //last flush but not dirty.
  stateReg:= stage_8
- busy := false.B
+ // I-38 fix: busy must be kept while stage_8 waits for d.ready — otherwise req.ready goes high,
+ // a new request fires and rewrites s_final_req, and the pending HintAck payload is clobbered
+ // (consistent with the :103 about_to_not_busy design: stage_8 is exited by d.fire, which clears busy)
+ busy := true.B
  tobedone := false.B
  mshr_wait_reg := false.B
}
```

(An equivalent alternative: add an enable to s_final_req so it updates only
when not pending — the patch takes the keep-busy option: a one-line change,
consistent with the existing design at :103/:248, minimal regression surface.)

**Fix verification**:

- Effectiveness 【Lean machine-checked proof】: `fmem_i38_fix_faithful` +
  `fmem_i38_witness_green` (in the original witness scenario the HintAck stays
  stable until fire);
- Regression safety 【Lean machine-checked proof】: `fmem_i3738_regress` /
  `fmem_i3738_step_regress` — keeping busy only affects the combination
  "stage_8 + new request arrives" (where the original behavior was a
  violation); backpressure-free paths are step-by-step equivalent;
- RTL-level patch regression: not run (same as §5; this entry is not in the
  suite executed in doc/22).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | SourceD.scala :82 (enable-less RegNext), :105 (req.ready=!busy), :193-196 (busy cleared on entering stage_8), :247-254 (busy cleared at exit), :264-269 (payload taken combinationally from s_final_req), :103 (about_to_not_busy design cross-check) | Line-by-line check |
| Lean machine-checked proof | `l2sT_stage8_accepts_req` (premise pinned down) + `l2sT_stage8_payload_clobber` (payload flip witness, HintAck 0xF1→AccessAckData 0xA5) + 6 normal-path control theorems | native_decide trace witnesses |
| Simulation reproduction | Ready-to-run (not executed in this environment; no record of this entry in doc/22) | Ready-to-run |
| Fix verification | i38 patch (keep busy in stage_8, single line); fixed version `fmem_i38_*` all green + regression equivalence | Machine-checked |

I-38 is a textbook instance of a decoupled-contract violation: the busy flag
is wrongly released when entering the wait state, breaking the implicit
invariant "reject new requests while waiting", and the enable-less payload
register is then overwritten by the new request — the pending response's
payload changes in full view on the bus. Its harm (loss of the flush
completion signal) strikes directly at the finishing step of the coherence-
maintenance path; the fix is consistent with the designer's own
about_to_not_busy semantics and lands in one line.
