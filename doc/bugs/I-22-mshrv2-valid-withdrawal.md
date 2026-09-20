> English translation of the Chinese master `doc/bugs/I-22-MSHRv2响应回撤.md`. Translated 2026-09-13.

# I-22 Detailed Defect Analysis Report: MSHRv2's to_pipe.valid Violates NoWithdraw (Harmless in the Current Integration)

| Item | Content |
|---|---|
| ID | I-22 |
| Source location | `ventus/src/pipeline/MSHR.scala:106` (`io.to_pipe.valid := complete.orR && state===s_out`); `:53`/`:56`/`:62`/`:64` (every path entering and staying in s_out contains the same-cycle `io.to_pipe.ready`); instantiation site `LSU.scala:565` (Coalscer, inside LSUexe) |
| Type | Handshake protocol violation (Decoupled NoWithdraw) — latent defect |
| Severity | **Low (current integration) / Medium (evolution risk)**: the mechanism is real and machine-checked, but the entire downstream chain consumes only on same-cycle valid&&ready, so it is harmless in the current integration; the risk lies in a future insertion of a non-transparent consumer |
| Confirmation status | 【Confirmed (mechanism) / harmless in the current integration】 — the fixed version has been modeled and verified; the patch compiles as part of the 38-patch merged tree |
| Main evidence | 【Lean machine-checked proof】 violation witness (`mshr_noWithdraw_violated`) + mechanism symbolic theorems (`mshr_out_entry_needs_ready`/`mshr_withdraw`) + downstream-harmlessness chain theorems (`lsu2wb_rspFire_iff`/`lsu2wb_retract_safe`); 【direct source reading】 MSHR.scala:49-65/:106, writeback.scala:52-61, operandCollector.scala:623-624 checked line by line |
| Lean model | `lean/Ventus/Mem/MSHR.lean` (mechanism and witness); `lean/Ventus/Mem/LSU.lean` (LSU2WB pass-through verdict); fixed version `lean/VentusF/Schedule.lean` (the two fix variants fschMshrA/B) |
| Reproduction/patch | No standalone simulation reproduction case (a mechanism-level handshake violation with low simulation observability, see §5); patch `i22-mshrv2-nowithdraw.patch` (internal fix manifest; not released) |
| Related entries | I-26 (L1MSHR ready/st0 inconsistency, a handshake defect of the same family — its missRspOut, buffered by a 1-deep pipe queue, is instead handshake-compliant: a positive control); the RRArbiter remark (count=1 is not Irrevocable — same "downstream consumption discipline bears the load" family) |

---

## 0. Summary

The output channel `to_pipe` of MSHRv2 (pipeline/MSHR.scala, the LSU's in-flight memory-miss bookkeeping table, instance name Coalscer)
is a Decoupled interface, but its implementation violates the Decoupled
**NoWithdraw** convention (once valid is raised, it must not be lowered before the transfer fires):

- Every path entering s_out requires `to_pipe.ready=1` **in the same cycle** (:53/:56/:62/:64);
- valid rises only on the next cycle (:106, `complete.orR && state===s_out`, where state is a
  register);
- If ready then drops, the state machine at :62 falls back to s_idle — **valid is withdrawn
  without having fired**: an "already raised response" is retracted.

On the Lean side, `¬ NoWithdraw` is machine-proven with a concrete-trace witness (cycle 2 valid=1/ready=0/not fired → cycle 3 valid=0),
and the mechanism is nailed down by two symbolic theorems.

The downstream-harmlessness verdict chain (2026-08-27 full-chain review + machine-checked proof): the consumption chain LSU2WB (pure combinational pass-through)
→ writeback's 0-deep Queue → a count=1 Arbiter (no cross-cycle locking) → operandCollector
writeback ready constant 1 — **the entire chain samples and consumes only on same-cycle valid&&ready**; an MSHR entry is released only
on fire, the complete bit persists, and s_idle can re-enter s_out to resend the same entry: nothing is lost or duplicated.
Hence the verdict: harmless in the current integration; a latent defect (broken-window condition = a future insertion of a non-transparent register stage or a
valid-sampling consumer). The fix (s_out exits only on fire) has been modeled, verified, and shipped as patch
i22 (defense-in-depth class); the fixing process also uncovered the companion pitfall that "the hold condition must use output_entry, not
valid_entry" (the naive fix deadlocks — caught by the machine proof `fschMshrA_sink`).

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **MSHR (Miss Status Holding Register)**: a hardware structure that keeps the ledger of "in-flight" memory requests.
  Ventus's LSU splits one memory instruction by address into several sub-requests sent to the DCache /
  ShareMem; MSHRv2 records one entry per in-flight instruction: the lane mask of responses received so far
  (currentMask), the data (data), and routing metadata (the tag carries wid/writeback flags, etc.).
- **Decoupled handshake and NoWithdraw**: Chisel's standard ready-valid interface. The convention: once the producer
  raises valid, before `valid && ready` (fire) occurs, **valid must hold and
  the payload must remain stable** (NoWithdraw + Stable). The consumer is entitled to rely on this convention — e.g.,
  sampling bits first and raising ready later, or latching valid into a register.
- **The MSHRv2 state machine**: s_idle (accepts allocation / fast path) → s_add (deferred allocation on
  same-cycle double fire) → s_out (a complete response is ready to output). 8 entries × 32 lanes; the sole instantiation site
  is LSU.scala:565, with downstream `io.lsu_rsp <> Coalscer.io.to_pipe` (:570).

### 1.2 Design Intent

Once an entry has collected all lane responses (complete), MSHRv2 sends the data via
to_pipe to LSU2WB → the writeback stage, and finally writes back to the register file. The state machine should leave
s_out and release the entry only after "the output has been accepted (fire)".

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: every path into s_out requires same-cycle ready=1** (`MSHR.scala:49-65`, ★ fault point):

```scala
when(state===s_idle){
  when(io.from_dcache.fire){
    ...
    }.elsewhen(io.to_pipe.ready && currentMask(...in...)==...){ // :53 fast path
      state := s_out
    }...
  }.elsewhen(complete.orR && io.to_pipe.ready){                  // :56
    state := s_out
  }...
}.elsewhen(state===s_out){
  when(io.to_pipe.ready && complete.bitSet(valid_entry, false.B).orR){  // :62 ★
    state:=s_out
  }.otherwise{state:=s_idle}                                            // :62 ★
}.elsewhen(state===s_add){
  when(io.to_pipe.ready && complete.orR){state:=s_out}.otherwise{state:=s_idle}  // :64
}
```

All four entry/hold conditions contain the **same-cycle** `io.to_pipe.ready` — the state machine treats
"ready to receive" as a precondition for "entering the output state".

**Construct 2: valid is derived from the registered state, one cycle late** (`MSHR.scala:106`):

```scala
io.to_pipe.valid := complete.orR && state===s_out    // :106
```

state is a register: the entry condition (including ready=1) holds at cycle T, and only at cycle T+1 is state=s_out and
valid raised. If ready drops at cycle T+1 (valid && ready does not hold, no fire),
the otherwise branch at :62 drives state back to s_idle — at cycle T+2 valid is lowered.
**valid is retracted without having fired: the NoWithdraw violation is established.**

**Construct 3 (why the downstream is harmless): the consumption chain is fully transparent**:

- LSU2WB (LSU.scala:490 onwards): pure combinational pass-through — ready/valid are derived directly from downstream,
  with no register stage at all;
- writeback.scala:52-59: `Queue.apply(io.in_x(i), 0)` — a **0-deep** queue, purely combinational;
- writeback.scala:60-61: `Module(new Arbiter(..., num_x))` — a count=1 Arbiter has no cross-cycle locking (under chisel 6.4.0 the lock registers are not generated);
- operandCollector.scala:623-624: `io.writeScalarCtrl.ready := true.B` /
  `io.writeVecCtrl.ready := true.B` — the writeback stage is always ready.

There is no consumer on the chain that "samples while valid is high and ready is low".

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

Violation sequence (i.e., the Lean witness trace `mshrTrWithdraw`):

1. Cycle 0: allocation — an entry is established for a memory instruction (from_addr/from_dcache fire);
2. Cycle 1: fast-path response complete (complete.orR=1) and to_pipe.ready=1 ⇒ enter s_out;
3. Cycle 2: state=s_out ⇒ valid=1; but ready=0 this cycle ⇒ **no fire**; :62 finds
   the hold condition false (ready=0) ⇒ next cycle returns to s_idle;
4. Cycle 3: state=s_idle ⇒ **valid=0** — valid is lowered without having fired.

Under Decoupled semantics, the valid retraction from cycle 2 to cycle 3 is a protocol violation: a compliant consumer
that sees valid=1 at cycle 2 is entitled to assume the response will remain until accepted.

Note that the entry itself is **not lost**: the `complete` bit persists, `used` is released only on fire, and after returning to
s_idle, :56 can re-enter s_out when ready recovers and resend the same entry. This is precisely the mechanism underlying "harmless
in the current integration" — but it is also the unintended behavior of "the response being raised and withdrawn repeatedly".

### 3.2 Root Cause

The state machine uses the handshake signal as a **state-transition enable** rather than a **commit point**: entering s_out on
same-cycle ready is an "optimistic entry" (betting that the next cycle will fire), but s_out's exit condition does not
hold valid when the bet is lost; instead it falls straight back to s_idle and withdraws. The correct form is for s_out to exit only on **fire**
(valid && ready) — once entered, the state must "honor the contract". The root cause is that the designer treated ready as
permission "to start outputting", conflating ready's instantaneous nature with valid's holding obligation.

### 3.3 Harm and Tolerability

- **Current integration: harmless (machine-checked downstream verdict chain)**. The consumption chain — LSU2WB pure combinational pass-through →
  0-deep Queue → count=1 Arbiter → writeback ready constant 1 — samples only on same-cycle
  valid&&ready throughout. When valid retracts, no consumption occurs; the entry is neither lost nor duplicated
  (used is released only on fire, complete persists, resend is possible).
- **Broken-window condition**: any future insertion into this chain of a non-transparent stage (a register latching valid/bits,
  a non-pipe queue of depth ≥1, a consumer that samples on valid), or any modification of LSU2WB's pure
  combinational structure, turns the withdrawal into a "lost response" (the consumer believes it already received it, or misses it) — at that point it becomes a
  correctness-level bug.
- **Tolerability verdict**: tolerable at present; rated Low (current) / Medium (evolution risk). The recommended fix is
  defense-in-depth (patch i22), classified in the internal fix manifest as Defense-in-depth
  (ISA-visible: No).

---

## 4. Lean Formal Evidence

**Mechanism and witness** (`lean/Ventus/Mem/MSHR.lean`, zero sorries, axiom audit archived;
native_decide theorems carry `Lean.ofReduceBool`):

- `mshr_noWithdraw_violated : ¬ Ventus.Base.Handshake.NoWithdraw
  (mshrTraceOf mshrTrWithdraw)` (MSHR.lean:701) — negates NoWithdraw over the concrete trace
  `mshrTrWithdraw` (:689; cycle 0 allocation → cycle 1 fast-path response with ready=1 →
  cycle 2 valid=1/ready=0, no fire → cycle 3 valid=0);
  the trace shape is pinned cycle by cycle by `mshrT_withdraw_witness` (:692, a four-way conjunction, native_decide);
- Mechanism symbolic theorems (arbitrary state, arbitrary input; cases on the FSM + simp):
  - `mshr_out_entry_needs_ready`: every path into s_out requires same-cycle
    `i.outReady = true` (a positive characterization);
  - `mshr_withdraw`: inside s_out, `outReady=false` ⇒ next-cycle valid is necessarily false
    (the withdrawal half).

**Downstream-harmlessness verdict chain** (2026-08-27 agent-11 full-chain review + machine-checked proof):

- `lsu2wb_rspFire_iff` (LSU.lean:1571): a three-way decomposition of LSU2WB's rsp.fire —
  consumption occurs only on same-cycle valid&&ready;
- `lsu2wb_retract_safe` (LSU.lean:1582): valid=1 and ready=0 ⇒ neither of the two writeback
  paths fires — **a valid retraction has no consumption side effect whatsoever**: the MSHR entry is neither consumed nor
  released;
- The purely combinational nature of the 0-deep Queue and the count=1 Arbiter is verified against the chisel 6.4.0 sources +
  direct reading of the wiring (writeback.scala:52-61, operandCollector.scala:623-624).

**Positive control**: L1MSHR, of the same MSHR family, buffers its missRspOut through a 1-deep pipe queue, so
NoWithdraw and Stable hold **unconditionally** (`l1m_rspOut_noWithdraw`/
`l1m_rspOut_stable`, L1MSHR.lean) — a control sample within the same codebase contrasting "output buffered through a queue" with
"FSM-driven output", corroborating that I-22's style is a local oversight rather than a convention.

---

## 5. Simulation Verification

**No standalone simulation reproduction was performed** (this entry has no ChiselSim/Verilator case; the two-channel
verdict summary table of doc/22 contains no I-22 row). Reasons and status:

- The defect is a **protocol-level** violation, not a data error — in the current integration (fully transparent downstream, writeback always
  ready), to_pipe.ready can in fact always be raised, so the violation sequence produces no
  observable consequence on the real whole machine; a module-level reproduction would need to artificially create ready backpressure and assert on the valid waveform;
- The mechanism is already nailed down by the Lean witness + symbolic theorems (§4), and the downstream harmlessness already has a machine-checked verdict chain;
- The patch itself was verified by mill compilation of the 38-patch merged tree (MILL_EXIT=0; the internal fix manifest note:
  agent-145 applied and compiled the full patch set, fixing an incorrect hunk-header line-count annotation
  in the i22 patch along the way; the hunk body was correct). Characterization: **machine proof sufficient; simulation ready-to-write** (if it is to be added, the targeted case would be:
  instantiate MSHRv2 at module level, pull to_pipe.ready low at cycle 2, and assert that cycle-3 valid holds —
  the original fails, the fixed version passes).

---

## 6. Upstream Impact Analysis

- **Impact surface**: the sole consumer of to_pipe is the LSU-internal LSU2WB→writeback chain,
  which is fully transparent; no third-party module relies on the persistence of this valid.
- **Nature of the risk**: an integration-contract risk (same family as the RRArbiter count=1 non-Irrevocable remark)
  — correctness depends on the uncodified consumption discipline that "the downstream always samples on fire".
  There is more than one instance of this style in the Ventus codebase (MSHRv2 is the LSU side's only Decoupled output
  driven directly by an FSM), and any future refactoring (pipelining, adding buffers) could change the consumption pattern.
- **Recommendation to upstream**: fix i22 is zero-risk defense-in-depth (its behavior is step-by-step equivalent to the original
  outside the trigger domain, see §7); it is recommended for submission with the defensive-patch batch.

---

## 7. Fix and Fix Verification

**Patch** (`i22-mshrv2-nowithdraw.patch` (internal fix manifest; not released),
the internal fix manifest: Defense-in-depth): the s_out exit at `MSHR.scala:62` is changed to be triggered **only by
fire**:

```scala
// Before the fix (:62):
when(io.to_pipe.ready && complete.bitSet(valid_entry, false.B).orR){state:=s_out}.otherwise{state:=s_idle}
// After the fix:
when(io.to_pipe.fire){
  state:=Mux(complete.bitSet(output_entry, false.B).orR, s_out, s_idle)
}.otherwise{state:=s_out}
```

**A companion finding from the fixing process (a demonstration of the value of fix verification)**: the naive fix (only changing ready to
fire, with the hold condition still using `valid_entry`) **deadlocks** — after the last entry fires,
valid_entry already points to some other free entry and differs from output_entry ⇒ the hold condition is wrongly judged true
⇒ s_out is never exited, and in s_out both the addr and dc ready paths die (a sink state). The fixed-version
model pins this down in two variants (`lean/VentusF/Schedule.lean`):

- Variant A (the wrong fix): `fschMshrA_sink`/`fschMshrA_sink_run` (s_out ∧ wrongly-judged hold
  ⇒ stuck forever, fully proved by induction) + numeric witness `fschMshrAT_deadlock`;
- Variant B (the correct fix, i.e., the patch): the hold condition uses `output_entry`.
  - `fschMshrB_no_withdraw`: NoWithdraw restored (symbolic level);
  - `fschMshrBT_withdraw_blocked`: the original violation witness trace no longer
    retracts on the fixed version (turns green);
  - `fschMshrB_no_sink_entry`: s_out ⇒ complete≠0 is an invariant (no sink state);
  - `fschMshrB_run_eq_orig`: trace step-by-step equivalent to the original model on non-triggering input sequences
    (regression-safe).

Patch engineering quality: the 38-patch merged tree compiles; i22's hunk-header line-count annotation was wrong and has been corrected in
the the internal fix manifest note (the hunk body was correct; application results unaffected).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | MSHR.scala:53/:56/:62/:64/:106, writeback.scala:52-61, operandCollector.scala:623-624 checked line by line | Three source-file sites consistent |
| Lean machine-checked proof | `mshr_noWithdraw_violated` (witness negation) + `mshr_out_entry_needs_ready`/`mshr_withdraw` (mechanism symbolic) + `lsu2wb_rspFire_iff`/`lsu2wb_retract_safe` (downstream-harmlessness chain) | Witness + symbolic over arbitrary states |
| Positive control | L1MSHR missRspOut passes through a 1-deep pipe queue; `l1m_rspOut_noWithdraw` holds unconditionally | Machine-checked |
| Simulation | No standalone case (protocol-level violation; no observable consequence in the current integration); ready-to-write | — |
| Fix verification | i22 patch (s_out exits only on fire); Lean variant-B theorem family + variant-A deadlock counterexample (evidence of the fix pitfall) + regression equivalence; 38-patch merged tree compiles | Machine-checked + compile-tested |

I-22 is a latent defect of the "literal handshake-protocol violation, with the downstream discipline bearing the load" type: the mechanism is real with complete machine-checked evidence,
the current integration is harmless because the consumption chain is fully transparent, and the fix is defense-in-depth. The fixing process also yielded a
methodological demonstration — **the fix itself needs verification** (the naive fire-ification introduces a deadlock,
and `fschMshrA_sink` killed that wrong approach before the patch landed).
