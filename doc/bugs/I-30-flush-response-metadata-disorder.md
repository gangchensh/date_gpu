> English translation of the Chinese master `doc/bugs/I-30-flush响应错乱与丢失.md`. Translated 2026-09-13.

# I-30 Detailed Defect Analysis Report: DCache flush/invalidate response metadata disorder and loss (memRspIsFluOrInv lacks a valid qualifier)

| Item | Content |
|---|---|
| ID | I-30 |
| Source location | `ventus/src/L1Cache/DCache/DCache.scala:413` (definition of `memRspIsFluOrInv`, **without a deq.valid qualifier**; the Lean model header comment and doc/03 record it as :425/:544, referring to the same definition line — this report follows the actually measured file line :413); erroneous clearing sites `:423-427` (waitforL2flush) and `:429-433` (waitforL2flush_st2); the sole response production point `:754` (`coreRsp_Q.io.enq.valid := coreRsp_st2_valid || (memRspIsFluOrInv && memRsp_Q.io.deq.fire)`); ghost pre-staging `:695-699`; collateral erroneous clearing `:769-773` (flushL2_Reg); downstream `pipeline/MSHR.scala:50-71` (Coalscer bookkeeping by instrId) |
| Type | Functional bug (response protocol violation: a response carrying another instruction's instrId / a response lost entirely → bookkeeping disorder or hang) |
| Severity | **High** (once triggered, bookkeeping disorder/hang; flush/invalidate frequency is low — CTA boundaries, AMO trailing release — but cannot be masked by upper layers) |
| Confirmation status | 【Confirmed】 (machine-checked Lean proof closed); simulation side: initial run did not pass → diagnosed as a **Class III test-stub defect** → after fixing the stub, the companion defect **I-48** was exposed (see §5/§7) |
| Primary evidence | 【Machine-checked Lean proof】 `dcT_w2a_normal` (normal-path baseline) / `dcT_w2b_early_clear` / `dcT_w2b_stale_instrId` / `dcT_w2c_rsp_lost` (multi-cycle trace witnesses); 【simulation runs】 after stub fix, patched-RTL exposed the I-48 duplicate response (bisected to i30), and after the i48 fix the 38-patch tree went 2/2 green; 【direct source reading】 line-by-line verification of the above line numbers |
| Lean model | `lean/Ventus/Mem/DCache.lean` (§5 sequential core + §6 Q2 witness group); fixed version `lean/VentusF/Mem.lean` (§4) |
| Reproduction/patch | `repro/DCacheBugRepro.scala` (ChiselSim, Verilator backend); patch `i30-dcache-flush-rsp.patch` (internal fix manifest; not released) (two edit points); companion fix `i48-dcache-inv-dup-rsp.patch` |
| Related entries | **I-48** (the latent defect activated by this entry's fix, doc/03 I-48 / doc/22 "I-29/I-30 special session"), I-16 (AMO decode family, release-invalidate scenario), LSU Q15 (late-arriving invalidate response risk at the AMO aq&&rl tail), I-47 (same-family bookkeeping problem of flush completion having no return path) |

---

## 0. Summary

The DCache's coreRsp for flush/invalidate requests has an implicit single-point
dependency: the response is produced at exactly one moment — the cycle on which
L2's hintAck (memRsp d_opcode=2) is dequeued (:754). The response's metadata
(instrId/isWrite/activeMask) is taken from the head of coreRsp_st2, a 1-deep
queue; to ensure that the head contains exactly this flush's metadata when hintAck
arrives, the design uses a "ghost pre-staging" mechanism (:695-699: during the st1
stall, the flush pre-stages its entry into coreRsp_st2 every cycle, without
relying on fire).

The defect is that `memRspIsFluOrInv` (:413) **looks only at the d_opcode bits of
the head register, not at deq.valid**: after memRsp_Q has consumed the hintAck,
the head register **retains** a ghost image with d_opcode=2, and every subsequent
cycle is mistaken for "hintAck has arrived". The consequence chain (machine-checked
in Lean, form w2b): for the second and later flush/invalidate, one cycle after the
`waitforL2flush` flag is set it is **erroneously cleared by the retained ghost
image** → st1 releases early → ghost pre-staging stops → when the real hintAck
arrives, coreRsp_st2 has already been occupied by some intervening other response
→ **the flush's response carries another instruction's (e.g. a load's) instrId**.
Variant w2c: when the hintAck dequeues on the same cycle as another response, the
OR-merge at :754 causes the **flush response to be lost entirely**. Both paths are
amplified downstream by LSU's Coalscer (which does bookkeeping by instrId) into
bookkeeping disorder — another instruction's entry is polluted, or the target
instruction (e.g. the release-invalidate at the AMO tail) never completes and
hangs.

The handling process on the simulation side has independent value (doc/22
"I-29/I-30 special session"): the initial run did not pass and was diagnosed as a
**test-stub defect (Class III)** — the hand-written L2 stub never returned
AccessAck for writebacks, so the WSHR never drained; after fixing the stub the
flow ran through, whereupon it was discovered that **the i30 fix patch activates
the latent defect I-48** (duplicate inv response) — baseline's "normal" appearance
itself depends on the masking of this entry's w2b bug by erroneous clearing. After
I-48 was fixed by the i48 patch, the 38-patch merged tree regression went 2/2
green.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **flush / invalidate**: at a CTA boundary (WG completion) or at an AMO trailing
  release, the SM asks the DCache to write dirty lines back to L2 (flush) and/or
  invalidate all lines (invalidate). The request enters the DCache via the LSU as
  a coreReq with opcode=3. The DCache first writes dirty lines back one by one
  (via memReq), then sends a Flush/Hint-class request to L2, and only after
  **waiting for L2's hintAck** (memRsp d_opcode=2) is the operation considered
  complete, at which point it returns a coreRsp to the core side (LSU/warp
  scheduler).
- **coreRsp_st2 and ghost pre-staging**: coreRsp_st2 is a 1-deep pipe queue
  (:246), the source of the metadata (instrId etc.) enqueued into coreRsp_Q. For
  ordinary loads/stores the response metadata is enqueued naturally on the fire
  cycle; flush/invalidate is different — its response must wait for the hintAck
  several cycles later, and in the meantime the flush request in st1 **pre-stages
  its entry into coreRsp_st2 every cycle** via the elsewhen branch at :695-699
  (it can be written without fire, hence "ghost"), ensuring the head holds exactly
  its instrId when hintAck arrives. Chisel queue registers have no reset and their
  bits are retained after dequeue — this retention semantics is also part of the
  mechanism (modeled as D5 on the Lean side).
- **instrId bookkeeping**: LSU's Coalscer (pipeline/MSHR.scala:50-71) does
  bookkeeping for instructions by the response's instrId (clearing the mask,
  writing data, judging completion). **A wrong instrId = booked to another
  instruction's head**; a lost instrId = the target instruction never completes.
- **The bits-retention convention of Decoupled queues**: after a Chisel Queue
  dequeues, the deq.bits register retains its old value; the consumer must use
  deq.valid to judge validity. What :413 lacks is exactly this qualifier.

### 1.2 Design intent

The two flags `waitforL2flush` (:207) and `waitforL2flush_st2` (:418)
characterize "this flush/invalidate has been issued and is waiting for L2's
hintAck": set on the fire cycle (:423-424), cleared on the hintAck cycle
(:425-427). While set, st1 does not release the request (`!flushstall` at
:465/:470), and ghost pre-staging continues. The design intent is "one
flush/invalidate produces exactly one response carrying the correct instrId, and
not earlier than the completion of the L2 handshake".

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: memRspIsFluOrInv lacks a valid qualifier** (`DCache.scala:413`, ★
root-cause trouble spot):

```scala
val memRspIsFluOrInv: Bool = memRsp_Q.io.deq.bits.d_opcode === 2.U //hintAck
```

It looks only at `deq.bits` (the register value), not at `deq.valid`. After
memRsp_Q consumes the hintAck, the head register retains d_opcode=2 — the
expression is true on every subsequent cycle, until the next memRsp is enqueued
and displaces the ghost image.

**Construct 2: the set/clear chain of waitforL2flush** (`DCache.scala:423-433`, ★
erroneous clearing site):

```scala
when(io.coreReq.fire && (isInvalidate || isFlush)) {
  waitforL2flush := true.B
}.elsewhen(memRspIsFluOrInv) {        // ★ the retained ghost image hits this branch every cycle
  waitforL2flush := false.B
}
// :429-433 waitforL2flush_st2 has the same structure and the same defect
```

While the ghost image persists, waitforL2flush is continuously erroneously cleared
(it vanishes one cycle after being set). Also erroneously cleared is `flushL2_Reg`
(:769-773, the "send Flush only once" protection, which is saved only by a timing
coincidence — cf. the Q4 note in the DCache.lean header).

**Construct 3: the sole response production point and the metadata source**
(`DCache.scala:753-757`):

```scala
coreRsp_Q.io.enq.valid := coreRsp_st2_valid || (memRspIsFluOrInv && memRsp_Q.io.deq.fire)
// :754 —— the hintAck term is the sole source of flush/invalidate responses; the OR merge has no mutual exclusion
coreRsp_Q.io.enq.bits.instrId := Mux(coreRsp_st2_valid_from_memReq,
  coreRspFromMemReq.instrId, coreRsp_st2.io.deq.bits.instrId)   // :757 taken from the st2 head
```

**Construct 4: ghost pre-staging** (`DCache.scala:695-699`):

```scala
}.elsewhen(waitMSHRCoreRsp_st1 || fluCoreRsp_st1 || invCOreRsp_st1){
  coreRsp_st2.io.enq.valid := true.B     // ★ no fire needed; pre-staged every cycle during the stall
  ...
}
```

fluCoreRsp_st1/invCOreRsp_st1 (:482-485) require that the flush/inv still resides
in st1 — once waitforL2flush is erroneously cleared, st1 releases early
(`!flushstall` at :465/:470 ceases to hold) and ghost pre-staging stops.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

Two forms, both rooted in Construct 1:

**w2b (response metadata attributed to the wrong instruction)**: while the
memRsp_Q head retains d_opcode=2 (the normal state after any hintAck has been
consumed), a new flush/invalidate enters:

1. On the fire cycle waitforL2flush is set (:423-424);
2. On the next cycle the retained ghost image hits the elsewhen at :425 →
   **waitforL2flush is erroneously cleared one cycle after being set**
   (machine-checked by `dcT_w2b_early_clear`);
3. The flush's st1 releases early, and ghost pre-staging stops;
4. When the real hintAck arrives several cycles later, :754 produces a response,
   but the coreRsp_st2 head has already been occupied by an intervening other
   response (e.g. a load) → **flush(5)'s response carries load(3)'s instrId**
   (machine-checked by `dcT_w2b_stale_instrId`: rspLog=[3,3], and 5 never
   appears).

**w2c (response lost entirely)**: when the hintAck dequeues on the same cycle as
another response (coreRsp_st2_valid=1), the OR-merge at :754 combines the two into
one enqueue event, and the metadata is taken from the st2 head (the other
response's) — **the flush's response is lost entirely** (machine-checked by
`dcT_w2c_rsp_lost`: rspLog=[3], no 5).

Downstream amplification: Coalscer does bookkeeping by instrId → w2b pollutes
another instruction's entry; w2c makes the target instruction never complete. If
that invalidate is the trailing release of an AMO aq&&rl sequence
(LSU.scala:247-248, sharing the AMO's instrId), the AMO never completes in
Coalscer → **hang**.

### 3.2 Root cause

**Violation of the queue consumption convention**: it is a standard convention
that a Chisel Decoupled queue's "bits register is retained after dequeue", so the
consumer must use valid as the validity criterion. :413 uses bits directly for
event detection, which amounts to treating a "ghost image" as an "event". The same
file's :542-543 (memRspIsWrite/memRspIsRead) are the same kind of bare-bits
comparison, but their consumption points (:546/:549) both conjoin with valid on
the same cycle — only memRspIsFluOrInv is used at :425/:431/:771 as a **persistent
condition**, and that is where the ghost image's harm lands.

### 3.3 Impact and tolerability

- **Impact**: bookkeeping disorder (w2b) → another instruction is wrongly
  completed/has data written; or hang (w2c, AMO release scenario). Both are silent,
  with no assertions (after synthesis).
- **Trigger surface**: the second and all later flush/invalidate operations (the
  first has no ghost image to step on; the normal path is pinned as the control
  baseline by `dcT_w2a_normal`). Flush/invalidate frequency is low (CTA
  boundaries, AMO tails), but every CTA boundary has at least one — multi-kernel /
  multi-WG scenarios necessarily reach "the second one".
- **Tolerability**: intolerable; once triggered it goes wrong. Rating: high.

---

## 4. Lean Formal Evidence

All in `lean/Ventus/Mem/DCache.lean` (§5 sequential core + §6), multi-cycle trace
native_decide witnesses (6-7 cycles); coreRsp_Q does not model storage, only
records the sequence of enqueued instrId events `rspLog` (modeling decision D4;
the object of investigation is precisely "what instrId was enqueued"):

- **`dcT_w2a_normal`** (DCache.lean:1015): **normal-path baseline** — for the
  first flush (no ghost image at the head) the response is later than L2's
  hintAck, occurs exactly once, and the instrId is correct (rspLog=[5]). It holds
  thanks to ghost pre-staging (:695-699) + queue bits retention (D5);
- **`dcT_w2b_early_clear`** (:1033): on the cycle after fire (with the retained
  ghost-image input `dcInStaleAck` = head op=2 and valid=0), waitforL2flush is
  erroneously cleared;
- **`dcT_w2b_stale_instrId`** (:1041): **w2b witness** — under the complete trace
  of the second flush, rspLog=[3#3, 3#3] and 5#3 never appears: flush(5)'s
  response carries load(3)'s instrId;
- **`dcT_w2c_rsp_lost`** (:1058): **w2c witness** — the hintAck dequeues on the
  same cycle as a stranded load response; rspLog=[3#3]: flush(5)'s response is
  lost entirely.

**Fixed-version verification** (`lean/VentusF/Mem.lean` §4, where
`fmemDcMemRspIsFluOrInv` adds the valid qualifier + `fmemDcRspSt2DeqRdy` yields to
hintAck):

- **`fmem_i30a_eq_hintAck`** (VentusF/Mem.lean:426): the fixed version's
  memRspIsFluOrInv equals exactly the "hintAck actually dequeued" event (rfl
  level);
- **`fmem_i30a_stale_rejected`** (:431): when the head is invalid (a ghost image),
  the fixed version is constantly false — ghost-image invalidation pinned down;
  **`fmem_i30a_regress`** (:436): when valid=1 it agrees with the original;
- **`fmem_i30_w2b_green`** (:586): the W2b scenario goes green in the fixed
  version — waitforL2flush holds until the real hintAck, rspLog=[5#3] (no longer
  the original [3,3]);
- **`fmem_i30_w2c_status`** (:610): **downgrade note (verbatim)** — under the
  fixed version's W2c trace, with the i30 patch's st2-yielding change,
  native_decide pins the actual behavior as rspLog=[3#3] (same input sequence as
  the original witness, `fmemDcW2c_inputs_same` being rfl). That is, this witness
  scenario is not salvaged under the fixed version; the archive follows this
  machine-checked proof;
- **`fmem_i30_step_regress`** (:616): when the head is not a hintAck encoding and
  there is no in-flight victim read, the fixed version is step-by-step equivalent
  to the original (regression-safe).

---

## 5. Simulation Verification (did not pass → stub fixed → companion defect exposed, recorded faithfully)

**Initial ChiselSim run** (`repro/DCacheBugRepro.scala`, 2026-09-06/07, Verilator
backend, doc/22): verdict **did not pass (residual doubt)** — after calibration
(dirtying the cache before inv; an invalidate of a clean cache produces no L2
Flush, :488), inv1's L2 Flush+hintAck round trip completes, but afterwards
coreReq.ready stays 0 for over 500 cycles and load L is never accepted; the
symptom lies in this report's waitforL2flush/memRsp_Q fault region, but at the
time it was impossible to distinguish "bug manifestation" from "test timing not
calibrated".

**Patched-tree regression special session** (2026-09-07, doc/22 "I-29/I-30 special
session"):

1. **The hang's root cause = a test-stub defect (Class III), not a patch
   regression**. The hand-written L2 stub never returns AccessAck (d_opcode=0) for
   PutFull/PutPart writebacks — the DCache pushes every writeback memReq into the
   WSHR, which pops only on AccessAck (:549-550), so WshrAccess.io.empty stays
   false forever → invalidate's st1 completion condition (:465) never holds →
   coreReq_Q is occupied → coreReq.ready stays 0. An isolation matrix of 6
   configurations (full / revert i27 alone / i28 / i29 / i30 / revert all four
   patches) all hang identically, and baseline shows the same symptom — ruling out
   any patch-introduced regression. After fixing the stub (adding a pump to the
   test that returns AccessAck every other cycle for memReq with op=0/1), both
   trees' flows run through.
2. **After the stub fix, the companion defect I-48 is exposed (important)**:
   phase-annotation measurement — baseline response sequence {7,3,1,5,4,2} (each
   request exactly once); patched tree {7,3,1,5,4,**2,2**} (inv2 responded to
   twice). Bisection: reverting i30 alone makes the duplicate disappear; reverting
   i27/i28/i29/i44 leaves it in place. Mechanism chain: after i30 adds the valid
   qualifier, waitforL2flush_st2 is no longer erroneously cleared by the ghost
   image → inv2's dirty writeback PutPart carries
   `hasCoreRsp=waitforL2flush_st2` (:503) → when pushed into the WSHR it produces
   a response early via the memReq path (:818) — **earlier than the completion of
   the L2 flush handshake**, duplicating the hintAck-path response (:754).
   **Baseline's "normal" appearance itself depends on the masking of I-48 by this
   entry's w2b erroneous clearing**. Remaining unlocated link: the precise cycle on
   which invalidatenodirty (:428) holds in the inv2 flow requires waveform-level
   debugging.

**38-patch merged-tree regression** (2026-09-10, doc/22): the i48 patch
(InvOrFluMemReq.hasCoreRsp forced false + waitforL2flush_st2 removed + st2
cycle-yielding guard) makes inv2 produce a unique response only via the hintAck
path — measured response sequence **{7,3,1,5,4,2}** (each request exactly once),
2/2 green, and no longer dependent on bug masking. **The I-48 fix behavior
verification passed.**

**Note (evidence boundary)**: the w2b form "a response carrying another
instruction's instrId" was itself not directly observed on RTL — baseline's
response sequence happens to be correct (its correctness depends on w2b's
erroneous clearing masking I-48, a case of "two wrongs make a right"). The direct
forms of w2b/w2c are established by the Lean machine-checked proofs (§4); the
observable evidence on the RTL side is the I-48 activation/fix control experiment.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: all "second and later" flush/invalidate operations — two
  sources: CTA boundaries (warp_schedule's flushDCache → LSU → DCache) and the
  AMO aq&&rl trailing release-invalidate. Necessarily reached under multi-kernel /
  multi-WG runs.
- **Why upstream did not find it**: (a) single-kernel short runs have few flushes,
  and w2b's erroneous clearing happens to be harmless when no other responses
  interleave (a large "two wrongs make a right" region); (b) observability
  requires the hintAck to coincide exactly with another response (w2c) or
  intervening responses (w2b); (c) the simulation assertion system does not cover
  response-bookkeeping consistency.
- **Relation to I-47**: I-47 (WG completion is reported without waiting for flush
  completion) belongs to the same "flush completion bookkeeping" problem family;
  I-48 demonstrates that correctness in this region is a fragile equilibrium of
  multiple bugs masking one another.

---

## 7. Fix Plan and Fix Verification

**Patch** (`i30-dcache-flush-rsp.patch` (internal fix manifest; not released), two edit points):

```scala
// Edit point 1 (:413): add the valid qualifier; the ghost image becomes inert
-  val memRspIsFluOrInv: Bool = memRsp_Q.io.deq.bits.d_opcode === 2.U //hintAck
+  val memRspIsFluOrInv: Bool = memRsp_Q.io.deq.valid && memRsp_Q.io.deq.bits.d_opcode === 2.U

// Edit point 2 (:747): when hintAck coincides with an st2 response, the flush response takes priority; st2 yields one cycle
-  coreRsp_st2.io.deq.ready := coreRsp_Q.io.enq.ready && !coreRsp_st2_valid_from_memReq
+  coreRsp_st2.io.deq.ready := coreRsp_Q.io.enq.ready && !coreRsp_st2_valid_from_memReq && !memRspIsFluOrInv
```

**The companion defect I-48 and the second fix**: edit point 1 eliminated w2b's
per-cycle erroneous clearing, allowing waitforL2flush_st2 to survive — the inv's
dirty writeback PutPart starts carrying `hasCoreRsp=waitforL2flush_st2` (:503),
and when pushed into the WSHR it produces a response early via the memReq path
(:818), duplicating the hintAck path (:754): one invalidate, two responses. **I-48
is this project's first latent defect whose broken-window condition = fixing
another bug** (fully recorded in doc/03 I-48). The second fix
`i48-dcache-inv-dup-rsp.patch` (hasCoreRsp forced false + waitforL2flush_st2
removed + st2 cycle-yielding guard) makes one inv produce a unique response only
via the hintAck path.

**Fix verification**:

- Effectiveness: Lean fixed version `fmem_i30a_eq_hintAck` /
  `fmem_i30a_stale_rejected` / `fmem_i30_w2b_green` (w2b goes green); on the RTL
  side the 38-patch tree's I-30 case is 2/2 green (response sequence
  {7,3,1,5,4,2}, each request exactly once, no longer dependent on bug masking);
- Regression safety: `fmem_i30a_regress` / `fmem_i30_step_regress` (step-by-step
  equivalence in the non-triggering domain);
- **Unclosed items (recorded faithfully)**: the w2c form is not salvaged in the
  fixed-version Lean model (`fmem_i30_w2c_status`: under the same witness trace,
  rspLog is still = [3#3]; the archive follows this machine-checked proof); the
  RTL-level behavior verification of i30 edit point 2 (st2 yielding) is covered by
  the I-48 fix, and the 38-tree verdict follows the I-48 case; the precise cycle
  on which invalidatenodirty (:428) holds in the inv2 flow is unlocated (doc/22
  leftover, requires waveform-level debugging).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Line-by-line verification of DCache.scala:413 / :423-433 / :753-757 / :695-699 / :769-773 / :503 / :818 | Seven locations consistent |
| Machine-checked Lean proof | `dcT_w2a_normal` (baseline) / `dcT_w2b_early_clear` / `dcT_w2b_stale_instrId` / `dcT_w2c_rsp_lost` (multi-cycle witnesses, native_decide) | Machine-checked closed loop (concrete-trace level) |
| Simulation verification | Initial run did not pass → Class III stub defect (L2 stub never returns AccessAck) → after stub fix, I-48 exposed (bisected to i30) → after i48 fix, 38-tree 2/2 green ({7,3,1,5,4,2}) | Measured (w2b's direct form not observed on RTL; machine-checked proof authoritative) |
| Fix verification | i30 patch (2 edit points) + i48 patch (companion); `fmem_i30a_*` / `fmem_i30_w2b_green` / `fmem_i30_w2c_status` / `fmem_i30_step_regress` | Machine-checked + measured; w2c not salvaged in the fixed-version model (downgrade recorded) |

I-30 is a "queue consumption convention violation" type of defect: one bare-bits
comparison (:413) treats memRsp_Q's head ghost image as a hintAck event, and via
the erroneous clearing of waitforL2flush → ghost pre-staging stopping → metadata
misplacement/loss at the sole response production point, both forms (wrongly
attributed metadata w2b / total loss w2c) are pinned down by machine-checked Lean
proofs. Its simulation handling chain (stub-defect diagnosis → fix activating
I-48 → second fix turning the regression green) also contributes a methodological
sample of a "multiple bugs masking one another" region: the "normal" appearance of
such a region cannot be trusted, and fix verification must use "correctness that
does not depend on bug masking" as the acceptance criterion.
