> English translation of the Chinese master `doc/bugs/I-48-修复激活的inv重复响应.md`. Translated 2026-09-13.

# I-48 Detailed Bug Analysis Report: duplicate response between the invalidate write-back path and the hintAck path (masked by I-30, activated by the i30 fix)

| Item | Content |
|---|---|
| ID | I-48 |
| Source location | `ventus/src/L1Cache/DCache/DCache.scala:413` (`memRspIsFluOrInv`, the I-30 fix point); `:511` (the dirty write-back PutPart carries `hasCoreRsp=waitforL2flush_st2`); `:832` (a response is produced via the memReq path when pushing into the WSHR); `:766` (the hintAck-path response) |
| Type | Functional bug (response-protocol violation: one request receives two responses) — **a fix-activated latent defect** |
| Severity | **High** (reachable immediately once the i30 patch is applied; response-bookkeeping mismatch can corrupt warp completion counts). Under the current original configuration it is masked by I-30's w2b bug and unreachable |
| Confirmation status | 【Confirmed · Latent / Fix-activated】; the i48 patch has been designed and verified by the 38-patch merged-tree ChiselSim regression |
| Main evidence | 【simulation run】patched-RTL patch-tree regression special campaign (doc/22): baseline response sequence {7,3,1,5,4,2} vs the 35-patch tree {7,3,1,5,4,2,2}, bisected to i30; the 38-patch tree (including i48) returns to exactly one response per request. 【Lean machine-checked proof】`VentusF/FixI48.lean`, three layers of evidence: signal-level / count-level / machine-level. 【direct source reading】line-by-line check of the four locations |
| Lean model | `lean/VentusF/FixI48.lean` (fixed-version model and verification, 156 lines); the machine-level witness reuses `dcStep`/`dcRun`/`rspLog` from `lean/Ventus/Mem/DCache.lean` |
| Reproduction / patch | The I-30 case of `repro/DCacheBugRepro.scala` (after the stub fix, Verilator backend); patch `i48-dcache-inv-dup-rsp.patch` (internal fix manifest; not released) |
| Related entries | I-30 (the bug that masks it — its fix point is this entry's activation point), I-29 (same suite, same special campaign), I-47 (flush completion signal missing, same domain), I-44 (same "response-protocol violation" family) |

---

## 0. Summary

When the DCache processes an invalidate with dirty lines, there are two paths that
can produce a coreRsp: the **write-back path** (when a dirty-line PutPart is pushed
into the WSHR, via the memReq path, `DCache.scala:832`) and the **hintAck path**
(after the L2 Flush handshake completes, `:766`). The write-back path's response
enable `InvOrFluMemReq.hasCoreRsp` is driven by the register `waitforL2flush_st2`
(`:511`).

On the original RTL, `waitforL2flush_st2` happens to be persistently mis-cleared by
**I-30's w2b bug** (`memRspIsFluOrInv` lacks a `deq.valid` qualifier, so after
memRsp_Q consumes the hintAck, the stale queue-head register d_opcode=2 triggers
the clear every beat); therefore the write-back path's response event never
happens, and the hintAck path is the sole response source — the surface behavior
looks normal.

**I-30's fix (the i30 patch, adding the `deq.valid` qualifier at `:413`) eliminates
the mis-clear, and `waitforL2flush_st2` survives** — the inv's dirty write-back
PutPart then carries hasCoreRsp=1, and when pushed into the WSHR it produces a
response **early** via the memReq path (earlier than the L2 flush handshake
completes, contrary to waitforL2flush's design intent), **duplicating** the
hintAck path's normal response: one invalidate receives two responses.

This is the project's first latent-defect case whose **"broken-window condition =
fixing another bug"** (the broken-window condition of all previous latent defects
was a design/contract change): the defect mechanism genuinely exists in the
original RTL, merely masked by the side effect of another bug in the same module.
It was discovered by the 2026-09-07 patch-tree regression special campaign
(agent-147): on the 35-patch tree the I-30 case's measured response sequence was
{7,3,1,5,4,**2,2**} (inv2 responded twice), bisected to i30; the i48 patch
(hasCoreRsp constant false + removing waitforL2flush_st2) brought the 38-patch
tree back to {7,3,1,5,4,2} (exactly one per request), passing fix verification.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **DCache flush/invalidate (flu/inv)**: at CTA boundaries or coherence windows,
  the host/scheduler requires dirty lines of the L1 DCache to be written back to
  L2 and invalidated. After receiving an inv request, the DCache scans the dirty
  bitmap set by set, sends a PutPart write-back to L2 for each dirty line (pushing
  the data to L2), and finally sends a Flush/Hint request to L2; L2 finishes and
  replies with a **hintAck** (TileLink HintAck, d_opcode=2).
- **WSHR (write-back status holding register)**: the DCache's internal write-back
  bookkeeping. Each pushed write-back memReq occupies one slot, popped when L2
  returns an AccessAck — the inv completion condition requires the WSHR to be
  drained (i.e. all dirty-line write-backs acknowledged by L2).
- **Response protocol**: every coreReq must receive **exactly one** response on
  coreRsp. The downstream LSU/warp scheduler does bookkeeping by instrId (one
  response per instruction); one response too many or too few breaks the
  bookkeeping.
- **`waitforL2flush` / `waitforL2flush_st2`**: the "waiting for L2 flush" flag
  set after an inv/flush request enters. Design intent: the inv's response must
  not be issued until the final L2 Flush's hintAck arrives. `st2` is its st1
  pipeline stage's delayed copy.
- **Decoupled/valid semantics**: a "what type is the queue head" judgment like
  `memRspIsFluOrInv` must carry a `deq.valid` qualifier, otherwise the stale old
  bits of an idle queue are mistaken for a new event — exactly I-30's w2b bug.

### 1.2 Design intent

inv lifecycle: coreReq(inv) enters → st1 scans dirty lines → dirty-line
write-back PutParts are pushed into the WSHR → after the WSHR drains, a Flush is
sent to L2 → the L2 hintAck returns → the unique coreRsp is produced. The intent
of the `hasCoreRsp` field is to mark "whether this memReq incidentally carries a
response to the core".

---

## 2. Line-by-Line Reading of the Original Code

**Construct one: memRspIsFluOrInv lacks a valid qualifier** (`DCache.scala:413`,
I-30's fix point, also the first link of this entry's activation chain):

```scala
val memRspIsFluOrInv: Bool = memRsp_Q.io.deq.bits.d_opcode === 2.U //hintAck
```

The original looks only at the queue-head bits, not valid: after memRsp_Q
consumes the hintAck, the queue-head register retains d_opcode=2, and this
expression is true on every idle beat. It drives the clear branch of both
`waitforL2flush` and `waitforL2flush_st2` (`:423-433`) — **I-30 w2b's
mis-clear**.

**Construct two: the dirty write-back PutPart's hasCoreRsp is driven by
waitforL2flush_st2** (`DCache.scala:511`, ★pitfall):

```scala
InvOrFluMemReq.a_mask := TagAccess.io.dirtyMask_st1.asTypeOf(InvOrFluMemReq.a_mask)
InvOrFluMemReq.hasCoreRsp := waitforL2flush_st2        // ★ the inv dirty write-back may carry a response
InvOrFluMemReq.coreRspInstrId := coreReq_st1.instrId
```

By design intent, the inv's response should be produced only by the final Flush
handshake; but here **every dirty-line write-back** is given a channel to carry a
response, enabled by the st2 flag.

**Construct three: a response is produced via the memReq path when pushing into
the WSHR** (`DCache.scala:832`):

The memReq path's response event = WSHR push × hasCoreRsp; a PutPart with
hasCoreRsp=1 issues a response to the coreRsp side on the very beat it is pushed
into the WSHR (instrId taken from coreReq_st1). This response comes **earlier
than the L2 flush handshake completes** — WSHR draining and the hintAck round
trip still need several more beats.

**Construct four: the hintAck path's normal response** (`DCache.scala:766`):

```scala
coreRsp_Q.io.enq.valid := coreRsp_st2_valid || (memRspIsFluOrInv && memRsp_Q.io.deq.fire)
```

The inv's formal response is produced when the hintAck arrives and dequeues — by
design intent the **unique** response.

Construct three coexisting with construct four ⇒ an inv with hasCoreRsp=1
produces two responses.

---

## 3. Bug Analysis

### 3.1 Precise description of the defect

Mechanism chain (four steps, following the structure of the doc/03 I-48 entry):

1. **The I-30 fix** (the i30 patch, adding the `deq.valid` qualifier at `:413`)
   eliminates w2b's per-beat mis-clear;
2. `waitforL2flush_st2` survives (set after the inv enters st1, no longer cleared
   by the stale queue head);
3. The inv's dirty write-back PutPart carries `hasCoreRsp=waitforL2flush_st2=1`
   (`:511`), and when pushed into the WSHR it produces a response early via the
   memReq path (`:832`, **earlier than the L2 flush handshake completes**,
   contrary to waitforL2flush's design intent);
4. This response **duplicates** the hintAck path's normal response (`:766`) — one
   invalidate produces two responses.

Measured anchor (patched-RTL, doc/22 "I-29/I-30 special campaign"): the 35-patch
tree's I-30 case response sequence = {7,3,1,5,4,**2,2**} — instrId=2's inv2
responded twice, where the early response appears **on the same beat** as inv2's
dirty write-back PutPart (addr=0x28080), and the normal response comes after the
hintAck. Control baseline = {7,3,1,5,4,2} (exactly one per request).

**Key characterization**: the baseline's "normal" appearance itself **depends on
the masking by the w2b bug's mis-clear** — on the original, waitforL2flush_st2 is
always mis-cleared to false, so construct three's response event never happens.
The mechanism genuinely exists in the original; it is just unreachable.

### 3.2 Root cause

A semantic design overlap in `hasCoreRsp`: both memReq paths — the write-back
PutPart and the final Flush — were given the ability to "carry a coreRsp", with
no mutual-exclusion mechanism enforcing "one inv may be responded to only once".
The w2b mis-clear happened to pin the write-back path's response enable at false
during long runs, so this design overlap was never exposed — until I-30 was
fixed.

### 3.3 Harm and tolerability

- **Harm**: response-protocol violation — one request receives two responses. The
  downstream (LSU/warp scheduler) response-count bookkeeping mismatches: the
  extra response is booked by instrId onto some other in-flight instruction or
  corrupts the target instruction's completion count (same domain as I-30's
  consequence chain, booked by instrId via the Coalescer).
- **Tolerability**: **unreachable under the original current configuration**
  (masked by I-30's w2b mis-clear); reachable immediately once the i30 patch is
  applied. This entry therefore belongs to the "**mandatory for the fixed
  version**" class — i30 and i48 must be applied as a pair; i30 must not be
  applied alone.
- **Unlocated link** (honestly recorded): the precise beat at which
  `invalidatenodirty` (`:430`) holds in the inv2 flow — store4 has already
  completed, so hasDirty should be 1, yet the PutPart did carry hasCoreRsp=1 —
  requires waveform-level debugging. This link does not affect the validity of
  the mechanism chain's last three steps or the fix direction (the fix directly
  removes construct two's response enable).

---

## 4. Lean Formal Evidence

The fixed-version model and verification live in `lean/VentusF/FixI48.lean` (156
lines; the machine-level witness reuses `dcStep`/`dcRun` and the response log
`rspLog` from `Ventus/Mem/DCache.lean`), in three layers:

**Signal level** (`:511` assembly × `:832` response event):

- `f48_wb_rsp_absent` (【Lean machine-checked proof】, decide): the fixed-version
  write-back-path response event **never happens**, for any push and any waitSt2
  value;
- `f48_orig_wb_rsp_possible` (rfl): in the original, a push with waitSt2=true
  responds immediately — the I-48 mechanism holds;
- `f48_regr_waitSt2_false` (decide): when waitSt2=false (the only case reachable
  on the original under I-30's masking), the fixed version and the original agree
  **event by event** — the signal-level characterization of regression safety.

**Count level** (response count of one inv = write-back events + hintAck term):

- `f48_orig_dup`: in the original, one write-back with waitSt2=true + hintAck =
  **2 responses**;
- `f48_fix_at_most_one` / `f48_fix_exactly_one`: in the fixed version the
  response count is ≤ 1 for any number of dirty lines, and the normal completion
  on hintAck arrival is exactly 1.

**Machine-level witness** (isomorphic to the patched-RTL regression
{…,2,2}→{…,2}, native_decide):

- `f48T_dup_witness`: the original mechanism trace (inv enters → write-back path
  responds early → hintAck → second response) has `rspLog = [2#3, 2#3]` —
  instrId=2 responds twice;
- `f48T_fix_single`: the fixed version over the same lifecycle has
  `rspLog = [2#3]` — exactly one response, still instrId=2's hintAck response
  (response content unchanged, regression-harmless);
- `f48T_no_early_rsp`: no response before the hintAck arrives — the
  waitforL2flush design intent "the response does not precede the final Flush
  handshake" holds in the fixed version.

Per project convention, native_decide witnesses carry the
`_native.native_decide.ax_*` trust axioms (archived and noted).

---

## 5. Simulation Verification (patched-RTL patch-tree regression, two rounds measured)

This entry is not "a test written to reproduce", but a **measured discovery of the
patch-tree regression** — the evidence chain is itself a complete controlled
experiment (the doc/22 sections "I-29/I-30 special campaign" and "38-patch
merged-tree regression"):

**Prerequisite (type-III stub fix)**: the hand-written L2 stub never returns an
AccessAck for PutFull/PutPart write-backs, so the WSHR never pops ⇒ the inv flow
hangs (a 6-configuration isolation matrix + baseline with the same symptom rules
out any patch-introduced regression). After adding an L2 AccessAck pump to the
test, the flow completes.

**Round one (35-patch tree, actually run 2026-09-07)**:

| Tree | I-30 case response sequence | Verdict |
|---|---|---|
| baseline (original snapshot) | 7,3,1,5,4,2 (exactly one per request, 2/2 green) | apparently normal (depends on masking by the w2b mis-clear) |
| 35-patch tree | 7,3,1,5,4,**2,2** (inv2 responds twice) | **duplicate response exposed** |

Phase annotation, measured: the early response appears on the same beat as inv2's
dirty write-back PutPart (addr=0x28080), and the normal response comes after the
hintAck. **Bisection**: reverting i30 alone → the duplicate disappears; reverting
i27/i28/i29/i44 → it persists in each case — the activation source is locked to
i30.

**Round two (38-patch merged tree, actually run 2026-09-10)**: merged tree =
original snapshot + 35 patches + i47 + i16 + **i48**. The I-30 case's measured
response sequence = **7,3,1,5,4,2** (exactly one per request, 6 entries, recorded
by in-test println) — with i48, inv2 produces its unique response only via the
hintAck path, the behavior returns to exactly one per request **and no longer
depends on bug masking**. The DCacheBugRepro suite is 2/2 green. **The I-48 fix
behavior passes verification.**

---

## 6. Upstream Impact Analysis

- **Trigger surface**: after applying the i30 patch (or any change that corrects
  the `memRspIsFluOrInv` valid qualifier), any invalidate/flush with dirty lines.
  Unreachable on the unpatched original.
- **Impact on the fix series**: i30 and i48 are strongly coupled — applying i30
  without i48 exchanges "response-metadata corruption" for "duplicate response";
  both are correctness-level. The 38-patch merged tree has already verified them
  as a pair.
- **Design lesson**: a field like `hasCoreRsp`, where "multiple producers may
  carry a response", must have a mutual-exclusion discipline (exactly one
  response per request is a system-level invariant); a masking-type latent defect
  shows that **bugs can mask each other** — regression tests for fixing one bug
  must cover the masked region. This is exactly the methodological value of the
  patch-tree regression special campaign.
- **Similar family**: I-30 (hintAck response corruption/loss), I-47 (flush has no
  completion signal back), I-44 (duplicate refill A on the same source) — the
  concentrated area of DCache/L2 response-protocol-family defects.

---

## 7. Fix Proposal and Fix Verification

**Patch** (`i48-dcache-inv-dup-rsp.patch` (internal fix manifest; not released), designed and
verified 2026-09-10), taking the **strongest form** of the "mutual exclusion of
the two paths" fix direction registered in doc/22:

1. `DCache.scala:511`: `InvOrFluMemReq.hasCoreRsp := waitforL2flush_st2`
   → `:= false.B` — **the write-back path never produces a coreRsp**; the unique
   response of inv/flush = the final L2 Flush's hintAck (`:766`); the write-back
   PutPart is only responsible for pushing dirty lines to L2;
2. The `waitforL2flush_st2` register is accordingly **removed** (its sole
   consumer is the :511 assembly; once constant false it has no value), together
   with an st2 stall guard (explained in the patch comments).

**Regression basis** (patch header comment): on the original (I-30 unfixed),
waitforL2flush_st2 is masked by the w2b mis-clear, so the hintAck path was
already the unique response source (the baseline measures exactly one response
per request); this fix is **observationally equivalent** to that — i.e. the fix
changes no original observable behavior and only removes the post-activation
duplicate response.

**The fix-verification triplet**:

- Effectiveness: the Lean fixed-version theorems (§4
  `f48_fix_at_most_one`/`f48_fix_exactly_one`/`f48T_fix_single`/
  `f48T_no_early_rsp`) + the 38-patch merged-tree ChiselSim regression with
  DCacheBugRepro 2/2 green (response sequence 7,3,1,5,4,2);
- Regression safety: signal-level `f48_regr_waitSt2_false` (event-by-event
  agreement in the masked domain) + all 11 suites of the 38 tree matching the
  35 tree's verdicts (the doc/22 verdict summary table);
- Residual item: the beat at which `invalidatenodirty` (`:430`) holds is not
  located (waveform-level debugging pending); this link does not affect the
  fix's correctness (what the fix removes is the response enable itself).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Line-by-line check of DCache.scala:413 / :511 / :832 / :766; all four links of the mechanism chain present | source level |
| patched-RTL regression | baseline {7,3,1,5,4,2} vs the 35 tree {7,3,1,5,4,2,2}; bisected to i30 (reverting i30 makes the duplicate disappear; reverting i27/28/29/44 does not) | measured (controlled experiment) |
| Lean machine-checked proof | `f48_orig_dup`/`f48_orig_wb_rsp_possible` (mechanism); `f48T_dup_witness` (machine-level witness isomorphic to {…,2,2}) | machine proof + native_decide witness |
| Fix verification | the i48 patch; Lean `f48_fix_at_most_one`/`f48T_fix_single`/`f48T_no_early_rsp`/`f48_regr_waitSt2_false`; the 38 tree regression {7,3,1,5,4,2}, 2/2 green | measured + machine proof |

I-48 is the **first case of a "fix-activated latent defect"**: the mechanism
genuinely exists in the original RTL, masked by the side effect of the same
module's I-30 w2b bug; fixing I-30 activates this entry. It extends the
latent-defect broken-window condition from "design/contract change" to "fixing
another bug", and directly demonstrates the necessity of patch-tree regression
(rather than per-patch verification alone) as a methodology — viewed in
isolation the i30 patch is a correct fix, and only in the merged-tree
regression's response-sequence comparison does the companion defect it unmasks
become visible.
