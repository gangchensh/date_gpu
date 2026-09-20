> English translation of the Chinese master `doc/bugs/I-50-vmerge写掩码偏离RVV.md`. Translated 2026-09-13.

# I-50 Detailed Bug Analysis Report: the vmerge write mask deviates from RVV — lanes with tmask=1 ∧ v0[t]=0 are not written

| Item | Content |
|---|---|
| ID | I-50 |
| Source location | `ventus/src/pipeline/execution.scala:559` (`wvd_mask := io.in.bits.mask` overrides unconditionally, turning the `:541` intent `wvd_mask(x):=true.B` into dead code); `ventus/src/pipeline/pipe.scala:366` (`io.in.bits.mask` is already assembled as v0∧tmask, an irreversible merge); linked points `DecodeUnit.scala:367-369`, `:588`, `operandCollector.scala:614` |
| Type | Functional bug (ISA-visible semantic deviation) — a follow-up exposure of the I-12 fix |
| Severity | **High** (silent wrong data under hand-written / non-standard compilation paths; the RVV compliance claim does not hold). Observability is conditional: unobservable when vd=vs2 (the LLVM tied destination-register convention) |
| Confirmation status | 【Confirmed】 (doc/28 special-campaign ruling, 2026-09-10); no patch (option-A fix proposal registered, the internal fix manifest "patch to be designed") |
| Main evidence | 【direct source reading】line-by-line check of the four source locations + the semantic-difference table (doc/28 §3); 【Lean consistency cross-check】the IsaSpec D6 golden semantics vs the machine-side wbVMaskFn of SMMem + the machine-level alignment gap registered in CapExist.lean; RTL reproduction 【ready-to-run (not executed in this environment)】 |
| Lean model | `lean/VentusF/IsaSpec.lean` (D6, :44-50/:415), `lean/VentusF/SMMem.lean:611-613`, `lean/VentusF/CapExist.lean:57-67`, `lean/VentusF/RefineVec.lean:277-289` |
| Reproduction / patch | the distinguishing program has been designed (doc/28 §5.4), not executed in this environment; no patch |
| Related entries | I-12 (only after its fix made the mask path usable did this entry become an observable problem), the B1 note (vmerge semantics), doc/28 (the special-campaign ruling report) |

---

## 0. Summary

RVV v1.0 §11.15 specifies: vmerge writes back over **all body elements** — v0 is
only the per-lane **data selector** (v0[t]=1 selects vs1[t], =0 selects vs2[t]),
**not a write enable**. Under the Ventus subset, body ≈ the SIMT active lanes
(the lanes with tmask=1).

After the I-12 fix (the i12 patch) made the mask path usable, the actual write
mask was exposed as the **unconditional override** at `execution.scala:559`,
`result.io.enq.bits.wvd_mask := io.in.bits.mask` — while `io.in.bits.mask` has
already been assembled as **v0 ∧ tmask** at `pipe.scala:366` (an irreversible
merge). Chisel last-connect-wins turns the `:541` VMERGE branch's intent
`wvd_mask(x):=true.B` into dead code. **The machine actually writes only the
v0∧tmask lanes, deviating from RVV's "write all active lanes"**.

The exact semantic difference: the only deviating lane class is **tmask=1 ∧
v0[t]=0** — RVV requires writing vs2[t], but the machine does not write (vd[t]
keeps its old value). When v0 ⊇ tmask the two sides are equivalent; the vmerge
data path (the selector) is entirely correct — only the write enable is wrong.

Observability is conditional: fully observable when vd≠vs2 (the distinguishing
program has been designed: v0=0x0000FFFF + vd preset to a sentinel + a vse32
readback; lanes 16–31 keep the sentinel); unobservable when vd=vs2 (the LLVM tied
destination-register convention, the norm for compiler output).

This entry belongs to the same "fix-exposure group" as I-48: the I-12 fix made
the mask path usable, and only then did the second-layer write-mask semantic
deviation become observable (previously blocked upstream by the I-12 deadlock).

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **vmerge (RVV §11.15)**: `vmerge.vvm vd, vs2, vs1, v0` — selects per lane by
  the v0 mask bit: if v0[t]=1 then vd[t]=vs1[t], else vd[t]=vs2[t]. The key
  difference from ordinary arithmetic instructions: **merge operates on all body
  elements** (the v-spec's original text: "the merge operates on all body
  elements") — v0 selects data rather than enabling writes; the write enable is
  determined solely by the body (≈ the activity mask tmask). vmerge.vxm/vim are
  analogous (vs1 replaced by a scalar/immediate).
- **tmask vs v0**: tmask (the SIMT active-thread mask, from simt_stack's
  out_mask) determines which lanes are "active threads"; v0 is vmerge's per-lane
  selector. The two masks are semantically orthogonal: activity decides "write or
  not", v0 decides "which source to write".
- **wvd_mask**: the write-back stage's per-lane write enable, via
  `operandCollector.scala:614` (`x.rdwmask := io.writeVecCtrl.bits.wvd_mask`) to
  the register file's bitwise write — lanes with mask 0 are not written.
- **Chisel last-connect-wins**: among multiple `:=` connections to the same
  signal, the last in code order takes effect — the unconditional assignment at
  `:559` turns the conditional assignment at `:541` into dead code.

### 1.2 Design intent

Decode (DecodeUnit.scala:367-369) forces mask=1 for the three VMERGE_VVM/VXM/VIM
opcodes (in RVV, vmerge is encoded with vm=0 and uses v0 as the selector);
execution.scala:539-542's VMERGE branch computes
`wb_wvd_rd(x) := Mux(mask(x), in1(x), in2(x))` (the data selection is correct)
and **intends** `wvd_mask(x):=true.B` (write all lanes) — i.e. the original
author knew vmerge should write everything, but that intent is overridden by
:559.

---

## 2. Line-by-Line Reading of the Original Code

**Construct one: tmask and v0 are irreversibly merged at the issue stage**
(`pipe.scala:366`, ★pitfall one):

```scala
exe_dataV.io.enq.bits.mask := collector.mask ∧ simt_stack.io.out_mask
```

The `io.in.bits.mask` entering the vALU = **v0 ∧ tmask** — two semantically
orthogonal masks are compressed into one field here, and downstream can no longer
distinguish "active but v0 selects 0" from "inactive".

**Construct two: the VMERGE branch's data selection is correct, but its write-mask
intent is overridden** (`execution.scala:539-542` + `:559`, ★core pitfall):

```scala
// :539-542 (VMERGE branch):
wb_wvd_rd(x) := Mux(mask(x), in1(x), in2(x))   // data correct: v0=1 selects vs1, v0=0 selects vs2
wvd_mask(x) := true.B                          // intent: write all lanes (RVV semantics)
// :559 (unconditional override, last-connect-wins):
result.io.enq.bits.wvd_mask := io.in.bits.mask // ★ actual write mask = v0 ∧ tmask
```

The `true.B` intent at `:541` becomes dead code; the actual write mask =
construct one's merged v0∧tmask.

**Construct three: write-back consumes the mask bitwise**
(`operandCollector.scala:614`):

```scala
x.rdwmask := io.writeVecCtrl.bits.wvd_mask
```

Lanes with mask 0 are not written and keep their old values — the deviation
lands here as observable behavior.

**Decode side** (correct, not a pitfall): `DecodeUnit.scala:367-369` forces
mask=1 for the three VMERGE opcodes (`:588`
`c.mask := ((~inst(25)) | alu_fn===FN_VMERGE) & ...`) — in RVV, vmerge is encoded
with vm=0 and uses v0 as the selector; the hardware uniformly treats it as "read
v0", which is correct.

---

## 3. Bug Analysis

### 3.1 Precise description of the defect

Per-lane semantic difference (the I-12-fixed machine vs the RVV-subset golden
semantics, the doc/28 §3 ruling table):

| lane class | RVV requires | fixed-version machine behavior | consistent? |
|---|---|---|---|
| tmask=0 | do not write (inactive thread) | do not write | ✓ |
| tmask=1 ∧ v0[t]=1 | write vs1[t] | write vs1[t] | ✓ |
| tmask=1 ∧ v0[t]=0 | **write vs2[t]** | **do not write (vd[t] keeps its old value)** | ✗ the only deviating class |

The necessary and sufficient condition for the deviation: there exists a lane t
with tmask[t]=1 ∧ v0[t]=0 ∧ vd's old value[t] ≠ vs2[t]. Equivalently: **when v0 ⊇
tmask (v0 covers all active lanes) the two sides are equivalent**. The vmerge
data path itself (the selector) is entirely correct — only the write enable is
wrong.

### 3.2 Root cause

Maintenance drift: the all-true intent at `:541` proves the original author knew
vmerge should write all lanes; the unconditional override at `:559` (put in place
as the uniform exit for ordinary instructions) turned it into dead code, and the
upstream v0∧tmask merge at `pipe.scala:366` means "restoring tmask" has no
ready-made signal at the execution stage — the fix must add a new datapath field
(see §7); it is not a single-point change.

### 3.3 Harm and tolerability

- **Harm**: **silent wrong data** under hand-written / non-standard compilation
  paths (lanes with tmask=1∧v0[t]=0 keep vd's old value instead of vs2[t]); the
  RVV compliance claim does not hold.
- **Observability**: fully observable when vd≠vs2; **unobservable when vd=vs2**
  (the unwritten lanes' old values happen to be vs2[t], agreeing with the RVV
  result). LLVM's RVV backend uses tied destination registers for merge-class
  pseudo-instructions (the destination is bound to the false/merge operand), so
  vd=vs2 is a structural norm in compiler lowering output; the Ventus toolchain
  is LLVM-based, hence **compiler-generated kernels normally do not trigger** the
  deviation (this item is a convention-level fact, not verified point by point on
  this project's toolchain; doc/02 additionally records that the official
  vecadd's vmerge never lies on the execution path, consistent with "the official
  software stack does not trigger it").
- **Tolerability**: unobservable in compiler output (the vd=vs2 convention);
  triggerable by hand-written kernels. Rating: high (ISA conformance level), but
  the trigger surface is masked by software convention.
- **Relation**: this entry is a "post-fix exposure" follow-up of I-12 — before
  the I-12 fix, vmerge deadlocked in the CU and this entry was unreachable; after
  the fix made the mask path usable, the write-mask semantic difference became
  observable.

---

## 4. Lean Formal Evidence

The evidence takes the form of a **consistency cross-check**: the ISA golden
semantics and the machine-side model are each established independently, and
their per-lane difference is exactly this entry's semantic difference —

- **Golden-semantics side** (`lean/VentusF/IsaSpec.lean` D6, header note :44-50
  + :415): the VMERGE write mask = **tmask** (RVV-subset semantics,
  `let wm := if row.aluFn = 51#6 then s.tmask else isaEffMask s inst row`); the
  header note already states "if the machine is not fixed, the capping theorem
  fails on vmerge — a registered expected-failure point" — i.e. the methodological
  registration of "failure points = the bug list".
- **Machine side** (`lean/VentusF/SMMem.lean:611-613`): the write mask
  `wbVMaskFn = smwWbMaskFn exeMaskV` (= v0∧tmask, faithful to the override
  semantics of execution.scala:559).
- **Selector consistency** (IsaSpec.lean:663 `isa_lane_vmerge_match`): VMERGE's
  selector (the v0 bit) agrees with the execution stage — no difference on the
  data side; the difference is only in the write mask.
- **Proof-side projection** (`lean/VentusF/CapExist.lean:57-67`, the G-E1-valu
  gap registration): the VMERGE segment's realizable domain = **v0 = tmask**
  (data side v0 ⊆ tmask + write-mask side tmask ⊆ v0) — the corresponding theorem
  `smwWbMaskFn = isaEffMask` is missing and carried as a hypothesis, which is
  exactly the proof-side projection of this entry's semantic difference in the
  capping refinement proof (:64-66 explicitly notes "the proof-side projection of
  the confirmed I-50 bug"). `RefineVec.lean:277-289` (`rfv_isaStep_valu`) likewise
  bridges via the VMERGE special case wm=tmask.

---

## 5. Simulation Verification

**Not executed in this environment; the distinguishing program has been designed
(ready-to-run (not executed in this environment))** 【ready-to-run (not executed
in this environment)】.

Distinguishing program (doc/28 §5.4, single warp, no divergence): preset v0's row
lane0 to 0x0000FFFF, preset vd (e.g. v3) to a sentinel value, execute
`vmerge.vvm v3, v2, v1, v0`, store back with vse32 and scalar-read lanes 16–31 —
RVV expects the vs2 values, while the machine yields the sentinel (lanes 16–31
are exactly the tmask=1∧v0[t]=0 deviating class). vmerge.vxm/vim are analogous
(same mask path; in1 replaced by a scalar/immediate broadcast).

Prerequisite: must run on the **I-12-fixed RTL** (on the original, vmerge dies of
the I-12 deadlock first, and this entry is unreachable). doc/22's existing suites
do not cover this item (the OperandCollectorBugRepro I-12 case only verifies
"masked instructions issue normally", not the write-mask semantics).

---

## 6. Upstream Impact Analysis

- **Trigger surface**: any vmerge (any of the three opcodes vvm/vxm/vim) with
  vd≠vs2 and at least one tmask=1∧v0[t]=0 lane. Compiler output is masked by the
  vd=vs2 convention; hand-written assembly, non-LLVM backends, and unconventional
  allocation under register-allocation pressure can all trigger it.
- **Why upstream did not find it**: same reason as I-12 — the official test stack
  does not issue vmerge (the official vecadd's vmerge is not on the execution
  path), and the I-12 deadlock makes any vmerge hang before execution, so this
  entry's semantic difference never even had a chance to be observed.
- **Compliance**: the RVV compliance claim does not hold on vmerge; under option
  B (contractualize without fixing), the claim "the fixed version conforms to
  RVV" must be downgraded to "conforms under the vd=vs2 convention".

---

## 7. Fix Proposal and Fix Verification

**No patch** (the internal fix manifest: functional fix (required), patch to be designed).
doc/28 recommends **option A**:

- `pipe.scala`: add a `tmask` field to vExeData (Vec(num_thread, Bool())), and
  near :366 `exe_dataV.io.enq.bits.tmask := simt_stack.io.out_mask` — pass tmask
  independently into the execution stage;
- `execution.scala:559` (the isomorphic branches) conditionalized:
  `result.io.enq.bits.wvd_mask := Mux(io.in.bits.ctrl.alu_fn===FN_VMERGE,
  io.in.bits.tmask, io.in.bits.mask)`.
- Cost: the vExeData bundle gains one field, threaded through the issue queue and
  the vALU input; the vMUL/FPU/SFU paths are unaffected. ISA-visible: yes
  (restores RVV semantics, in the same direction as the D1 decision "fix and
  conform to the RVV standard subset"). Low risk.

**The explicitly forbidden option C** (recorded in doc/28 §4): directly
activating the dead-code intent at `:541` (making `wvd_mask(x):=true.B` take
effect) — io.in.bits.mask = v0∧tmask is already merged at pipe.scala:366, so an
all-true mask would **also write the tmask=0 inactive lanes** (writing vs2's
values into these lanes), polluting the live registers of other threads on the
SIMT divergence path — turning "under-writing" into "over-writing", worse than
the status quo.

**Lean-side follow-up** (doc/28 §5.3, not started): after option A lands, add a
vmerge mask-fixed version to the VentusF execution stage (write mask = tmask) and
the machine-level alignment theorem `smwWbMaskFn = tmask` (the VMERGE special
case), which would exactly fill the gap registered under CapExist G-E1 and turn
the capping refinement green on vmerge; if it is not fixed for now, keep the
IsaSpec D6 status quo with the "expected-failure point" registration.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | line-by-line check of execution.scala:539-542/:559, pipe.scala:366, DecodeUnit.scala:367-369/:588, operandCollector.scala:614; the semantic-difference table (doc/28 §3) | source level, special-campaign ruling |
| Lean consistency cross-check | IsaSpec D6 (golden wm=tmask) vs SMMem wbVMaskFn=v0∧tmask (machine-faithful); `isa_lane_vmerge_match` (no difference on the selector side); the CapExist.lean G-E1-valu gap = the proof-side projection of the semantic difference | machine-checked (the two-side models established independently) |
| Simulation reproduction | the distinguishing program has been designed (v0=0x0000FFFF + sentinel + vse32 readback), not executed in this environment; requires the I-12-fixed RTL | ready-to-run |
| Fix proposal | doc/28 option A (tmask into vExeData + :559 conditionalization); no patch; option C (activating the dead code) argued infeasible | design level |

I-50 belongs to the same "fix-exposure group" as I-48 but in a different form:
I-48 is "fixing bug A activates a latent bug B" (same-module masking), while I-50
is "after a fix makes the path usable, a second-layer semantic deviation becomes
observable" (cross-module layered exposure). Together the two support one
methodological conclusion: **fix verification must not only check "the original
symptom disappears", it must also specifically evaluate the downstream semantics
of the repaired path** — doc/28's per-lane semantic-difference table is a model
of that evaluation.
