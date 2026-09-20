> English translation of the Chinese master `doc/bugs/I-52-ScalarFPU出端bits切换.md`. Translated 2026-09-13.

# I-52 Detailed Defect Report: fudian ScalarFPU output switches out.bits under cross-fu interleaving + backpressure (literal DecoupledIO contract violation)

| Item | Content |
|---|---|
| ID | I-52 |
| Source location | `dependencies/fpuv2/src/main/scala/FPU.scala:8-45` (ScalarFPU: `:33-37` in.ready MuxLookup accepting five leaves independently + `:39-44` fixed-priority Arbiter at the output) — **the defect is in the fpuv2/fudian library**, pulled into Ventus via the fpuv2 dependency |
| Type | Handshake protocol violation (literal violation of DecoupledIO Stable/Irrevocable) — latent defect |
| Severity | **Medium** (the literal violation is real; current downstream consumes on fire so it is functionally tolerable; broken-window condition = a change in the downstream consumption pattern) |
| Confirmation status | 【Confirmed·Latent】 |
| Main evidence | [Lean machine-checked proof] concrete witness `fwSfpu_stable_violation` (native_decide) + negative theorem `fwSfpu_not_stable` + positive boundary `fwSfpu_out_irrevocable_of_singleFu`; [direct source reading] FPU.scala:8-45 verified line by line |
| Lean model | `lean/VentusF/FpuWrap.lean` (1420 lines; §4 FwPipe2 elastic pipeline, §5 ScalarFPU dispatch and arbitration) |
| Reproduction/patch | Ready-to-run (not executed in this environment) (doc/22 has no execution record); no patch (fix = monitoring assertion suggestion + making the output Irrevocable) |
| Related entries | I-53 (boundary points of the FMA compound in the same library); RRArbiter note (the same-kind phenomenon of chisel Arbiter being non-Irrevocable, doc/03 review note); doc/29 (fudian numeric-core project plan); doc/30 §R5-B |

---

## 0. Summary

ScalarFPU (fpuv2/FPU.scala:8-45) is the per-lane scalar floating-point unit wrapper in Ventus: on the input side it dispatches transactions to five leaf units (FMA/FCMP/FPMV/FPToInt/IntToFP) according to `fu = op(5,3)`; on the output side a fixed-priority Arbiter (chisel `Arbiter`, lowest index wins) collects the five leaves' outputs.

The defect: **the five leaves accept transactions independently, with no global ordering constraint**. When transactions of two different fus are in flight and their completion times interleave, under backpressure (`out.ready=0`) the output switches `out.bits` from the value of the earlier-completing leaf to the value of another leaf — a strict literal violation of Chisel DecoupledIO's "bits stable while valid" convention (Stable/Irrevocable).

Machine-checked witness: at t0 a fu=1 (FCMP) transaction (payload 0xAA) is accepted, at t1 a fu=0 (FMA) transaction (payload 0xBB) is accepted, with backpressure throughout; at t2 the output has valid=1, bits=0xAA (the FCMP transaction completes first); at t3 bits switches to 0xBB (the FMA transaction completes, and fu=0 has higher priority) — **bits changed during a single unfinished handshake**.

The positive boundary is nailed down in the same file: when a single fu is in flight (input stream with constant fu), the output satisfies Irrevocable (`fwSfpu_out_irrevocable_of_singleFu`) — the violation **requires** cross-fu interleaving.

Under the current integration it is functionally tolerable: the downstream (FPUexe direct connection + writeback arbitration) consumes on fire (valid && ready on the same cycle); each transaction's bits are self-consistent and eventually consumed. It is a latent defect: as soon as the downstream switches to "sample first, wait later" (any consumption pattern that samples bits on valid), it breaks. **The defective code is in the upstream library and should be reported to OpenXiangShan/fudian** (the fpuv2 wrapper and the fudian numeric core belong to the same upstream family, doc/29).

---

## 1. Module function and design intent

### 1.1 Background concepts

- **fpuv2/fudian**: Ventus's floating-point datapath comes from the OpenXiangShan project family's fpuv2 wrapper + fudian numeric core (`dependencies/fpuv2/`; ownership confirmed by the doc/29 project plan). ScalarFPU is the per-lane scalar FPU wrapper; VectorFPU packs 32 ScalarFPUs into a vector unit (current configuration softThread==hardThread==32, the equality branch is a pure combinational broadcast).
- **fu dispatch**: the high 3 bits of the 6-bit op (`op.head(3)`, FPU.scala:23) select the leaf: 0=FMA (fused multiply-add / add-sub / multiply), 1=FCMP, 2=FPMV, 3=FPToInt, 4=IntToFP. Each leaf is an independent elastic pipeline (HasPipelineReg, latency=1/2), each with its own in.ready / out.valid.
- **The DecoupledIO contract**: Chisel's valid/ready channel convention — once valid is raised, until fire (valid && ready) valid must not be withdrawn and bits must not change (the former is NoWithdraw, the latter Stable; together Irrevocable). A consumer may legitimately "sample bits on the valid cycle and wait for ready at leisure".
- **Arbiter (chisel fixed-priority)**: `out.valid = OR of the inputs' valid`, `out.bits = bits of the lowest-index valid input` — the selection is **purely combinational**, with no locking.

### 1.2 Design intent

The intent of the output Arbiter is clearly "whichever leaf finishes first goes out first". The designer's implicit assumption is "at most one leaf has an unfinished output at any time" or "the downstream consumes on fire" — but nothing in the code guarantees the former.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: the five leaves accept independently, with no global ordering constraint** (`FPU.scala:15-37`):

```scala
val subModules = Array[FPUSubModule](
  Module(new FMA(...)), Module(new FCMP(...)), Module(new FPMV(...)),
  Module(new FPToInt(...)), Module(new IntToFP(...)))            // :15-21
val fu = io.in.bits.op.head(3)                                    // :23
for((module, idx) <- subModules.zipWithIndex){
  ...
  module.io.in.valid := idx.U===fu && io.in.valid                 // :31
}
io.in.ready := MuxLookup(fu, false.B)(                            // :33-37 ★
  subModules.zipWithIndex.map{ case (module, idx) => idx.U -> module.io.in.ready }
)
```

★ Hazard 1: the input side only looks at the **target leaf's** ready — while a fu=0 leaf is busy, a fu=1 transaction can still be accepted (its leaf is idle). Two transactions of different fus in flight simultaneously is structurally allowed.

**Construct 2: fixed-priority combinational arbitration at the output** (`FPU.scala:39-44`):

```scala
val outArbiter = Module(new Arbiter(new FPUOutput(64, ctrlGen), 5))  // :39 ★
subModules.zipWithIndex.foreach{ case (module, idx) =>
  outArbiter.io.in(idx) <> module.io.out
}
io.out <> outArbiter.io.out                                          // :43
io.select := outArbiter.io.chosen                                    // :44
```

★ Hazard 2: `io.out.bits` = the combinational output of the currently lowest-index valid leaf. If, during backpressure, a **higher-priority** (lower fu index) leaf completes, `out.bits` switches on that cycle — the bits of the transaction that was holding valid and waiting are swapped out. This is the direct mechanism of the Stable violation.

(Cross-reference: this project's same-kind examination of the chisel RRArbiter is recorded in a doc/03 review note — with count=1, out is non-Irrevocable; during backpressure chosen can be changed on the spot by a newly arriving request; the `rra3_not_stable` witness is on record. I-52 is an instance of that phenomenon family on the fixed-priority Arbiter in the fudian library.)

**Construct 3: the leaves themselves are compliant** (HasPipelineReg.scala:16-39, elastic pipeline skeleton): when stage 2 stalls, valid and bits are both held in registers — a single leaf's output satisfies Irrevocable (fully proven on the Lean side as `fwPipe2_out_irrevocable`). **The violation arises only at the five-leaf composition layer.**

---

## 3. Defect analysis

### 3.1 Precise description of the defect

**Machine-checked witness** (`fwSfpuWitStream`, FpuWrap.lean:825-828; payloads abstracted as BitVec 8):

| Cycle | Event | out.valid | out.ready | out.bits |
|---|---|---|---|---|
| t0 | accept fu=1 (FN_MIN→FCMP leaf) transaction, payload 0xAA | — | 0 | — |
| t1 | accept fu=0 (FN_FADD→FMA leaf) transaction, payload 0xBB | — | 0 | — |
| t2 | FCMP transaction reaches the leaf output | **1** | 0 | **0xAA** |
| t3 | FMA transaction reaches the leaf output (fu=0 has higher priority) | 1 | 0 | **0xBB** ← switch |

t2→t3: valid stays high, no fire (ready=0), bits change from 0xAA to 0xBB — a literal violation of Stable. Beyond that, if backpressure continues and the FCMP transaction is "forgotten" first, there is a second-layer problem of response-order confusion (the completion of the earlier transaction gets presented as superseded by the later one).

**Boundary (nailed down positively in the same file)**: when the input stream has constant fu (single fu in flight), the isolation invariant (`fwSfpu_iso_run`: non-k leaves stay empty; leaf k matches standalone operation) degenerates the output to a single-leaf output, and Irrevocable holds (`fwSfpu_out_irrevocable_of_singleFu`). That is: **cross-fu interleaving is a necessary condition**.

### 3.2 Root cause

The output arbitration is a purely combinational fixed-priority selection, with no "transaction locking" mechanism (no record of "which leaf the currently presented output belongs to; only allow switching once it fires"). The unconstrained input dispatch (construct 1) makes cross-leaf interleaving legitimately possible. Combined: an earlier-completing lower-priority transaction can be displaced from presentation by a later-completing higher-priority transaction during backpressure.

### 3.3 Harm and tolerability

- **Harm (potential)**: any downstream that "samples bits on the valid cycle, then waits for ready" will sample transaction A's bits but consume transaction B at fire — responses attributed to the wrong transaction. Moreover, out.bits.ctrl carries writeback routing information (wvd/wxd/regIndex/warpID/vecMask); a switch means the writeback target is swapped wholesale.
- **Basis for current tolerability** [direct source reading + Lean model header note Q-FW-1]: Ventus's current downstream (execution.scala FPUexe direct connection + writeback arbitration) **consumes on fire** (sampling when valid && ready on the same cycle); the bits consumed are then always the bits of the fire cycle, and each transaction's bits are self-consistent (leaf-level Irrevocable guarantees that a single transaction is not modified while presented... no — strictly speaking bits do change, but the value sampled at the fire cycle belongs to some genuinely completed transaction, and ctrl is paired with its transaction (leaf-level FIFO ordering, `fwPipe2_fifo_*`). Functionally, every transaction is eventually consumed exactly once). Hence the doc/03 judgment: **functionally tolerable, but the tolerability depends on the downstream consumption discipline**.
- **Broken-window condition**: the downstream switches to "sample first, wait later" (e.g. inserting a non-transparent register stage, or adding a consumer that pre-samples on valid). Rating: latent, medium.

---

## 4. Lean formal evidence

Everything is in `lean/VentusF/FpuWrap.lean` (handshake contract definitions `Stable`/`Irrevocable` from `Ventus/Base/Handshake.lean`; the axiom audit block is in the file's §9 — native_decide tests carry the `Lean.ofReduceBool` trust axiom, structural theorems use only the standard axioms; noted for archival):

**Negative (machine-checked violation)**:

- `fwSfpu_stable_violation` (:832, native_decide): the witness stream has (valid=1, ready=0) at t2/t3 ∧ bits differ cycle to cycle — the mechanization of the §3.1 table;
- `fwSfpu_not_stable` (:842): `¬ Handshake.Stable (fwSfpuOutTrace …)` — the theorem-level conclusion that the output channel does not satisfy Stable (and hence not Irrevocable).

**Positive (boundary nailed down)**:

- `fwPipe2_out_irrevocable` (:474): a HasPipelineReg single leaf's output is Irrevocable (arbitrary backpressure streams) — leaf-level compliance;
- `fwSfpu_iso_step`/`fwSfpu_iso_run` (:699/:755): the isolation invariant — when the input stream's fu is constantly k, non-k leaves stay empty and leaf k matches standalone operation;
- **`fwSfpu_out_irrevocable_of_singleFu`** (:790): single fu in flight ⟹ ScalarFPU output is Irrevocable — the necessary-and-sufficient boundary of the violation: "cross-fu interleaving" is a necessary condition;
- Support: `fwSfpuArbSel_of_iso` (:663, characterization of the arbitration selection under an isolated leaf), `fwK_cases` (:659, case split of fu<5), `fwPipe2Step_outRdy_irrel` (:647).

**Incidental structural adjudications** (same file, registered in doc/03 as Q-FW-2/Q-FW-3):

- `fwSfpu_inRdy_dead`/`fwSfpu_inRdy_dead_apply` (:621/:628): with fu ≥ 5 (illegal op), in.ready is constantly false — deadlock rather than an error; the current decode table never produces it (fpu_utils.scala's max FN=35 → fu=4), unreachable;
- unselected leaves' bits zeroed (FPU.scala:25-30): harmless (leaves do not sample them); registered in header note Q-FW-3.

---

## 5. Simulation verification

【Ready-to-run (not executed in this environment)】**Not executed in this environment**. doc/22 has no I-52 entry. Directed reproduction plan (ChiselSim, directly instantiating fpuv2's ScalarFPU): issue one transaction to fu=1 at t0 and one to fu=0 at t1, hold out.ready low throughout, observe the out.bits switch at t2→t3; control group: a single-fu stream (should be stable). The reproduction code is yet to be written.

---

## 6. Upstream impact analysis

- **Report target**: **OpenXiangShan/fudian** (stated explicitly in doc/03; the fpuv2 wrapper and the fudian numeric core belong to the OpenXiangShan project family, ownership confirmed in doc/29 §risk table). Ventus merely pulls it in via a dependency; the same ScalarFPU structure is inherited by any downstream adopting fpuv2.
- **Trigger surface**: any integration that issues to two different fus simultaneously while the output is backpressured. Ventus's FPUexe issues at most one transaction per cycle, but cross-fu back-to-back issue (t0 FCMP, t1 FMA) is perfectly legal and common (floating-point code mixes comparisons and arithmetic).
- **Why upstream did not find it**: fudian's official downstreams (XiangShan etc.) consume on fire; and most verification checks only "numeric correctness", not the literal handshake convention. A literal Stable/Irrevocable violation is exactly the hit surface of formal contract checking (the Handshake specification).

---

## 7. Fix proposal and fix verification

**Fix suggestions** (copied verbatim from doc/03, pick one):

1. Register the output for one cycle (make it Irrevocable): pass the Arbiter output through `Queue(..., 1, pipe=false)` or manual valid/bits registers (lock once valid is raised until fire);
2. Lock the arbitration selection during backpressure: freeze `chosen` while not fired (latch the current selection until out.fire).

**Monitoring assertion** (defense in depth, do first): `assert(!out.valid || out.ready || stable(out.bits))` — bits do not change cycle to cycle while valid and not fired.

**Fix verification**: not done (no patch, no fixed-version model). A fixed version can be verified directly with the existing FpuWrap.lean framework: after remodeling the output with a locked selection, the negated goal of `fwSfpu_not_stable` should become provable (the witness stream turns green).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | FPU.scala:15-21/:23/:31/:33-37/:39-44 verified line by line (§2 of this report) | Precisely located |
| Lean machine-checked proof (negative) | fwSfpu_stable_violation (concrete witness) + fwSfpu_not_stable (¬Stable) | Theorem-level |
| Lean machine-checked proof (positive boundary) | fwSfpu_out_irrevocable_of_singleFu (single fu in flight ⇒ Irrevocable) + fwPipe2_out_irrevocable (leaf-level compliance) | Arbitrary input streams, conditional form |
| Simulation reproduction | Ready-to-run (doc/22 has no execution record) | Not executed |
| Fix verification | No patch; suggested output Irrevocable-ization + monitoring assertion | Not done |

I-52 is a typical case of the "literal handshake-contract violation" family (same family as the project's internal RRArbiter count=1 note): simple mechanism (combinational arbitration without locking), currently harmless (the downstream happens to consume on fire), and the literal violation is ironclad (theorem-level witness + negation). Its value lies in narrowing H-FPU-2's universal "Irrevocable" claim to the conditional form "single fu in flight" — the applicability boundary of the contract is itself the precise characterization of this bug. The defect is in the upstream library and should be reported to OpenXiangShan/fudian.
