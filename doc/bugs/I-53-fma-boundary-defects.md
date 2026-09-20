> English translation of the Chinese master `doc/bugs/I-53-FMA边界缺陷组.md`. Translated 2026-09-13.

# I-53 Detailed Defect Report: Two boundary points of the fudian FMA compound (Q-FM-2 silent drop + Q-FM-1 fragile lockstep) and one misleading comment (Q-FM-3)

| Item | Content |
|---|---|
| ID | I-53 (three items recorded together: Q-FM-2 / Q-FM-1 / Q-FM-3) |
| Source location | `dependencies/fpuv2/src/main/scala/FMA.scala`: `:166` (the Mux dispatch of io.in.ready; doc/03 records :162) and `:133-161` (addPipe data/ctrl split wires; doc/03 records :151-158); `utils/FPUOps.scala:61-86` (the isADDSUB/isFMA/isFMUL classification); `ventus/src/pipeline/fpu_utils.scala:20` (misleading FN_FSUB comment) — **all on the fpuv2/fudian library side or its interface comments toward Ventus** |
| Type | Q-FM-2: latent functional defect (currently unreachable); Q-FM-1: fragile point (not a bug); Q-FM-3: documentation-level comment error (harmless) |
| Severity | **Low** (all three are currently unobservable/harmless; broken-window conditions are respectively decode-table evolution, parameter changes, and readers trusting the comment) |
| Confirmation status | 【Confirmed·Latent】 |
| Main evidence | [Lean machine-checked proof] Q-FM-2 witness `ffm_test_op3_silent_drop` (native_decide); Q-FM-1 lockstep theorem family `ffm_lockstep_straight_step/run`, `ffm_lockstep_fma_step/run` (fully proven by induction); [direct source reading] FMA.scala/FPUOps.scala/fpu_utils.scala verified line by line |
| Lean model | `lean/VentusF/FpuFma.lean` (1134 lines, R5-B second wave: modeling of the FMA compound's real pipeline structure) |
| Reproduction/patch | Not needed (Q-FM-2 is unreachable under the current decode table; Q-FM-1/Q-FM-3 are not functional bugs); no patch |
| Related entries | I-52 (ScalarFPU output arbitration in the same library); doc/29 (fudian numeric-core project plan); doc/30 §R5-B |
| Upstream | **Should be reported to OpenXiangShan/fudian** (stated explicitly in doc/03; fpuv2/fudian belongs to the OpenXiangShan project family, doc/29) |

---

## 0. Summary

In the R5-B second wave, while modeling the real pipeline structure of fpuv2's FMA compound (FMA.scala:115-177: FMULPipe lat=2 + FADDPipe lat=1 + 6 queues + 2 arbiters), source review found three boundary issues, registered together as I-53:

- **Q-FM-2 (latent, currently unreachable)**: op=3 (fu=0 and op(2,0)=3) belongs to no operation class (neither ADDSUB nor FMA nor FMUL), but io.in.ready takes the else branch (= mulPipe.ready) and can still fire — once accepted, the transaction **enters no container and is silently dropped**. The current decode table has no such encoding, so it is unreachable; the broken-window condition = the decode table gains this encoding without connecting it to the FMA datapath.
- **Q-FM-1 (fragile point, not a bug)**: addPipe's data and ctrl/op travel on separate wires — data comes from inToAddFIFO/mulToAddFIFO, ctrl/op from the arbiter output — so safety depends entirely on the lockstep equality of two pairs of parallel FIFOs. Lockstep has been proven as theorems under the current configuration (`ffm_lockstep_*`), but this is a "dies the moment any queue depth/flow-through parameter changes" fragile point; any change requires re-proof.
- **Q-FM-3 (documentation level, harmless)**: the ventus-side comment at `fpu_utils.scala:20`, "FN_FSUB io.(b * 1 - a)", conflicts with the fpuv2 comment "io.(a - b)"; the implementation (FMA.scala:85-98: invAdd negates b) agrees with the fpuv2 comment (a - b) — the ventus-side comment is misleading.

Disposition: latent registration + monitoring assertion suggestions; for Q-FM-3, suggest a comment fix to upstream.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **FMA compound**: the fu=0 leaf unit in fpuv2; a single physical pipeline carries three kinds of floating-point operations: FADD/FSUB (add/subtract), FMUL (multiply), FMADD/FMSUB/FNMSUB/FNMADD (fused multiply-add). Internally = FMULPipe (two-stage multiply pipeline) + FADDPipe (one-stage add pipeline) + several 1-deep pipe queues and two arbiters: FMA transactions pass through mulPipe then addPipe (two stages in series), pure-multiply transactions go through mulPipe and exit directly via mulFIFO, pure-add transactions go from the input through fifo1∥inFifo straight into addPipe.
- **op classification** (FPUOps.scala:61-86): `isADDSUB` (op(2,1)=0 and head(3)=0, i.e. op∈{0,1}), `isFMA` (op(2)=1 and head(3)=0, i.e. op∈{4,5,6,7}), `isFMUL` (op=2). **op=3 is none of the three classes** — it is the carrier of Q-FM-2.
- **Data/ctrl split wires**: a Bundle-granularity problem in Chisel — addPipe needs the complete input transaction (data) plus the arbitrated op/ctrl. The designer routes data through one pair of FIFOs and ctrl/op through another pair (toAddArbiterFIFO); the two pairs are parallel with identical parameters, kept synchronized by "same cycle, same fire" — this is Q-FM-1's lockstep dependency.
- **withSUB** (FPUOps.scala:88-90): `op(0)` indicates subtraction — for FSUB (op=1), negate the second operand and implement subtraction as addition (Q-FM-3 concerns its implementation semantics).

### 1.2 Design intent

The intent of the compound pipeline is area reuse: one multiplier and one adder, shared by three operation classes. The split wires (Q-FM-1) are an engineering compromise of "ctrl/op needs the arbiter's selection while data needs to flow through"; the else branch for op=3 (Q-FM-2) is an unintended side effect of the Mux default branch — the designer put no guard on "out-of-class ops" because the decode layer guarantees they never occur.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: input dispatch and the acceptance window for out-of-class ops (carrier of Q-FM-2)** (`FMA.scala:122,:139,:147,:166`):

```scala
mulPipe.io.in.valid := io.in.valid && (FPUOps.isFMA(io.in.bits.op) || FPUOps.isFMUL(io.in.bits.op))  // :122
...
toAddArbiterFIFO(1).io.enq.valid := FPUOps.isADDSUB(io.in.bits.op) && io.in.valid                     // :139
inToAddFIFO.io.enq.valid       := FPUOps.isADDSUB(io.in.bits.op) && io.in.valid                       // :147
...
io.in.ready := Mux(FPUOps.isADDSUB(io.in.bits.op), toAddArbiterFIFO(1).io.enq.ready,
                   mulPipe.io.in.ready)            // :166 ★ else branch = mulPipe.ready
```

★ Hazard (Q-FM-2): with op=3, `isADDSUB(3)=false` (op(2,1)=01≠0, FPUOps.scala:61-68), so :166 takes the else branch — in.ready = mulPipe.io.in.ready, **which can be 1**; but mulPipe's enq.valid at :122 includes `isFMA||isFMUL`=false, and the FIFOs' enq.valid at :139/:147 include `isADDSUB`=false — **every container's enq.valid is 0**. in.fire holds while no container receives the transaction: the transaction is "successfully accepted" at the interface and physically dropped.

**Construct 2: addPipe's data/ctrl split wires (carrier of Q-FM-1)** (`FMA.scala:133-161`):

```scala
val toAddArbiterFIFO = Seq.fill(2)(Module(new Queue(new ArbiterIO, entries = 1, pipe = true)))  // :134 ctrl/op wire
...
val inToAddFIFO = Module(new Queue(io.in.bits.cloneType, entries = 1, pipe = true))   // :145 data wire (direct path)
inToAddFIFO.io.deq.ready := toAddArbiter.io.in(1).ready                                          // :150 ★lockstep coupling point
val mulToAddFIFO = Module(new Queue(new MulToAddIO(...), entries = 1, pipe = true))   // :152 data wire (multiply path)
mulToAddFIFO.io.enq.valid := toAddArbiterFIFO(0).io.enq.fire                                     // :154 ★lockstep coupling point
mulToAddFIFO.io.deq.ready := toAddArbiter.io.in(0).ready                                         // :156
...
addPipe.io.in.bits := inToAddFIFO.io.deq.bits            // :148 data taken from the data FIFO
addPipe.io.in.bits.op := toAddArbiter.io.out.bits.op     // :149 op taken from the arbiter output (ctrl/op wire)
addPipe.fromMul := mulToAddFIFO.io.deq.bits              // :155
```

★ Fragile point (Q-FM-1): one addPipe transaction = the data-wire FIFO's deq.bits (data) + the arbiter output (op/ctrl), and **the two must describe the same transaction**. Safety depends on the cycle-by-cycle lockstep of two FIFO pairs:
- L1 (multiply path): toAddArbiterFIFO(0) (carries ctrl/op) ≡ mulToAddFIFO (carries multiply data) — :154 connects the latter's enq.valid to the former's enq.fire; deq.ready likewise at :141/:156;
- L2 (direct path): toAddArbiterFIFO(1) ≡ inToAddFIFO — same enq.valid (:139/:147), same deq.ready (:150).

**Construct 3: FSUB's subtraction implementation (the adjudication basis for Q-FM-3)** (`FMA.scala:87-99` + the two sides' comments):

```scala
val srcA = io.in.bits.a
val srcB = Mux(isFMA, fromMul.addAnother, io.in.bits.b)       // :88 when not FMA, srcB = b
val invAdd = withSUB(io.in.bits.op)                           // :90 op(0) (FSUB=1 → true)
val add2 = Cat(Mux(invAdd, invertSign(srcB), srcB), 0.U(precision.W))  // :96-99 ⇒ a + (−b)
```

Compare the comments — fpuv2 `utils/FPUOps.scala:13`: `FN_FSUB ... io.(a - b)` (consistent with the implementation ✓); ventus `pipeline/fpu_utils.scala:20`: `FN_FSUB ... io.(b * 1 - a)` (★ misleading: the operand order is written backwards). The implementation computes a − b. On the vector side there is an additional reverse mechanism (DecodeUnit.scala:283-284 + s(7) at :585) that swaps vfsub's ports to a=in2, b=in1, yielding in2−in1 = vs2−vs1, so the RISC-V operand order is correct — the mislead exists only at the comment level.

---

## 3. Defect analysis

### 3.1 Precise description

- **Q-FM-2**: a transaction with op=3 can fire at the FMA compound boundary (in.ready=mulPipe.ready), but enters none of mulPipe, fifo0, fifo1, inFifo — **accepted and dropped, with no response**. Machine-checked witness: `ffm_test_op3_silent_drop` (FpuFma.lean:775, native_decide) — boundary fire holds (`ffmInRdy = true`) and after stepping, the whole state is unchanged (`ffmStep s e = s`). Currently unreachable: the Ventus decode table (fpu_utils.scala:16-43) has no FN=3 encoding; fudian's FPUOps has no such definition either. Broken-window condition = the decode table gains this encoding without connecting it to the FMA datapath.
- **Q-FM-1**: not a bug — lockstep **is proven to hold** under the current configuration (§4). It is registered as a fragile point because its safety depends on the implicit invariant "both FIFO pairs have identical parameters and identical fire": change any queue's depth/flow-through parameters (pipe/flow), or touch the fire wiring at :154, and the split wires desynchronize (addPipe pairs transaction A's data with transaction B's op/ctrl) with no assertion able to detect it.
- **Q-FM-3**: a pure comment error with no functional impact; the harm is that a later reader trusting the ventus-side comment will misunderstand FSUB's operand order and write wrong upper-level code/tests.

### 3.2 Root cause

- Q-FM-2: the Mux default branch (else) inadvertently admits out-of-class encodings; there is no guard or assertion that "op must belong to one of the three classes".
- Q-FM-1: the engineering compromise of splitting a Bundle across wires demotes the identity of "the same transaction" from the type level to a timing coincidence.
- Q-FM-3: after the fpuv2 comment evolved, the ventus-side copy was not synchronized (fpu_utils.scala is the ventus local copy of FPUOps).

### 3.3 Harm and tolerability

All three are **currently harmless**: Q-FM-2 is decode-unreachable; Q-FM-1 is proven safe under the current configuration; Q-FM-3 is harmless. Disposition per doc/03: latent registration + monitoring assertion suggestions (for Q-FM-2, add an "op=3 must not fire" assertion; for Q-FM-1, add content-equality assertions on both FIFO pairs); for Q-FM-3, propose a comment fix upstream. Rating: low.

---

## 4. Lean formal evidence

Everything is in `lean/VentusF/FpuFma.lean` (8-container real pipeline structure model: mulPipe=FwPipe2, fifo0/fifo1/inFifo/mulAddFifo/addFifo/mulFifo=FfmQ1 (Queue(1,pipe)), addPipe=FfmPipe1; axiom audit block in §9):

**Q-FM-2 witness**:

- `ffm_classify_anchors` (:87, decide): with op=3, isADDSUB/isFMA/isFMUL are all false — the bit-level pinning-down of the out-of-class encoding;
- **`ffm_test_op3_silent_drop`** (:775, native_decide): an op=3 transaction's boundary fire holds (`ffmInRdy = true`) ∧ the state is wholly unchanged after stepping (`ffmStep s e = s`) — the mechanized witness of accept-and-silently-drop.

**Q-FM-1 lockstep theorem family** (universal proofs that it holds under the current configuration):

- `ffmQ1_step_valid_collapse` (:333): the collapse of a queue's enq.valid with its fire (L1's core algebraic fact: when full, enq.ready=deq.ready synchronizes fire);
- `ffm_lockstep_fma_step`/`ffm_lockstep_fma_run` (:348/:356): L1 — fifo0 ≡ mulAddFifo holds cycle by cycle (arbitrary environment streams, fully proven by induction);
- `ffm_lockstep_straight_step`/`ffm_lockstep_straight_run` (:340/:363): L2 — fifo1 ≡ inFifo holds cycle by cycle;
- Upper-level consumption: `ffmInv_step` (:497, the authenticity invariant preserved per step, whose premise is exactly the two pairs' lockstep equality) and `ffmInv_run` (:595, trace-level) — lockstep is the load-bearing wall of the invariant "all container payloads are authentic (= accepted inputs)"; `ffm_out_authentic` (:613)/`ffm_out_passthrough` (:642) discharge H-FPU-1 for the FMA path into theorems.

**Q-FM-3**: no theorem (a comment-level issue); the implementation semantics a−b is pinned down jointly by the direct source reading of §2 construct 3 and the contract table `ffmSpecSem` (FpuFma.lean:1007-1033: op=1 → `fsSub fsF32 rm a b`).

---

## 5. Simulation verification

Not applicable / not needed: Q-FM-2 is decode-unreachable today (no legal stimulus can produce op=3); Q-FM-1 is the registration of a fragile point that is not a bug (its "safe under current configuration" is already covered by the §4 theorems, which is stronger than simulation); Q-FM-3 is a comment issue. doc/22 has no I-53 entry and no pending test cases.

---

## 6. Upstream impact analysis

- **Report target**: **OpenXiangShan/fudian** (stated explicitly in doc/03). Q-FM-2/Q-FM-1 are in fpuv2's FMA.scala; Q-FM-3's misleading comment is in the ventus-side local copy (fpu_utils.scala), but the source of the correct wording is fpuv2 — the suggestion is to fix the comment on the ventus side; no action needed on the fudian side.
- **Broken-window conditions**: Q-FM-2 = the decode table gains an op=3 encoding without connecting it to the FMA datapath (easiest to hit during FPU feature extension); Q-FM-1 = any FIFO parameter change (easiest to hit during performance tuning).
- Value to the fudian community: both are low-cost improvements of the "turn into an assertion and you get defense" kind (`assert(op =/= 3 || !in.fire)`, content-equality assertions on both FIFO pairs).

---

## 7. Fix proposal and fix verification

- Q-FM-2: suggest adding a simulation assertion that "op=3 must not fire" (or change the Mux default branch at :166 to false.B — note this changes the behavior for illegal ops to "in.ready=0, wait", cleanest when paired with the assertion).
- Q-FM-1: add content-equality assertions on the two pairs of parallel FIFOs (at simulation time); re-run the lockstep proofs after any queue parameter change (the model is ready).
- Q-FM-3: change the ventus-side comment at `fpu_utils.scala:20` to `io.(a - b)` (consistent with the implementation and the fpuv2 comment).
- No patches and no fixed-version verification for any of them (handled as "latent registration + monitoring assertions", conclusion copied verbatim from doc/03).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | FMA.scala:122/:139/:147/:166 (Q-FM-2), :133-161 (Q-FM-1), :87-99 + fpu_utils.scala:20 + FPUOps.scala:13 (Q-FM-3) verified line by line | Three locations precisely pinpointed |
| Lean machine-checked proof (Q-FM-2) | ffm_classify_anchors + ffm_test_op3_silent_drop (accept-and-drop witness) | Theorem-level (decide/native_decide) |
| Lean machine-checked proof (Q-FM-1 positive) | ffm_lockstep_fma_step/run, ffm_lockstep_straight_step/run (fully proven by induction over arbitrary environment streams) + ffmInv_run as the load-bearing consumer | Universal / trace-level |
| Simulation reproduction | Not applicable (unreachable / not a bug / comment level) | — |
| Fix verification | No patch; assertion suggestions pending | Not done |

I-53 is a byproduct group from the source review during FPU wrapper-layer modeling: one latent defect of "Mux default branch admitting an out-of-class encoding", one fragile point of "split-wire transmission relying on timing coincidence", and one misleading comment. Individually none of them merits a standalone case; the value of recording them together is that they are all **mines for feature extension / parameter tuning** — registration + assertion-ization is the lowest-cost way to move the "broken-window condition" forward into an "immediate error report".
