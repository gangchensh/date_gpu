> English translation of the Chinese master `doc/bugs/I-31-汇合点重复入队排除.md`. Translated 2026-09-13.

# I-31 Detailed Defect Analysis Report: branch_join's pc_reconv valid Not fire-Gated; Reconvergence Point Could Be Enqueued Repeatedly 【Excluded】

| Item | Content |
|---|---|
| ID | I-31 |
| Source location | `ventus/src/pipeline/pipe.scala:390` (`simt_stack.io.pc_reconv.valid := issueV.io.out_SIMT.valid` — valid passes through directly, not fire-gated; the source carries its own `//todo check this`); downstream `branch_join.scala:84-86` (`Queue(io.pc_reconv, 1, flow=true)`) and `:124-138` (both queues' deq.ready assigned the same value, lockstep); `issue.scala:118-128` (out_SIMT.valid generation) |
| Type | Suspected functional bug (reconvergence-point bookkeeping corruption: the same RPC enqueued repeatedly) → excluded by machine-checked proof |
| Severity | None (excluded); residual fragility in §3.3 |
| Confirmation status | 【Excluded】(2026-08-27, `lean/Ventus/SIMT/PcReconv.lean`; doc/03 original verdict carried over verbatim) |
| Primary evidence | [Lean machine-checked proof] main theorem `pcrMain_i31_excluded` (enqueue counts 1:1 on arbitrary traces) + witnesses pcrW1–W5; [Direct source reading] the wiring chain across pipe.scala/issue.scala/branch_join.scala + semantics check against chisel 6.4.0 `Decoupled.scala:243-307` |
| Lean model | `lean/Ventus/SIMT/PcReconv.lean` (adjudicative model: a combinational slice of Issue valid generation + dual flow queues + branch_join consumption logic); corroborating evidence `Ventus/Top.lean` B-I31 (pinning the mechanism scene) |
| Repro/patch | ChiselSim directed test (backpressure out_SIMT for several cycles and observe dequeue count) ready-to-write — no longer necessary after exclusion, not executed in this environment; the internal fix manifest: No fix (excluded) |
| Related entries | doc/modules/16 (full record of the PcReconv adjudicative model), doc/modules/14 (the original suspicion raised on the Issue side) |

---

## 0. Summary

`pipe.scala:390` wires `simt_stack.io.pc_reconv.valid` directly to
`issueV.io.out_SIMT.valid` — **valid passes through directly, not fire-gated** (the
source carries its own `//todo check this` comment; the original author themselves
had doubts). Downstream sits a `Queue(_, 1, flow=true)`. The suspicion: while
out_SIMT is backpressured, valid stays high, and every time the flow queue frees a
slot it **enqueues the same simt_rpc once more** → the same reconvergence point (RPC)
gets popped multiple times → the SIMT stack's reconvergence bookkeeping goes wrong.

Via adjudicative modeling (PcReconv.lean), it was excluded by machine-checked proof
through two **mutually independent** mechanisms:

1. **vbranch side**: `out_SIMT.valid` is combinationally gated by ready
   (issue.scala:121-124: when opcode=0, `valid = inputV & out_SIMT.ready &
   out_vALU.ready`) — during backpressure, valid drops immediately, so "valid stays
   high under backpressure" is **structurally unreachable** (this coding style itself
   violates the Decoupled convention, but it happens to block half of the
   suspicion);
2. **join side**: valid can indeed stay high and backpressure is reachable — but the
   two queues `branch_ctl_buf` and `PC_reconv_buf` have their deq.ready assigned the
   **same expression** (branch_join.scala:124-138, lockstep), and when
   `Queue(1, flow=true)` is full, `enq.ready = !full` (verified line by line against
   chisel 6.4.0 Decoupled.scala:243-307) ⇒ while full, the pending item is **not
   overwritten**, and on the cycle a slot frees, the new item is **not accepted**. On
   arbitrary traces, the two queues' enqueue counts are always 1:1
   (`pcrMain_i31_excluded`); "the same RPC enqueued repeatedly" requires the
   pc_reconv count to be strictly larger, contradicting the theorem.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **RPC (reconvergence PC)**: when a vector branch instruction executes, the CSR
  unit computes the reconvergence address `simt_rpc` at which the two paths rejoin;
  it is sent into the SIMT stack along with the branch event, serving as the basis
  for pop matching. Repeated enqueue of a reconvergence point = the same
  reconvergence point consumed multiple times, corrupting the stack bookkeeping.
- **Decoupled handshake convention**: once valid is raised it must be held until
  ready accepts it (fire = valid∧ready). "valid passing through without fire gating"
  itself **violates** this convention — this entry's suspicion arises precisely from
  that coding style.
- **flow queue**: `Queue(_, 1, flow=true)` is a depth-1 flow-through queue: when
  empty, the input can pass straight through to the output in the same cycle; when
  full, `enq.ready = !full` — **on a full cycle no new data is accepted**, which is
  exactly the mechanical core of the exclusion argument.

### 1.2 Design intent

pc_reconv and branch_ctl are a bundled pair of information (reconvergence PC +
branch control), driven by the same valid, entering two identically parameterized
queues respectively, and consumed synchronously by branch_join. The design intent is
that the two queues are always in lockstep; the suspicion is that no mechanism
guarantees "no repeated enqueue during backpressure".

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: valid pass-through** (`pipe.scala:389-390`, ★ suspicion scene):

```scala
simt_stack.io.pc_reconv.bits := csrfile.io.simt_rpc
simt_stack.io.pc_reconv.valid := issueV.io.out_SIMT.valid//true.B //todo check this
```

Compare the `branch_ctl` side (around pipe.scala:382), likewise wired to
`out_SIMT.valid` — the two queues' enq.valid share the same source.

**Construct 2: vbranch-side valid combinationally gated by ready** (`issue.scala:118-128`):

```scala
when(inputBuf.bits.ctrl.simt_stack){
  when(io.out_SIMT.bits.opcode === 0.U){            // vbranch
    val beqv_ready = io.out_SIMT.ready & io.out_vALU.ready
    io.out_vALU.valid := inputBuf.valid & beqv_ready
    io.out_SIMT.valid := inputBuf.valid & beqv_ready  // ★ under backpressure, valid drops the same cycle
    inputBuf.ready    := beqv_ready
  }.otherwise{                                       // join
    io.out_SIMT.valid := inputBuf.valid               // ★ not gated by ready, stays high under backpressure
    inputBuf.ready    := io.out_SIMT.ready
  }
}
```

**Construct 3: dual-queue lockstep consumption** (`branch_join.scala:124-138`):
`branch_ctl_buf.ready` and `PC_reconv_buf.ready` are assigned the **same expression**
in every branch of the when/elsewhen/otherwise (`if_mask_buf.fire` / `true.B` /
`false.B`) — the two queues always advance in the same cycle.

---

## 3. Defect Analysis

### 3.1 Suspicion description and exclusion argument

**Suspicion chain**: out_SIMT backpressured → pc_reconv.valid stays high → the flow
queue re-enqueues the same simt_rpc every time a slot frees → the reconvergence
point gets popped multiple times → SIMT stack reconvergence bookkeeping corrupted.

**Exclusion (dual mechanism, each independently sufficient)**:

- **Mechanism R2 (vbranch side, structural)**: vbranch is the only opcode that
  consumes the simt_rpc **value**, and its valid is gated by ready (construct 2) —
  during backpressure valid cannot stay high, so the suspicion's premise fails.
- **Mechanism R1 (join side, bookkeeping level)**: on the join side valid is not
  gated and backpressure is genuinely reachable; but (a) when the queue is full,
  `enq.ready = !full`, so the pending item is not overwritten and the new item is
  not accepted on the cycle a slot frees; (b) the two queues are in lockstep
  (construct 3) ⇒ enqueue/dequeue fires are 1:1. Repeated enqueue requires the
  pc_reconv queue's enqueue count to be strictly greater than the branch_ctl
  queue's — contradicting the 1:1 theorem.

### 3.2 Root cause (why the suspicion arose)

The literal code `valid := out_SIMT.valid` violates the Decoupled convention, so
paper review naturally suspects repeated enqueue; the facts the exclusion relies on
are scattered across three files (the gating in issue.scala, the lockstep in
branch_join.scala, the flow semantics of the chisel-library Queue) plus
chisel-version behavior — a typical "hard to close the loop on paper, closable by
machine-checked proof" shape.

### 3.3 Harm and tolerability (including residual fragility)

No harm after exclusion. **Residual fragility**: R1 depends on the coding pattern
"both queues' deq.ready assigned the same value" (branch_join.scala:124-138,
synchronized assignment across four branches) — any future change that makes the two
diverge in any branch instantly revives duplication/loss. Suggest upstream add a
lockstep assertion (e.g. `assert(ctl.deq.ready === rpc.deq.ready)`) or switch to a
single bundled queue.

---

## 4. Lean Formal Evidence

All in `lean/Ventus/SIMT/PcReconv.lean`, zero sorry (axiom audit archived in module
report doc/modules/16 §6; full-proof theorems use only the standard axioms, witnesses
via native_decide additionally carry `Lean.ofReduceBool`, as expected).

**Foundation** [Lean machine-checked proof]: `pcrQ1FStep_correct` — the simplified
queue model agrees with the reference implementation translated branch-by-branch per
Decoupled.scala:269-278 on all 8 (full, enqV, deqR) combinations (full enumeration);
the anchor for the correctness of the Queue-semantics translation.

**R2 chain** [Lean machine-checked proof]: `pcrT_vbranch_valid_gated` (vbranch
valid=1 ⇒ simtR=1, combinational level); contrasted with
`pcrT_join_valid_ungated` (join side valid=inputV, backpressure reachable) — the only
case where the suspicion could possibly hold is left to R1.

**R1 chain** [Lean machine-checked proof]: `pcrT_lockstep` (the lockstep invariant
is preserved), `pcrT_enqFire_eq`/`pcrT_deqFire_eq` (enqueue/dequeue fires 1:1),
`pcrT_pending_stable` (the pending item is not overwritten while full),
`pcrT_count_equal` (enqueue counts equal on arbitrary traces, by induction on the
trace) → main theorem **`pcrMain_i31_excluded`** (from reset, on arbitrary input
traces, the two queues' enqueue counts are equal).

**Witnesses** [Lean machine-checked proof]: pcrW1–W5 (native_decide) actually walk
the suspicion scenario through — join backpressured for 4 cycles: c1 transaction A
lands in the slot; c2 backpressure cycle: valid stays high but **nothing is
enqueued**, and the pending item is not overwritten (`pcrW2_stall_no_dup`); c3
downstream consumes A, and on the cycle the slot frees, B is not accepted; c4 B
flows through and is consumed exactly once. Over the whole trace each queue enqueues
exactly once (`pcrW5_count`) — no duplication, no loss.

**Corroborating evidence** [Lean machine-checked proof]: `Ventus/Top.lean` B-I31 —
the mechanism scene that pc_reconv.valid at pipe.scala:390 passes through only with
out_SIMT.valid is pinned at the whole-machine wiring-contract level (module report
doc/modules/32).

**Contract dependencies registered as-is** (PcReconv.lean file header F1–F4,
[Direct source reading] level): the three wiring facts in
issue.scala/pipe.scala/branch_join.scala are not re-proved in Lean; F4 is chisel
6.4.0 library semantics (manually checked line by line against
Decoupled.scala:243-307).

---

## 5. Simulation Verification

doc/03 originally listed the reproduction method as "ChiselModSim directed test
(backpressure out_SIMT for several cycles, observe the pc_reconv queue's dequeue
count), ready-to-write". Once the exclusion verdict held, that case became **no
longer necessary**; doc/22's ChiselSim/Verilator channels contain no case for this
entry, and it was **not executed in this environment**. The exclusion evidence rests
on the §4 machine-checked proofs.

---

## 6. Upstream Impact Analysis

- No functional problem at present;
- The coding style at `pipe.scala:390` itself violates the Decoupled convention
  (valid should be held until ready), and is "just happens to be safe" thanks to
  downstream queue semantics and lockstep consumption — suggestions for upstream:
  either switch to the proper form (`valid := out_SIMT.fire` semantics, or latch the
  data internally after acceptance), or add a lockstep assertion to make the
  implicit contract explicit (see §3.3).

---

## 7. Fix and Fix Verification

No fix (the internal fix manifest: No fix (excluded); no corresponding module in VentusF). The
suggestion to upstream is assertion-level hardening (§3.3/§6), not a functional fix.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | Wiring chain at pipe.scala:389-390, issue.scala:118-128, branch_join.scala:84-86/:124-138; semantics check against chisel 6.4.0 Decoupled.scala:243-307 (registered as F1–F4) | Line-by-line check |
| Lean machine-checked proof | `pcrQ1FStep_correct` (queue-semantics foundation, full enumeration); `pcrT_vbranch_valid_gated`/`pcrT_join_valid_ungated` (R2); `pcrT_lockstep`/`pcrT_enqFire_eq`/`pcrT_deqFire_eq`/`pcrT_pending_stable`/`pcrT_count_equal` → **`pcrMain_i31_excluded`** (R1, full proof by induction over arbitrary traces) | Universal level |
| Lean witnesses | pcrW1–W5 (join backpressured 4 cycles, no duplicate enqueue, native_decide) | Concrete-trace level |
| Simulation | None (excluded class; the ready-to-write case is no longer necessary, not executed) | — |

I-31 is a model example of "adjudicative modeling": the modeled object is not a
single module but a combinational slice of Issue valid generation + dual flow queues
+ branch_join consumption logic; two independent mechanisms (vbranch-side gating
structurally excludes backpressure, join-side lockstep + flow semantics excludes
duplicate enqueue at the bookkeeping level) are each closed by machine-checked
proof. Status remains 【Excluded】; the residual fragility (lockstep depending on
same-value assignment) has been registered with a suggestion to add an upstream
assertion.
