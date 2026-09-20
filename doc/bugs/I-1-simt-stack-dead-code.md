> English translation of the Chinese master `doc/bugs/I-1-SIMT栈死代码.md`. Translated 2026-09-13.

# I-1 Detailed Defect Report: The `SIMT_STACK` class is dead code in its entirety; the live implementation is `branch_join`

| Item | Content |
|---|---|
| ID | I-1 |
| Source location | `ventus/src/pipeline/SIMT_STACK.scala:126` (`class SIMT_STACK`, a dead class in live-code form); the same file also holds ~200 lines of a commented-out older version starting at :388 (a second `class SIMT_STACK` inside a block comment); the live instantiation site is `ventus/src/pipeline/pipe.scala:129` |
| Type | Non-functional issue (dead code / maintenance risk) |
| Severity | **Low** (no functional impact; the risk lies in maintenance and cognitive misdirection) |
| Confirmation status | 【Pending】 (doc/03 original verdict carried over verbatim; the dead-code fact itself has been nailed down by this project's grep re-verification, see §4) |
| Primary evidence | [Direct source reading] repo-wide grep for `SIMT_STACK` finds only two declarations and zero instantiations; the `simt_stack.io.pc_reconv` port referenced in pipe.scala exists only on `branch_join` |
| Lean model | `lean/Ventus/SIMT/BranchJoin.lean` (the verification target is explicitly locked to `branch_join`; SIMT_STACK is not modeled, see module report doc/modules/15) |
| Reproduction/patch | Non-functional issue; instantiation-site inspection is the reproduction. Patch `i01-simt-stack-deadcode.patch` (internal fix manifest; not released) (merged into the 38-patch combined tree, compiles cleanly, doc/22) |
| Related entries | I-3 (the complete-semantics divergence between the two versions is a direct instance of this entry's risk); I-10/I-14 (same kind of dead code/dead hardware); the coralNPU LsuV2 lesson of the same kind |

---

## 0. Abstract

`SIMT_STACK.scala` defines a complete SIMT branch-reconvergence stack class
`SIMT_STACK` (:126, with input/output ports, buffer queues, thread_masks and all
other implementation), yet a repo-wide search proves it is **never instantiated**:
the real instantiation site is `pipe.scala:129`, which instantiates the
`branch_join` class from `branch_join.scala`. An even harder piece of evidence:
`pipe.scala` references the `io.pc_reconv` port on the `simt_stack` instance
(pipe.scala:389-390), while the IO Bundle of `SIMT_STACK` has no such port at
all — structurally, `SIMT_STACK` **cannot** be the class of `simt_stack`.

Functional impact is zero (dead code takes no part in hardware generation). The
harm lies on the maintenance side: the two versions genuinely diverge in
semantics — e.g. the complete condition, `!elseOnly` in SIMT_STACK
(SIMT_STACK.scala:211) versus `takeif` in branch_join (branch_join.scala:120) —
so a later reader who opens the wrong file acquires a wrong microarchitectural
understanding (the I-3 investigation experienced exactly this divergence).
In addition, the tail of the file preserves ~200 lines of an older version in a
block comment (a second `class SIMT_STACK` starting at :388): three versions
coexist in one file.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **SIMT branch divergence/reconvergence**: a GPU executes warps (32 threads) in
  lockstep. On hitting a data-dependent vector branch (vbranch), the threads of
  a warp split into if/else paths according to the condition; the hardware
  **pushes** the mask and reconvergence PC of the path not taken first onto a
  stack and executes one path; on reaching a join with the PC matching the
  stack-top reconvergence point, it **pops** to resume the other path, and
  finally both paths reconverge with the full mask restored. This is the
  "SIMT stack".
- **Classes and instantiation in Chisel**: Chisel is a Scala-embedded hardware
  language; hardware modules are Scala classes, and only classes instantiated
  via `Module(new X(...))` generate circuits. A class that is defined but never
  instantiated is dead code — it generates no transistors, yet stays in the
  codebase being read and misunderstood.

### 1.2 Design intent (conjectured, 【Inferred】)

`SIMT_STACK` is the reconvergence-stack implementation of an early version
(supporting a per-warp multi-stack structure, etc.), later rewritten as
`branch_join` (single-warp perspective, simpler interface). The old file was
not deleted at replacement time — a typical refactoring leftover.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the dead class itself** (`SIMT_STACK.scala:126`, ★ hazard):

```scala
//this is the REAL SIMT-STACK for divergence management
class SIMT_STACK(val depth_stack : Int) extends Module{
  val io = IO( new Bundle() {
    val  branch_ctl  =  Flipped(Decoupled(new simtExeData()))
    val  if_mask     =  Flipped(Decoupled(new vec_alu_bus()))
    val  input_wid   =  Input(UInt(depth_warp.W))
    val  out_mask    =  Output(UInt(num_thread.W))
    val  complete   =  Valid(UInt(depth_warp.W))
    val  fetch_ctl   =  Decoupled(new BranchCtrl())
    ...
```

The comment calls itself "the REAL SIMT-STACK" — the truth is exactly the
opposite: this is the version that is **not** used. Note that its IO has
**no `pc_reconv` port**.

**Construct 2: the live instantiation site** (`pipe.scala:129`):

```scala
val simt_stack=Module(new branch_join(num_thread))
```

The instance is named `simt_stack` but the class is `branch_join` — the name
itself misleads readers into looking for SIMT_STACK.scala.

**Construct 3: hard evidence of port incompatibility** (`pipe.scala:389-390`):

```scala
simt_stack.io.pc_reconv.bits := csrfile.io.simt_rpc
simt_stack.io.pc_reconv.valid := issueV.io.out_SIMT.valid//true.B //todo check this
```

The `pc_reconv` port exists only on `branch_join`. If `simt_stack` really were
an instance of `SIMT_STACK`, these two lines could not compile — the dead-code
fact is therefore not merely "no instantiation found" but "impossible to
instantiate".

**Construct 4: the commented-out older version at the tail** (from
`SIMT_STACK.scala:388`): a block comment `/* ... */` preserves a second
complete `class SIMT_STACK`, running to end of file (539 lines total). Three
"reconvergence stacks" coexist in the same file.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

A non-functional defect, nailed down by three independent facts:

1. A repo-wide grep for `SIMT_STACK` hits only two **declarations**,
   SIMT_STACK.scala:126 and :388, with no `Module(new SIMT_STACK(...))`
   instantiation anywhere [direct source reading];
2. The actual instantiation `pipe.scala:129` points to `branch_join`
   [direct source reading];
3. The `pc_reconv` port used at the consumption site does not exist in
   SIMT_STACK's IO, so SIMT_STACK structurally cannot serve as that instance
   [direct source reading].

### 3.2 Root cause

Post-refactoring cleanup was skipped: when the live implementation was switched
from SIMT_STACK to branch_join, both the old class and the even older commented
version were left in the file; the instance name `simt_stack` disagrees with
the class name `branch_join`, further reinforcing the "go read
SIMT_STACK.scala" misdirection.

### 3.3 Harm and tolerability

- **Harm**: no functional impact (dead code generates no hardware). The
  maintenance risk is real: the two versions diverge semantically (the complete
  condition `!elseOnly` vs `takeif`, the very subject of I-3's check); reading
  the wrong file yields a wrong microarchitectural understanding, and
  modifications or reviews may be based on that wrong understanding.
- **Tolerability**: tolerable. Recommend upstream delete it or mark it
  deprecated. For this verification project: the verification target is locked
  to `branch_join`, and this record prevents accidental verification of dead
  code (the coralNPU project had the same-kind lesson with LsuV2).

---

## 4. Lean Formal Evidence

This entry is a non-functional issue with no corresponding theorem; the
counterpart measure on the formalization side is **locking and recording the
modeling target**:

- `lean/Ventus/SIMT/BranchJoin.lean` models only `branch_join`; the file header
  explicitly states that SIMT_STACK is not modeled [direct source reading +
  modeling decision, see doc/modules/15 §5];
- The divergence of the complete condition between the two versions found in
  the I-3 investigation (`!elseOnly` vs `takeif`) is registered by this entry,
  preventing later waves from mistaking SIMT_STACK's semantics for design
  intent.

---

## 5. Simulation Verification

Not applicable / not needed: this is a non-functional issue; "reproduction" is
the instantiation-site inspection of §3.1 (grep + the port-incompatibility
argument), already completed in this environment. The ChiselSim/Verilator
channels of doc/22 have no test case for this entry (none was ever planned).

**Patch-side verification** [simulation run, indirect]: the i01 patch has been
merged into the 38-patch combined tree (2026-09-10, doc/22 §38-patch combined
tree regression); `git apply` is clean and `ventus[6.4.0].tests.compile`
compiles successfully (MILL_EXIT=0) — after deleting the dead class the whole
tree still compiles, confirming conversely that "no live code references
SIMT_STACK".

---

## 6. Upstream Impact Analysis

- Dead code takes no part in elaboration and has zero impact on generated
  hardware;
- The risk is purely cognitive: the file name SIMT_STACK.scala, the instance
  name `simt_stack`, and the class comment claiming "REAL SIMT-STACK" stack
  three layers of misdirection;
- Recommendation to upstream: delete the entire dead class and the commented
  tail version (keeping live Bundles such as `simtExeData`/`vec_alu_bus`), or
  at least mark them deprecated.

---

## 7. Fix Plan and Fix Verification

**Patch**: `i01-simt-stack-deadcode.patch` (internal fix manifest; not released) — deletes
418 lines starting at SIMT_STACK.scala:122 (the `class SIMT_STACK` body plus
the commented tail version), keeps the live-code Bundles
(`simtExeData`/`vec_alu_bus`/hash/`ipdom_stack`), and leaves a comment at the
file tail explaining the reason and provenance of the deletion. Registered in
the internal fix manifest as "Dead-code removal (optional)".

**Verification**: the 38-patch combined tree `git apply` is clean and mill
compilation passes (doc/22, 2026-09-10); no functional test case (none is
needed — the deleted code never generated hardware anyway).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | repo-wide grep finds zero instantiations; pipe.scala:129 instantiates branch_join; the pc_reconv port exists only on branch_join (structurally impossible to instantiate) | hard evidence |
| Patch verification | after i01 deletes 418 lines, the 38-patch combined tree compiles (doc/22) | actually measured |
| Maintenance-risk argument | the two versions diverge on complete semantics (experienced firsthand in the I-3 investigation) | qualitative |

I-1 is a paradigmatic case of "refactoring-leftover dead code": functionally
harmless, but a real misdirection risk for the verification project itself —
the core value of this report is **locking the verification target to
`branch_join`**, preventing later work from wasting effort on, or misreading,
dead code.
