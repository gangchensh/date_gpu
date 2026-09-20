> English translation of the Chinese master `doc/bugs/I-33-向量CSR死状态.md`. Translated 2026-09-13.

# I-33 Detailed Defect Analysis Report: vector CSR state (vl/vstart/vcsr/vlenb/vxrm/vxsat) is entirely dead state

| Item | Content |
|---|---|
| ID | I-33 |
| Source location | `ventus/src/pipeline/CSR.scala:262-264` (the isvec write branch only modifies the writeback data, **vl is never written**); `:198-202` (vstart/vcsr/vl have RegInit but no write path); `:225-252` (the read table does not contain vl/vstart/vcsr/vlenb/vxrm/vxsat) |
| Type | Functional bug (ISA semantics deviation) — vsetvli's state effect falls through, vector CSRs are unreadable |
| Severity | **Medium** (tolerable under Ventus's fixed 32-lane flow; must be fixed for RVV compatibility goals) |
| Confirmation status | 【Confirmed】, Verilator full-machine reproduction + fixed-version Lean modeling verification + patch ready |
| Primary evidence | 【Machine-checked Lean proof】 `csr_vl_write_ignored` + `csr_vl_read_zero` + `csr_isvec_no_state` + `csr_step_dead_vcsr` (original), `farith_csr_vl_rw`/`farith_csr_vl_read`/`farith_i33_witness`/`farith_csr_read_regr` (fixed version); 【simulation run】 Verilator kernel `i33_vl_dead` reproduction (doc/22); 【direct source reading】 line-by-line verification of CSR.scala |
| Lean model | `lean/Ventus/Arith/CSR.lean` (original); fixed version `lean/VentusF/Arith.lean` |
| Reproduction/patch | `repro/verilator/` kernel `i33_vl_dead`; patch `i33-csr-vl-rw.patch` (internal fix manifest; not released) |
| Related entries | I-32 (same file, fcsr half-implementation), I-16 (same "silent" family); module report `doc/modules/07-Arith-RegFile与CSR.md`, fixed version `doc/modules/33-VentusF-Schedule与Arith修复版.md` §2.6 |

---

## 0. Summary

RISC-V Vector (RVV)'s `vsetvli` instruction sets the vector length `vl`: hardware
updates the vl register by `vl = min(AVL, VLMAX)` and writes vl back to rd;
software can then read it back with `csrrs vl` — the standard idiom of
strip-mining loops.

In Ventus's CSRFile, `vsetvli`-class instructions go through the isvec write
branch (CSR.scala:262-264), but that branch **only changes the writeback data to
min(AVL, VLMAX) and never writes the vl register itself**. At the same time, the
six addresses vl (0xC20), vstart (0x008), vcsr (0x00F), vlenb, vxrm, vxsat are
**all absent from the read table** — `Lookup` defaults to reading 0. As a result:
after vsetvli executes, rd receives the correct min(AVL,32) (this value is
supplied directly by the writeback-data path, independent of the vl register), but
vl is constantly 0 and unreadable — **the vector length state does not persist**.

Four Lean theorems pin down "dead state" as universal facts: writes to vl are
ignored, reads of vl are constantly 0, the isvec branch changes no state, and all
11 vector CSR fields never update under any input. Verilator full-machine
measurement: vsetvli writes back rd=0x20 (correct), then `csrrs vl` reads
0x00000000. The fix patch (adding vl to the read table + writing vl in the isvec
branch) has been verified by modeling: read-after-write = min(v, 32).

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **RVV vector length state**: RVV maintains the vector execution environment with
  a group of CSRs — `vl` (current vector length), `vtype` (element
  width/LMUL/tail policy; Ventus stores it split as vsew/vlmul/vill/vma/vta),
  `vstart` (exception restart index), `vcsr`/`vxrm`/`vxsat` (fixed-point rounding
  and saturation flags), `vlenb` (vector register byte count). Software sets vl
  with `vsetvli rd, rs1, vtypei`: `vl := min(AVL=rs1, VLMAX)`, with vl also
  written back to rd. Strip-mining is RVV's signature loop structure: each
  iteration `vsetvli t0, a0, e32` takes the smaller of the remaining amount and
  VLMAX, the loop body processes t0 elements, and `a0 -= t0` — **loop correctness
  depends on the vl state being readable and persistent**.
- **Ventus's simplification**: Ventus is a SIMT GPGPU with num_thread fixed at 32
  (VLMAX=32, CSR.scala:197 `val VLMAX = RegInit(num_thread.U(xLen.W))`); the
  vector length is fixed by hardware, and the custom flow does not read the length
  from vl. Under this design trade-off, vl's "statefulness" was omitted: vsetvli
  degenerates into "just write a constant upper-bound value to rd".

### 1.2 Design intent

The existence of the isvec write branch shows the designer implemented the
**writeback-data** half of vsetvli (software can get min(AVL,VLMAX) from rd —
Ventus's own flow uses it exactly this way); the vl register proper (which has a
RegInit at :202) and its absence from the read table show that the "vl as a
readable CSR state" half was omitted. This is a trade-off between "good enough for
the custom flow" and "RVV compliance", but it exceeds what the documentation
claims: to standard RVV software, vl=0 is an observable violation.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: vector CSR registers are declared but have no write path**
(CSR.scala:198-202):

```scala
val vstart = RegInit(0.U(xLen.W))   // :198
...
val vcsr = RegInit(0.U(xLen.W))     // :201
val vl = RegInit(0.U(xLen.W))       // :202  ★ the register entity exists; there is no assignment point anywhere in the file
```

**Construct 2: the isvec write branch touches only the writeback data, not vl**
(CSR.scala:262-264, ★ trouble spot):

```scala
.elsewhen(io.ctrl.isvec){
  wdata:=Mux(AVL<VLMAX,AVL,VLMAX)   // :263  writeback data = min(AVL, VLMAX)
//               Mux(AVL>(VLMAX<<1.U).asUInt,VLMAX,AVL>>1.U))
}                                    // ★ note: there is no vl := ...; the vl register is never written
```

Compare with the other branches in the same chain (fflags/frm/mstatus/...), all of
which write real registers — the isvec branch is the only one in the whole chain
that "only decorates the writeback data and lands no state".

**Construct 3: the read table contains none of the vector CSRs**
(CSR.scala:225-252):

```scala
val csrFile = Seq(
  BitPat(CSR.mstatus)->mstatus, ... ,
  BitPat(CSR.frm)->frm, BitPat(CSR.fcsr)->fcsr, BitPat(CSR.fflags)->fflags,
  BitPat(CSR.vtype)->vtype,          // :237  ★ among vector CSRs only vtype is in the read table (and vtype is constantly 0x10)
  BitPat(CSR.threadid)->threadid, ... // CTA dispatch group
)
csr_rdata := Lookup(csr_addr, 0.U(xLen.W), csrFile).asUInt  // :254 a miss reads 0
```

vl(0xC20), vstart(0x008), vcsr(0x00F), vlenb, vxrm, vxsat are all absent from the
table — `csrrs vl` reads the Lookup default value 0.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

1. **vsetvli's state effect falls through**: after the isvec write branch
   executes, vl keeps its old value (constantly 0, because RegInit 0 and no write
   path); software only gets min(AVL,32) from rd.
2. **vl is unreadable**: `csrrs/csrrw vl` reads constantly 0 (not in the read
   table); writes to the vl address are likewise silently ignored (no such branch
   in the write chain).
3. **The whole vector CSR group is dead state**: the 11 fields
   vsew/vlmul/vill/vma/vta (vtype stored split), vstart, vl, vcsr, vlenb, vxrm,
   vxsat never update under any CSR input (except that vtype reads out the
   constant 0x10; the rest also read constantly 0).

Trigger surface: all software that reads vl per the RVV specification — typically
strip-mining loops (which read vl to decide this round's processing
amount/advancement); exception recovery relying on vstart and fixed-point
saturation-flag checks relying on vxsat fail in the same way.

### 3.2 Root cause

Design pruning crossing the compliance boundary: Ventus fixed the vector length as
the hardware constant 32, leaving vl with only the cosmetic function of "write a
number to rd". Under the custom assembly flow (Ventus's bundled runtime) this is
good enough — the length convention is carried by programming discipline; but the
CSR space exposes an RVV-shaped interface to software (the vsetvli instruction,
readable vtype) without maintaining its state semantics, forming a
half-implementation with "interface present, state empty". Same family as I-32
(fcsr read-write asymmetry): half-implementation + silence (no trap, no
assertion).

### 3.3 Impact and tolerability

- **Impact**: RVV standard code (any strip-mining product of compiler
  vectorization) is silently wrong on hardware — reading vl as 0 makes the loop
  advancement 0 (infinite loop) or processes with the wrong length; this is the
  "standard software stack steps directly on the mine" type.
- **Tolerability**: tolerable under the current Ventus software stack (fixed 32
  lanes, custom flow does not read vl) — doc/03's original verdict is exactly
  "tolerable; must be fixed for RVV compatibility goals". Rated medium: does not
  corrupt data, but the ISA compliance gap is clear.
- **Incidental (note level, verbatim from doc/03)**: CSR writes to CTA-dispatch
  registers and vtype are silently ignored with no illegal-instruction exception
  (mtvec is constantly 0, no trap mechanism); seven registers have no reset value;
  vtype is constantly 0x10; misa/mcycle read 0 (no consumer).

---

## 4. Lean Formal Evidence

Original pinned down (`lean/Ventus/Arith/CSR.lean`, zero sorry):

- **`csr_vl_write_ignored`** (:878): `∀ s v, csrStep s (csrInWrite csrOpW
  csrAddrVl v) = s` — writing the vl address leaves the state unchanged;
- **`csr_vl_read_zero`** (:883): `∀ s, csrRead s csrAddrVl = 0` — reads of vl are
  constantly 0;
- **`csr_isvec_no_state`** (:887): after the isvec write branch (not custom0, not
  CTA dispatch), **the entire state is field-by-field unchanged** — the universal
  characterization of vsetvli landing no state;
- **`csr_step_dead_vcsr`** (:943): for any input, all eleven fields
  vsew/vlmul/vill/vma/vta/vstart/vl/vcsr/vlenb/vxrm/vxsat are preserved — the
  complete enumeration-style proof of "the vector CSR group is entirely dead
  state".

Fixed-version machine-checked proofs (`lean/VentusF/Arith.lean`; `farithCsrStep`
appends a post-write vl branch, whose legitimacy is supported by the original
model's `csr_isvec_no_state`, see doc/modules/33 §2.6):

- **`farith_csr_vl_read`** (:272): the fixed version's read of vl = the state vl;
- **`farith_csr_vl_rw`** (:291): after a vsetvl write of v, reading vl = min(v,
  32) (for any state/write value);
- **`farith_i33_witness`** (:300): numeric witness of writing 17 reading 17, and
  writing 40 clamped to 32 (in the original, the write is ignored and reads are
  constantly 0);
- **`farith_csr_read_regr`** (:276) and `farith_csr_step_regr` (:330): read/step
  agree with the original in the non-triggering domain — regression-safe.

## 5. Simulation Verification

**Verilator full-machine reproduction** (actually run 2026-09-07, doc/22 §"10
kernel execution verdicts"):

| Kernel | Verdict | Key evidence |
|---|---|---|
| `i33_vl_dead` | **Reproduced** | `vsetvli` writes back rd=0x20 (w0, min(AVL,32) correct — the writeback-data half works); then `csrrs vl` reads 0x00000000 (w4) — the vl register is in dead state |

This result cuts the two halves apart precisely: the writeback-data path works
(rd=0x20), the state path is missing (vl=0) — corresponding point-by-point with
source Constructs 2/3 and the Lean theorem group. Log:
`repro/verilator/logs/i33_vl_dead.log`.

**ChiselSim module level / patched-RTL regression**: no CSR directed suite,
【ready-to-run (not executed in this environment)】 (same as recorded in §5 of the
I-32 section; the internal fix manifest records i33 as "Functional fix (required)" and notes
the minimal fix scope: only fix vl read/write; vstart/vcsr/vlenb/vxrm/vxsat remain
dead state, to be handled separately with RVV subset semantics).

## 6. Upstream Impact Analysis

- **Trigger surface**: RVV standard flows (strip-mining reading vl) will
  definitely hit it; Ventus's custom flow does not read vl, so neither upstream
  repository tests nor FPGA deployments were exposed.
- **Why upstream did not find it**: same as I-32 — the writeback-data half gives
  vsetvli a "working appearance"; only external software that reads vl per the
  spec discovers that the state is empty.
- **Fix trade-off** (the internal fix manifest original ruling): the minimal fix restores only
  vl's readability/writability (vl enters the read table + the isvec branch lands
  vl); semanticizing vstart/vcsr/vlenb/vxrm/vxsat (exception restart index,
  fixed-point flags) exceeds the current Ventus execution semantics — they remain
  dead state, to be designed separately with RVV subset support, avoiding a
  "half-fix" introducing new semantic illusions.

## 7. Fix Plan and Fix Verification

**Patch**: `i33-csr-vl-rw.patch` (internal fix manifest; not released) (two edit points):

```scala
// 1. Add vl to the read table (inside csrFile)
BitPat(CSR.vl)->vl , // I-33 fix: vl is readable

// 2. The isvec write branch lands vl (next to :263)
.elsewhen(io.ctrl.isvec){
  wdata:=Mux(AVL<VLMAX,AVL,VLMAX)
  vl:=Mux(AVL<VLMAX,AVL,VLMAX) // I-33 fix: vsetvl writes vl (previously never written, vl constantly 0)
}
```

**Fix verification**:

- Effectiveness: Lean fixed version `farith_csr_vl_rw` (read-after-write =
  min(v,32), universal) + `farith_i33_witness` (17→17, 40→32 numeric witness);
- Regression safety: `farith_csr_read_regr`/`farith_csr_step_regr` (step-by-step
  equivalent to the original in the non-triggering domain); the patch makes no
  semantic change to existing branches (the isvec branch gains a register
  assignment; the wdata logic is unchanged);
- patched-RTL ChiselSim regression: 【ready-to-run (not executed in this
  environment)】 (doc/22 status recorded faithfully).

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | CSR.scala:198-202 (RegInit present, no write path), :262-264 (isvec branch lands no state), :225-254 (read table missing six addresses), line-by-line verification | Three constructs mutually corroborate |
| Machine-checked Lean proof | `csr_vl_write_ignored`/`csr_vl_read_zero`/`csr_isvec_no_state`/`csr_step_dead_vcsr` — four theorems pinning down the dead state universally | Universal level, 11-field enumeration closed |
| Verilator full-machine reproduction | vsetvli rd=0x20 but csrrs vl=0 (measured, doc/22) | Measured, and cuts the two halves apart precisely |
| Fix verification | i33 patch (2 edit points); Lean fixed-version read-after-write theorem + witness + regression equivalence | Machine-checked; RTL regression ready-to-run |

I-33 and I-32 form a "half-implementation" pair in the same module: one has the
read side complete and the write side missing (fcsr), the other has the writeback
appearance complete and the state side missing (vl/vector CSRs). Together they
show that the correctness of "address-space" interfaces like CSRs must be checked
address by address in both read and write directions — this is exactly the
structural advantage of formal enumeration (`csr_step_dead_vcsr`-style per-field
theorems) over spot-check simulation.
