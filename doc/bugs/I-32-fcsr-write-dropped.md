> English translation of the Chinese master `doc/bugs/I-32-fcsr写被静默丢弃.md`. Translated 2026-09-13.

# I-32 Detailed Defect Analysis Report: fcsr (0x003) is in the read table but has no branch in the write chain — csrrw/csrrs fcsr are silently dropped

| Item | Content |
|---|---|
| ID | I-32 |
| Source location | `ventus/src/pipeline/CSR.scala:235` (read table `BitPat(CSR.fcsr)->fcsr`), `:254` (`csr_rdata := Lookup(...)`); ★ missing point: the write chain `:257-295` has no fcsr branch |
| Type | Functional bug (ISA semantics deviation) — a "half-implementation" with the read side complete and the write side missing |
| Severity | **Medium** (whole-register fcsr writes silently have no effect; separate frm/fflags write paths exist and can serve as a software workaround) |
| Confirmation status | 【Confirmed】, Verilator full-machine reproduction + fixed-version Lean modeling verification + patch ready |
| Primary evidence | 【Machine-checked Lean proof】 `csr_fcsr_write_ignored` (original) + `farith_csr_fcsr_write_mask`/`farith_csr_fcsr_write_frm`/`farith_i32_witness` (fixed version); 【simulation run】 Verilator kernel `i32_fcsr_write_dropped` reproduction (doc/22); 【direct source reading】 line-by-line verification of CSR.scala read table / write chain |
| Lean model | `lean/Ventus/Arith/CSR.lean` (original); fixed version `lean/VentusF/Arith.lean` |
| Reproduction/patch | `repro/verilator/` kernel `i32_fcsr_write_dropped`; patch `i32-csr-fcsr-write.patch` (internal fix manifest; not released) |
| Related entries | I-33 (same file, vector CSR dead state), I-16 (same "silent no-op" style: AMO silent NOP); module report `doc/modules/07-Arith-RegFile与CSR.md`, fixed-version module report `doc/modules/33-VentusF-Schedule与Arith修复版.md` §2.6 |

---

## 0. Summary

RISC-V's `fcsr` (address 0x003) is the **whole-register view** of the
floating-point control and status register: the upper 3 bits (bit7:5) are the
rounding mode `frm`, and the lower 5 bits (bit4:0) are the exception flags
`fflags`. The specification requires that writing fcsr be equivalent to writing
the frm and fflags fields simultaneously.

In Ventus's CSRFile, fcsr is complete on the **read** side:
`fcsr := Cat(0.U(24.W), frm, fflags)` (CSR.scala:188), and
`BitPat(CSR.fcsr)->fcsr` is in the read table (:235), so `csrrs fcsr` correctly
reads back the assembled value. But the **write** chain (the :257-295 branch chain
under `when(wen)`) compares against the addresses fflags, frm, mstatus, mip, mie,
mscratch, mepc, mcause, mtval one by one — **with no fcsr branch at all** —
`csrrw/csrrs fcsr` falls off the end of the chain, writes nothing, and is silently
dropped.

Consequence: after software writes fcsr, reading it back returns the old value (0
after reset). The Lean theorem `csr_fcsr_write_ignored` pins down this behavior in
universal form: "for any state and any write value, the state is unchanged after
writing fcsr"; Verilator full-machine measurement reads back 0x00000000 after
`csrrw fcsr 0xE5`. The fix patch (adding an fcsr branch to the write chain,
splitting the write into the frm/fflags fields) has been verified by modeling: the
fixed version's `farith_csr_fcsr_write_mask` pins down read-after-write = the low
8 bits of the written value.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **CSR (Control and Status Register)**: RISC-V's control and status register
  space; software accesses it with instructions such as `csrrw` (read-then-write),
  `csrrs` (read-then-set), `csrrc` (read-then-clear). The semantics of a CSR
  instruction is "read the old value into rd, and simultaneously update the CSR
  according to the operand".
- **The floating-point CSR trio** (RISC-V F extension):
  - `fflags` (0x001): 5 accrued exception flag bits NV/DZ/OF/UF/NX;
  - `frm` (0x002): 3-bit dynamic rounding mode;
  - `fcsr` (0x003): **the whole-register view of the former two**, bit7:5=frm,
    bit4:0=fflags.
  The specification is explicit: writing fcsr must update frm and fflags
  simultaneously; software such as the glibc math library and debuggers reads and
  writes fcsr as a whole by this convention.
- **Ventus CSRFile**: one set of CSRs per warp (the `CSRFile` module in
  CSR.scala). The combinational read table `csrFile` (:225-252) plus `Lookup`
  (:254) produces `csr_rdata`; the write chain is a series of
  `.elsewhen(csr_addr === CSR.xxx)` address matches under `when(wen)` (:257-295);
  the CTA dispatch chain (from :296) does not intersect the write chain.

### 1.2 Design intent

fcsr's presence in the read table shows that by design intent fcsr is a visible
register; fflags and frm each have their own branch in the write chain
(:267-271), showing that per-field write paths were implemented. The absence of an
fcsr write branch looks more like an **implementation omission** than deliberate
pruning (contrast: intentionally read-only registers such as threadid/vtype
likewise have no write branch, but their read-only nature is backed by alternative
paths such as CTA dispatch; fcsr's specified semantics is precisely that it is
writable).

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the fcsr read side is complete** (CSR.scala:186-188, :235, :254):

```scala
val fflags = Cat(NV,DZ,OF,UF,NX)     // :186  assemble the 5 flag bits
val frm = RegInit(0.U(3.W))          // :187
val fcsr = Cat(0.U(24.W),frm,fflags) // :188  fcsr = 0(24) ‖ frm(3) ‖ fflags(5)
...
BitPat(CSR.frm)->frm,                // :234
BitPat(CSR.fcsr)->fcsr,              // :235  ★ fcsr is in the read table
BitPat(CSR.fflags)->fflags,          // :236
...
csr_rdata := Lookup(csr_addr, 0.U(xLen.W), csrFile).asUInt   // :254 combinational read
```

**Construct 2: the write chain has no fcsr branch** (CSR.scala:257-295, ★ the
trouble spot is the absence itself):

```scala
when(wen){
  when(io.ctrl.custom_signal_0){ ... }        // :258-261 custom setrpc
  .elsewhen(io.ctrl.isvec){ wdata := Mux(AVL<VLMAX,AVL,VLMAX) }  // :262-264 (see I-33)
  .elsewhen (csr_addr === CSR.csr_print){ ... }
  .elsewhen(csr_addr === CSR.fflags){ NX:=csr_wdata(0); UF:=csr_wdata(1);
      OF:=csr_wdata(2); DZ:=csr_wdata(3); NV:=csr_wdata(4) }     // :267-272
  .elsewhen (csr_addr === CSR.frm){ frm:=csr_wdata(2,0) }        // :273-274
  .elsewhen (csr_addr === CSR.mstatus) { MIE := ...; MPIE := ... }
  ... // mip / mie / mscratch / mepc / mcause / mtval
  // ★ the whole chain has no csr_addr === CSR.fcsr (0x003) branch — a write to fcsr falls off the end of the chain, a no-op
}
```

The write chain implements field-level update logic for both fflags (:267) and frm
(:272) — adding the fcsr branch only requires assembling the corresponding bits
from the two pieces, at minimal cost, further corroborating that this is an
omission rather than a design decision.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

For any CSR state and any write value v, after executing `csrrw fcsr, v` /
`csrrs fcsr, v` / `csrrc fcsr, v`: frm is unchanged and the five fflags bits are
unchanged; a subsequent `csrrs fcsr` reads back the old pre-write value (0 after
reset). That is, a half-implemented register that is "readable but not writable".

- Trigger surface: all software that operates on fcsr as a whole per the RISC-V
  convention (`csrrw fcsr` / `csrrs fcsr` / `csrrc fcsr`); typical sources: the
  glibc `fesetround`/`feclearexcept` family, debugger register windows,
  hand-written assembly.
- Form: **silent** — no trap, no assertion (during simulation, pipe.scala's
  assertion only covers the default-row decode with alu_fn=63; fcsr decodes
  normally); the write "succeeds" but has no effect.

### 3.2 Root cause

A single-point implementation omission: the read table and the write chain are
maintained independently, and fcsr got into only one of them. The frm/fflags
field-level write paths exist (software can work around with `csrrw frm` /
`csrrw fflags`), so this defect is unobservable under "software stacks that only
use field-level access" — Ventus's own tests are exactly such, which is why it
went unexposed for so long.

### 3.3 Impact and tolerability

- **Impact**: any software that writes rounding modes / exception flags through
  fcsr as a whole silently fails — setting the rounding mode "succeeds" but the
  FPU actually still operates with the old frm, causing systematic deviation of
  floating-point results with no error reported; a debugger failing to clear
  exception flags will mislead troubleshooting.
- **Tolerability**: separate frm/fflags write paths exist, so software aware of
  the defect can work around it (per-field writes); but it is incompatible with
  standard RISC-V software stacks (the glibc math library goes through fcsr by
  default). An ISA compliance gap; rated medium: less insidious about corrupting
  data than I-15/I-17, but "silent + on the standard software stack's
  unavoidable path" makes it a must-fix.
- The fix cost is low (one elsewhen branch); there is no tolerability reason to
  keep the status quo.

---

## 4. Lean Formal Evidence

Original pinned down (`lean/Ventus/Arith/CSR.lean`, zero sorry, full build
passes):

- **`csr_fcsr_write_ignored`** (:863): `∀ s v, csrStep s (csrInWrite csrOpW
  csrAddrFcsr v) = s` — for any state and any write value, after writing fcsr
  **the entire 40-field state is bit-for-bit unchanged**. This is a universal
  statement (not a witness); the characterization of the dropped write leaves no
  room for exceptions.
- Same-family controls pinned down: `csr_fflags_write_mask` (:850, writing fflags
  takes effect and only the low 5 bits are taken), `csr_frm_write_low3` /
  `csr_frm_set_narrow` (writing frm takes effect and only the low 3 bits are
  taken) — the field-level paths work normally, which precisely contrasts with the
  absence of the fcsr whole-register path.

Fixed-version machine-checked proofs (`lean/VentusF/Arith.lean`, `farithCsrStep` =
the original `csrStep` with two post-write branches appended; the legitimacy of
"appended post-write ≡ in-place elsewhen insertion" is supported by the original
model's `csr_fcsr_write_ignored`/`csr_isvec_no_state`, see doc/modules/33 §2.6):

- **`farith_csr_fcsr_write_mask`** (:308): read-after-write of fcsr = the low 8
  bits of the written value (frm(7:5) ‖ fflags(4:0)), for any state/write value,
  decided by bv_decide;
- **`farith_csr_fcsr_write_frm`** (:315): the frm field pinned down separately;
- **`farith_i32_witness`** (:321): the 0xE5 round-trip witness (write 0xE5, read
  back 0xE5; the original reads back 0);
- **`farith_csr_step_regr`** (:330): for inputs where neither patch branch fires,
  the fixed version is step-by-step identical to the original — regression safety
  (the fix does not touch existing behavior).

---

## 5. Simulation Verification

**Verilator full-machine reproduction** (actually run 2026-09-07, doc/22 §"10
kernel execution verdicts"):

| Kernel | Verdict | Key evidence |
|---|---|---|
| `i32_fcsr_write_dropped` | **Reproduced** | After `csrrw fcsr, 0xE5`, read-back = 0x00000000 — the write was dropped (had it taken effect, the read-back would be 0xE5: frm=111, fflags=00101) |

This kernel is one of the 8 full-machine reproductions among the 9 target bugs
(the k00_smoke channel self-check passed, ruling out image/loading-path problems).
Log: `repro/verilator/logs/i32_fcsr_write_dropped.log`.

**ChiselSim module level**: no dedicated CSR directed suite was built; among the 9
suites covered by the patched-tree regression (38-patch merged tree, 2026-09-10,
doc/22) there is no CSR entry — the i32 patch's correctness is borne jointly by
the Lean fixed-version machine-checked proofs (§4) + the Verilator reproduction
(original side); the patched-RTL ChiselSim regression is 【ready-to-run (not
executed in this environment)】 (the internal fix manifest records i32 as "Functional fix
(required)", verification status Yes).

## 6. Upstream Impact Analysis

- **Trigger surface**: fcsr is the standard entry point of RISC-V F-extension
  software; Ventus targets GPGPU scenarios, and its bundled runtime/tests do not
  operate on fcsr, so upstream was not exposed. The moment a standard glibc math
  library or an application needing dynamic rounding modes (interval arithmetic,
  random numbers, numerical verification tools) is hooked up, it silently fails.
- **Why upstream did not find it**: the frm/fflags field-level write paths exist,
  so a customized software stack can work around with them; the absence of
  whole-register fcsr writes only shows up on external software that "programs by
  the spec".
- **Related**: together with I-16 (AMO silent NOP) and I-33 (vl dead state), this
  belongs to the "ISA surface implemented, semantics hollow" family — the
  interface is there, the effect is not, and all are silent. This family is the
  hardest kind for simulation to catch (no crash, just "something missing"), and
  is exactly the strength of formal per-address / per-instruction enumeration
  audits.

## 7. Fix Plan and Fix Verification

**Patch**: `i32-csr-fcsr-write.patch` (internal fix manifest; not released) (one edit point,
inserted after the frm branch in the CSR.scala write chain):

```scala
} .elsewhen (csr_addr === CSR.fcsr){  // I-32 fix: writing fcsr splits into frm/fflags writes (previously silently dropped)
  NX:=csr_wdata(0)
  UF:=csr_wdata(1)
  OF:=csr_wdata(2)
  DZ:=csr_wdata(3)
  NV:=csr_wdata(4)
  frm:=csr_wdata(7,5)
}
```

**Fix verification**:

- Effectiveness: Lean fixed version `farith_csr_fcsr_write_mask` /
  `farith_csr_fcsr_write_frm` / `farith_i32_witness` (§4) — read-after-write is
  correct for any state; the 0xE5 witness round-trips consistently;
- Regression safety: `farith_csr_step_regr` (step-by-step equivalent to the
  original on non-triggering inputs); the patch only adds an elsewhen branch and
  does not change the semantics of existing branches;
- patched-RTL ChiselSim regression: no CSR directed suite, 【ready-to-run (not
  executed in this environment)】 (doc/22 status recorded faithfully).

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | CSR.scala:186-188/235/254 (read side complete) vs :257-295 (write chain has no fcsr branch), line-by-line verification | Read-write asymmetry directly visible |
| Machine-checked Lean proof | `csr_fcsr_write_ignored` (universal: for any state and any write value the state is unchanged) + field-level write-path control theorems | Universal level, no room for exceptions |
| Verilator full-machine reproduction | `csrrw fcsr 0xE5` reads back 0 (measured, doc/22) | Measured |
| Fix verification | i32 patch (1 edit point); Lean fixed-version read-after-write theorems + 0xE5 witness + regression equivalence | Machine-checked; RTL regression ready-to-run |

I-32 is a "textbook-shaped" ISA compliance defect: independent maintenance of the
read table and the write chain led to a half-implementation. Its value lies not in
mechanism complexity but in its **silence** — no trap, no assertion, and the
field-level paths serve as a "smokescreen"; only per-address enumeration-style
audits (formal methods) or testing with a standard software stack can catch it.
