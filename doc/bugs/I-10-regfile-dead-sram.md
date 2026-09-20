> English translation of the Chinese master `doc/bugs/I-10-RegFile死SRAM.md`. Translated 2026-09-13.

# I-10 Detailed Defect Report: RegFileBank declares SyncReadMem twice, generating an unconnected dead SRAM

| Item | Content |
|---|---|
| ID | I-10 |
| Source location | `ventus/src/pipeline/regfile.scala` — doc/03 records :19 (the outer `val regs = SyncReadMem(...)` at class-body level) and :22 (the same-named declaration inside the `if (!GVM_ENABLED)` block); re-checked against snapshot 6811725, this report's actual line numbers are :20 (outer declaration) and :23-24 (the if block and the inner same-named declaration), overall 1-2 lines off from what doc/03 records, pointing to the same construct |
| Type | Non-functional defect (area/power waste — dead hardware) |
| Severity | Low (no functional impact; one extra 512×32 dead SRAM per instantiated block, ×4 banks/SM) |
| Confirmation status | 【Confirmed】, fix patch merged into the 38-patch merged tree and regression passed |
| Primary evidence | [direct source reading] regfile.scala:20/:23-24 double declaration checked line by line; [simulation run] 38-patch merged tree mill compile + full ChiselSim regression (doc/22) |
| Lean model | None (dead hardware does not participate in behavior; RegFile.lean models only the actually used inner SyncReadMem; see doc/modules/07 D2) |
| Reproduction/patch | Non-functional issue; instantiation check suffices, no behavioral reproduction needed; patch `i10-regfile-dead-sram.patch` (internal fix manifest; not released) |
| Related entries | I-11 (the address-width defect of the same module's scalar bank), I-1 (same "dead code" family), the regfile remark (the unifiedBank dead module, doc/03 review-remarks section) |

---

## 0. Summary

The class body of `RegFileBank` (the scalar register-file bank) declares **two same-named** `val regs`: one at the outer level (regfile.scala:20), and another same-named variable inside the `if (!GVM_ENABLED)` branch (:24) that shadows the outer one. Under Scala/Chisel semantics, when the class body is evaluated the outer declaration is executed as usual, and Chisel generates a real storage node for it (SyncReadMem is a hardware declaration, not an ordinary Scala value); once the outer variable is shadowed by the inner same-named binding, no code ever references it again — its read and write ports all dangle. So regardless of whether `GVM_ENABLED` is true or false, every RegFileBank instance carries one extra 512×32-bit, completely unconnected dead SRAM.

This is pure area/power waste with no functional impact; but it sits in the same module as I-11 (the scalar bank address-width defect) and reveals that regfile.scala has long lacked maintenance review.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **Register-file bank**: a GPU's register file is organized into banks (storage arrays) to provide a multi-port effect. Ventus instantiates `num_bank=4` pairs of scalar/vector banks per SM (operandCollector.scala:531-532). A scalar bank is physically a `SyncReadMem(NUMBER_SGPR_SLOTS/num_bank, UInt(xLen.W))` = 512-entry × 32-bit synchronous-read SRAM (1-cycle read latency).
- **GVM_ENABLED**: a simulation/debug switch. When enabled, the scalar bank is instead implemented as a `RegInit(VecInit(...))` register array (:32), so that the full register contents can be exported for observation via the `all_regs` port; when disabled, a real SyncReadMem is used.
- **Chisel's class-body evaluation semantics**: a Chisel module is a Scala program; every hardware construct executed in the `Module` class body (`SyncReadMem(...)`, `Reg(...)`, etc.) adds a node to the generated circuit graph. **Variable shadowing only affects Scala-side visibility; it does not retract hardware nodes that have already been generated** — this is exactly the language mechanism by which this bug exists.

### 1.2 Design intent

The designer clearly intended to keep only one storage: an SRAM when GVM is off, an observable register array when it is on. The outer declaration is a leftover from an earlier version (unconditional SRAM); when the GVM branch was added later, a same-named variable was re-declared inside the if block and the outer one was forgotten.

---

## 2. Construct-by-construct reading of the original code

```scala
class RegFileBank extends Module  {
  val io = IO(new RegFileBankIO())                                     // :19
  val regs = SyncReadMem(NUMBER_SGPR_SLOTS/num_bank, UInt(xLen.W))     // :20 ★ hazard: outer declaration
  val bypassSignal = Wire(Bool())                                      // :21
  bypassSignal := RegNext((io.rsidx===io.rdidx)&io.rdwen)              // :22
  if (!GVM_ENABLED) {                                                  // :23
    val regs = SyncReadMem(NUMBER_SGPR_SLOTS/num_bank, UInt(xLen.W))   // :24 ★ same-named inner, shadows the outer
    io.rs := Mux(bypassSignal,RegNext(io.rd), regs.read(io.rsidx))     // :25 (reads the inner one)
    when (io.rdwen) {
      regs.write(io.rdidx, io.rd)                                      // :27-29 (writes the inner one)
    }
  }
  else {
    val regs_gvm = RegInit(VecInit(Seq.fill(NUMBER_SGPR_SLOTS / num_bank)(0.U(xLen.W))))  // :32
    io.rs := Mux(bypassSignal, RegNext(io.rd), RegNext(regs_gvm(io.rsidx)))
    when(io.rdwen) { regs_gvm(io.rdidx) := io.rd }
    io.all_regs.get := regs_gvm
  }
}
```

Construct-by-construct reading:

1. **:20 outer `regs`**: when the class body evaluates this line, a 512×32 SyncReadMem node is generated. From then on, every `regs` in the code resolves to the inner same-named binding (:24) — the outer one's read/write ports have no connection at all; it is a pure dead node.
2. **:23-30 non-GVM branch**: the storage actually in use; io.rs reads and io.rd writes all act on the inner regs.
3. **:31-38 GVM branch**: uses the `regs_gvm` register array, likewise never referencing the outer regs — i.e. the outer dead SRAM is generated under the GVM configuration too.

Conclusion: under both configurations, every RegFileBank instance carries one extra unconnected 512×32 SRAM; at num_bank=4, that is 4 extra blocks (64 Kbit total) of dead storage per SM.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

- **What it is**: the projection of a Scala variable-shadowing mistake onto the hardware-generation layer — the shadowed SyncReadMem declaration is not retracted and becomes an unconnected dead hardware node.
- **What it is not**: not a functional bug. The dead SRAM's inputs dangle (synthesizers typically constant-fold dangling read/write enables to 0); it injects no data into any active logic, and its outputs are consumed by nothing.

### 3.2 Root cause

Maintenance leftover: originally declared unconditionally; when the GVM branch was added, the same-named inner declaration "overrode" it without deleting the outer one. The Scala compiler only warns about shadowing (and compile warnings in Chisel projects are routinely drowned out), and the FIRRTL/Verilog generation flow does not error on "a storage node with no connections" — neither toolchain layer proactively exposes this kind of problem.

### 3.3 Harm and tolerability

- **Harm**: pure area/power. Each SM carries 64 Kbit (4 × 512×32) of SRAM that is never accessed; after synthesis it occupies real silicon area and draws leakage power; it does not change any observable behavior.
- **Tolerability**: tolerable; does not affect functional-verification conclusions; upstream is advised to delete the outer declaration. Impact on formal verification: the Lean model (RegFile.lean) models only the actually used inner SyncReadMem (the D2 idealization of doc/modules/07); the dead node does not enter the model and does not affect the validity of any theorem.

---

## 4. Lean formal evidence

This entry is a **non-functional defect**, for which behavioral machine-checked proof is neither needed nor appropriate — dead hardware is by definition "having no effect on any observable behavior". Related modeling facts:

- [Direct source reading + modeling decision] `lean/Ventus/Arith/RegFile.lean` models the inner SyncReadMem (physical depth 512 entries, of which the 8-bit index reaches only the low 256 entries; D2), and the file header explicitly states "the outer dead SRAM is not modeled". The model is consistent with the "active hardware".
- There is no theorem dedicated to I-10 — and that is itself the correct treatment (writing theorems for dead hardware amounts to endorsing behavior that does not exist).

---

## 5. Simulation verification

Non-functional issue; no behavioral reproduction case exists (nor can one exist — "one extra SRAM nobody uses" has no observable manifestation in simulation). Verifiable evidence:

- [Direct source reading] instantiation-chain grep: in the whole repo, RegFileBank is instantiated only at operandCollector.scala:532 (num_bank=4 instances);
- [Simulation run (indirect)] the 38-patch merged tree (containing the i10 deletion patch) compiled with mill, MILL_EXIT=0, and all ChiselSim regression suites judged identically to the 35-patch tree (doc/22 "38-patch merged tree regression" section) — after deleting the outer declaration, elaboration/simulation all pass, which conversely confirms the node truly had no connections (had there been any connection, the deletion would have reported a dangling reference at elaboration).

---

## 6. Upstream impact analysis

- **Impact surface**: all RegFileBank instantiations (4 banks per SM), under both GVM configurations. A real cost for area-sensitive FPGA/ASIC deployments.
- **Why upstream did not find it**: no functional manifestation + compilation produces only an easily drowned-out shadowing warning; upstream testing is function-focused and does not audit area.
- **Same-family reminder**: the same file also contains `unifiedBank` (regfile.scala:67-88), a dead module instantiated nowhere in the repo (recorded in the doc/03 review-remarks section) — the same kind of "maintenance leftover" issue; upstream is advised to clean it up together.

---

## 7. Fix and fix verification

**Patch** (`i10-regfile-dead-sram.patch` (internal fix manifest; not released), single edit point): directly delete the outer `val regs = SyncReadMem(...)` line in regfile.scala, with a comment marking the I-10 fix in its place. the internal fix manifest handling category: **Dead-code removal**; the Lean fixed-version theorem annotation is Not needed (deleting dead hardware requires no behavioral proof).

**Fix verification**:

- [Simulation run] 38-patch merged tree regression (2026-09-10, doc/22): mill compile passed; all 11 ChiselSim suites judged identically to the 35-patch tree (no regression);
- [Inference] after deletion each RegFileBank has one fewer 512×32 SRAM, reducing synthesized area/leakage; no synthesis-level quantification was done (no synthesis flow in this environment).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | regfile.scala:20 outer declaration shadowed by the :24 same-named inner; no reference in either branch | Line-by-line check |
| Lean model | No theorem needed; the model models the active inner SyncReadMem (RegFile.lean D2) | Modeling decision on record |
| Simulation/regression | 38-patch merged tree compile + full ChiselSim regression consistent (doc/22) | Measured (indirect) |

I-10 is a textbook "language-semantics trap" defect: Scala variable shadowing only affects visibility; it does not retract an already-generated hardware node. The harm is limited to area/power, and the fix is a zero-risk pure deletion. Its existence, together with the same file's I-11 (address-width defect) and the unifiedBank dead module, shows that regfile.scala is an area where upstream has long lacked maintenance review.
