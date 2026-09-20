> English translation of the Chinese master `doc/bugs/I-13-接受拍混用新旧控制.md`. Translated 2026-09-13.

# I-13 Detailed Defect Report: collectorUnit regOrder=2 branch mixes old and new control signals

| Item | Content |
|---|---|
| ID | I-13 |
| Source location | `ventus/src/pipeline/operandCollector.scala:303-307` (the regOrder=2 return branch uses `controlReg.sel_alu3/isvec` — registered values of the **old** instruction); comparison points :268/:288 (the rsType of the regOrder=0/1 branches has an accept-cycle Mux guard), :271-275/:291-295 (the regIdx zero-test has a state Mux guard), :168-171 (the imm input on the s_idle accept cycle comes from `io.control.bits` — the **new** instruction) |
| Type | Latent functional bug (inconsistent mixing of old and new signals, currently masked by system timing) |
| Severity | Medium (currently unreachable; broken-window condition = a change in bank response timing, e.g. SyncReadMem changed to combinational read) |
| Confirmation status | 【Confirmed (currently unreachable)】, defense-in-depth fix modeled and verified, and regression passed with the merged tree |
| Primary evidence | [Lean machine-checked proof] interface-liveness theorem `cuQ129_bankInRdy_accept` + fixed-version comparison witness; [direct source reading] inconsistent guards within the same function checked line by line; [simulation run] 38-patch merged tree regression (no regression, indirect) |
| Lean model | Original side `lean/Ventus/Schedule/CollectorUnit.lean` (`cuQ129_bankInRdy_accept`, :1158); fixed version `lean/VentusF/Schedule.lean` (`fschCu_i13_uses_new_decode` :232, `fschCuT_i13_orig_stale` :222, `fschCuT_i13_fix_fresh` :227) |
| Reproduction/patch | Currently unreachable within the system; no RTL reproduction case; patch `i13-operandcollector-accept-mux.patch` (internal fix manifest; not released) |
| Related entries | I-12 (same-module mask deadlock, sister report `doc/bugs/I-12-掩码向量指令死锁.md`), I-14 (same-module dead hardware), I-4 (same-module race, the "old and new in the same cycle" family) |

---

## 0. Summary

When collectorUnit (CU) processes data returned from a bank, its four regOrder branches face the same boundary case — "a bank return arriving in the same cycle as a new instruction's accept cycle (s_idle + control.fire)" — with three different coding styles: the regOrder=0/1 branches use `Mux(io.control.fire, new-instruction decode, registered value)` to explicitly choose between new and old control signals (:268/:288), the regIdx zero-test uses `MuxLookup(state, ...)` to distinguish (:271-275/:291-295), and **only the regOrder=2 branch (:303-307) unconditionally uses the old instruction's `controlReg`**. Meanwhile the `imm.io.out` referenced inside that branch comes from the **new** instruction on the accept cycle (:168-171 selects the source by state; s_idle → io.control.bits) — old and new signals mixed in the same expression.

Within the current system this path is unreachable: the crossbar response goes through RegNext (:549-552) plus SyncReadMem's 1-cycle read latency, so a same-cycle return on the accept cycle is impossible; moreover a CU accepts a new instruction only after the previous instruction has collected all operands, issued, and returned to s_idle, at which point no in-flight response belonging to this CU exists. This is a latent bug masked by timing — if a bank is ever changed to combinational read or the response path is shortened, the fill selection of A3_SD/A3_PC will follow the old instruction's decode, silently filling rsReg(2) with a wrong value.

---

## 1. Module function and design intent

(For collectorUnit's overall function, the regOrder/rsType concepts, and the state machine, see `doc/bugs/I-12-掩码向量指令死锁.md` §1; not repeated here — this section only adds the "old/new instruction alternation" context this entry needs.)

A CU's lifecycle: s_idle accepts a new instruction (on the `io.control.fire` cycle the decode control word `io.control.bits` is latched into `controlReg`, and the `*Wire` combinational signals are used for first-cycle decode) → s_add waits for bank returns to fill `rsReg` → s_out issues. **The accept cycle is a special window**: the new instruction's bits are already on the port, while the old instruction's controlReg has not yet been overwritten (the latch happens at the same cycle's clock edge). Every expression participating in combinational logic on that cycle must explicitly choose between "new" (io.control.bits/*Wire) and "old" (controlReg/rsType registers) — :268/:288/:271-275 all made that choice; :303 did not, and its imm source is forced to be "new".

The regOrder=2 branch's fill method is determined by sel_alu3 (decoded at :189-195):

- `A3_PC`: branch/jump class, op3 = imm + rs1 (a PC-relative concatenated value);
- `A3_SD`: store class, vector data or scalar broadcast selected by isvec;
- `A3_VRS3` / `A3_FRS3`: vector/floating-point third operand taken directly.

Choosing the wrong fill method = rsReg(2) silently filled with a wrong value.

---

## 2. Construct-by-construct reading of the original code

**The hazard itself** (`operandCollector.scala:302-310`):

```scala
}.elsewhen(io.bankIn(i).bits.regOrder === 2.U) { //operand3
  rsReg(2) := MuxLookup(controlReg.sel_alu3, VecInit.fill(num_thread)(0.U(xLen.W)))(   // :303 ★ always uses the old controlReg
    Array(A3_PC -> VecInit.fill(num_thread)(imm.io.out + io.bankIn(i).bits.data(0)),   // :304 ★ yet imm is the new instruction's
      A3_VRS3 -> io.bankIn(i).bits.data,                                                // :305
      A3_SD -> Mux(controlReg.isvec, io.bankIn(i).bits.data,                            // :306 ★ always uses the old controlReg
                   VecInit.fill(num_thread)(io.bankIn(i).bits.data(0))),
      A3_FRS3 -> VecInit.fill(num_thread)(io.bankIn(i).bits.data(0))                    // :307
    )
  )
  ready(2) := 1.U
}
```

**Comparison 1: the regOrder=0/1 branches have an accept-cycle Mux** (:268; :288 identical):

```scala
rsRead := MuxLookup(Mux(io.control.fire, rsTypeWire(0), rsType(0)), ...)(  // :268: on the fire cycle take the new decode
```

**Comparison 2: the register-number zero-test has a state Mux** (:271-275; :291-295 identical):

```scala
MuxLookup(state, false.B)(Array(
  s_idle -> regIdxWire(0).orR,   // on the accept cycle look at the new instruction's wire
  s_add -> regIdx(0).orR         // during collection look at the registered value
))
```

**Comparison 3: imm's source is selected by state** (:168-171):

```scala
imm.io.inst := MuxLookup(state, 0.U)(
  Array(s_idle -> io.control.bits.inst,   // accept cycle = new instruction
        s_add  -> controlReg.inst))       // collection period = old instruction
```

So if a regOrder=2 return really does arrive on the accept cycle and hits :303-307: the MuxLookup key and the A3_SD select bit are taken from the **old** instruction (controlReg), while the imm being added is taken from the **new** instruction — control signals from two different epochs in a single expression. Three guarding styles coexist within the same function and only this spot lacks one — clearly a maintenance omission, not design intent.

**Interface-side fact** (:129; the path is alive at the interface level):

```scala
io.bankIn(i).ready := (state === s_add && (ready(i)===0.U)) || (io.control.fire && (readyWire(i)===0.U))
```

The second disjunct explicitly allows "receiving a bank return on the accept cycle" — the CU's ready signal does not rule out such a same-cycle event; the mismatch is only masked by timing in the real system.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

- **Mechanism**: when a regOrder=2 bankIn return arrives in the same cycle as the accept cycle (s_idle ∧ control.fire), rsReg(2)'s fill method is selected by the old instruction's `controlReg.sel_alu3/isvec`, while the imm inside the expression comes from the new instruction — the filled value is wrong, with no error raised.
- **Inconsistency within the same function**: :268/:288 (rsType) and :271-275/:291-295 (regIdx zero-test) all have accept-cycle guards; only :303 lacks one — the inconsistency itself is evidence of a defect (it shows the designer knew guarding was needed and missed one spot).

### 3.2 Argument for current unreachability (timing masking)

[Direct source reading] three timing layers stack up to make "a same-cycle return on the accept cycle" impossible within the system:

1. The crossbar output is latched through RegNext (operandCollector.scala:549-552), so the response comes ≥1 cycle later than the grant;
2. The bank is a SyncReadMem, adding another cycle of read latency (regfile.scala:25);
3. The CU's precondition for accepting a new instruction is being back in s_idle (io.control.ready = state===s_idle && !valid.orR, :140), and leaving s_add requires all 4 ready bits collected — i.e. all returns of the previous instruction have already been consumed, so no in-flight response belonging to this CU exists on the accept cycle.

[Lean machine-checked proof] `cuQ129_bankInRdy_accept` (CollectorUnit.lean:1158) simultaneously pins down the other side: **the path is alive at the interface level** — on the accept cycle `bankIn(k).ready = !readyWire(k)`, which is high for operands that need a register read. In other words: if external timing really did deliver a same-cycle return, the CU would accept it and fill it with the wrong control word. The unreachability rests entirely on the two system properties "response path ≥2 cycles + lifecycles do not overlap"; the module itself has no defense.

### 3.3 Harm and tolerability

- **Harm (after the window breaks)**: A3_SD/A3_PC fills follow the old instruction's decode — store data / PC-relative values silently filled wrong (wrong-data level); the A3_VRS3/A3_FRS3 keys do not reference controlReg and happen to be immune.
- **Broken-window condition**: the bank response path shortened (e.g. SyncReadMem replaced by a combinational-read SRAM, or the RegNext pipeline stage removed from the crossbar) making accept-cycle returns possible. This is exactly what doc/03 meant by "a latent bug masked by timing".
- **Tolerability**: tolerable under the current configuration (unreachable); the fix is zero-risk defense in depth (it only changes the selection source on the accept cycle, and that cycle currently has no returns, so behavior is unchanged).

### 3.4 Relationship to related entries

Together with I-12 it belongs to operandCollector's "old and new designs coexisting / internal inconsistency" family (cross-referenced in the I-12 report §3.4); together with I-4 (the same-cycle in/out race) it belongs to the "two events in the same cycle" methodology lesson — this entry's unreachability argument covers the complete enable chain (an application instance of the III-3 lesson).

---

## 4. Lean formal evidence

**Original side** (`lean/Ventus/Schedule/CollectorUnit.lean`):

- `cuQ129_bankInRdy_accept` (:1158, single cycle, arbitrary state, arbitrary input): `cuControlFire s i = true ⇒ cuBankInRdyK s i k = !cuRwK i.ctrl k` — on the accept cycle, bankIn(k)'s ready is determined by the new instruction's readyWire, so "receiving a return on the accept cycle" is legal at the interface level. The argument for unreachability within the system is in the file-header note Q3 (response goes through RegNext + SyncReadMem, ≥2 cycles).
- The model is a faithful translation: `cuBankPort`'s regOrder=2 branch takes the old controlReg directly (doc/modules/12 §2 records this modeling landing point), i.e. the model preserves the defective semantics, and the theorem characterizes the mechanistic face of "live interface + wrong signal".

**Fixed-version comparison** (`lean/VentusF/Schedule.lean`, #print axioms audit :2256-2257):

- `fschCu_i13_uses_new_decode` (:232): the fixed version's accept-cycle rsReg(2) fill uses the new instruction's decode (the same Mux style as :268/:288);
- Broken-window witness duality: `fschCuT_i13_orig_stale` (:222, the original uses the old controlReg in the accept-cycle same-cycle-return scenario, filling wrong) vs `fschCuT_i13_fix_fresh` (:227, the fixed version uses the new instruction's decode, filling right) — an original/fixed comparison on the same trace, pinning down "once the window breaks, it goes wrong" for the latent mechanism.

---

## 5. Simulation verification

Currently unreachable within the system ⇒ **no RTL reproduction case** (a designed reproduction would have to dismantle the timing masking first, and then it would no longer be a reproduction of the original). The simulation-side evidence for this entry:

- [Simulation run (indirect)] the i13 patch is included in the 38-patch merged tree (2026-09-10, doc/22): mill compile passed, and all 11 ChiselSim suites judged identically to the 35-patch tree — the defensive change introduced no regression (as expected: that cycle currently has no returns, so the patch changes no reachable behavior);
- [Ready-to-run (not executed in this environment)] a directed test for the broken-window scenario (a combinational-read bank variant) was not written — it would have to be constructed on experimental RTL with modified response timing, beyond the scope of this entry.

---

## 6. Upstream impact analysis

- **Current impact**: zero (unreachable).
- **Evolution risk**: the response-path timing of operandCollector is a coincidence stacked out of two places, "RegNext + SyncReadMem"; no comment or assertion pins down the "no returns on the accept cycle" contract; a performance optimization at either place (removing the RegNext pipeline stage, switching to a combinational-read SRAM) would silently open the window. This is the typical scenario for a defense-in-depth fix.
- **Methodological significance**: this entry and I-4 together show that adjudicating "same-cycle event" defects requires walking the entire enable chain (here: interface alive ⇒ mechanism real; system timing ⇒ currently unreachable; both layers pinned by machine-checked proof / direct source reading — neither can be omitted).

---

## 7. Fix and fix verification

**Patch** (`i13-operandcollector-accept-mux.patch` (internal fix manifest; not released), two edits at :303-307):

1. MuxLookup key: `controlReg.sel_alu3` → `Mux(io.control.fire, io.control.bits.sel_alu3, controlReg.sel_alu3)`;
2. A3_SD's select bit: `controlReg.isvec` → `Mux(io.control.fire, io.control.bits.isvec, controlReg.isvec)`.

Fully aligned with the guarding style of :268/:288. the internal fix manifest handling category: **Defense-in-depth**.

**Fix verification**:

- [Lean machine-checked proof] `fschCu_i13_uses_new_decode` + the original/fixed comparison witnesses (`fschCuT_i13_orig_stale` vs `fschCuT_i13_fix_fresh`);
- [Simulation run] 38-patch merged tree regression with no collateral damage (doc/22);
- Regression safety: the patch only changes the selection source on the accept cycle, and that cycle currently has no returns — reachable behavior is cycle-by-cycle unchanged (this is also the basis for the "zero-risk defense-in-depth" verdict).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | :303-307 unguarded vs :268/:288/:271-275/:291-295 guarded; :168-171 imm sourced from the new instruction; :129 second disjunct | Five-point comparison within one function |
| Lean machine-checked proof | `cuQ129_bankInRdy_accept` (interface liveness); fixed version `fschCu_i13_uses_new_decode` + the original/fixed witness duality | Single-cycle universal + concrete trace |
| Unreachability argument | RegNext (:549-552) + SyncReadMem 1 cycle + CU lifecycles do not overlap | Three layers of direct source reading |
| Simulation | No reproduction case (unreachable); merged-tree regression clean (indirect) | Measured (indirect) |
| Fix verification | i13 patch; Lean fix theorems + merged-tree regression | Machine-checked + measured |

I-13 is a latent bug exposed by "internal inconsistency": five instances of the same kind of boundary within one function, four of them making the new/old choice, one missed. It does not bite today, but it bets correctness on two unpinned timing coincidences. The defensive fix costs nothing, risks nothing, and has been merged into the patch tree.
