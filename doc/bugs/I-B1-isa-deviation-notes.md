> English translation of the Chinese master `doc/bugs/I-B1-ISA层偏离组.md`. Translated 2026-09-13.

# B1 Note Group Detailed Analysis Report: four ISA-level deviations (JALR bit0 / vbranch comparison direction / vmv.s.x all-lane write / instDemux second-lowest CU)

| Item | Content |
|---|---|
| ID | B1 note group (doc/03-bug发现报告.md:1191-1209, "ISA-level deviations", discovered 2026-09-01; the instDemux entry was added later) |
| Status | 【Remark】 — the first three are ISA deviations where **the machine deviates from the manual and the spec is modeled after the machine** (D8/D10/D12); the fourth is a performance-level stall risk (not a functional bug) |
| Source location | JALR: `operandCollector.scala:243-246` (A3_PC passes pc+imm straight through; the imm+rs1 back-fill for B_R is at `:304`), `PCcontrol.scala:29-36` (only fetch-group alignment is done); vbranch: `DecodeUnit.scala:585` (`c.reverse := s(7)`) + `:473-478` (the six lines VBNE…VBGEU have reverse=Y); vmv.s.x: `DecodeUnit.scala:414` (the VMV_S_X row); instDemux: `operandCollector.scala:499-502` |
| Evidence | 【Machine-checked Lean proof】 instDemux entry: `VentusF/Progress.lean:521` `prg_ocOrR_ocRdy2_of_two`; 【direct source reading】 all four entries verified line by line; 【inference/modeling convention】 the first three are modeled after the machine and recorded in `VentusF/IsaSpec.lean` (D8/D10/D12, see `doc/modules/36-VentusF-IsaSpec黄金语义.md`) |
| Disposition | Hardware not fixed; the spec follows the machine (ensuring the capstone theorems remain provable); the program contract requires JALR targets to be 4B-aligned; the instDemux entry is recorded as a performance observation |

---

## 0. Summary

None of the four entries in this group is a "functional wrong-data" level bug;
they are records of **machine behavior deviating from ISA-manual
intuition/specification**: the first three (JALR not clearing bit0, vbranch
comparison direction, vmv.s.x writing all active lanes) were ruled to be handled
as "spec follows machine" — the IsaSpec golden semantics is modeled after the
hardware as-is (D8/D10/D12), ensuring the capstone theorems remain provable while
the deviations are faithfully reported; the fourth (instDemux on the scalar side
always taking the second-lowest free CU) is a performance-level stall risk whose
mechanism has been pinned down by machine-checked proof. This report records the
mechanisms and evidence compactly in the note style.

---

## 1. JALR target address does not clear bit0

**Mechanism** 【direct source reading】: RISC-V specifies the JALR target as
`(rs1 + imm) & ~1` (bit0 cleared, to support the convention of tagging flags in
the low bit of instruction addresses). Ventus's JALR (DecodeUnit.scala:178 row,
branch=B_R, sel_alu3=A3_PC) gets its target address back-filled by the
operandCollector: for B_R, regOrder=2 reads rs1 (operandCollector.scala:191/:209),
and when bankIn returns, `rsReg(2) := imm.io.out + bankIn.data(0)`
(operandCollector.scala:304) — **imm+rs1 passes straight through, with no bit0
clearing**; execution.scala:56 `new_pc := io.in.bits.in3` forwards it as-is;
PCcontrol's `align()` (PCcontrol.scala:29-36) only aligns the PC to the
fetch-group (16B) boundary and does not clear bit0 either.

**Observability**: with RV32I and no C extension, every legal jump target is
4B-aligned and bit0 is necessarily 0 — the deviation is **unobservable**, making
this a fragility-point record (it shows up the moment RVC is introduced or foreign
code relying on bit0 semantics is run). Spec-side handling: IsaSpec D8 models
after the machine (bit0 not cleared), and the program contract requires aligned
targets (doc/modules/36 "D8/D10/D12 modeled after the machine" section).

## 2. vbranch comparison direction (when reverse=true it actually compares rs2<rs1)

**Mechanism** 【direct source reading】: the decode `c.reverse := s(7)`
(DecodeUnit.scala:585, with a self-describing comment "for some vector inst,
change in1 and in2"); all six vbranches (VBNE/VBEQ/VBLT/VBLTU/VBGE/VBGEU,
DecodeUnit.scala:473-478) have s(7) = **Y** — the vbranch comparison operands are
swapped on the datapath (`Mux(ctrl.reverse, in2, in1)` in each execution body of
execution.scala, e.g. the same pattern in the SFU block at :840-841). As a result,
vblt actually computes (rs2)<(rs1), contrary to the RVV intuition of "in vd order,
rs1<rs2".

**Characterization**: vbranch is a Ventus custom instruction family (not a
standard RVV instruction), so the direction choice is itself design freedom; the
note's value is that the **counter-intuitive semantics has been pinned down
after the machine** — spec-side, IsaSpec D10 models the hardware's reverse swap
(`doc/modules/36-VentusF-IsaSpec黄金语义.md`:177), and theorems such as
`isa_lane_vsub_match` pin down the consistency of the swap direction. The
assembler/compiler backend must generate operand order according to the machine
direction.

## 3. vmv.s.x writes all active lanes (RVV writes only lane 0)

**Mechanism** 【direct source reading】: RVV specifies that `vmv.s.x vd, rs1`
writes only element 0 of vd (the other elements are handled per the tail policy).
Ventus's VMV_S_X (DecodeUnit.scala:414: A1_RS1 broadcast + FN_A2ZERO) goes through
the ordinary vALU path, with write mask = instruction mask (all active lanes when
vm=1) — **the scalar is broadcast into all active lanes**.

**Characterization**: the machine deviates from RVV. For Ventus's custom flow,
"broadcast" is arguably even more useful; but code compiled per RVV semantics that
relies on lanes 1..31 keeping their old values (undisturbed) will be silently
polluted. Spec-side, IsaSpec D12 models after the machine (broadcast write to all
lanes); the deviation has been recorded and reported
(doc/modules/36:371-372,394-395).

**Related**: the same family's fourth item, the vmerge write-mask deviation (the
unconditional overwrite of `wvd_mask` at execution.scala:559 makes vmerge write
only the lanes in v0∧tmask), has been promoted to the standalone entry **I-50**
(doc/28 special-session ruling); it is not in this note group and is
cross-referenced here only.

## 4. instDemux: the scalar (X) side always takes the "second-lowest ready CU"; with only 1 free CU, scalar instructions cannot issue

**Mechanism** 【direct source reading + machine-checked Lean proof】: the
operandCollector's instDemux (operandCollector.scala:499-502, the num_warp>1
branch) sends vector requests to the **lowest** free CU (`outV_sel =
OHToUInt(PriorityEncoderOH(outReady1))`) and scalar requests to the
**second-lowest** free CU:

```scala
outReady2 := outReady1 & (~outV_sel_oh).asUInt   // :499  unconditionally removes the lowest ready bit
outX_sel := PriorityEncoder(outReady2)           // :500  the X side can only take the second-lowest
io.in(0).ready := outReady1.orR                  // :501  V side: any free CU suffices
io.in(1).ready := outReady2.orR                  // :502  X side: needs ≥2 free CUs
```

With only 1 free CU, `outReady2=0` and the scalar instruction **cannot issue**
(even though that CU is free); it must wait for another CU to be released or for
the vector side to occupy the lowest bit. This is not a deadlock: CUs are
eventually released (reclaimed after instruction issue); it is a
**performance-level stall risk**; single-instruction scenarios after quiesce are
unaffected.

**Evidence** 【machine-checked Lean proof】: `lean/VentusF/Progress.lean:521`
`prg_ocOrR_ocRdy2_of_two` — for any ready bitmap f, the existence of two distinct
ready CUs (f l ∧ f j ∧ l≠j) implies `ocOrR (ocRdy2 f) = true` (still non-empty
after removing the lowest bit); its comment (:519-520) explicitly records the
OcDemuxRes D-demux semantics that "instDemux's X side always takes the
second-lowest ready CU". This theorem is also positive support for the
fixed-version progress proof (with two ready CUs the X side can always issue);
read in the contrapositive: with a single ready CU this theorem's premise fails
and X-side issue is not guaranteed.

---

## 5. Conclusion

| Entry | Nature | Evidence layer | Disposition |
|---|---|---|---|
| JALR does not clear bit0 | ISA deviation, unobservable under RV32I (fragility point) | Direct source reading (operandCollector.scala:304, execution.scala:56, PCcontrol.scala:29-36); IsaSpec D8 | Not fixed; program contract requires 4B alignment |
| vbranch comparison direction | Custom-instruction semantics contrary to intuition | Direct source reading (DecodeUnit.scala:585/473-478); IsaSpec D10 + `isa_lane_vsub_match` | Not fixed; spec follows machine, toolchain must be informed |
| vmv.s.x writes all lanes | ISA deviation, observable by RVV-semantics programs | Direct source reading (DecodeUnit.scala:414); IsaSpec D12 | Not fixed; spec follows machine, deviation reported |
| instDemux second-lowest CU | Performance-level stall risk (not a functional bug) | Direct source reading (operandCollector.scala:499-502) + machine-checked proof `prg_ocOrR_ocRdy2_of_two` | Recorded as observation; if elimination is needed, the X side falls back to outReady1 as backstop |

The four entries share one trait: **each looks like a bug in isolation, yet each
is self-consistent within Ventus's custom-ISA trade-offs** — their value lies in
explicitly pinning down the boundary where "machine ≠ manual intuition": the spec
is modeled after the machine (capstone provable), and the deviations are
faithfully reported (so the software stack and future readers are not misled). If
the first three are ever to move toward RVV compliance, they must be handled
together with I-32/I-33/I-50 in a dedicated "RVV subset semantics" effort.
