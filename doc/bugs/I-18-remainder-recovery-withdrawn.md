> English translation of the Chinese master `doc/bugs/I-18-余数恢复撤案.md`. Translated 2026-09-13.

# I-18 Detailed Defect Analysis Report: IntDivMod Remainder Recovery "Truncate-Then-Add" — Withdrawn (Class II mistranslation; no such bug in RTL)

| Item | Content |
|---|---|
| ID | I-18 (**Withdrawn**, 2026-09-07; reclassified as II-1 after withdrawal) |
| Source location | Accused point `ventus/src/pipeline/IntDivMod.scala:70` (remainder recovery addition) — **on review, this RTL line is correct** |
| Type | Originally judged a Class I functional bug; final ruling: **Class II (Lean model mistranslation)**; the defect never existed in the RTL |
| Severity | No hardware harm after withdrawal; the incident itself is a top-priority methodology case (first empirical evidence for trust-base concern W1) |
| Confirmation status | 【Withdrawn (Class II, 2026-09-07)】; model fixed and full re-verification passed |
| Primary evidence | [Simulation run] ChiselSim module-level, both witnesses (4/3, 0xDEADBEEF/0x1234) produce spec-correct results + Verilator whole-machine level also fails to reproduce; [Direct source reading] Chisel 6.4.0/5.3.0 `Bits.scala:479,542-543` confirm `+` is wrapping semantics; [Lean machine-checked proof] fixed model exhaustively (xLen=4/8) conforms to the RISC-V spec, and the fixed model is regression-equivalent to the repaired version |
| Lean model | Mistranslation point: original `divCommonRNext` in `lean/Ventus/Arith/IntDivMod.lean` (former :198-203, widening add); corrected `divCommonRNext` (now :201-206, wrapping add); repaired version `lean/Ventus/Arith/IntDivModFixed.lean` |
| Repro/patch | `repro/IntDivModBugRepro.scala` (I-18/I-18b cases); `repro/verilator/` kernel `i18_rem_recovery`; patch `i18-intdivmod-recoveryr.patch` (internal fix manifest; not released) (ruled a semantics-preserving no-op, withdrawn from the upstream delivery list) |
| Dedicated reports | `doc/23-I18存废核查.md` (technical review), `doc/24-I18撤案决策分析.md` (disposition decision), `doc/25-宽度假设排查报告.md` (whole-library sweep, isolated-case conclusion); actual-run records in `doc/22-复现执行结果.md` |
| Related entries | II-1 (the formal home of this case after withdrawal — two faces of the same thing); I-17 (cnt truncation in the same module, a real bug whose v1 patch was invalidated by the same wrapping semantics — doc/23 §7); I-19 (stale zeroQReg in the same module, a real bug, unaffected) |

---

## 0. Summary

The original I-18 accusation: IntDivMod's remainder-recovery path (IntDivMod.scala:70)
"truncates then adds" — the two (xLen+2)-bit addends are each truncated to bits[xLen:1]
before being added, so a negative partial remainder (two's complement) loses its sign
bit, making the remainder systematically too large by 2^(xLen-dLez) when remIsNeg=1
(exhaustive xLen=8 error rate ≈13%). It was one of the flagship bugs in this project's
paper.

In the 2026-09-07 reproduction wave, **RTL reproduction failed on both channels**: the
ChiselSim module-level witnesses (4/3(u) and 0xDEADBEEF/0x1234(u)) both produced
spec-correct results, and the Verilator whole-machine level was likewise correct.
Bit-by-bit comparison located the single divergence: **the Lean model mistranslated
the wrapping add at :70 as a widening add** — in Chisel 5/6, `+` has wrapping semantics
(`do_+ = do_+%`, result width = max(operands)), and the wrap-around happens to discard
exactly the 2^xLen phantom-bias term on which the mistranslated model based its wrong
formula. The RTL's remainder recovery was correct all along; I-18 never existed.

After the case was refuted at step 3 (reproduction) of the standard Class I bug
handling procedure, it went through the full withdrawal process: paired rulings by
technical review (doc/23, including line-level checks against two Chisel versions and
mechanism derivation) + decision analysis (doc/24); the model was fixed to wrapping
semantics and fully re-verified; the i18 patch was ruled a bit-exact no-op and
withdrawn; a whole-library sweep for the same class (doc/25) confirmed I-18 as an
isolated case. The original analysis is archived at doc/03:448-484; this document is
its complete narrative.

**Methodological significance**: this is the project's first formal Class II record,
and the first empirical answer to the reviewers' strongest challenge (W1: "with zero
Class II records in manual translation, why should we trust it") — it simultaneously
demonstrates that the risk is real and that the "test-first + RTL reproduction"
workflow works: the process caught its own mistake.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **Non-restoring division**: a hardware division algorithm. Both dividend and
  divisor are taken as absolute values and left-shifted for normalization (leading-zero
  alignment), then iterated bit by bit: each cycle, depending on the sign of the
  current partial remainder, the divisor is added or subtracted and one quotient bit
  is produced. After the iterations, the final partial remainder may be negative
  (two's complement) and needs one **remainder recovery** step: if negative, add the
  divisor back. The quotient is corrected accordingly (the difference of the two
  quotient-bit registers Q and QN).
- **The IntDivMod module**: Ventus's 32-bit integer divide/remainder unit, serving
  the four RISC-V instructions DIV/DIVU/REM/REMU; a 5-state FSM (s_idle → s_pre →
  s_compute → s_recovery → s_finish), instantiated num_sfu=8 times at
  execution.scala:846 to serve 32 lanes.
- **Chisel operator width semantics (the crux of this case)**: in Chisel 5/6, `+`/`-`
  on UInt are **wrapping** operations (result width = max(operand widths), overflow
  bit discarded); widening requires explicitly writing `+&`/`-&`. This differs from
  the Chisel 3.x-era memory of "widening add" — all three parties on the team (the
  modeler, the fix verifier, and the patch author) fell into the same trap (doc/23 §1).

### 1.2 Design intent

The remainder-recovery cycle (s_recovery): at the end of iteration, `aReg` (xLen+2
bits) holds the two's complement of the final partial remainder, and `dReg` holds the
normalized divisor (also left-shifted by dLez bits). `remIsNeg = aReg`'s top bit. The
recovery operation right-shifts both by one bit (dropping the lowest bit — the extra
bit shifted in during normalization), adds them (only when remIsNeg), then
right-shifts by dLez bits to return to the original scale, yielding the true
remainder.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: remainder recovery (`IntDivMod.scala:68-71`, :70 is the original accused point, ★ actually the mistranslation site)**:

```scala
68:  val remIsNeg = aReg.head(1)
69:  val commonQReg = RegEnable(Mux(remIsNeg.asBool, Q + (~QN).asUInt, Q - QN), state===s_recovery)
70:  val recoveryR = Mux(remIsNeg.asBool, aReg.tail(1).head(xLen)+dReg.tail(1).head(xLen), aReg.tail(1).head(xLen))  // ★
71:  val commonRReg = RegEnable((recoveryR>>dLez)(xLen-1, 0), state===s_recovery)
```

Bit-level reading: `aReg.tail(1).head(xLen)` = take bits[xLen:1] (xLen bits). The two
**xLen-bit** addends are added with `+%` wrapping under Chisel 6, and the result is
still **xLen bits** — the 2^xLen borrow term in the two's complement of a negative
partial remainder is naturally discarded by the wrap. Let the final partial remainder
be a 34-bit two's-complement negative value P and the normalized divisor be dNorm
(always even, constructed by `Cat(0,…,0.U(1.W))`, IntDivMod.scala:51); then

```
(aPart + dPart) mod 2^xLen = ⌊(P + dNorm)/2⌋ mod 2^xLen
```

and the algorithm invariant gives P + dNorm ∈ [0, 2^(xLen+1)), hence
⌊(P+dNorm)/2⌋ < 2^xLen — **the wrap is lossless and yields exactly the correct
recovered value** (full mechanism derivation in doc/23 §1).

**Construct 2: normalization and iteration (:44-66, context)**:

```scala
46:  val iter = Mux(aLez > dLez, 0.U, dLez - aLez + 1.U)
51:  val dNorm = Cat(0.U(1.W), (unsignedDReg<<dLez)(xLen-1, 0), 0.U(1.W))
56:  val cnt = RegInit(0.U(log2Up(xLen).W))
66:  val aNext = Mux(sel_pos, aShift + dNegNorm, Mux(sel_neg, aShift + dNorm, aShift))
```

:46/:56 are the I-17 scene (a real bug, unaffected by this case); the
`aShift + dNegNorm` at :66 is likewise a wrapping add (xLen+2 bits), modeled
consistently, no divergence.

**Construct 3 (the mistranslation scene): the Lean model's original `divCommonRNext`** (IntDivMod.lean former :198-203, now corrected; archived for comparison):

```lean
-- mistranslated version (deleted): both addends zeroExtend'd to xLen+1 bits before adding — modeled as widening add
let aPart : BitVec (xLen + 1) := (aReg.extractLsb' 1 xLen).zeroExtend (xLen + 1)
let dPart : BitVec (xLen + 1) := (dReg.extractLsb' 1 xLen).zeroExtend (xLen + 1)
let recoveryR := if aReg.msb then aPart + dPart else aPart
(recoveryR >>> dLez).setWidth xLen
```

The widening add preserves the +2^xLen term of P/2, which lands via `>>dLez` as a
**phantom bias** of +2^(xLen-dLez) — the original Q7 formula
`commonR = |r_true| + 2^(xLen-dLez)` is correct *for the widened model* (exhaustively
self-consistent at xLen=4/8), but the widened model ≠ RTL. The corrected version (now
IntDivMod.lean:201-206) adds with wrapping directly at xLen bits (Lean's `BitVec.+`
is natively wrapping, corresponding exactly to Chisel 6's `+%`).

---

## 3. Defect Analysis

### 3.1 Original analysis (archived, now refuted)

Original accusation chain (preserved at doc/03:448-484): the two (xLen+2)-bit addends
at :70 are "each truncated first" to bits[xLen:1] before being added, so a negative
partial remainder loses its sign bit ⇒ when remIsNeg=1,
commonR = |r_true| + 2^(xLen-dLez); the quotient is completely correct on all
non-I-17 inputs (the quotient does not go through the recovery add), and the
remainder is wrong if and only if remIsNeg=1; xLen=8 error rate ≈13%. Original
witnesses: `4/3 → (1,5)` should be `(1,1)`; `-4/3 → r=-5` should be -1;
`0xDEADBEEF/0x1234 (u) → r=0x276B` should be `0x76B`.

That analysis is fully valid for the mistranslated model (machine-checked +
exhaustively self-consistent), but it rests on the wrong width semantics.

### 3.2 Withdrawal argument (root cause)

1. **RTL reproduction failed on both channels** (§5) — of 9 target bugs, 8 were
   reproduced; only I-18's two witnesses produced spec-correct results on both
   independent channels;
2. **Bit-by-bit comparison located the divergence**: the only divergence is the bit
   width semantics of the recovery addition;
3. **Chisel source line-level evidence** [Direct source reading]: Chisel 6.4.0
   `Bits.scala:479` `override def do_+(that: UInt): UInt = this +% that`;
   `:542-543` `do_+% = (this +& that).tail(1)` (widen then cut the MSB = wrapping).
   Chisel 5.3.0 is likewise wrapping (checked from v5.3.0 Bits.scala:473 on).
   "Widening +" is a Chisel 3.x-era memory;
4. **Algorithm-side losslessness argument**: the 2^xLen term discarded by the wrap is
   exactly the phantom bias, guaranteed by the invariant P + dNorm < 2^(xLen+1)
   (§2 construct 1);
5. **Three-way reconciliation of the corrected model**: the corrected model, exhaustively
   at xLen=4 (512) / xLen=8 (131072), has q and r both equal to the RISC-V spec on
   the non-I-17 cone, and both witness outputs match the RTL actual runs value by value.

Ruling (doc/23 §1): **case (a) holds — a Class II translation error; I-18 is
withdrawn; the RTL's remainder-recovery path was correct all along.**

### 3.3 Harm and tolerability

- **Hardware harm: none** (the RTL is correct; no fix needed).
- **Engineering harm (actually occurred)**: (i) a nonexistent bug entered the paper
  draft and technical report as a flagship result (doc/24 §1.3 — the abstract /
  Results preview / Table I all need coordinated revision); (ii) the i18 patch,
  written against the mistranslated model, is a no-op that rewrites correct code into
  an equivalent form, and delivering it as-is upstream would damage credibility
  (doc/24 §1.1); (iii) collateral finding of a sibling issue: i17 patch v1 only
  widens cnt, which is ineffective under Chisel 6 wrapping semantics (the
  `dLez - aLez + 1.U` at :46 wraps within 5 bits, iter=32≡0) — the correct fix needs
  double widening of both cnt and iter (doc/23 §7).
- **Trust-layer gain**: the zero-Class-II-record situation was broken, and it was
  caught by our own process; the "fix-as-verification" narrative upgraded to "the
  same discipline applied to RTL and to the model" (doc/24 §5).

### 3.4 Why the mistranslation stayed self-consistent for so long (doc/23 §3)

1. In-model exhaustiveness can only verify "model ≡ the model's own predicted
   formula" (divCheckOne once branched on divBug3R); it cannot detect a Class II
   mistranslation — **exhaustive self-consistency ≠ faithfulness to RTL**;
2. The quotient does not go through the recovery add (commonQ uses Q±QN), so the
   symptom "quotient all right, remainder wrong" directed suspicion at the algorithm
   layer; nobody suspected bit widths;
3. The repaired version dvfCommonRNext (add-then-truncate) happens to equal the
   correct value mathematically ⟹ repaired version ≡ real RTL — the verification
   that "the fix works" conversely reinforced the false premise that "the original
   is buggy";
4. The tests shared the model's error: the expected values of the original numeric
   regression tests were derived from the model itself, with no independent source,
   leaving no ability to clear a Class II landmine.

---

## 4. Lean Formal Evidence

Two periods; the evidence objects must be kept distinct:

**Pre-withdrawal (machine-checked proofs about the mistranslated model — invalid for
the RTL; archived)**: xLen=4 all 512 combinations and xLen=8 all 131072 combinations
verified the wrong formula with zero mismatches; witnesses `div_test_32_bug3_*`
(4/3→(1,5) etc.). These theorems prove "the behavior of the mistranslated model" and
were mistakenly taken as evidence about RTL behavior.

**Post-withdrawal (machine-checked proofs about the corrected model — currently in
force)** (`lean/Ventus/Arith/IntDivMod.lean`):

- `divCommonRNext` (:201-206): wrapping-semantics corrected version, with the Q7
  withdrawal record embedded in the comment;
- `div_test_xlen4_exhaustive` / `div_test_xlen8_exhaustive` (:487/:493,
  native_decide): the corrected `divCheckOne` has dropped the remIsNeg branch — on
  the non-I-17 trigger cone, q and r are both identically equal to
  `divSpecQ`/`divSpecR` (the RISC-V spec);
- `div_test_32_recovery_unsigned` / `div_test_32_recovery_signed` /
  `div_test_32_recovery_eq_spec` (:535-541): 4/3 → (1,1), -4/3 → (-1,-1), matching
  the ChiselSim actual runs value by value;
- `div_test_32_random_u` / `div_test_32_random_s` (:529-531): 0xDEADBEEF/0x1234
  → (0xC3BA5, 0x76B) / (0xFFFE2B63, 0xFFFFF8D3), in three-way agreement with the
  ChiselSim I-18b actual run and the IntDivModFixed repaired version — **the expected
  values come from RTL actual runs, no longer from the model**.

**Repaired-version-side adaptation** (`lean/Ventus/Arith/IntDivModFixed.lean`):

- `dvfT_i18_unsigned` / `dvfT_i18_signed` / `dvfT_i18_random_u` / `dvfT_i18_random_s`
  / `dvfT_i18_eq_spec`: all repaired-version witnesses still hold — the repaired
  version was a correct model all along, and is now equivalent to the corrected
  original on the recovery path;
- `dvf_commonR_eq_orig_of_not_neg` (restored via the supplementary lemma
  `div_setWidth_ushiftRight`) + `dvf_exec_eq_orig_of_safe`: regression chain restored;
- strengthened regression `dvfRegrOneFull`/`dvfRegrAllFull` +
  `dvf_test_regr_full_xlen4`/`dvf_test_regr_full_xlen8`: **the corrected original ≡
  the repaired version, pointwise on all inputs outside the I-17 trigger cone** (no
  longer excluding remIsNeg; all 131072 combinations at xLen=8 pass) — this is the
  formal evidence that "the i18 fix is a semantics-preserving no-op";
- ExeSFU side: `exs_test_reverse` now pins the spec value 6 (previously pinned the
  BUG3 value 14); `exs_test_reverse_bug3_ne_spec` renamed to
  `exs_test_reverse_eq_spec`.

**Isolation** (doc/23 §4): the evidence chains for I-17/I-19 do not pass through
`divCommonRNext` (on the I-17 trigger cone remIsNeg is identically 0 — proved both by
derivation and by exhaustion; I-19 goes through the specialR path), so the conclusion
that both reproduce exactly on RTL is unaffected.

---

## 5. Simulation Verification (both channels "failed to reproduce" — the decisive counter-evidence of this case)

**ChiselSim module level** (`repro/IntDivModBugRepro.scala`, actually run
2026-09-06/07, doc/22 verdict table):

- I-18 case `4/3(u)`: actual `(1,1)` — **spec-correct** (the model predicted the
  buggy value (1,5));
- I-18b cross case `0xDEADBEEF/0x1234(u)`: actual `(0xC3BA5, 0x76B)` —
  **spec-correct** (the model predicted r=0x276B).

**Verilator whole-machine level** (`repro/verilator/` kernel `i18_rem_recovery`,
actually run 2026-09-07, doc/22): for rem 4/3, both the quotient (memory word w0)
and the remainder (w4 = mem[0x90000004]) are 0x00000001 — correct; on the
whole-machine channel, 8 of 9 target bugs were reproduced, I-18 being the only one
not reproduced.

**Patch-tree regression** (2026-09-07/10, doc/22): IntDivModBugRepro is 4/4 green on
the 35/38 patch trees — the I-18/I-18b cases have been converted into "correctness
regression tests" (asserting spec values).

doc/22's record at the time (the "comparison against Lean model conclusions" section)
correctly pointed out the next step: "strongly suggests that IntDivMod.lean's
modeling of the recovery path deviates from the RTL (Class II suspicion); recommend
re-checking the bit-by-bit correspondence of aNext/dNorm/dNegNorm/iter before ruling
on I-18's standing" — the bit-by-bit comparison in doc/23 is the execution of that
recommendation.

---

## 6. Upstream Impact Analysis

- **No bug to report**: the RTL is correct; upstream needs no change; I-18 was
  withdrawn from the upstream delivery list.
- **Ruling on the i18 patch** (doc/23 §6): `i18-intdivmod-recoveryr.patch`
  (`recoveryR = Mux(remIsNeg, (aReg +% dReg).tail(1).head(xLen), ...)`) is
  **bit-exactly equivalent** to the original on all reachable states (proof key:
  dReg is always even ⟹ ⌊(aReg+dReg)/2⌋ = ⌊aReg/2⌋ + dReg/2, no LSB carry; numeric
  evidence dvf_test_regr_full_xlen4/8). Applying it is harmless but pointless, and
  its comment "Chisel's + widens to xLen+3 bits" is false for Chisel 5/6. **Withdrawn
  from the upstream delivery list**; the I-18 line of the internal fix manifest has been changed
  to "WITHDRAWN 2026-09-07 (Class II …)".
- **Toolchain sensitivity note** (end of doc/23 §6): if compiled with Chisel ≤3, the
  `+` at :70 widens, and I-18 would conversely be real with the i18 patch a true fix.
  This project's snapshot pins Chisel 6.4.0, and the ruling is based on that; the
  sensitivity is worth explaining in upstream communication.
- **Collateral impact on the I-17 delivery**: i17 patch v1 is ineffective (doc/23
  §7); it has been revised to double widening of cnt+iter and empirically verified on
  patched RTL (the internal fix manifest I-17 line, divu 0x80000000/1 → (0x80000000,0),
  2026-09-07).

---

## 7. Fix and Fix Verification

The object being "fixed" in this case is the **model**, not the RTL:

1. **Model correction** (doc/23 §2): `divCommonRNext` dropped the zeroExtend widening
   and now adds with wrapping at xLen bits; deleted `divBug3CommonR`/`divBug3R`,
   which served only BUG3; the non-trigger-cone branch of `divCheckOne` now requires
   both q and r = spec; witnesses renamed and re-pinned (`div_test_32_bug3_*` →
   `div_test_32_recovery_*`) to RTL actual values.
2. **Verification**: `lake env lean Ventus/Arith/IntDivMod.lean` EXIT=0 (cgroup 48G);
   axiom audit shows only propext/Classical.choice/Quot.sound/native_decide trust
   axioms, zero sorry; IntDivModFixed likewise green after adaptation; full
   `lake build` passes (doc/23 appendix).
3. **Strengthened regression equivalence**: `dvfRegrAllFull` proves exhaustively that
   the corrected original ≡ the repaired version (outside the I-17 cone) — all
   repaired-version theorem assets retain their value.
4. **Discipline codification** (doc/24 decision point 5, executed): the AGENTS.md
   pitfalls appendix gained "Chisel 5/6's `+`/`-` are wrapping semantics
   (do_+ = do_+%); widening requires `+&`/`-&`; for any translation point that
   depends on operator width semantics, the expected values of numeric regression
   tests must be derived independently of the model"; doc/25's E1-E4 width-review
   four forms have been written into the AGENTS.md translation discipline section.
5. **Whole-library sweep** (doc/25): 21 groups of extend/arithmetic co-occurrence
   hits were checked one by one against the Chisel source — **OK 21/21, suspicions 0,
   confirmed mistranslations 0** — I-18 is an isolated case (its peculiarity: the
   widened result is not truncated back but feeds directly into a shift, and the path
   had no independent test coverage).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| ChiselSim reproduction (negative) | Both I-18/I-18b witnesses yield spec-correct results ((1,1), (0xC3BA5,0x76B)); the model-predicted wrong values never appeared | Empirical, decisive |
| Verilator whole-machine reproduction (negative) | i18_rem_recovery kernel remainder correct; the only one of 9 target bugs not reproduced | Empirical, decisive |
| Chisel source direct reading | 6.4.0 `Bits.scala:479` `do_+ = do_+%`, `:542-543` `do_+% = (this +& that).tail(1)`; 5.3.0 same | Line-level check (doc/23) |
| Mechanism derivation | The wrap discards the 2^xLen phantom-bias term; invariant P+dNorm < 2^(xLen+1) guarantees losslessness | Mathematical derivation + three-way reconciliation on an instance (4/3 cycle by cycle) |
| Lean machine-checked proof (corrected) | xLen=4/8 exhaustive: q, r both conform to the RISC-V spec; witnesses match RTL actual runs value by value; corrected original ≡ repaired version regression equivalence (dvf_test_regr_full_xlen4/8) | Full exhaustion + numeric pinning |
| Patch ruling | i18 patch = semantics-preserving no-op, withdrawn; the internal fix manifest marked withdrawn | Machine-checked proof + decision record |
| Whole-library sweep | doc/25: 21/21 OK, I-18 an isolated case; E1-E4 four forms entered into AGENTS.md | Systematic closure |

I-18 is the most important methodological lesson of this project: **no matter how
complete the formal evidence (full exhaustion + symbolic derivation + fix
verification closed loop), if the model and the RTL diverge semantically at one
point, all the evidence is merely a self-consistent proof about the wrong model**.
What caught it was not a stronger proof but the RTL reproduction channel in our
discipline — this directly answers the reviewers' challenge about "zero Class II
records" (W1), and turned the "three-way disposition" (Class I/II/III) from a
taxonomy into a practice with a complete evidence chain. The formal record on the
translation side is II-1.
