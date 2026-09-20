> English translation of the Chinese master `doc/bugs/II-1-恢复加法升宽误译.md`. Translated 2026-09-13.

# II-1 Detailed Defect Analysis Report: IntDivMod Remainder-Recovery Addition Mistranslated as Widening Add (Chisel→Lean Translation Error)

| Item | Content |
|---|---|
| ID | II-1 (this project's first formal Class II record; reclassified from I-18's withdrawal on 2026-09-07) |
| Mistranslation location | Original `divCommonRNext` in `lean/Ventus/Arith/IntDivMod.lean` (former :198-203) — mistranslated the wrapping add at `IntDivMod.scala:70` as a widening add (add after `zeroExtend (xLen+1)`) |
| Corresponding source | `ventus/src/pipeline/IntDivMod.scala:70` (`recoveryR = Mux(remIsNeg, aReg.tail(1).head(xLen)+dReg.tail(1).head(xLen), …)`, RTL correct) |
| Type | Class II (Chisel→Lean translation error) — the model does not match the source |
| Severity | High (methodology level): this mistranslation supported a paper flagship bug conclusion, a no-op patch, and escaped detection by the whole-library numeric regression tests |
| Confirmation status | 【Confirmed · Fixed】model corrected to wrapping semantics and full re-verification passed (2026-09-07, doc/23) |
| Primary evidence | [Simulation run] RTL dual-channel reproduction of I-18 both failed (ChiselSim 4/3 and 0xDEADBEEF/0x1234 both correct; Verilator whole-machine same) → bit-by-bit comparison located the mistranslation point; [Direct source reading] Chisel 6.4.0/5.3.0 `Bits.scala:479,542-543` (`do_+ = do_+%` wrapping semantics); [Lean machine-checked proof] corrected model: full exhaustion + value-by-value agreement with RTL actual runs + regression equivalence with the repaired version |
| Lean model | Mistranslated file `lean/Ventus/Arith/IntDivMod.lean` (now corrected; current `divCommonRNext` :201-206); adaptations in `lean/Ventus/Arith/IntDivModFixed.lean`, `lean/Ventus/Arith/ExeSFU.lean`, `lean/VentusF/IsaSpec.lean` |
| Dedicated reports | `doc/23-I18存废核查.md` (technical ruling), `doc/24-I18撤案决策分析.md` (disposition decision), `doc/25-宽度假设排查报告.md` (whole-library sweep: isolated case) |
| Related entries | I-18 (the original entry before withdrawal — two faces of the same thing); I-17 (whose v1 patch was ineffective due to the same wrapping-semantics misunderstanding, doc/23 §7); III-1/III-2/III-3 (siblings of prior lessons on the spec/briefing/analysis side) |

---

## 0. Summary

II-1 is an operator-width-semantics mistranslation in the Chisel→Lean translation:
the remainder-recovery addition at IntDivMod.scala:70 is a **wrapping add** under
Chisel 6 (result width = max(operands) = xLen bits), but the model translated it as
a **widening add** (each addend `zeroExtend`ed to xLen+1 bits before adding). The
widened model preserves the 2^xLen borrow term in the two's complement of a negative
partial remainder, which lands via the subsequent `>>dLez` as a phantom bias of
+2^(xLen-dLez) — from this the model derived "the RTL remainder recovery is
systematically wrong" (the original I-18, xLen=8 exhaustive error rate ≈13%), backed
by a full set of self-consistent machine-checked proofs and fix verification. RTL
actual runs (dual channel) proved the hardware has no such bug; after bit-by-bit
comparison the mistranslation point was located and fixed, and full re-verification
passed.

The lesson of this entry is twofold: (i) **Chisel 5/6's `+`/`-` are wrapping
semantics** (`do_+ = do_+%`); "widening +" is a Chisel 3.x-era memory, and all three
parties (modeler, fix verifier, patch author) fell into the same trap; (ii) **when
the tests share the model's error, the tests have no ability to clear Class II
landmines** — the expected values of the original numeric regression were derived
from the model itself, sharing the mistranslation's error. What caught it was the
RTL reproduction channel in our workflow ("test-first + RTL reproduction"), which
simultaneously demonstrated that the risk feared by reviewer concern W1 (the
translation trust base) is real and that the workflow works.

---

## 1. Background: Translation Workflow and Trust Base

### 1.1 Background concepts

- **This project's translation discipline**: Chisel signals are translated as
  `BitVec n`/`Bool`, combinational logic as pure functions, sequential logic as a
  state structure + single-cycle step pure function, with line-by-line correspondence
  and Chisel source file:line annotations in comments. Lean's `BitVec.+` is natively
  wrapping (mod 2^n), so **naive translation is natively correct**; the risk
  concentrates at translation points with **explicit `zeroExtend`/`signExtend`/
  `setWidth` before arithmetic** (doc/25 §1).
- **Class II defect**: a translation error where the model does not match the source.
  It threatens every theorem built on that model — a "bug" proved on the model may
  not exist (this case), and correctness proved on the model may also fail to hold.
- **Reviewer concern W1 (translation trust base)**: the external reviewers' strongest
  challenge — "58,814 lines of manual translation with zero Class II records; why
  should we believe the model matches the RTL". II-1 is the first empirical answer
  to that challenge: the risk is real, and it was caught by the project's own
  process.

### 1.2 Design context of the mistranslation point

IntDivMod's remainder recovery (see I-18 report §1-§2): after iteration, aReg
(xLen+2-bit two's complement) holds the final partial remainder; when remIsNeg, the
normalized divisor dReg is added back, followed by a right shift to restore scale.
The RTL's entire width arrangement (xLen-bit wrapping add + wrap discarding the
2^xLen term) is exactly lossless under the algorithm invariant
P+dNorm < 2^(xLen+1).

---

## 2. Construct-by-Construct Reading of the Mistranslation Point

**RTL original (`IntDivMod.scala:70-71`, correct, no landmine)**:

```scala
70:  val recoveryR = Mux(remIsNeg.asBool, aReg.tail(1).head(xLen)+dReg.tail(1).head(xLen), aReg.tail(1).head(xLen))
71:  val commonRReg = RegEnable((recoveryR>>dLez)(xLen-1, 0), state===s_recovery)
```

Two xLen-bit addends are added; under Chisel 6 semantics `+` = `+%` = wrapping,
result xLen bits; the `(xLen-1,0)` extraction at :71 is the identity on an xLen-bit
result.

**Mistranslated model (former `IntDivMod.lean` :198-203, ★ landmine; deleted, archived)**:

```lean
let aPart : BitVec (xLen + 1) := (aReg.extractLsb' 1 xLen).zeroExtend (xLen + 1)  -- ★ widening invented out of thin air
let dPart : BitVec (xLen + 1) := (dReg.extractLsb' 1 xLen).zeroExtend (xLen + 1)  -- ★
let recoveryR := if aReg.msb then aPart + dPart else aPart
(recoveryR >>> dLez).setWidth xLen
```

★ Landmine: `zeroExtend (xLen+1)` turned "wrapping add" into "widening add followed
by truncation". The two are equivalent for non-negative sums, but not when
remIsNeg=1: as an xLen-bit value, aPart is the low-bit form of a negative two's
complement (containing the +2^xLen modular-equivalence term); the wrapping add folds
its sum with dPart back into [0, 2^xLen); the widening add preserves the 2^xLen
term, which lands via `>>dLez` as the phantom bias 2^(xLen-dLez).

**Corrected model (now `IntDivMod.lean:201-206`)**:

```lean
/-- commonR right-hand side (:70-71): both addends take bits[xLen:1] (xLen bits), then add with [wrapping]…
    (Q7/doc/23 withdrawal record embedded) -/
def divCommonRNext {xLen : Nat} (aReg dReg : BitVec (xLen + 2))
    (dLez : BitVec (divW xLen)) : BitVec xLen :=
  let aPart : BitVec xLen := aReg.extractLsb' 1 xLen
  let dPart : BitVec xLen := dReg.extractLsb' 1 xLen
  let recoveryR := if aReg.msb then aPart + dPart else aPart   -- BitVec addition is natively wrapping
  recoveryR >>> dLez
```

**Chisel semantics evidence** [Direct source reading, checked in doc/23 §1]:

- Chisel 6.4.0 `Bits.scala:479`: `override def do_+(that: UInt): UInt = this +% that`;
- `:542-543`: `do_+% = (this +& that).tail(1)` (widen then cut the MSB = wrapping);
- `do_-`/`do_-%` likewise wrap (:480, :550-551); Chisel 5.3.0 likewise wraps (from
  :473 on). Widening requires explicit `+&`/`-&`; only `*` widens (width = sum of the
  two operand widths).

---

## 3. Defect Analysis

### 3.1 Precise description of the mistranslation

| | Chisel 6 RTL | Mistranslated model |
|---|---|---|
| Addition semantics | xLen-bit wrapping (`+%`) | xLen+1-bit widening (zeroExtend then `+`) |
| recoveryR when remIsNeg=1 | (aPart + dPart) mod 2^xLen = correct recovered value | (aPart + dPart) ∈ [0, 2^(xLen+1)), containing the +2^xLen term |
| After >>dLez | spec value | spec value + 2^(xLen-dLez) (phantom bias) |
| Observable symptom | quotient and remainder both correct | "quotient all right, remainder wrong iff remIsNeg=1" (the original I-18 formula) |

### 3.2 Root cause

1. **The root cause is the Chisel 3→5/6 change of `+` semantics** (widening →
   wrapping) — the whole team (modeler, fix verifier, patch author) carried the same
   wrong memory (doc/23 §1).
2. **Tests sharing the model's error** (the core lesson of I-18): the original
   `divCheckOne` branched its expected value on the `divBug3R` formula derived from
   the model — the exhaustion verified "model ≡ the model's own predicted formula",
   structurally incapable of clearing a Class II mistranslation.
3. **Misleading symptom**: the quotient does not go through the recovery add, so the
   symptom "quotient all right, remainder wrong" directed suspicion at the algorithm
   layer rather than the bit-width layer.
4. **Reverse reinforcement by fix verification**: the repaired version
   `dvfCommonRNext` (add-then-truncate) happens to equal the correct value
   mathematically ⟹ repaired version ≡ real RTL — "the fix works" conversely
   reinforced the false premise "the original is buggy" (doc/23 §3).

### 3.3 Harm and tolerability

- **Threat to proof assets (the standard harm of Class II)**: the original I-18
  evidence built on the mistranslated model (full exhaustion + witnesses +
  repaired-version regression) all became invalid at the RTL level; fortunately the
  mistranslation was isolated to the single site `divCommonRNext`, and the I-17/I-19
  evidence chains do not pass through it (doc/23 §4 — on the trigger cone remIsNeg
  is identically 0, proved by both derivation and exhaustion), so no collateral
  reversal occurred.
- **Threat to deliverables**: the i18 patch is a no-op based on the mistranslated
  model (fixing a nonexistent problem); delivering it as-is upstream would damage
  credibility. Withdrawn (the internal fix manifest I-18 line marked withdrawn).
- **Threat to the paper**: the original I-18 was one of the abstract's flagship bugs
  and the source of the "≈13%" figure; the coordinated revision upon withdrawal was
  handled by doc/24 decision point 1 (option b: withdraw + convert into a
  methodology case).
- **Tolerability**: fixed + whole-library sweep clean (doc/25); residual risk is
  zero; kept permanently as a lesson entry.

---

## 4. Lean Formal Evidence (post-correction)

The "discovery evidence" for the mistranslation is simulation (§5); the Lean-side
evidence is machine-checked proof of **fix validity and isolation**:

- **Corrected model conforms to the spec**: `div_test_xlen4_exhaustive` /
  `div_test_xlen8_exhaustive` (IntDivMod.lean:487/:493, native_decide) — on the
  non-I-17 cone, q and r both = `divSpecQ`/`divSpecR`; the corrected `divCheckOne`
  (:405-414) has dropped the remIsNeg branch.
- **Pinned value-by-value against RTL actual runs**: `div_test_32_recovery_unsigned`
  / `div_test_32_recovery_signed` / `div_test_32_recovery_eq_spec` (4/3→(1,1),
  -4/3→(-1,-1)); `div_test_32_random_u` / `div_test_32_random_s`
  (0xDEADBEEF/0x1234 → (0xC3BA5, 0x76B) / (0xFFFE2B63, 0xFFFFF8D3)) — **the expected
  values come from ChiselSim actual runs (doc/22), no longer from the model itself**.
- **Repaired-version regression equivalence (strengthened)**: IntDivModFixed.lean's
  `dvfRegrOneFull`/`dvfRegrAllFull` + `dvf_test_regr_full_xlen4` /
  `dvf_test_regr_full_xlen8` — the corrected original ≡ the repaired version,
  pointwise on all inputs outside the I-17 trigger cone (all 131072 combinations at
  xLen=8), no longer excluding remIsNeg; `dvf_commonR_eq_orig_of_not_neg` (restored
  via the supplementary lemma `div_setWidth_ushiftRight`) and
  `dvf_exec_eq_orig_of_safe` regression chains all green.
- **Isolation machine-checked proof**: the evidence chains of I-17 (cnt truncation)
  and I-19 (stale zeroQReg) do not pass through `divCommonRNext`; the conclusion
  that both reproduce exactly on RTL is unchanged (doc/23 §4).
- **Build and audit**: `lake env lean Ventus/Arith/IntDivMod.lean` EXIT=0 (cgroup
  48G); axioms only propext/Classical.choice/Quot.sound/native_decide trust axioms,
  zero sorry; full `lake build` passes (doc/23 §2/appendix).

---

## 5. Simulation Verification (the discovery channel)

This mistranslation was caught by the RTL reproduction channel (doc/22, actually run
2026-09-06/07):

- **ChiselSim module level** (`repro/IntDivModBugRepro.scala` I-18/I-18b cases):
  4/3(u)=(1,1), 0xDEADBEEF/0x1234(u)=(0xC3BA5,0x76B) — both spec-correct results;
  the model-predicted wrong values ((1,5), r=0x276B) never appeared. **Not
  reproduced**.
- **Verilator whole-machine level** (`repro/verilator/` kernel `i18_rem_recovery`):
  for rem 4/3, both quotient and remainder are 1 — correct; on the whole-machine
  channel, 8 of 9 target bugs were reproduced, I-18 the only one not reproduced.
- **Follow-up**: the I-18/I-18b cases have been converted into correctness
  regression tests (asserting spec values), staying green in the 35/38 patch-tree
  regression (doc/22 patch-tree regression: IntDivModBugRepro 4/4 green).

Methodological point: of the 18 ChiselSim cases, 14 reproduced successfully and the
rest each had an explanation (I-8 premise refuted, I-29/I-30 test calibration); only
I-18's "failure to reproduce" could not be explained by test-engineering issues — it
is exactly this "isolated failure against the backdrop of an overall trustworthy
process" that gave the bit-by-bit comparison maximal confidence.

---

## 6. Impact Analysis

- **Direct contamination surface**: the original I-18 conclusion (archived at
  doc/03:448-484), the related claims in the paper draft and technical report, the
  i18 patch and its comment ("Chisel's + widens" is false for Chisel 5/6). All
  handled (doc/24 decision points 1/4).
- **Collateral finding**: the same misunderstanding made i17 patch v1 ineffective
  (the `dLez - aLez + 1.U` at IntDivMod.scala:46 wraps within 5 bits, iter=32≡0;
  widening cnt alone is insufficient) — revised to double widening of cnt+iter and
  empirically verified on patched RTL (doc/23 §7; the internal fix manifest I-17 line).
- **Whole-library sweep** (doc/25): a five-dimension grep (extend×arithmetic
  co-occurrence, toNat/ofNat fallbacks, shift mixing, extend×comparison, and reverse
  checks of Chisel-side `+&`/`.tail/.head`) covering ~77k lines of lean/; 21 groups
  of hits were checked one by one against the Chisel source — **OK 21/21,
  suspicions 0, confirmed mistranslations 0**. Structural reason for the isolated
  case: BitVec addition is natively wrapping, so every explicit widening site either
  truncates back to the original width afterwards (E1), or lies in a provably
  non-overflowing value range (E3), or sits in an assembly/shift-amount context
  (E4/E2); I-18 is special in that the widened result is **not truncated back** but
  feeds directly into a shift, and the path had no independent test coverage.
- **Test-independence spot check** (doc/25 §5): the expected-value sources of the
  10 regression-dense files were classified one by one; only the multi-cycle
  trace class (CuInterface and whole-machine level) has somewhat weaker
  landmine-clearing ability; the corrected IntDivMod's expected values come from RTL
  actual runs — the strongest tier in the whole library.

---

## 7. Disposition and Lesson Codification

1. **Model fix**: `divCommonRNext` dropped the widening and adds with wrapping;
   deleted `divBug3CommonR`/`divBug3R`, which served only BUG3; `divCheckOne`
   simplified; witnesses renamed and re-pinned to RTL actual values; Q7 rewritten as
   a withdrawal record (lesson embedded). Adapted IntDivModFixed/ExeSFU/IsaSpec
   (doc/23 §2/§5).
2. **Patch withdrawal**: i18 ruled a semantics-preserving no-op (dReg always even ⟹
   add-then-truncate ≡ truncate-then-add), withdrawn from the upstream delivery list
   (doc/23 §6).
3. **Discipline codification** (written into the AGENTS.md pitfalls appendix and
   translation-discipline section):
   - "Chisel 5/6's `+`/`-` are wrapping semantics (`do_+ = do_+%`); widening requires
     explicit `+&`; when translating, do not default-translate `+` as a widening
     add";
   - "For any translation point that depends on operator width semantics, the
     expected values of numeric regression tests must be derived independently of
     the model" (I-18's tests shared the model's error; the tests failed to clear
     the landmine);
   - doc/25's E1-E4 width-review four forms as a referenced artifact.
4. **Methodological gain** (doc/24 §5): Class II went from "a zero-record latent
   worry" to "recorded, caught by the process, fixed, fully re-verified across the
   library + whole-library sweep clean" — the strongest answer to reviewer concern
   W1.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Mistranslation located | Sole divergence = widening vs wrapping in `divCommonRNext`; confirmed by bit-by-bit comparison | Line-by-line code comparison |
| Chisel semantics | 6.4.0 `Bits.scala:479,542-543`; 5.3.0 same — `+` wraps | Direct source reading (doc/23) |
| Discovery channel | RTL dual-channel reproduction failure (ChiselSim ×2 witnesses + Verilator whole-machine) | Empirical (doc/22) |
| Fix verification | Corrected model exhaustively spec-conformant, value-by-value agreement with RTL actual runs, regression-equivalent to the repaired version | Lean machine-checked proof + empirical reconciliation |
| Isolation | I-17/I-19 unaffected; i18 patch withdrawn as no-op; i17 patch collaterally revised | Machine-checked proof + decision record |
| Systematic closure | doc/25 whole-library sweep 21/21 OK, isolated-case conclusion; E1-E4 and test-independence discipline entered into AGENTS.md | Whole-library ruling |

II-1 and I-18 are two faces of the same event: the I-18 report records "how an RTL
bug was refuted", while this report records "how a model mistranslation existed, why
it survived, how it was caught, and how recurrence is prevented". The core
discipline it establishes is: **the model's internal self-consistency (exhaustion,
fix verification, regression equivalence) does not constitute any evidence of
faithfulness to the RTL; only tests with independent expected values and the RTL
reproduction channel can clear Class II landmines.**
