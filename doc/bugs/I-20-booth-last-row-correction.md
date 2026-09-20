> English translation of the Chinese master `doc/bugs/I-20-Booth末行修正丢失.md`. Translated 2026-09-13.

# I-20 Defect Analysis Report: Booth last-row negation correction lost under general len (implicit contract, unreachable in the current configuration)

| Item | Content |
|---|---|
| ID | I-20 |
| Source location | `ventus/src/pipeline/Multiplier.scala:62-69` (the `~s` of the last-row partial product `Cat(~s, pp_temp, t)` lands in column 2·len, i.e. a bit position discarded from the result); linked `:47-54` (`neg_b` inverts without adding one), `:56-60` (the `t` correction is repaid by the next row) |
| Type | Implicit contract / robustness gap (mechanism confirmed, unreachable in the current configuration) |
| Severity | Low (current configuration) → High (when reused outside the contract: products systematically too small, silent data corruption) |
| Status | 【Confirmed (mechanism) / currently unreachable】; RTL not to be fixed; recommend upstream add a contract comment or elaboration assertion |
| Key evidence | 【Lean machine-checked proof】`mulPlacedSum_eq` (precise characterization of the defect term, fully proved for arbitrary inputs) + `mulCorr_window32_eq0`/`mul_sext33_corr0`/`mul_zext33_corr0` (always correct on reachable inputs) + `mulPlacedSum_quirk` (off-contract counterexample) + full len=8 exhaustion; 【inference】Python replica: all 3000 random reachable inputs correct (independent cross-check) |
| Lean model | `lean/Ventus/Arith/Multiplier.lean` (arithmetic layer + wrapper), `lean/Ventus/Arith/MultiplierCSA.lean` (circuit-layer = arithmetic-layer bridge) |
| Repro/patch | No RTL repro (unreachable in the current configuration; no corresponding entry in doc/22); no patch (the internal fix manifest classifies it as a "contract comment / assertion" level recommendation) |
| Related entries | I-15 (same module, MULHSU high-half selection omission — the only live functional bug in this module); I-2 (precedent for the same kind of "mechanism confirmed / unreachable under legal execution" verdict); upstream XiangShan has the same code and the same contract |

---

## 0. Abstract

The Booth-2 partial-product generation of ArrayMulDataModule has a
textbook-level boundary detail: negative digits (−b, −2b) are implemented by
"inversion", with the +1 repaid by the **next row's** t correction bit
(:56-60). The last row has no next row — its own `~s` sign bit lands in
column 2·len, exactly one position beyond the 2·len-bit result width, and is
discarded (:62-69); consequently, whenever the last-row window takes a
negative digit (x∈{4,5,6}), the product misses one correction term.

**But this defect is unreachable under Ventus's current configuration**: the
module is instantiated with len=33 (32-bit operands extended by one bit), and
the wrapper always extends its inputs to 33 bits (sign extension, bit32=bit31,
or zero extension, bit32=0); both forms force the last-row correction term to
be identically zero (machine proofs `mulCorr_window32_eq0` et al., three
lemmas). The module is correct only under the **implicit contract** that "len
is odd and inputs are (len−1)-bit extended values" — correct within the
contract, not a live functional bug; it becomes a landmine as soon as the
module is reused at other bit widths or in extension-free scenarios. Upstream
XiangShan has the same code and the same contract.

---

## 1. Background and mechanism

### 1.1 Booth-2 encoding primer

Radix-4 Booth recoding cuts multiplier a into a 3-bit window every 2 bits
(Multiplier.scala:46); each window decodes to a digit d∈{0,±1,±2}, and the
partial product = d·b shifted left to the window's position. In hardware, −b
is implemented as `neg_b = ~b_sext` (:49, **inversion without adding one**),
and the owed +1 is repaid by the **next row's** `t` correction bit (:56-60,
t=1/2 when the previous row's window ∈{4,5,6}) — "the 1 owed by inversion is
repaid by the next row".

### 1.2 Defect-site construct (:62-69, ★)

```scala
val (pp, weight) = i match {
  case 0 =>
    (Cat(~s, s, s, pp_temp), 0)                    // first row: ~s,s,s form the sign-correction constant
  case n if (n==len-1) || (n==len-2) =>
    (Cat(~s, pp_temp, t), i-2)                     // ★ last row: ~s lands in column 2·len
  case _ =>
    (Cat(1.U(1.W), ~s, pp_temp, t), i-2)           // middle rows: ~s is within the result width
}
```

The last row (i=len−1) has weight = len−3; `Cat(~s, pp_temp, t)` is len+4
bits wide, and `~s` lands at column (len−3)+(len+3) = **2·len** — the result
is 2·len bits, so that column is discarded wholesale. When the last-row
window takes a negative digit (x_last∈{4,5,6}), the correction term
corr(x_last)·2^(len−1) is lost.

---

## 2. Defect mechanism and unreachability argument

### 2.1 Precise characterization of the mechanism (machine-checked)

`mulPlacedSum_eq` (Multiplier.lean:1721, manual proof for arbitrary 33-bit
a b, axioms only [propext, Classical.choice, Quot.sound]):

```
Σ partial products = sext(a)·sext(b) − corr(x_last)·2^(len−1)   (mod 2^2len)
```

corr is nonzero only when the last-row window x_last∈{4,5,6} (negative
digits). Exhaustive checking over all 2^16 inputs at len=8
(`mul_dataModule8_exhaustive`, Multiplier.lean:2123, native_decide) confirms:
for the a's whose last-row window ∈{4,5,6} (3/8 of them), the circuit-layer
output always carries the correction-term deviation — **mechanism
confirmed**.

### 2.2 Contract boundary (machine-checked)

The last-row window x_last is determined by the top 3 bits of a (including
the sign-extension bit). The reachability characterization
`mulCorr_window32_eq0` (Multiplier.lean:1756, manual proof):

```
bit32 = 0  ∨  bit31 = 1  ⇒  corr = 0
```

Two corollaries pin down the current configuration:

- `mul_sext33_corr0` (:1770): a 32-bit sign-extended value (bit32=bit31) ⇒
  corr=0;
- `mul_zext33_corr0` (:1782): a 32-bit zero-extended value (bit32=0) ⇒
  corr=0.

The wrapper (ArrayMultiplier) extends 32-bit inputs to 33 bits for **every**
opcode (Multiplier.scala:178-179, one of sext or zext), so the data core's
reachable inputs always satisfy the contract ⇒
`mulPlacedSum_eq_of_corr0` (:1789)/`mulPlacedSum_eq_reachable` (:1798) give
**products fully correct on reachable inputs**. Independent cross-check: a
Python replica verified all 3000 random reachable inputs correct
【inference-layer evidence】.

### 2.3 Off-contract counterexample (machine-checked)

`mulPlacedSum_quirk` (Multiplier.lean:1805, native_decide): there exist
off-contract inputs that make the product wrong — a=0x100000000#33 (bit32=1
and bit31=0, neither a legal sign extension nor a zero extension) loses
corr·2^32.

### 2.4 Broken-window conditions

The conditions under which this defect turns from "latent" to "live" (all
require the module to be reused / re-parameterized):

1. **Other bit widths**: len changed to a value other than an odd number or
   other than 33, with inputs no longer in the (len−1)-bit extended form
   (e.g. feeding raw len-bit data without extension);
2. **Extension-free scenario**: a caller bypasses the wrapper, instantiates
   ArrayMulDataModule directly, and feeds non-extended values;
3. **Associated parameterization trap (Q2, recorded in the same file)**: the
   pipeline-alignment theorem `mulPipe_two_cycles` (:2106) relies on CSA
   converging in 4 rounds at len=33 and on the depth==4 registers at :133-136
   not being instantiated; at len≥64 the CSA needs 5 rounds, the registers
   get instantiated, and func/cVec/valid all run one cycle ahead of the
   product — same "change one parameter and it dies" family.

### 2.5 Disposition rationale

Correct within the contract + the only instantiation in the current
configuration satisfies the contract ⇒ **RTL not fixed** (the internal fix manifest
classification); recommend upstream add a contract comment or elaboration
assertion ("len is odd and inputs are (len−1)-bit extended values"). Upstream
XiangShan has the same code and the same contract — this is an inherited
implicit assumption of the lineage, not a regression introduced by Ventus.
Together with I-2 (the branch_join stack sized exactly right) it belongs to
the precedent family of "mechanism confirmed / unreachable under legal
execution" verdicts.

---

## 3. Evidence summary and conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Source reading | Line-by-line verification of Multiplier.scala:46-69 (windows/pp_temp/t/three row formats); :178-179 wrapper extension forms | Both the mechanism and the contract premise nailed down |
| Lean machine-checked proof (mechanism) | `mulPlacedSum_eq` (:1721, precise characterization of the defect term); `mul_dataModule8_exhaustive` (:2123, full len=8 exhaustion, 3/8 of inputs wrong); `mulPlacedSum_quirk` (:1805, off-contract counterexample) | Universal/exhaustive level |
| Lean machine-checked proof (unreachability) | `mulCorr_window32_eq0` (:1756) + `mul_sext33_corr0` (:1770) + `mul_zext33_corr0` (:1782) → `mulPlacedSum_eq_of_corr0` (:1789)/`mulPlacedSum_eq_reachable` (:1798) | Always correct on reachable inputs, fully proved |
| Independent cross-check | Python replica: all 3000 random reachable inputs correct (expectations derived independently of the model) | Inference/spot-check level |
| Circuit-layer bridge | `mcsaDataModule33_eq_placedSum'` (MultiplierCSA.lean:1406, axioms only the standard three) — the above characterization holds for the real circuit layer, no idealization residue | Universal/symbolic level |

**Conclusion**: the loss of the Booth last-row negation correction is a real
mechanism defect, but it is completely sealed off by the implicit contract
"len=33 + wrapper always extends"; it is unreachable in the current
configuration and not a functional bug. Classified as a robustness gap: reuse
of the module is a landmine; recommend upstream fix the contract in place
(comment + elaboration assertion). This entry is also both a by-product of
the I-15 sweep and the same-module control group — I-15 (result selection
omitting an opcode) is the module's only live functional bug, while I-20
proves the Booth core itself is correct within its contract.
