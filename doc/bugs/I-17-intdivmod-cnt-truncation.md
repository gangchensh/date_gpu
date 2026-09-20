> English translation of the Chinese master `doc/bugs/I-17-除法器计数器位宽截断.md`. Translated 2026-09-13.

# I-17 Detailed Defect Analysis Report: IntDivMod `cnt` bit-width truncation — quotients all wrong for large dividends divided by 1

| Item | Content |
|---|---|
| ID | I-17 |
| Source location | `ventus/src/pipeline/IntDivMod.scala:46` (`iter = dLez - aLez + 1.U`, 5-bit wraparound); `:56` (`cnt : UInt(log2Up(xLen).W)` = 5 bits); `:118` (`cnt := iter`) |
| Type | Functional bug (silent wrong data) — bit-width mismatch + Chisel wraparound semantics |
| Severity | **High** (the trigger cone covers the entire upper half of the unsigned domain divided by 1, and signed INT_MIN÷1; both quotient and remainder are wrong, with no trap/assertion) |
| Confirmation status | 【Confirmed】, Lean machine-checked proof + ChiselSim/Verilator dual-channel reproduction + fix patch-tree regression green |
| Primary evidence | 【Lean machine-checked proof】native_decide witnesses `div_test_32_bug1_*` + xLen=4/8 trigger-cone enumeration + wrapper-level pass-through witnesses; 【simulation runs】reproduced at both ChiselSim module level and Verilator whole-machine level; 【direct source reading】three locations checked line by line |
| Lean model | `lean/Ventus/Arith/IntDivMod.lean` (original model), `lean/Ventus/Arith/IntDivModFixed.lean` (fixed version), `lean/Ventus/Arith/ExeSFU.lean` (wrapper-level pass-through) |
| Reproduction / patch | `repro/IntDivModBugRepro.scala` (ChiselSim); `repro/verilator/` kernel `i17_divu_cnt_trunc`; patch `i17-intdivmod-cnt-width.patch` (internal fix manifest; not released) (v2, dual widening of cnt+iter) |
| Related entries | I-19 (stale zeroQReg in the same module), I-18/II-1 (mistranslation withdrawal in the same module, doc/23/24; its adjudication process exposed the ineffectiveness of the I-17 v1 patch, see §7), doc/25 (library-wide width-assumption sweep) |

---

## 0. Abstract

Ventus's integer divider IntDivMod (a 32-bit non-restoring divider
implementing the four instructions DIV/DIVU/REM/REMU) normalizes by leading
zeros and then iterates bit by bit; the iteration count
`iter = dLez − aLez + 1` is loaded into the counter `cnt` and decremented
cycle by cycle. `cnt` has only `log2Up(32) = 5` bits (IntDivMod.scala:56),
while at the corner where "the dividend's MSB is set (|a| ≥ 2³¹) and
|d| = 1", iter reaches **32** — exactly the wraparound point of a 5-bit
unsigned number — and after being loaded into cnt it becomes **0**, so the
divider iterates only once (instead of 32 times) before entering the recovery
state.

Consequence: for unsigned `a ∈ [0x80000000, 0xFFFFFFFF], d = 1` the quotient
output is 1 (it should be a itself) and the remainder output is 0; for signed
INT_MIN÷1 the quotient output is 0xFFFFFFFF (it should be 0x80000000).
Inside the trigger cone, q and r are **both wrong and silent** — no trap, no
assertion.

The evidence chain is fully closed: Lean model native_decide witness (the
model predicts hardware output (1,0)) → ChiselSim module-level measurement
(1,0) → Verilator whole-machine measurement quotient = 0x00000001 — three
layers of numerically identical results. The fix patch (v2, dual widening of
cnt+iter) turned green 4/4 in the patch-tree ChiselSim regression. **Fix
lesson** (doc/23 §7): Chisel 6's `+`/`-` have wraparound semantics — the
`dLez - aLez + 1.U` at :46 itself wraps around to 0 within 5 bits — widening
only cnt is not enough, since what gets loaded is still 0; the cnt and iter
arithmetic must **both be widened**.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **Non-restoring division**: a hardware division algorithm. Take absolute
  values of dividend and divisor and left-shift-normalize them (leading-zero
  counts are aLez and dLez respectively), then perform
  `iter = dLez − aLez + 1` rounds of "shift — add/subtract — record quotient
  bit" iteration, and finally restore the quotient and remainder according to
  the signs. The number of iterations equals "the number of bits the quotient
  may occupy": the larger the dividend and the smaller the divisor, the more
  rounds.
- **Leading-zero count (PriorityEncoder on reversed bits)**: count how many
  0s precede the most significant 1 of a binary number. For a 32-bit number
  the range is 0–31, needing 5 bits; but iter = difference + 1 **can reach
  32**, needing 6 bits — this is the entire arithmetic root of this bug.
- **SFU wrapper**: in Ventus's default configuration, 32 lanes share only
  num_sfu = 8 dividers (instantiated at execution.scala:846); the 32 lanes
  are split into 4 groups scheduled group by group by SFUexe. This bug is
  inside the divider core; the wrapper layer only transports (pass-through,
  see §3.3).
- **RISC-V spec**: DIVU(a, 1) = a; REMU(a, 1) = 0. These are self-evident
  expected values and the judgment basis for the witnesses.

### 1.2 Design intent

Five-state FSM: s_idle (accept input, register it) → s_pre (compute
aLez/dLez/iter, normalize, load cnt; when |a|<|d| go directly to s_finish
with output (0, a)) → s_compute (cnt decrements by 1 each cycle, iterating
iter rounds) → s_recovery (remainder recovery) → s_finish (output (q, r),
wait for out.fire to return to idle). Two special cases, divByZero and signed
overflow (INT_MIN÷−1), go directly from s_idle to s_finish.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: computation of iter** (`IntDivMod.scala:44-46`, ★ defect point one):

```scala
val aLez = PriorityEncoder(unsignedAReg.asBools.reverse)   // :44, 5 bits
val dLez = PriorityEncoder(unsignedDReg.asBools.reverse)   // :45, 5 bits
val iter = Mux(aLez > dLez, 0.U, dLez - aLez + 1.U)        // :46 ★
```

aLez/dLez are both 5 bits. Chisel 5/6's `-`/`+` are **wraparound operations**
(`do_+ = do_+%`, result width = max(operand widths); doc/23 §7 verified the
6.4.0 source Bits.scala:479-480,542-551) — `dLez - aLez + 1.U` is computed
entirely **within 5 bits**, and at the corner (aLez=0, dLez=31) iter =
32 mod 32 = **0**.

**Construct 2: cnt's bit width** (`IntDivMod.scala:56`, ★ defect point two):

```scala
val cnt = RegInit(0.U(log2Up(xLen).W))   // :56 ★ xLen=32 → 5 bits
val cnt_next = Mux(cnt===0.U, 0.U, cnt - 1.U)
```

A 5-bit counter's range is 0–31; it cannot represent 32.

**Construct 3: loading in the pre state** (`IntDivMod.scala:112-121`):

```scala
is(s_pre){
  when(unsignedAReg < unsignedDReg){
    cnt := 0.U
  }.otherwise{
    aReg := aNorm
    dReg := dNorm
    cnt := iter                            // :118 ★ wide→narrow load (the bit-loss point is at :46, see §3.2)
    Q := 0.U
    QN := 0.U
  }
}
```

Note that when `|a| ≥ 2³¹`, aLez=0 means "MSB set", not "|a| is very small" —
|a| ≥ |d| = 1 always holds, so the **zeroQ branch (|a|<|d|) does not
intercept**, and transactions in the trigger cone enter s_compute as usual.

**Construct 4: iteration termination** (`IntDivMod.scala:96-99`):

```scala
is(s_compute){
  when(cnt_next =/= 0.U){ state := s_compute
  }.otherwise{ state := s_recovery }       // when cnt=1, cnt_next=0, only 1 round is done
}
```

cnt loaded with 0 ⇒ `cnt_next = 0` ⇒ one cycle after entering s_compute it
switches to s_recovery, doing only **1** iteration in total (should be 32).
After 1 iteration Q=1, QN=0, remIsNeg=false, so q = qSign ? all-ones : 1,
r = 0.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

**Trigger cone** (formally characterized by `divCorner` on the Lean side,
IntDivMod.lean:392-396):

```
d ≠ 0 and |d| = 1 and msb(|a|) = 1 and not the overflow special case
```

i.e., unsigned `a ∈ [0x80000000, 0xFFFFFFFF], d = 1` (2³¹ combinations);
signed INT_MIN ÷ 1.

**Wrong outputs** (`divCornerBuggyQ`, IntDivMod.lean:399-400): after only 1
iteration, Q=1, QN=0, remIsNeg=false ⇒ q = sign bit ? all-ones : 1, r = 0.
Concretely:

| Input | Hardware output (q, r) | RISC-V spec (q, r) |
|---|---|---|
| 0x80000000 / 1 (u) | (1, 0) | (0x80000000, 0) |
| 0xFFFFFFFF / 1 (u) | (1, 0) | (0xFFFFFFFF, 0) |
| INT_MIN / 1 (s) | (0xFFFFFFFF, 0) | (0x80000000, 0) |

For xLen=4 the trigger cone has 9 combinations, for xLen=8 it has 129
(`div_test_xlen4_corners` / `div_test_xlen8_corners`, pinned down one by one
by native_decide); outside the trigger cone, q and r are both constantly
equal to the spec (`div_test_xlen4/8_exhaustive` full-input enumeration) —
**the bug boundary is completely pinned down by exhaustive evidence**.

### 3.2 Root cause

A superposition of a bit-width bookkeeping error and Chisel wraparound
semantics:

- **Design level**: `log2Up(xLen)` can represent 0–31, but iter's range is
  0–**32** (maximum difference 31, plus 1). At `:56`, "the width of the
  leading-zero count" was directly reused as "the width of the iteration
  count", one bit short.
- **Semantics level (the precision correction of doc/23 §4/§7)**: under
  Chisel 6, the bit-loss point is actually **at :46 itself** —
  `dLez - aLez + 1.U` wraps around within 5 bits, so iter is 0 to begin with;
  `:118 cnt := iter` is a same-width load, not a truncation. The Lean model
  originally narrated it as "6-bit iter → 5-bit cnt truncation"; the two are
  numerically identical ((x+1) mod 64 mod 32 = (x+1) mod 32), the observable
  behavior is the same, and the existence conclusion of I-17 is unaffected;
  but this precision correction directly determines **the correct form of the
  fix** (see §7).
- An initial review conjectured "iter=32 must be accompanied by |a|<|d| and
  thus intercepted by zeroQ" — **does not hold**: aLez=0 means MSB set
  (|a| ≥ 2³¹), |a| ≥ |d| always holds, zeroQ does not intercept.

### 3.3 Harm and tolerability

- **Harm**: the DIV(U)/REM(U) instructions of the num_sfu=8 instances at
  execution.scala:846 silently produce wrong results on the trigger cone,
  with both q and r wrong. `x/1` is an utterly ordinary operation that both
  compilers and handwritten code may produce — any large unsigned number
  (≥2³¹, e.g. large array lengths, addresses, counters) divided by 1 is hit.
  No trap, no assertion; the host side observes wrong computation results.
- **Wrapper-level pass-through**: ExeSFU's `exs_test_bug1_lane3` /
  `exs_test_bug1_ne_spec` (native_decide witnesses) prove that lane 3's wrong
  value 1 for 0x80000000/1 **passes through the SFUexe wrapper unchanged to
  the write-back port** — the bug is not masked by the wrapper layer.
- **Tolerability**: the existing official test kernels do not hit this cone
  (no "large number ÷ 1" pattern) — "the mine was not stepped on", not
  "there is no mine". The trigger condition requires no special timing; a
  single transaction suffices — **High**.

---

## 4. Lean formal evidence

Model `lean/Ventus/Arith/IntDivMod.lean` (803 lines, zero sorry; line numbers
checked one by one at the time of writing this report):

**Trigger cone and wrong-value characterization**:

- `divCorner` (:392): Boolean characterization of the trigger cone (d≠0 ∧
  |d|=1 ∧ msb(|a|) ∧ not overflow);
- `divCornerBuggyQ` (:399): predicted wrong output on the trigger cone (after
  1 iteration Q=1, QN=0, remIsNeg=false ⇒ q = sign bit ? all-ones : 1).

**Exhaustive evidence** (native_decide):

- `div_test_xlen4_exhaustive` (:487) / `div_test_xlen8_exhaustive` (:493):
  all 512 combinations for xLen=4 and all 131072 combinations for xLen=8
  verified one by one — **outside the trigger cone, q and r are both
  constantly equal to the RISC-V spec; on the trigger cone they are exactly
  the `divCornerBuggyQ` wrong values and ≠ spec**;
- `div_test_xlen4_corners` (:490) / `div_test_xlen8_corners` (:496): trigger
  cone sizes 9 / 129.

**32-bit targeted witnesses** (native_decide, :544-553):

- `div_test_32_bug1_unsigned`: `divExec 0x80000000 1 false = (1, 0)`;
- `div_test_32_bug1_unsigned_max`: `0xFFFFFFFF/1 (u) → (1, 0)`;
- `div_test_32_bug1_signed`: `INT_MIN/1 (s) → (0xFFFFFFFF, 0)`;
- `div_test_32_bug1_ne_spec`: indeed differs from the spec (bug
  substantiated).

**Wrapper-level pass-through** (`lean/Ventus/Arith/ExeSFU.lean`):
`exs_test_bug1_lane3` (lane 3's 0x80000000/1 writes back 1),
`exs_test_bug1_ne_spec`.

**Corroboration (termination is unaffected by the bug)**: `div_terminates`
(:723) — the original with this bug still halts within at most 2^divW+4
cycles (truncation only makes cnt smaller), i.e. this bug is a pure numerical
error, not a livelock.

Axiom audit: native_decide theorems carry the `Lean.ofReduceBool` family of
trust axioms (archived per AGENTS.md; see the `#print axioms` block at
:780-790 at the end of the file).

---

## 5. Simulation verification (dual-channel real runs + patch-tree regression)

**ChiselSim module level** (`repro/IntDivModBugRepro.scala` I-17 case,
actually run 2026-09-06/07, doc/22 ChiselSim channel): `txn(c, 0x80000000,
1, false)` measured = **(1, 0)**, value-for-value identical to the Lean
witness prediction (should be (0x80000000, 0)). Verdict: **reproduction
succeeded**.

**Verilator whole-machine level** (`repro/verilator/` kernel
`i17_divu_cnt_trunc`, actually run 2026-09-07, doc/22 Verilator channel): in
the whole-machine environment, executing `divu 0x80000000/1` gives measured
quotient = **0x00000001** (correct value 0x80000000). Verdict:
**reproduction succeeded** (one of 8 reproductions among the 9 target bugs).

**Patch-tree regression** (35-patch tree 2026-09-07 and 38-patch merged tree
2026-09-10, two rounds of real runs, doc/22): `pipeline.IntDivModBugRepro`
**4/4 green** — the I-17/I-19 cases turn green after the fix, and I-18/I-18b
(turned into spec-correctness regressions after the withdrawal) stay
consistent. The patch file header self-reports the measurement:
divu 0x80000000/1 → (0x80000000, 0), and non-trigger cases are unchanged in
behavior.

---

## 6. Upstream impact analysis

- **Trigger surface**: all DIVU/REMU inputs with `d=1 ∧ a≥2³¹`, plus
  DIV/REM's INT_MIN÷1. Decode path: DecodeUnit → issue → the IntDivMod
  instances at execution.scala:846, with no downstream compensation point.
- **Why upstream did not find it**: the division cases in conventional tests
  are mostly small integers; the combination of `x/1` with x's high bit set
  is a low-probability input in functional testing. A single-transaction
  directed test exposes it — a "test coverage blind spot".
- **Relationship with this project's sibling entries**: I-19 is another
  independent bug in the same module (stale zeroQReg); I-18 once reported
  "remainder recovery truncates before adding", which was falsified by
  dual-channel reproduction and adjudicated as a Type II model
  mistranslation (doc/23/24) — its adjudication process in turn corrected
  I-17's localization of the bit-loss point (wraparound at :46 rather than
  truncation at :118) and exposed the v1 patch as ineffective (§7).
  Additionally: doc/25's library-wide width-assumption sweep targets
  translation-side (Type II) widening assumptions, concluding clean except
  for I-18/II-1 — I-17 is an RTL-side (Type I) bit-width defect, outside the
  scope of that sweep; its fix lesson (dual widening under wraparound
  semantics) has been written into the AGENTS.md pitfall appendix along with
  doc/23 §7.

---

## 7. Fix plan and fix verification

**Fix lesson (doc/23 §7, must be delivered upstream together with the
patch)**: the first fix version (v1, 2026-08-31) only widened cnt from 5 bits
to 6 bits — **ineffective under Chisel 6**: the `dLez - aLez + 1.U` at :46
wraps around to 0 within 5 bits, and zero-extending that into a 6-bit cnt is
still 0. The correct fix must **widen both cnt and the iter arithmetic**.

**Patch** (`i17-intdivmod-cnt-width.patch` (internal fix manifest; not released), v2,
2026-09-07, two edit points):

1. `IntDivMod.scala:46`: `dLez - aLez + 1.U` → `(dLez -& aLez) + 1.U` — the
   `-&` widening subtraction expresses the difference in 6 bits (diff ≤ 31,
   no wraparound), then +1 (6-bit wraparound add, ≤ 32 < 64, no wraparound),
   making iter 6 bits;
2. `IntDivMod.scala:56`: widen `cnt` to `(log2Up(xLen)+1).W` = 6 bits —
   `:118 cnt := iter` becomes a same-width load with no truncation.

**Fix verification trio**:

- Effectiveness: the Lean fixed version (`lean/Ventus/Arith/IntDivModFixed.lean`,
  `DvfState`'s cnt widened by 1 bit + `dvfStep`'s pre branch loads the full
  `divIter`) — `dvfT_i17_unsigned` / `dvfT_i17_unsigned_max` /
  `dvfT_i17_signed` (the original witnesses all turn green and are exactly
  the correct values), `dvfT_i17_eq_spec` (exactly the RISC-V spec values),
  `dvf_pre_cnt_full` (symbolic for arbitrary xLen: the pre cycle loads the
  full iter, no longer truncated), `dvf_terminates` (fixed-version
  termination); ChiselSim patch-tree regression 4/4 green (§5);
- General correctness: `dvf_test_xlen4_exhaustive` /
  `dvf_test_xlen8_exhaustive` — the fixed version's full-input enumeration
  for xLen=4/8 **matches the RISC-V spec point by point** and always halts;
- Regression safety: `dvf_exec_eq_orig_of_safe` (symbolic for arbitrary xLen:
  on the original trajectory, if the three bug conditions are not triggered
  at any cycle, the two versions' outputs are completely identical, via the
  `dvf_step_match` / `dvf_run_match` induction chain) +
  `dvf_test_regr_xlen4/8` full-input numerical regression +
  `dvf_test_regr_full_xlen4/8` (strengthened regression after the I-18
  withdrawal: point-by-point identical over all inputs except the I-17
  trigger cone).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | IntDivMod.scala:46 / :56 / :118 checked line by line; Chisel 6 wraparound semantics verified (Bits.scala:479-480,542-551, doc/23) | Three source locations consistent |
| Lean machine-checked proof | `div_test_32_bug1_unsigned`/`_max`/`_signed`/`_ne_spec` witnesses; `div_test_xlen4/8_exhaustive` enumeration pins down the trigger-cone boundary; `exs_test_bug1_lane3` wrapper pass-through | Numerical witnesses + enumeration + symbolic level |
| ChiselSim reproduction | 0x80000000/1(u) measured (1,0), value-for-value identical to the model prediction | Actually run |
| Verilator whole-machine reproduction | divu 0x80000000/1 quotient = 0x00000001 | Actually run |
| Fix verification | i17 v2 patch (dual widening, 2 edit points); Lean fixed-version effectiveness/enumeration/regression trio + patch-tree regression 4/4 green | Actually run + machine-checked proof |

I-17 is a textbook case of the "bit-width bookkeeping error" defect family: a
`log2Up(xLen)` off-by-one bit width, superposed with Chisel wraparound
semantics, silently breaks division for a full 2³¹ input combinations. Its
evidence chain (machine-checked witness → dual-channel RTL reproduction with
value-for-value agreement → dual-widening fix + regression) is fully closed;
and the lesson learned during fixing — "the v1 patch was ineffective"
(doc/23 §7) — also became one of the sources of this project's "Chisel
wraparound semantics" pitfall entry.
