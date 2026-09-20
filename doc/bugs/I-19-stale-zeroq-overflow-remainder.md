> English translation of the Chinese master `doc/bugs/I-19-陈旧zeroQ污染溢出余数.md`. Translated 2026-09-13.

# I-19 Detailed Defect Analysis Report: IntDivMod stale zeroQReg pollutes the remainder of overflow transactions

| Item | Content |
|---|---|
| ID | I-19 |
| Source location | `ventus/src/pipeline/IntDivMod.scala:54` (`zeroQReg = RegEnable(unsignedAReg < unsignedDReg, state===s_pre)`, no reset, updated only in s_pre); `:77` (`specialR = Mux(divByZeroReg||zeroQReg, rawAReg, 0.U)`); linkage point `:88-89` (overflow/divByZero go directly to s_finish without passing through s_pre) |
| Type | Functional bug (silent wrong data) — cross-transaction state residue (stale register) |
| Severity | **Medium** (conditional wrong data: affects only the remainder of an overflow/divByZero transaction immediately following a zeroQ transaction; q is unaffected; cross-transaction timing dependency, undetectable by single-transaction tests) |
| Confirmation status | 【Confirmed】, Lean machine-checked proof + ChiselSim/Verilator dual-channel reproduction + fix patch-tree regression green |
| Primary evidence | 【Lean machine-checked proof】symbolic-level theorem `div_t1_overflow` (r precisely characterized as `if s.zeroQ then a else 0`) + native_decide two-transaction witness `div_test_stale_zeroQ_bug2`; 【simulation runs】reproduced at both ChiselSim module level and Verilator whole-machine level; 【direct source reading】three locations checked line by line |
| Lean model | `lean/Ventus/Arith/IntDivMod.lean` (original model), `lean/Ventus/Arith/IntDivModFixed.lean` (fixed version) |
| Reproduction / patch | `repro/IntDivModBugRepro.scala` (ChiselSim); `repro/verilator/` kernel `i19_rem_stale_zeroq`; patch `i19-intdivmod-zeroq.patch` (internal fix manifest; not released) |
| Related entries | I-17 (cnt bit-width truncation in the same module), I-18/II-1 (mistranslation withdrawal in the same module, doc/23/24); the SFU wrapper "cleansing" effect (doc/03 review note, execution.scala SFU/FPU side) |

---

## 0. Abstract

IntDivMod uses the `zeroQReg` register to record "|dividend| < |divisor|"
(zeroQ, the special case where the quotient is 0), for the finish state to
select the special output. This register is a `RegEnable` — **no reset**,
**updated only in the s_pre state** (IntDivMod.scala:54). The two special
cases overflow (signed INT_MIN÷−1) and divByZero, however, go **directly from
s_idle to s_finish** (:88-89), never passing through s_pre — so the
`specialR` (:77) consumed in the finish state is the **stale zeroQ value left
by the previous transaction**.

Trigger sequence: a previous transaction with |a|<|d| (zeroQ=1, e.g. 3/5),
immediately followed by an INT_MIN ÷ (−1) (overflow) transaction ⇒ the
remainder output is `rawAReg` = 0x80000000, whereas RISC-V specifies r = **0**
on overflow. The quotient is unaffected (specialQ only consults
divByZeroReg/overflowReg). This is a cross-transaction timing-dependent bug —
no single-transaction test can detect it.

The evidence chain is fully closed: the Lean symbolic-level theorem
`div_t1_overflow` precisely characterizes the remainder as `if s.zeroQ then a
else 0` (one theorem pins down both the "present" and "absent" faces of the
bug) → native_decide two-transaction witness → ChiselSim measured
r=0x80000000 → Verilator whole-machine measured remainder 0x80000000 — three
layers of numerically identical results. The fix patch (clear zeroQReg on the
s_idle cycle) turned green in the patch-tree regression.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **IntDivMod module**: Ventus's 32-bit non-restoring integer divider,
  implementing RISC-V's four instructions DIV/DIVU/REM/REMU (for the full
  module picture see `doc/bugs/I-17-除法器计数器位宽截断.md` §1, not repeated
  here).
- **Special cases**: the divider short-circuits three classes of input
  without iterating: |a|<|d| (zeroQ, output (0, a)); d=0 (divByZero, RISC-V
  specifies output q=all-ones, r=a); signed INT_MIN÷−1 (overflow, RISC-V
  specifies output q=INT_MIN, r=0). All three share the finish state's
  `specialQ`/`specialR` output selection logic.
- **RegEnable and stale values**: `RegEnable(x, en)` is a "register with
  enable" — it updates only when en is true and **holds its old value** on
  all other cycles; without a reset (RegInit), its power-on initial value is
  undefined. It holds the value from "the most recent enabled cycle" and
  naturally carries cross-transaction residue risk.
- **Cross-transaction bugs**: each individual transaction is completely
  correct internally; the error appears only under specific transaction
  **sequences**. Such bugs are structurally undetectable by
  single-transaction directed tests — a classic blind spot of simulation
  coverage.

### 1.2 Design intent

The designer's intent was clearly: the zeroQ determination (|a|<|d|) is done
in the s_pre state and stored into zeroQReg, and the finish state reads the
register directly to assemble the output. The implicit premise is that
"**every transaction that consumes zeroQReg necessarily passes through
s_pre**" — the direct path of overflow/divByZero (:88-89) breaks this
premise, and the code has no compensation.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: definition of zeroQReg** (`IntDivMod.scala:54`, ★ defect point):

```scala
val zeroQReg = RegEnable(unsignedAReg < unsignedDReg, state===s_pre)  // :54 ★
```

No reset (RegEnable rather than RegInit), updated only when
`state===s_pre`. Contrast: the same file's `aReg/dReg/cnt` etc. are
explicitly cleared in s_idle (:107-110); zeroQReg **is not**.

**Construct 2: the direct path bypasses s_pre** (`IntDivMod.scala:86-91`):

```scala
is(s_idle){
  when(io.in.fire){
    when(overflow || divByZero){ state := s_finish      // :88-89 ★ direct path
    }.otherwise{ state := s_pre }
  }
}
```

Overflow/divByZero transactions jump directly from s_idle to s_finish, and
zeroQReg keeps the value written **by the previous transaction** on its s_pre
cycle.

**Construct 3: specialR consumes the stale value** (`IntDivMod.scala:75-80`):

```scala
val specialQ = Mux(divByZeroReg, (-1).S(xLen.W).asUInt,
                 Mux(overflowReg, Cat(1.U(1.W), 0.U((xLen-1).W)), 0.U(xLen.W)))
val specialR = Mux(divByZeroReg||zeroQReg, rawAReg, 0.U(xLen.W))   // :77 ★

io.out.bits.q := Mux(divByZeroReg||zeroQReg||overflowReg, specialQ, signedQ)  // :79
io.out.bits.r := Mux(divByZeroReg||zeroQReg||overflowReg, specialR, signedR)  // :80
```

Note the asymmetry between the two outputs' conditions: **q only consults
divByZeroReg/overflowReg** (this-transaction registers, registered at the
accept cycle by :41-42, no staleness issue), **while r additionally consults
zeroQReg** — staleness seeps into the remainder path from here. The correct
output of an overflow transaction should be (q=INT_MIN, r=0); a stale
zeroQReg=1 rewrites r to rawAReg = 0x80000000.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

**Trigger conditions** (both must hold simultaneously; cross-transaction
timing dependency):

1. The previous transaction satisfies |a|<|d| (setting zeroQReg to 1 on its
   s_pre cycle);
2. It is immediately followed by an overflow (signed INT_MIN÷−1) or divByZero
   transaction (going directly to s_finish, so zeroQReg is not refreshed).

**Wrong output**: the overflow transaction's remainder r = rawAReg (the
original dividend value, e.g. 0x80000000), whereas RISC-V specifies r = 0.
The divByZero spec is r = a to begin with, so r=rawA happens to be the
correct value there — **the bug is observable only on overflow
transactions**.

**Concrete witness** (3/5 first, then INT_MIN/−1, signed):

| Transaction | Hardware output (q, r) | RISC-V spec (q, r) |
|---|---|---|
| txn1: 3/5 (u) | (0, 3) correct | (0, 3) |
| txn2: INT_MIN/−1 (s) | (0x80000000, **0x80000000**) | (0x80000000, **0**) |

q is unaffected (0x80000000 = INT_MIN, correct); only r is wrong.

### 3.2 Root cause

A **broken premise** at the design level: the finish-state output logic
assumes zeroQReg is always "this transaction's zeroQ", but the
overflow/divByZero direct path bypasses s_pre, the only update point. The
three constructs are each locally self-consistent (RegEnable faithfully
holds, the direct path faithfully short-circuits, specialR faithfully looks
up), and the error exists only in the **cross-transaction state
lifecycle** — the same "locally self-consistent, broken in composition"
family as I-12, except that here "inter-module" becomes "inter-transaction".

Incidental note: zeroQReg has no reset; if the very first transaction after
power-on is an overflow, it consumes an undefined initial value — the Lean
model's `divInit` takes all zeros (the file header of IntDivMod.lean, D6,
notes the practical impact of this choice), and ChiselSim without
randomization is likewise 0, so the first transaction does not expose it.

### 3.3 Harm and tolerability

- **Harm**: the REM instruction outputs a wrong remainder (0x80000000
  instead of 0) after specific instruction sequences. Signed INT_MIN÷(−1) is
  low-frequency in software but not nonexistent (e.g. boundary handling of
  negating INT_MIN, `abs` implementations, hash/checksum code).
- **Impact-scope correction (the SFU wrapper "cleansing" effect, doc/03
  review note)**: under the SFUexe wrapper, masked-off slots run dummy 1/1
  transactions (|a|=|d|=1, not zeroQ), which flush zeroQReg back to false —
  so wrapper-level reachability requires **two consecutive real transactions
  on the same divider slot with no dummy in between**. The Verilator
  whole-machine kernel `i19_rem_stale_zeroq` is exactly such a sequence, and
  the reproduction succeeded (§5) — the cleansing effect does not change the
  reachability conclusion of this bug on the real whole machine; it only
  narrows the trigger surface.
- **Tolerability**: q is unaffected; single-transaction tests structurally
  cannot detect it; triggering requires specific transaction adjacency.
  Rating: **Medium** (conditional wrong data).

---

## 4. Lean formal evidence

Model `lean/Ventus/Arith/IntDivMod.lean` (803 lines, zero sorry; line numbers
checked one by one at the time of writing this report):

**Symbolic-level precise characterization** (:584-610, arbitrary xLen,
arbitrary state, proved by simp unfolding):

```lean
theorem div_t1_overflow {xLen : Nat} (s : DivState xLen) (i : DivInputs xLen)
    (h : s.phase = .idle) (hv : i.in_valid = true)
    (hovf : divOvfDet i.a i.d i.signed = true) (hndz : i.d ≠ 0) :
    (divStep s i).phase = .finish ∧
    divOutQ (divStep s i) = divIntMin xLen ∧
    divOutR (divStep s i) = (if s.zeroQ then i.a else 0)
```

One theorem pins down both faces of the bug simultaneously: remainder =
`if s.zeroQ then i.a else 0` — zeroQ is a **stale field in the state**, not
the current transaction's fact. Two corollaries pin down the "no-bug face"
and the "bug face" respectively:

- `div_t1_overflow_r_zero` (:595): when zeroQ=0, the overflow remainder = 0,
  conforming to RISC-V;
- `div_t1_overflow_r_stale` (:604): when zeroQ=1, the remainder = rawA,
  violating the spec.

**Two-transaction witness** (native_decide, :556-564):

```lean
def divBug2Seq : DivState 32 :=
  let s1 := divExecState (3 : BitVec 32) 5 false            -- txn1: zeroQ transaction, zeroQReg←1
  let s2 := divStep s1 (divNop 32)                          -- out.fire → s_idle
  divRunTo (divStep s2 ⟨true, 0x80000000, 0xFFFFFFFF, true, true⟩) (divNop 32) 72  -- txn2: INT_MIN ÷ -1

theorem div_test_stale_zeroQ_bug2 :     -- q correct (INT_MIN), r wrong (rawA, should be 0)
    divOutQ divBug2Seq = 0x80000000#32 ∧ divOutR divBug2Seq = 0x80000000#32
theorem div_test_stale_zeroQ_ne_spec :  -- indeed differs from the spec (bug substantiated)
    divOutR divBug2Seq ≠ divSpecR (0x80000000 : BitVec 32) 0xFFFFFFFF true
```

**Control**: `div_test_32_overflow_fresh` (:506) — when zeroQ is clean,
INT_MIN÷−1's output conforms to RISC-V, proving the stale value is a
necessary condition.

Axiom audit: native_decide theorems carry the `Lean.ofReduceBool` family of
trust axioms (archived per AGENTS.md; see the `#print axioms` block at
:780-790 at the end of the file; both `div_t1_overflow` and
`div_test_stale_zeroQ_bug2` are in the audit list).

---

## 5. Simulation verification (dual-channel real runs + patch-tree regression)

**ChiselSim module level** (`repro/IntDivModBugRepro.scala` I-19 case,
actually run 2026-09-06/07, doc/22 ChiselSim channel): first `txn(c, 3, 5,
false)` (zeroQReg←1), then `txn(c, 0x80000000, 0xFFFFFFFF, true)`; measured
remainder r = **0x80000000** (should be 0) — value-for-value identical to the
Lean witness prediction. Verdict: **reproduction succeeded**.

**A Type III interlude in the test itself** (on record in doc/22, worth
noting as a methodology note): the first run once produced a false witness
r=3 — the original `txn()` neither waited for `in.ready` nor consumed the
response, so the second input of the back-to-back transactions was never
accepted, and the r=3 read was **the stale output of the first transaction**,
not the I-19 mechanism. Only after fixing the testbench handshake (waiting
for in.ready, consuming out.fire) was the predicted value 0x80000000
reproduced precisely. This interlude itself demonstrates that "tests for
cross-transaction bugs must be orchestrated strictly by handshake semantics".

**Verilator whole-machine level** (`repro/verilator/` kernel
`i19_rem_stale_zeroq`, actually run 2026-09-07, doc/22 Verilator channel):
rem 3/5 gives 3 (correct, sets zeroQReg); then INT_MIN % −1 gives measured
remainder = **0x80000000** (w4) and quotient 0x80000000 (w8, correct) — the
stale zeroQReg holds on the real RTL whole machine. Verdict: **reproduction
succeeded** (one of 8 reproductions among the 9 target bugs).

**Patch-tree regression** (35-patch tree 2026-09-07 and 38-patch merged tree
2026-09-10, two rounds of real runs, doc/22): `pipeline.IntDivModBugRepro`
**4/4 green** — the I-19 case turns green after the fix.

---

## 6. Upstream impact analysis

- **Trigger surface**: the REM instructions of the num_sfu=8 IntDivMod
  instances at execution.scala:846; triggering requires the transaction
  adjacency "a zeroQ transaction immediately followed by an overflow
  transaction" (under the SFU wrapper it additionally requires no dummy
  cleansing on the same slot in between, see §3.3). No downstream
  compensation point.
- **Why upstream did not find it**: single-transaction tests structurally
  cannot detect it; the probability of a random test hitting "a 3/5-type
  transaction adjacent to an INT_MIN/−1-type transaction" is extremely low.
  A "cross-transaction coverage blind spot".
- **Relationship with sibling entries**: I-17 (same module, triggerable by a
  single transaction) has an evidence chain completely independent of this
  entry (doc/23 §4 adjudication: I-19's evidence chain `div_t1_overflow`/
  `divSpecialR`/`divBug2Seq` does not pass through the recovery path, so the
  I-18 withdrawal does not affect this entry's conclusions).
- **Design lesson**: the finish state's shared output selection logic
  references registers with inconsistent lifecycles (divByZeroReg/overflowReg
  are registered on the accept cycle, zeroQReg on the s_pre cycle) — mixing
  signals from two time domains in the three special cases' output conditions
  is a root-level coding-style problem.

---

## 7. Fix plan and fix verification

doc/03 originally listed three candidates: change specialR to use the
same-cycle combinational zeroQ (the current transaction's fact
`unsignedAReg < unsignedDReg`); or explicitly give 0 on the overflow path; or
clear zeroQReg on the s_idle cycle. **The third was actually adopted**
(minimal change, output logic untouched).

**Patch** (`i19-intdivmod-zeroq.patch` (internal fix manifest; not released), one edit
point):

```scala
is(s_idle){
  aReg := 0.U
  dReg := 0.U
  cnt := 0.U
  zeroQReg := false.B  // I-19 fix: clear stale zeroQ
}
```

After clearing on the s_idle cycle, whenever any transaction enters s_finish,
zeroQReg is either the current transaction's fact written on its s_pre cycle
(normal transactions) or stays false (direct-path transactions) — the
`zeroQReg` branch of specialR never misleads for direct-path transactions.

**Fix verification trio**:

- Effectiveness: the Lean fixed version
  (`lean/Ventus/Arith/IntDivModFixed.lean`, `dvfStep`'s idle branch adds
  `zeroQ := false`) — `dvfT_i19_fixed` (the two-transaction sequence witness
  turns green: q=INT_MIN and r=0, conforming to RISC-V overflow semantics),
  `dvfT_i19_eq_spec` (exactly the spec values), `dvf_t1_overflow` (symbolic
  level: the fixed version's overflow remainder is **r = 0 unconditionally**
  — contrast with the original `div_t1_overflow`'s `if s.zeroQ then i.a else
  0`); ChiselSim patch-tree regression 4/4 green (§5);
- General correctness: `dvf_test_xlen4_exhaustive` /
  `dvf_test_xlen8_exhaustive` — the fixed version's full-input enumeration
  for xLen=4/8 matches the RISC-V spec point by point (single-transaction
  domain; the cross-transaction surface is covered by the two-transaction
  witness and the symbolic theorem above);
- Regression safety: `dvf_exec_eq_orig_of_safe` (symbolic for arbitrary xLen:
  if every cycle of the original trajectory satisfies the safe-step condition
  — including "no stale zeroQ" — the two versions' outputs are completely
  identical) + `dvfT_regr_multitxn` (multi-transaction numerical regression:
  when the previous transaction is not zeroQ, an immediately following
  overflow is identical between the two versions).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | IntDivMod.scala:54 / :77 / :88-89 checked line by line; the time-domain asymmetry between the :41-42 accept-cycle registering and the :54 s_pre registering | Source file consistent |
| Lean machine-checked proof | `div_t1_overflow` (+`_r_zero`/`_r_stale`) symbolic-level characterization; `div_test_stale_zeroQ_bug2`/`_ne_spec` two-transaction witnesses; `div_test_32_overflow_fresh` control | Symbolic level + numerical witnesses |
| ChiselSim reproduction | 3/5 followed by INT_MIN/−1(s), measured r=0x80000000, value-for-value identical to the model prediction | Actually run |
| Verilator whole-machine reproduction | Same sequence on the whole machine: measured remainder 0x80000000, quotient 0x80000000 | Actually run |
| Fix verification | i19 patch (1 edit point); Lean fixed-version symbolic theorem + witness + regression + patch-tree regression 4/4 green | Actually run + machine-checked proof |

I-19 is a representative of the "cross-transaction state residue" defect
family: each individual transaction is completely correct, the error appears
only under specific transaction adjacency sequences, and single-transaction
tests are structurally blind to it. The symbolic-level theorem
`div_t1_overflow` pinpoints "when the stale value is harmful" down to a
Boolean condition — the unique contribution of formal methods over simulation
in this entry's evidence chain; and the test-fix interlude (the false witness
r=3) demonstrates in reverse the orchestration pitfalls of cross-transaction
testing.
