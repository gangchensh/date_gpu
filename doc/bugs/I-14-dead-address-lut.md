> English translation of the Chinese master `doc/bugs/I-14-地址查表死硬件.md`. Translated 2026-09-13.

# I-14 Detailed Defect Report: the address lookup tables of collectorUnit/operandCollector are dead hardware with no consumers

| Item | Content |
|---|---|
| ID | I-14 |
| Source location | `ventus/src/pipeline/operandCollector.scala:89-98` (the three lookup tables inside collectorUnit: `bankIdLookup` (264 entries), `addrLookupScalar`, `addrLookupVector`) and :583-591 (the same-named three tables inside the top-level operandCollector) |
| Type | Non-functional defect (area/power waste — dead-hardware ROM) |
| Severity | Low (no functional impact; a 264-entry ROM × (8 CUs + 1 top-level copy) = 9 copies of dead lookup tables) |
| Confirmation status | 【Confirmed】, fix patch merged into the 38-patch merged tree and regression passed |
| Primary evidence | [direct source reading] repo-wide grep finds no references + two comparison points where the actual addresses are computed directly by combinational formulas; [simulation run] 38-patch merged tree regression (indirect) |
| Lean model | None (dead hardware not modeled: CollectorUnit.lean header notes D5/D8, OperandCollector.lean header note records the non-modeled items) |
| Reproduction/patch | Non-functional issue; a reference check suffices; patch `i14-operandcollector-dead-lut.patch` (internal fix manifest; not released) |
| Related entries | I-10 (same-family dead hardware, regfile.scala), I-11 (the real defect of the address formulas — the lookup tables are the abandoned alternative to those formulas), I-12/I-13 (same module) |

---

## 0. Summary

operandCollector.scala contains two groups, six tables in total, of address-transformation lookup tables: one group inside the collectorUnit class body (:89-98) and one inside the top-level operandCollector class body (:583-591), with identical contents — `bankIdLookup` (a 264-entry warp_id→bank_id modulo ROM), `addrLookupScalar`, and `addrLookupVector` (lookup tables for warp base address ÷4). A repo-wide grep shows these six names have **no readers at all**: the actual bank number and intra-bank address are computed directly by combinational formulas (read side :103-126, writeback side :603-606). These lookup tables are leftovers of an early design — after the ROM-based address-transformation scheme was replaced by combinational formulas, the declarations were never deleted.

Each bankIdLookup is a 264-entry ROM; the 8 collectorUnits each carry one copy and the top level carries one more, for 9 copies of dead lookup tables (plus 2×9 smaller addrLookup tables). Pure area/power waste, no functional impact.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **The address-transformation problem**: operand collection needs to map a "warp's logical register number" to physical addressing `(bankID, rsAddr)`: `bankID = (wid + regIdx) mod num_bank`, `rsAddr = base(wid)>>2 + regIdx>>2` (design details in `doc/bugs/I-11-标量bank地址回绕别名.md` §1).
- **Two implementation routes**: (a) combinational formulas — addition and bit slicing, computed directly; (b) lookup tables — the mapping materialized into ROM, indexed by warp_id. This module's history evidently tried route (b), eventually adopted route (a), but left (b)'s declarations behind.
- **Chisel's ROM generation**: `Seq.map(...).map(x => (x._1.U -> x._2))` produces a sequence of tuples, itself just a Scala value; but what matters is that the hardware-signal references they hold (such as `io.sgpr_base(x)`), once disconnected from any subsequent MuxLookup-style use, may still persist in the generated circuit as constant ROM/multiplexer structures (and in any case they are source-level dead logic and maintenance noise).

### 1.2 Design intent (inferred)

The comments say it themselves: "Lookup table for address transformation / generate tuple: warp_id -> bank_id (bank id of r0 in this warp. this is interleave)" (:87-88) and "bankID = (wid + regIdx) % num_bank / rsAddr = [gpr_base(i) + regIdx)] / num_bank" (:581-582) — the latter is exactly the comment of the current combinational formula, the former the comment of the superseded lookup-table scheme. The two comment blocks coexisting is direct evidence of "scheme replaced, cleanup not done".

---

## 2. Construct-by-construct reading of the original code

**Inside collectorUnit** (:87-98, ★ hazard):

```scala
// Lookup table for address transformation
// generate tuple: warp_id -> bank_id (bank id of r0 in this warp. this is interleave)
val bankIdLookup = (0 until num_warp + 256).map { x =>      // :89, 264 entries
  (x -> x % num_bank)
}.map { x => (x._1.U -> x._2.U) }
// reg addr in one bank
val addrLookupScalar = (0 until num_warp).map { x =>        // :93
  (x -> (io.sgpr_base(x) >> log2Ceil(num_bank)).asUInt)
}.map { x => (x._1.U -> x._2) }
val addrLookupVector = (0 until num_warp).map { x =>        // :96
  (x -> (io.vgpr_base(x) >> log2Ceil(num_bank)).asUInt)
}.map { x => (x._1.U -> x._2) }
```

**Inside the top-level operandCollector** (:581-591, ★ same names, same contents, one more copy):

```scala
// writeback control
// bankID = (wid + regIdx) % num_bank
// rsAddr =  [gpr_base(i) + regIdx)] / num_bank
val bankIdLookup = (0 until num_warp + 256).map { x => ... }    // :583
val addrLookupScalar = (0 until num_warp).map { x => ... }      // :586
val addrLookupVector = (0 until num_warp).map { x => ... }      // :589
```

**The combinational formulas actually in use** (comparison, showing the tables are indeed superseded):

```scala
// read side :103-105 (bankID) and :110-125 (rsAddr)
io.outArbiterIO(i).bits.bankID := Mux(io.control.fire && (state === s_idle),
  io.control.bits.wid(widSliceHigh, 0) + regIdxWire(i)(log2Ceil(num_bank)-1, 0), ...)
io.outArbiterIO(i).bits.rsAddr := (io.sgpr_base(...) >> log2Ceil(num_bank).U).asUInt + ...
// writeback side :603-606
wbVecBankId := ...reg_idxw(...)+...warp_id(...)
wbScaBankAddr := (io.sgpr_base(...) >> ...) + ...
```

[Direct source reading] a repo-wide grep of `bankIdLookup`/`addrLookupScalar`/`addrLookupVector` finds no references outside the declaration sites (doc/03's original conclusion, re-verified by this report).

---

## 3. Defect analysis

### 3.1 Precise description of the defect

Six lookup tables (3 tables × 2 sites) are **dead logic with no consumers**: values are constructed but never read. Among them, bankIdLookup materializes a 264-entry (num_warp+256 = 8+256) modulo mapping; the other two have 8 entries each. Scale: a 264-entry ROM × 9 copies, plus several small tables.

### 3.2 Root cause

The old declarations were not cleaned up after the design-scheme replacement (lookup tables → combinational formulas). Same family as I-10: in Chisel code, "declared but unused" is not flagged by any toolchain stage (Scala only gives an unused warning; FIRRTL is silent about fanout-free nodes), so such things inevitably accumulate when maintenance review is absent.

### 3.3 Harm and tolerability

- **Harm**: pure area/power and readability. No functional impact (no consumers ⇒ no effect on any observable behavior; that is the defining fact of "dead hardware").
- **Incidental risk**: the dead code still carries "correct design knowledge" (the mapping formulas in the comments), which later readers may misread as the current mechanism; and `addrLookupScalar` references `io.sgpr_base(x)` — if it ever really gets wired up someday, its width behavior would need fresh review (cf. the lesson of I-11).
- **Tolerability**: tolerable; upstream is advised to delete them.

---

## 4. Lean formal evidence

No dedicated theorems, and that is the correct treatment — [direct source reading + modeling decision]:

- `lean/Ventus/Schedule/CollectorUnit.lean` header notes D5/D8: the three lookup-table groups are registered as "dead hardware with no consumers, not modeled";
- `lean/Ventus/Schedule/OperandCollector.lean` header note likewise registers the top-level three tables as not modeled.

The model covers only the combinational-formula path (i.e. the active hardware); the dead tables do not enter the model and affect no theorem. Writing behavioral theorems for hardware with no consumers is both meaningless and misleading (it would imply they participate in behavior).

---

## 5. Simulation verification

Non-functional issue; no behavioral reproduction case. Evidence:

- [Direct source reading] repo-wide reference grep, zero hits (the judgment method recorded in doc/03, re-verified by this report);
- [Simulation run (indirect)] the 38-patch merged tree (containing the i14 deletion patch) compiled with mill, MILL_EXIT=0, and all ChiselSim suites judged identically to the 35-patch tree (doc/22) — elaboration/simulation all green after the deletion, conversely confirming the absence of connections (had there been any reference, the deletion would have been a compile error).

---

## 6. Upstream impact analysis

- **Impact surface**: collectorUnit ×8 instantiations + top level ×1, for 9 copies of dead lookup tables.
- **Why upstream did not find it**: no functional manifestation; the unused warning is drowned in Chisel elaboration's warning noise (this project measured 26 warnings from emitVerilog, doc/22).
- **Evolution risk**: dead tables coexisting with live formulas is a "dual source of truth" hazard — someone modifying the address mapping in the future may edit the wrong place (changing the dead table while the live formula stays unchanged), or mistakenly trust the dead tables' comments.

---

## 7. Fix and fix verification

**Patch** (`i14-operandcollector-dead-lut.patch` (internal fix manifest; not released), two edit points): the six lookup tables at :89-98 and :583-591 are deleted wholesale, with comments marking the I-14 fix in their place. the internal fix manifest handling category: **Dead-code removal**; Lean fixed-version theorems Not needed.

**Fix verification**:

- [Simulation run] 38-patch merged tree regression (2026-09-10, doc/22): compile passed, all suites judged identically (no regression);
- [Inference] deletion is pure gain (area/readability), no behavior change, no behavioral fix proof needed.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | six table declarations at :89-98/:583-591 + zero repo-wide references + live formulas at :103-126/:603-606 as comparison | Line-by-line check |
| Lean model | Not-modeled decision on record (CollectorUnit D5/D8, OperandCollector header note) | Modeling decision |
| Simulation/regression | 38-patch merged tree compile + full ChiselSim regression consistent (doc/22) | Measured (indirect) |

I-14 and I-10 both belong to "maintenance-leftover dead hardware": the cleanup value is certain and the risk is zero. Its other significance is archaeological: the comments and the lookup tables together prove that operandCollector's address mapping went through a "lookup tables → combinational formulas" scheme replacement — and the current formulas are exactly where I-11 (the width-wraparound aliasing) lives. Once the dead tables are cleaned out, I-11's fix surface (combinational formulas + width parameters) becomes the single source of truth.
