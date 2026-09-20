> English translation of the Chinese master `doc/bugs/I-11-标量bank地址回绕别名.md`. Translated 2026-09-13.

# I-11 Defect Analysis Report: Scalar bank address width computed from VGPR size; cross-warp register aliasing when sgpr_base ≥ 1024

| Item | Content |
|---|---|
| ID | I-11 |
| Source location | `ventus/src/top/parameters.scala:22` (`depth_regBank = log2Ceil(num_vgpr/num_bank)` = 8, root cause); `ventus/src/pipeline/regfile.scala:10-12` (`rsidx/rdidx` port width depth_regBank=8 bits) and :20/:24 (scalar bank mem depth `NUMBER_SGPR_SLOTS/num_bank` = 2048/4 = **512** entries, needs 9 bits; doc/03 records it as :21, snapshot line numbers verified to drift by 1-3 lines, same construct); `ventus/src/pipeline/operandCollector.scala:606` (writeback `wbScaBankAddr` 8-bit wrapping addition) and :110/:112/:122/:124 (read side, same formula) |
| Type | Functional bug (silent data corruption) — bit-width mismatch |
| Severity | **High** (cross-warp / cross-WG scalar registers overwrite each other with no error reported; trigger surface = any high-base allocation once the low region is occupied) |
| Status | 【Confirmed】, ChiselSim reproduction succeeded + fix patch regression green on the merged patch tree |
| Key evidence | 【Lean machine-checked proof】Address aliasing theorem family + allocation-side reachability witness; 【simulation】ChiselSim module-level reproduction + patched-tree regression; 【source reading】four sites in parameters/regfile/operandCollector/cta line-verified |
| Lean model | Original side `lean/Ventus/Schedule/OperandCollector.lean` (`ocI11_*`); allocation side `lean/Ventus/CTA/ResourceTable.lean` (T8 `rtI11`/`rtI11max`/`rtV11`); fixed version `lean/VentusF/Arith.lean` (`farith_i11_*`) |
| Repro/patch | `repro/OperandCollectorBugRepro.scala` (ChiselSim, actually executed and reproduced); patch `i11-regfile-addrwidth.patch` (internal fix manifest; not released) |
| Related entries | I-10 (dead SRAM in the same file), I-45 (host-side alignment/size contract with zero checking, same "allocation ↔ addressing" contract family), I-12 (same module, shared repro suite) |

---

## 0. Abstract

The bank address width of the Ventus register file is determined by a single
global parameter `depth_regBank`, which is computed from the **vector**
register file size: `log2Ceil(num_vgpr/num_bank) = log2Ceil(1024/4) = 8`
bits. But the actual storage depth of a **scalar** bank is
`NUMBER_SGPR_SLOTS/num_bank = 2048/4 = 512` entries, which requires a 9-bit
address. Both the scalar read and write sides compute the intra-bank address
with the combinational formula `(sgpr_base(w) >> 2) + (reg_idx >> 2)` and
truncate it to 8 bits: when a warp has `sgpr_base ≥ 1024` the address wraps
around and **aliases into the low 256 entries** — landing in another warp's
register region. The CTA allocator assigns sgprs across the entire 2048-slot
space (no <1024 restriction exists on the rt side; there is a machine-checked
witness: once the low region is occupied, base=1792 is allocated), so
triggering is a legal, routine scheduling outcome requiring no malformed
input.

The consequence is silent data corruption: a high-base warp's scalar write
lands on a low-base warp's physical register, and the read side aliases
identically with the same formula — two warps overwrite / read back each
other's data, with no error anywhere in the machine. ChiselSim reproduction
has been executed: after warp7 (sgpr_base=1792) writes, warp3 (base=768)
reads back the other warp's data 0xdeadbeef.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **SGPR/VGPR and base allocation**: each warp has its own logical spaces of
  scalar registers (sgpr) and vector registers (vgpr). Physically all warps
  share a register file organized by banks. When the CTA scheduler dispatches
  a warp it allocates a physical region for it, delivered via the
  `sgpr_base(w)`/`vgpr_base(w)` base registers. Logical register numbers in
  instructions are mapped to physical locations via "base + index".
- **Bank-interleaved mapping**: num_bank=4. Physical addressing is split into
  two levels — bank number `bankID = (wid + regIdx) mod 4`, and intra-bank
  address `rsAddr = base>>2 + regIdx>>2` (each warp's base is interleaved by
  4, hence the divide by 4). This design scatters adjacent registers of the
  same warp across different banks, increasing parallel read bandwidth.
- **depth_regBank**: the bit-width parameter of the regfile bank ports
  (rsidx/rdidx), which is supposed to cover "the deepest bank".
- **Parameter values** (parameters.scala): num_warp=8, num_vgpr=128×8=1024,
  num_sgpr=256×8=2048; NUMBER_SGPR_SLOTS=2048 (doc/03 records
  parameters.scala:181 `NUM_SGPR_MAX = num_sgpr`).

### 1.2 Design intent

The designer's intent was clearly "one width parameter serves all banks".
This happens to be correct on the vector side (a vgpr bank is 1024/4=256 =
2^8 deep, exactly 8 bits); the mistake is that a scalar bank is twice as deep
as a vector bank, so the unified width cuts off the most significant bit of
the scalar-side address.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: width parameter computed from VGPR** (`parameters.scala:22`, ★root cause):

```scala
def depth_regBank = log2Ceil(num_vgpr/num_bank)   // = log2Ceil(256) = 8
```

**Construct 2: scalar bank is 512 deep, ports are only 8 bits** (`regfile.scala:10-12`, :20/:24):

```scala
val rsidx  = Input(UInt(depth_regBank.W))    // :10, 8 bits
val rdidx  = Input(UInt(depth_regBank.W))    // :12, 8 bits
...
val regs = SyncReadMem(NUMBER_SGPR_SLOTS/num_bank, UInt(xLen.W))  // :24, 512 entries need 9 bits
```

The upper 256 of the 512 entries are therefore **permanently unreachable**
(there is nowhere for address bit 8 to go) — on top of the functional defect,
half of the scalar SRAM degenerates into dead area.

**Construct 3: 8-bit wrapping addition on the writeback side** (`operandCollector.scala:595-606`, ★defect site):

```scala
val wbScaBankAddr = Wire(UInt(depth_regBank.W))   // :596, 8 bits
...
wbScaBankAddr := (io.sgpr_base(io.writeScalarCtrl.bits.warp_id) >> log2Ceil(num_bank).U).asUInt
               + (io.writeScalarCtrl.bits.reg_idxw >> log2Ceil(num_bank).U)   // :606
```

Chisel's `+` has wrapping semantics and the result is assigned to an 8-bit
Wire — it wraps naturally whenever `sgpr_base>>2 ≥ 256`.

**Construct 4: same formula on the read side** (`operandCollector.scala:110/:112/:122/:124`):

```scala
io.outArbiterIO(i).bits.rsAddr := (io.sgpr_base(...) >> log2Ceil(num_bank).U).asUInt
                                + (regIdxWire(i) >> log2Ceil(num_bank).U)   // :110 (accept cycle), etc.
```

The rsAddr port is likewise `UInt(depth_regBank.W)` (readArbiterInnerIO :31).
Read and write sides use the same formula with the same truncation, so the
**aliasing is perfectly identical**: wherever a write goes wrong, a read goes
wrong too — two warps see one "shared" physical register.

**Numerical instance** (same source as the machine-checked witness): with
sgpr_base=1792, reg=0, the mathematical address = (1792>>2)+0 = 448, which
truncated to 8 bits = 448 mod 256 = **192**; and 192 is exactly the intra-bank
address of sgpr0 of the warp with sgpr_base=768 (768>>2=192).

---

## 3. Defect analysis

### 3.1 Precise description of the defect

Bit-width mismatch chain (evidence for every link):

1. parameters.scala:22 sets the bank address width to 8 bits (computed from vgpr);
2. a scalar bank is actually 512 deep (regfile.scala:24), needing 9 bits;
3. the address formulas of the collector read side (:110-125) and writeback
   side (:606) wrap within 8 bits;
4. sgpr_base ≥ 1024 ⇔ base>>2 ≥ 256 ⇒ address wraps mod 256;
5. the CTA allocator assigns sgprs across the entire 2048-slot space
   (resource_table's `baseaddr_sgpr_reg`, delivered via CTA2warp as the
   collectorUnit's sgpr_base input); once the low region is occupied, a legal
   allocation yields base ≥ 1024;
6. two warps (bases differing by 1024 and warp IDs differing by 4 — same low
   2 bits of wid) have **fully colliding bank number and intra-bank address**
   for the same-named scalar register: the same physical register.

Trigger surface = "any high-base allocation once the low region is occupied".
`NUM_WG_SLOT=8` supports multiple concurrently resident WGs; a single WG with
8 warps × 256 sgprs already fills all 2048 slots, so high-base allocation is
the norm in multi-WG scenarios.

### 3.2 Root cause

The single-point root cause is that the width formula at parameters.scala:22
chose the wrong reference (vgpr instead of max(vgpr, sgpr)). The deeper
reason is that the "one parameter serves both bank classes" design omitted
the degree of freedom "scalar/vector capacities may differ"; the vector
side's 256 = 2^8 happens to be unproblematic, masking the fact that the
scalar side's 512 needs 9 bits.

### 3.3 Impact and tolerability

- **Impact**: silent cross-warp / cross-WG scalar register interference —
  writes overwrite another warp's data, reads return another warp's data.
  Scalar registers carry critical values such as addresses, loop counters and
  branch conditions; the corruption can be any combination of wrong data,
  wrong control flow, and out-of-bounds memory access; the whole machine has
  no trap and no assertion (no runtime check can catch it).
- **Tolerability**: under a single warp / low-occupancy small kernel (the
  typical shape of the official tests) base stays small and it does not
  trigger; under real workloads with multiple WGs or large register usage it
  is a high-risk data-correctness defect. Rating: **High**.

### 3.4 Relationship to related entries

- **I-45** (zero hardware checking of allocation alignment/size): same
  "allocation-side ↔ addressing-side contract" family. I-11 triggers even
  under perfectly aligned, size-compliant allocation (the defect is in the
  hardware addressing width itself); I-45 is the contract gap when the host
  violates the contract. The two stand independently.
- **I-10**: dead SRAM in the same file regfile.scala; I-11's upper-256-entry
  dead region (8 bits cannot reach the upper half of 512 entries) is another
  kind of "wasted area", which disappears once I-11 is fixed.

---

## 4. Lean formal evidence

All proofs sorry-free; full build passes.

**Original side: machine-checked address aliasing** (`lean/Ventus/Schedule/OperandCollector.lean`,
theorem block :1215-1250, `#print axioms` audit :1469-1472):

- `ocI11_witness` (decide): with sgpr_base=1792, reg_idxw=0,
  `ocWbScaAddr 1792 0 = 192`, while the mathematical address 448 ≠ 192 —
  concrete numbers pin the wraparound down;
- `ocI11_alias` (bv_decide, arbitrary b/r): `ocWbScaAddr (b + 1024) r =
  ocWbScaAddr b r` — bases differing by 1024 always alias ((b+1024)>>2 ≡ b>>2
  (mod 256));
- **`ocI11_full_alias`** (bv_decide): when the bases differ by 1024 **and the
  warp IDs differ by 4**, bank number and intra-bank address collide
  simultaneously — the two warps' writebacks interfere with the **same
  physical register** (same address with different banks would not be a
  physical collision; this theorem closes the sufficient condition for "full
  collision" with machine proof);
- `ocI11_read_witness` (decide): the read side (:110-125, same formula as
  :606) aliases identically — a scalar read request with sgpr_base=1792,
  reg_idx1=0 yields rsAddr=192, i.e. operand collection also reads another
  warp's register.

**Allocation side: machine-checked trigger surface** (`lean/Ventus/CTA/ResourceTable.lean` T8,
:1750-1767, all `by decide`):

- `rtI11` witness: after rt free-list slot 3 occupies [0,1792), allocating 256
  more yields `rtAllocBase rtI11 rtNUM_SGPR 5 256 = 1792` (flush against the
  upper bound 1792+256=2048, completely legal allocation) — the allocation
  side has no interception whatsoever against high bases;
- `rtI11max`: with size=1, base can reach 2047 (extreme upper bound);
- `rtV11` contrast: the vgpr path has N=1024 ⇒ base is always ≤ 1023, so the
  vector side never triggers — a machine-checked proof that "this defect is
  confined to the scalar channel".

**Fixed version** (`lean/VentusF/Arith.lean:356-401`):

- `farith_i11_alias_gone` (bv_decide): with a 9-bit address, bases differing
  by 1024 no longer alias (premise b < 3072, covering the 12-bit value range
  b+1024 < 4096);
- `farith_i11_full_alias_gone`: both address and bank-number aliasing
  eliminated simultaneously;
- `farith_i11_regr` (regression safety): when the mathematical address < 256,
  the fixed-version address equals the zero-extension of the original address
  — behavior on the non-triggering domain is unchanged;
- `farith_i11_witness`: the fixed version yields 448 for 1792/0 (the
  mathematically correct value);
- `farith_i11_depth`: 2^9 = 512, covering the full scalar bank depth.

---

## 5. Simulation verification (ChiselSim execution + patched-tree regression)

**ChiselSim module level** (`repro/OperandCollectorBugRepro.scala`, executed
2026-09-06/07, doc/22 verdict table): two warps are allocated so that the
latter has a high base — **after warp7 (sgpr_base=1792) writes a scalar
register, warp3 (base=768) reads back 0xdeadbeef (should be 0x12345678)** —
the 8-bit bank address wraparound and cross-warp aliasing hold on real RTL.
Verdict: **reproduction succeeded**. The numbers agree with the aliasing
prediction of the Lean witness (1792→192=768>>2).

**Verilator whole-machine level**: this channel's 10 kernels do not include an
I-11-specific kernel (doc/22 Verilator verdict table) — not executed in the
whole-machine environment; the ChiselSim module-level reproduction plus the
machine proofs already form a closed loop, and whole-machine reproduction is
an optional reinforcement (ready to write).

**Patched-tree regression** (doc/22, two rounds):

- 35-patch tree (2026-09-07): OperandCollectorBugRepro **3/3 green** — the
  I-11 aliasing disappears (i11 patch effective), and the I-12 case in the
  same suite is also green;
- 38-patch merged tree (2026-09-10): same suite 3/3 green, verdict identical
  to the 35-patch tree — i11 coexists with the other 37 patches without
  regression.

---

## 6. Upstream impact analysis

- **Trigger surface**: all "scalar bank address computation" paths (4 read
  sites + 1 writeback site); any warp with sgpr_base ≥ 1024 is hit;
  concurrent multi-WG execution or a single WG with a large register
  footprint both enter high-region allocation.
- **Why upstream never found it**: the official test kernels are mostly
  single-WG, small-register-usage (vecadd-style) cases where sgpr_base always
  stays in the low region; this defect only manifests when "allocation
  pressure pushes a warp to a high base" — a classic "test workload too
  light" blind spot.
- **Relationship to the software stack**: the defect is in the hardware
  addressing width; software cannot work around it (unless the driver
  artificially restricts sgpr allocation to ≤1024, which amounts to disabling
  half of the scalar register capacity).
- **Side effect**: the 8-bit address makes the upper 256 of the 512 scalar
  bank entries permanently unreachable — half of the scalar SRAM per SM
  (4 × 256 × 32 bits = 32 Kbit) is dead area; fixing I-11 reclaims this area
  at the same time.

---

## 7. Fix and fix verification

**Patch** (`i11-regfile-addrwidth.patch` (internal fix manifest; not released), single edit
point, `parameters.scala:22`):

```scala
// before fix
def depth_regBank = log2Ceil(num_vgpr/num_bank)
// after fix
def depth_regBank = log2Ceil((num_sgpr max num_vgpr)/num_bank)   // = log2Ceil(512) = 9
```

Taking the maximum of the two (9 bits), the read side, writeback side, and
regfile ports all uniformly adopt this width — Chisel's type inference
automatically widens every `UInt(depth_regBank.W)` port/wire, so no
point-by-point edits are needed. the internal fix manifest disposition category:
**Functional fix (required)**.

**Three-part fix verification**:

- Effectiveness: Lean fixed-version theorems
  `farith_i11_alias_gone`/`farith_i11_full_alias_gone` (aliasing eliminated)
  + `farith_i11_witness` (1792/0 → 448); ChiselSim patched-tree regression
  shows the aliasing gone (3/3 green);
- Regression safety: `farith_i11_regr` (low-region address behavior is
  zero-extension equivalent) + full regression on the 38-patch merged tree
  with no collateral damage;
- Width self-consistency: `farith_i11_depth` (2^9=512 covers the full scalar
  bank depth).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Source reading | Line-by-line verification of parameters.scala:22, regfile.scala:10-12/:20/:24, operandCollector.scala:110/:112/:122/:124/:606 | Five source sites consistent |
| Lean machine-checked proof | `ocI11_witness`/`ocI11_alias`/`ocI11_full_alias`/`ocI11_read_witness` (full original-side aliasing chain); `rtI11`/`rtI11max`/`rtV11` (allocation-side trigger surface, T8); fixed version `farith_i11_*` | Universal bit-level (bv_decide/decide) |
| ChiselSim repro | warp7(1792) writes, then warp3(768) reads back 0xdeadbeef (should be 0x12345678) | Executed |
| Verilator whole machine | Not executed (10 kernels do not include an i11 case) | Ready to write |
| Fix verification | i11 patch (single point at parameters.scala:22); Lean fix theorems + patched-tree regression 3/3 green + regression equivalence | Executed + machine-checked |

I-11 is a "global width parameter chose the wrong reference" type of defect:
one line of formula cuts one bit off the scalar bank address, leaving half of
the scalar register space both unreachable and wraparound-aliased. Together
with I-21 (ShareMem setIdx 8 bits vs 10 needed) it forms a family — in
Ventus, "parameterized width mismatched with physical capacity" is not an
isolated case but a class of systemic risk, worth a library-wide width audit
upstream (this project already did a width-assumption sweep in doc/25).
