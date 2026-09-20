> English translation of the Chinese master `doc/bugs/I-45-寄存器分配零检查.md`. Translated 2026-09-13.

# I-45 Detailed Defect Analysis Report: Zero Hardware Checks on Register-Allocation Alignment and Size Constraints

| Item | Content |
|---|---|
| ID | I-45 |
| Source location | `ventus/src/cta/resource_table.scala:305-311` (allocation granularity = 1 register, no rounding); `ventus/src/top/GPGPU_top.scala:76-79` (num_vgpr/num_vgpr_per_wf etc. passed straight through from the host); `ventus/src/cta/cu_interface.scala:95-96` (the assertion only checks the global NUM_SGPR/NUM_VGPR=2048/1024 totals) |
| Type | Robustness gap (a host contract not hardened in hardware); on contract violation it escalates to a functional bug (cross-WG register aliasing, silently wrong data) |
| Severity | **Medium** (premised on a host contract violation; the consequence of violation is correctness-level) |
| Confirmation status | 【Confirmed (contingent on host contract violation)】; per the internal fix manifest the hardware is not fixed (host contract) — only a guarded variant and assertion recommendations are provided |
| Primary evidence | 【Lean machine-checked proof】counterexample witness triple (misalignment collision / fit overflow / assertion too weak) + full proof of the positive invariant (host alignment ⇒ whole-chain alignment); 【direct source reading】line-by-line check of the three zero-check points on the allocation chain |
| Lean model | `lean/Ventus/Spec/Discharge3.lean` (the dcg3 series); guarded variant `lean/VentusF/Arith.lean` (`farith_i45_guard_*`) |
| Reproduction/patch | No patch (host-contract handling); no RTL reproduction (the Lean counterexamples already pin down the trigger cone) |
| Related entries | The WB-A1 contract family (Discharge2/3: the main theorems that allocation disjointness ⟹ physical-register disjointness, `dcg2_wba1_bank_disjoint`/`dcg3_wba1_capstone`); I-11 (address-width aliasing on the same chain, also an "allocation-side assumption not hardened" case) |

---

## 0. Abstract

Ventus's physical register file is partitioned into per-warp ranges: the CTA allocation chain (resource_table linked list + cu_interface splitter + the vgpr_base/sgpr_base tables in CSR) assigns each WG a base range; register r of warp i within a WG maps to physical address `base>>2 + (w·perWf + r)>>2` and bank number `wid + regIdx(1,0)`. The correctness of this mapping implicitly rests on two premises: **(b) each WG's base and allocation size are 4-aligned (num_bank=4)**, and **(c) numWf×perWf ≤ vgprSize (warps within a WG do not overflow the WG's range)**.

This entry confirms: both premises receive **zero hardware checks** — the allocation granularity is exactly 1 register with no rounding; parameters like num_vgpr/perWf are passed straight through from the host; the only assertion (cu_interface.scala:95-96) checks the global totals rather than this WG's range — **it checks the wrong quantity**. When the host supplies a non-4-aligned size, the next WG's base becomes unaligned as well, and the two WGs' registers map to the same physical address (Lean counterexample: register 8 of warp A and register 4 of warp B alias); when numWf×perWf > vgprSize, the last WF overflows its WG's range and intersects the neighboring WG — while the assertion passes throughout.

The positive direction is also proven: if all host sizes are k-aligned ⇒ all chain bases are k-aligned (`dcg3_wba1_rt_run_aligned`, fully proven by induction over arbitrary event sequences). Hence this entry is a robustness gap of the form "a contract not hardened in hardware": with the current driver honoring the contract it cannot be triggered; on violation it silently produces wrong data.

---

## 1. Module Function and Design Intent

### 1.1 Background Concepts

- **The register allocation chain**: the host gives each WG's resource requirements in the kernel-launch parameters (num_vgpr/num_sgpr/num_lds totals and per-warp sizes) → resource_table uses linked-list best-fit to allocate a contiguous range (base address base) → cu_interface's splitter splits the WG into num_wf warps, accumulating perWf warp by warp to obtain each warp's base → at dispatch these are written into CSR's vgpr_base(wid)/sgpr_base(wid) tables.
- **Bank interleaving**: the physical register file has 4 banks; the mapping formulas on the operand-collector/writeback side are `bankID = wid + regIdx(1,0)`, `rsAddr = base>>2 + regIdx>>2` (read side operandCollector.scala:110,122; writeback side :604,606). The `>>2` means **only when the base is 4-aligned does "warp ranges are disjoint" imply "physical addresses are disjoint"**.
- **The WB-A1 contract**: the premises (b)(c) of this project's core Writeback/allocation-correctness theorem `dcg2_wba1_bank_disjoint` (same physical bank address ⟹ same warp) are exactly the alignment and size constraints above. I-45 was discovered while discharging (b)(c) — "the hardware simply does not guarantee them".

### 1.2 Design Intent

The allocator (resource_table)'s FIND FSM scans the linked list for the first free segment with `size ≥ wgsize` (the best-fit update is at :305-311) and performs no alignment normalization on the values of size/wgsize — the design intent is "the host/driver is responsible for supplying legal parameters"; the hardware only does arithmetic.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: allocation granularity = 1 register, no rounding** (`resource_table.scala:305-311`, ★ hazard one):

```scala
val size = WireInit(UInt(log2Ceil(NUM_RESOURCE+1).W), addr2 - addr1) // resource segment size
val result_update = (size >= wgsize) && (size < fsm_a_found_size)
fsm_a_found_size := Mux(fsm_a_valid_p1 && result_update, size, fsm_a_found_size)
fsm_a_found_addr := Mux(fsm_a_valid_p1 && result_update, addr1 + 1.U, fsm_a_found_addr)
```

The found free segment's start `addr1 + 1` is used directly as the base, and the allocation size `wgsize` is deducted as-is — any value is accepted; there is no alignment normalization such as `roundUp(wgsize, 4)`. When the first WG's size is 5, the next WG's base = 5 (the Lean counterexample `dcg3T_misalign_base` pins down exactly this value).

**Construct 2: allocation parameters are passed straight through from the host** (`GPGPU_top.scala:76-79`):

```scala
cta_sche.io.host_wg_new.bits.num_sgpr        := io.host2CTA.bits.host_sgpr_size_total
cta_sche.io.host_wg_new.bits.num_vgpr        := io.host2CTA.bits.host_vgpr_size_total
cta_sche.io.host_wg_new.bits.num_sgpr_per_wf := io.host2CTA.bits.host_sgpr_size_per_wf
cta_sche.io.host_wg_new.bits.num_vgpr_per_wf := io.host2CTA.bits.host_vgpr_size_per_wf
```

num_vgpr/per_wf etc. all come from the host interface; there is no legality check on the hardware side.

**Construct 3: the only assertion checks the wrong quantity** (`cu_interface.scala:95-96`, ★ hazard two):

```scala
assert(splitter_cnt <= 1.U || NUM_SGPR.U - splitter_sgpr_addr > fifo.io.deq.bits.num_sgpr_per_wf)
assert(splitter_cnt <= 1.U || NUM_VGPR.U - splitter_vgpr_addr > fifo.io.deq.bits.num_vgpr_per_wf)
```

The assertion checks "the global 2048/1024 register file still has room for one more warp" — not "this warp lands within this WG's allocated range". Lean counterexample `dcg3_wba1_hw_assert_too_weak`: in a scenario where the last WF overflows its WG's range by a factor of 7, the assertion passes throughout. Moreover the assertion exists only in simulation; after synthesis there is no check at all.

---

## 3. Defect Analysis

### 3.1 Precise Description of the Defect

The two premises — (b) alignment and (c) size fit — receive zero hardware checks. The consequences of violating each:

- **(b) violated (non-4-aligned size)**: first WG size 5 ⇒ next WG base 5 (counterexample `dcg3T_misalign_base`). An unaligned base distorts the rsAddr formula: register 8 of warp A (base=5) and register 4 of warp B (base=4) compute the same bank address 1 (`5/4 + 8/4 = 3 = 4/4 + 4/4`, whereas mathematically `(5+8)/4 = 3 ≠ (4+4)/4 = 2` — the information lost to truncation manufactures the collision) — the two WGs' register writebacks trample each other (`dcg3_wba1_misalign_collision`).
- **(c) violated (numWf×perWf > vgprSize)**: the splitter accumulates perWf warp by warp; the last WF's base +perWf overflows this WG's range and intersects the neighboring WG (`dcg3_wba1_fit_violation`: `B + (nw-1)·p < B + S < B + nw·p` precisely characterizes the overflow shape).
- **Assertion failure**: under both violations above, the assertion at cu_interface.scala:95-96 passes throughout (`dcg3_wba1_hw_assert_too_weak`) — the last line of defense does not exist either.

### 3.2 Root Cause

The design intent that "allocation legality is a host contract" **exists only at the verbal/documentation level**; the hardware treats the host parameters as trusted input all the way down. The WB-A1 main theorem family (Discharge2/3) decomposes the proof of "registers never trample each other" into three premises (a)(b)(c): (a) (ranges disjoint) is supported by allocator contracts such as H-ALLOC-FIT; the verification of (b)(c) only revealed, when it descended to Discharge3, that the hardware side has no mechanism guaranteeing them — this entry is a product of the contract-discharge workflow "verification uncovering a gap", not a chance review finding.

### 3.3 Harm and Tolerability

- **Harm**: when the host/driver configuration violates the contract, register data tramples across WGs — silently wrong data, with no trap/assertion (after synthesis).
- **Tolerability**: if the current driver always supplies 4-aligned and size-matched allocations it cannot be triggered — this is a "contract not hardened in hardware" robustness gap; rating: **medium**. The positive direction is proven (`dcg3_wba1_rt_run_aligned`: all host sizes k-aligned ⇒ all chain bases k-aligned after any event sequence), i.e. the "honor the contract ⟹ safe" loop is closed; what is missing is "violate ⟹ reject".
- **Handling decision** (the internal fix manifest): **do not fix the hardware** (host contract); recommend adding alignment assertions on the hardware side or rounding up at allocation, to be followed up with upstream separately; the Lean side provides an alignment-guard variant (`farith_i45_guard_iff`/`farith_i45_guard_accept_witness`: an if-and-only-if characterization of guard ⟺ divisibility, plus accept/reject witnesses).

---

## 4. Lean Formal Evidence

All in `lean/Ventus/Spec/Discharge3.lean` (the dcg3 series), zero sorry.

**The counterexample triple (nails in the hole)**:

- `dcg3T_misalign_base` (by decide): after the first WG allocates size 5, `rtAllocBase` gives the next base = 5 — an unaligned base really is produced;
- `dcg3_wba1_misalign_collision` (by decide): under an unaligned base the rsAddr formula distorts (the numeric equalities of the previous section, machine-checked);
- `dcg3_wba1_fit_violation` (symbolic theorem): when `S < nw·p` and `(nw-1)·p < S`, `B+(nw-1)·p < B+S < B+nw·p` — the last WF strictly overflows this WG's range;
- `dcg3_wba1_hw_assert_too_weak` (by decide): in a scenario overflowing by a factor of 7 (for all k=0..6, `0 + k·32 + 32 < 1024`), the assertion conditions all hold — it checks the global totals rather than this WG's range.

**Positive closure (fully proven by induction over arbitrary event sequences)**:

- `dcg3_wba1_rt_run_aligned`: starting from the empty table, if the event sequence satisfies the per-prefix contract (rtEventOk) and all alloc sizes are k-aligned, then after any evolution the base and end+1 of every resident node are k-aligned (invariant `dcg3RtAligned`; the alloc and dealloc branches each preserve it: `dcg3_rt_alloc_step_aligned`/`dcg3_rt_dealloc_step_aligned`).

**Guarded variant** (`lean/VentusF/Arith.lean`): `farith_i45_guard_iff` (guard accepts ⟺ size divisible by k, if-and-only-if), `farith_i45_guard_accept_witness` — the "if a guard were added, its semantics is precise" evidence under the no-hardware-fix premise.

---

## 5. Simulation Verification

**No RTL reproduction case** (doc/22 has no record for this entry). The reason matches the nature: this entry is a host-contract-violation class gap; the trigger cone and the consequences have been precisely pinned down by Lean counterexample witnesses (decide-level numerics), so the marginal value of an RTL reproduction is low (it would be nothing more than "behavior is wrong after illegal parameters are given", which is uncontroversial). If upstream decides to add hardware assertions, a targeted ChiselSim is recommended: after the host issues a WG of size 5 followed immediately by a second WG, observe the two WGs trampling the same physical address (ready to be written, not executed in this environment).

---

## 6. Upstream Impact Analysis

- **Impact surface**: the entire allocation chain (resource_table → cu_interface splitter → CSR base tables → collector address formulas). The violation consequence lands on data correctness.
- **Why upstream didn't find it**: the current software stack/driver always supplies aligned and matched parameters (RVV-style per-warp register counts are naturally multiples of 4); the violation domain has never been stepped on.
- **Relationship to I-11**: I-11 (sgpr bank address truncated to 8 bits) is another defect on the same "allocation-side assumptions not hardened" chain (there the assumption is "base < 1024", broken by the NUM_SGPR_MAX=2048 allocation space). Taken together: the contracts between the allocation chain and the consumption chain (base alignment, size fit, base upper bound) are entirely lacking hardware hardening.
- **Recommendation**: on the hardware side, add assertions when cu_interface loads a new WG (`num_vgpr % 4 == 0 && num_vgpr_per_wf % 4 == 0 && num_wf * per_wf ≤ size`), at zero RTL cost; the root-cause fix is for the allocator to round sizes up to a multiple of 4 (a small change but it alters the allocation layout — an upstream decision).

---

## 7. Fix and Fix Verification

**Handling decision** (the internal fix manifest: No fix, host contract): do not change the hardware; recommend adding alignment assertions on the hardware side or rounding up at allocation, to be followed up with upstream separately.

**Delivered on the Lean side**:

- Hole characterization (§4 counterexample triple): "where it goes wrong" on violation, pinned down to exact values;
- positive closure `dcg3_wba1_rt_run_aligned`: host honoring the contract is a **sufficient condition** for whole-chain safety — the driver-side compliance checklist thereby gains machine-checked backing;
- guarded variant `farith_i45_guard_iff`/`farith_i45_guard_accept_witness`: if a hardware guard is added in the future, its acceptance semantics has been pre-proven (guard ⟺ divisibility).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | resource_table.scala:305-311 (no rounding), GPGPU_top.scala:76-79 (host pass-through), cu_interface.scala:95-96 (assertion checks the wrong quantity) | Line-by-line check |
| Lean machine-checked proof | Counterexamples `dcg3T_misalign_base`/`dcg3_wba1_misalign_collision`/`dcg3_wba1_fit_violation`/`dcg3_wba1_hw_assert_too_weak`; positive `dcg3_wba1_rt_run_aligned` (induction over arbitrary event sequences) | decide numeric-level + full inductive proof |
| Simulation | None (host-contract class; Lean counterexamples already pin down the trigger cone) | — |
| Fix | Hardware not fixed (host contract); guarded variant `farith_i45_guard_iff` pre-proven | Machine proof |

I-45 is a typical case of "contract discharge uncovering a gap": premises (b)(c) of the WB-A1 main theorem bear no weight in hardware; both the positive direction (honor ⟹ safe) and the negative direction (violate ⟹ the precise shape of the collision) are machine-checked closed. What remains is a clear engineering decision item — whether to harden the contract in hardware (assertions/rounding). It is not a functional bug under the current configuration, but it precisely marks the boundary of "how far the hardware trusts the host", and the cost of crossing it.
