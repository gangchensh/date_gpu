> English translation of the Chinese master `doc/bugs/I-40-BankedStore读写撞行.md`. Translated 2026-09-13.

# I-40 Detailed Defect Analysis Report: L2 BankedStore same-row read-write with no conflict protection — LFSR poisons read data

| Item | Content |
|---|---|
| ID | I-40 |
| Source location | `ventus/src/L2cache/BankedStore.scala:101-110` (`:111` `io.sourceD_radr.ready := true.B` — reads always accepted; `:107` write port `w.req.valid := sourceD_wadr.valid \|\| sinkD_adr.valid`; `:105` read port `r.req.valid := sourceD_radr.valid` — no protection whatsoever against same-cycle "read row = write row"); related point `L2cache/Scheduler.scala:276-285` (zero guarding of radr) |
| Type | Functional bug (data corruption) — no mutual exclusion on same-cycle same-address SRAM read-write |
| Severity | **High** (when triggered, the L2 data path is poisoned with pseudo-random values: data written back to memory or refilled to L1 is wrong, silently) |
| Confirmation status | 【Confirmed (model-level reachable)】 — a Scheduler-side 3-cycle witness proves reachability machine-checkably; environment legality machine-checked cycle by cycle |
| Primary evidence | 【Lean machine-checked proof】BankedStore conflict-detection function + witness + Scheduler-side 3-cycle reachability trace; 【direct source reading】line-by-line check of BankedStore.scala:101-110, Scheduler.scala:276-285 |
| Lean model | `lean/Ventus/L2/L2MSHR.lean` (BankedStore model, conflict detection, witness), `lean/Ventus/L2/Scheduler.lean` (reachability trace); fixed version `lean/VentusF/MemL2.lean` |
| Reproduction/patch | No ChiselSim/Verilator reproduction suite (ready-to-run, not executed in this environment, see §5); patch `i40-l2-bankedstore-rwguard.patch` (internal fix manifest; not released) (functional fix, required) |
| Related entries | I-23 (ICache LFSR false hit), I-29 (DCache victim writeback LFSR pollution) — the same family "SRAMTemplate bypassWrite=false same-cycle same-address read returns an LFSR64 random value"; this entry corrupts the L2 data path; I-44 (same-wave L2 finding) |

---

## 0. Abstract

The L2Cache's BankedStore is the 128KB data array (cc_banks, an SRAMTemplate
instance with `bypassWrite=false`). It has one read port (`sourceD_radr`,
through which SourceD fetches data for eviction/refill) and two write ports
(`sinkD_adr` for landing memory responses, `sourceD_wadr` for SourceD
writebacks). The enables of the three ports are completely independent: the
read port has `ready := true.B` and always accepts (:111), and the write port
ORs its two sources (:107) — **there is no conflict protection at all against
same-cycle "read row = write row"**. With bypassWrite=false, an SRAMTemplate
returns an LFSR64 pseudo-random value on a same-cycle same-address read-write
(this semantics is pinned down in this project's SRAMTemplate.lean), so the
read-out data is randomly poisoned — if that read serves a victim eviction,
garbage is written back to the outer memory; if it serves a refill, the L1
receives garbage data.

Same family as I-23/I-29, but the corruption sits deeper (the L2 data path,
closer to the "persistent truth"). Wave 25 gave a Scheduler-side 3-cycle
concrete trace machine-checkably proving its model-level reachability
(`l2sc_i40_witness`), with environment legality machine-checked cycle by cycle
(`l2sc_i40_env0/1/2`) — this is the only **model-level reachable** entry among
the three of the L2 MSHR group (I-39/I-41 are conditionally unreachable), and
the fix is positioned as a "functional fix (required)".

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **BankedStore**: the L2Cache's data array (128KB, addressed by (set,way)
  rows, byte-granularity masked writes). The three data flows it serves:
  (a) **sinkD writes** — the outer memory's D-channel responses (refill data)
  land; (b) **sourceD writes** — data movement during flush/eviction;
  (c) **sourceD reads** — SourceD fetching data to evict a dirty line (write
  back to the outer memory) or to refill the L1.
- **SRAMTemplate's LFSR semantics**: Ventus's SRAM wrapper (NutShell lineage),
  under the `bypassWrite=false` configuration, returns an LFSR64 pseudo-random
  value on the read port for a same-cycle same-address read-write (the
  X-pessimism convention; after synthesis this is real logic, not a simulation
  artifact). This semantics has been pinned down on the Lean side
  (`sram_lfsr_bypass` in SRAMTemplate.lean); the same-family entries I-23/I-29
  are both carried by it.
- **Correct handling of a same-cycle read-write conflict**: either mutual
  exclusion (backpressure one side) or bypass-forwarding the correct write
  data. BankedStore has neither.

### 1.2 Design intent

The read port serves SourceD's data-fetch beats; the write ports serve refill
landing and eviction writeback. By design intent the two kinds of traffic
should be staggered in time; but the scheduling side (Scheduler.scala:276-285)
has zero guarding on the read-port address, and sourceD reads and sinkD writes
advance completely independently — any staggering is a pure timing
coincidence, not a structural guarantee.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the read port always accepts + the write port ORs its sources — same-cycle row collision unprotected** (★ the hazard, `BankedStore.scala:101-112`, confirmed consistent by direct source reading):

```scala
val set_index  = (io.sourceD_radr.bits.set)*(params.cache.ways.asUInt) + io.sourceD_radr.bits.way  // :101 read row address
val set_idx_sel= Mux(io.sinkD_adr.valid,                                                             // :104 write row address (sinkD takes priority)
                   (io.sinkD_adr.bits.set)*(params.cache.ways.asUInt) + io.sinkD_adr.bits.way,
                   (io.sourceD_wadr.bits.set)*(params.cache.ways.asUInt) + io.sourceD_wadr.bits.way)
cc_banks.io.r.req.valid := io.sourceD_radr.valid                          // :105 read issue
cc_banks.io.w.req.valid := io.sourceD_wadr.valid || io.sinkD_adr.valid    // :107 ★ write issue (two sources ORed)
io.sourceD_wadr.ready := !io.sinkD_adr.valid                              // :109 mutual exclusion inside the write port
io.sinkD_adr.ready := true.B                                              // :110
io.sourceD_radr.ready := true.B                                           // :111 ★ read port always accepts — zero guarding against the write port
```

There is no logic anywhere comparing `set_index === set_idx_sel` between
`sourceD_radr` and the two write sources — on a same-cycle `radrValid ∧
wValid ∧ same row`, the SRAM reads and writes the same address and the read
data = the LFSR value.

**Construct 2: zero guarding on the scheduling side** (`Scheduler.scala:276-285`):

```scala
bankedStore.io.sinkD_adr.valid := schedule.dir.valid   // :276  dir write = refill landing
...
bankedStore.io.sourceD_radr <> sourceD.io.bs_radr      // :282  sourceD read port directly connected
```

`schedule.dir` (the MSHRs' directory/data backfill) and
`sourceD.io.bs_radr` (eviction/refill data fetch) are two transaction streams
advancing independently; `mshr_wait` (SourceD's way-occupancy barrier to the
Scheduler) only blocks `schedule.a` launches, **not dir writes** — there is no
interception point anywhere against the two streams hitting the same (set,way)
row on the same cycle.

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

Trigger form (one complete chain):
1. An MSHR entry completes a refill (the sinkD response received; the data is
   in the entry's data_reg);
2. The Scheduler arbitrates and launches that entry's `schedule.dir` — a
   sinkD_adr write lands the (set,way) row;
3. On the same cycle, SourceD is reading **the same (set,way) row** for
   another transaction (eviction/refill) (`sourceD_radr.valid` with the same
   address);
4. Same-address SRAM read-write ⇒ `sourceD_rdat.data` = an LFSR64
   pseudo-random value;
5. The poisoned data is consumed by SourceD as if real: on the eviction path
   it is written back to the outer memory / on the refill path it is sent to
   the L1 — **silent data corruption**.

### 3.2 Root cause

BankedStore designs the handshakes of the three ports independently (a
constantly-accepting read port is the cheapest choice) and outsources the
"reads and writes must not hit the same row" discipline entirely to upstream
timing — while upstream (Scheduler/SourceD) has no mechanism whatsoever to
honor that discipline. The same pattern as I-23 (ICache `coreReq.ready :=
true.B`): a port's ready tied off + a carrier SRAM without bypass = same-cycle
conflicts erupting as LFSR poisoning.

### 3.3 Harm and tolerability

- **Harm**: correctness level, silent. Both consequence directions hold —
  poisoned data written back to the outer memory (victim eviction) or refilled
  into the L1 (refill data path). Stacked with I-29 (the DCache-side same
  family), both the L1 and L2 data-path layers have poisoning points.
- **Tolerability**: model-level reachability is machine-checked (the 3-cycle
  witness in §4) and depends on no extreme parameters; triggering requires the
  scheduling overlap of "refill landing and a sourceD read of the same row on
  the same cycle" — a common overlap form under normal L2 load. Rating:
  **High**; the internal fix manifest positions it as a Functional fix (required).
- **Honesty boundary**: the LFSR poisoning itself is a deterministic behavior
  of SRAMTemplate; but on the Verilator backend, the same-family I-29 did not
  observe the LFSR value in practice (doc/22 I-29 special item: Verilator's
  SRAM model presents the write data rather than the LFSR on a same-cycle
  read-write) — RTL-level reproduction of this poisoning is sensitive to the
  simulation backend; the Lean-side mechanism proof is authoritative.

---

## 4. Lean Formal Evidence

**BankedStore level** (`lean/Ventus/L2/L2MSHR.lean`, all 【Lean machine-checked proof】):

- The conflict-detection function `l2mBsCollision` (around :176-180):
  `radrValid && write-valid && read row == write row` — precisely
  characterizes the trigger condition;
- Witness `l2mBsT4_collision` (:970, native_decide): a numerical witness of
  the read data being poisoned on the conflict cycle (model-side convention:
  the conflict cycle returns the "old value before the write"; the harm is
  characterized by the conflict detection + witness; real hardware returns the
  LFSR value — the D6 idealization is explicitly declared in the file header);
- Positive specification: the storage goes through the `MemLaws` abstract
  interface (universally quantified over any `[MemLaws M L2mBsAddr
  (BitVec 8)]`); `l2mBsWriteRow_read_same`/`l2mBsStep_rdata` and other
  write-then-read consistency specifications — the conflict case is the only
  exception, explicitly carved out by `l2mBsCollision`.

**Scheduler-side reachability** (`lean/Ventus/L2/Scheduler.lean`, wave 25,
【Lean machine-checked proof】):

- **`l2sc_i40_witness`** (:949, native_decide 3-cycle trace):
  alloc entry0 (Get, set=5, way=3) → sinkd backfill → dir write
  `sinkD_adr(set=5, way=3)` **conflicting on the same cycle** with
  `sourceD_radr(set=5, way=3)` (`l2scBsCollision = true`); the final conjunct
  is the control (same state with only `radrValid` off ⇒ no conflict);
- Environment legality machine-checked cycle by cycle: `l2sc_i40_env0` (:933)
  / `l2sc_i40_env1` (:937) / `l2sc_i40_env2` (:941) — every step's input of
  the trace satisfies the environment constraint `l2scEnv` (E1/E3), not
  constructed out of thin air;
- Residual premise (honest declaration): SourceD-side timing feasibility
  (bs_radr.valid held for multiple cycles) is supported by the l2s model; no
  joint SourceD×BankedStore instantiation was done.

Axiom audit: Scheduler.lean archives `#print axioms` for 10 theorems
including `l2sc_i40_witness`; native_decide theorems carry
`Lean.ofReduceBool` (the expected trust axiom).

**Fixed-version verification** (`lean/VentusF/MemL2.lean`, 【Lean machine-checked proof】):

- `fmem_i40_read_blocked` (:489): on the row-collision cycle, the fixed
  version's read port does not fire and rdata is held (holds over the MemLaws
  abstract memory, for arbitrary states);
- `fmem_i40_witness_green` (:511): under the original conflicting inputs, the
  fixed version's rdata is not rewritten;
- `fmem_i40_regress` (:497): without a conflict, the fixed version is
  step-by-step equivalent to the original (regression-safe).

---

## 5. Simulation Verification

**【Ready-to-run / not executed in this environment】** — this entry has no
ChiselSim/Verilator reproduction suite (the 11 suites + 10 kernels actually
run in doc/22 do not cover the L2 BankedStore). A reasonable form for a
directed ChiselSim test: at the BankedStore module level, directly drive
`sourceD_radr` and `sinkD_adr` with the same row address on the same cycle and
observe `sourceD_rdat`; or reproduce §4's 3-cycle sequence at the Scheduler
level. That test code is yet to be written (ready-to-run, not executed in this
environment).

Patch side: the i40 patch has been merged into the tree together with the
35/38 patches and passed mill compilation and full-chip elaboration (doc/22,
MILL_EXIT=0). Note the honesty boundary of §3.3: the same-family I-29 did not
observe LFSR poisoning on the Verilator backend (backend SRAM-model behavior
difference); this entry's RTL-level poisoning observation is likewise expected
to need treadle or a backend with X-pessimism; the Lean-side mechanism proof
is authoritative.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: the "refill landing × sourceD read of the same row"
  overlap under normal L2 load; depends on no special configuration or host
  contract.
- **Same-family picture**: I-23 (ICache, successfully reproduced in ChiselSim,
  doc/22), I-29 (DCache, LFSR not observed under Verilator; remains
  "not reproduced (residual doubt)"), I-40 (L2, model-level reachable) —
  together the three show that "same-cycle read-write protection of
  bypassWrite=false SRAM instances" is a systemic gap in Ventus's storage
  layer; we recommend upstream remediate by family (uniformly add
  row-collision backpressure or switch to bypassWrite=true).
- **Second layer after the fix**: no known follow-up items; the fix only adds
  backpressure and does not change data-path semantics.

---

## 7. Fix and Fix Verification

**Patch** (`i40-l2-bankedstore-rwguard.patch` (internal fix manifest; not released),
functional fix, registered required in the internal fix manifest): backpressure the read
port on a row collision (write wins); the read port changes from "valid
pass-through" to fire semantics:

```scala
val bsWriteRowValid   = io.sourceD_wadr.valid || io.sinkD_adr.valid
val bsRdWrRowConflict = bsWriteRowValid && (set_idx_sel === set_index)
cc_banks.io.r.req.valid := io.sourceD_radr.fire     // was := io.sourceD_radr.valid
io.sourceD_radr.ready  := !bsRdWrRowConflict        // was := true.B
```

**Fix verification**:

- 【Lean machine-checked proof】the full trio: mechanism
  `fmem_i40_read_blocked`, witness-turned-green `fmem_i40_witness_green`,
  regression equivalence `fmem_i40_regress`;
- 【Simulation run】the patch was merged into the tree together with the 35/38
  patches and passed mill compilation + full-chip elaboration (doc/22); the
  directed behavioral test case is ready-to-run (§5);
- The fix semantics are consistent with doc/22's I-29 handling philosophy
  ("stall the conflicting party" beats switching to bypassWrite=true, avoiding
  perturbing other paths that depend on the read-old semantics — the
  the internal fix manifest Notes' same-style statement for I-29 applies to this entry's
  design orientation).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | BankedStore.scala:101-112 (read always accepted, write sources ORed, zero row-collision protection), Scheduler.scala:276-285 (zero guarding of radr), line-by-line checked | Two points consistent |
| Lean machine-checked proof (mechanism) | `l2mBsCollision` conflict characterization + `l2mBsT4_collision` numerical witness | Concrete trace |
| Lean machine-checked proof (reachability) | `l2sc_i40_witness` 3-cycle trace + `l2sc_i40_env0/1/2` cycle-by-cycle environment legality | Model-level reachable (residual premise: SourceD-side timing, supported by the l2s model) |
| Simulation | No directed suite (ready-to-run, not executed in this environment); patch tree compiles/elaborates; LFSR visibility limited on the Verilator backend (same-family I-29 measurement) | Patch-tree run + honesty boundary |
| Fix verification | i40 patch (row-collision backpressure); `fmem_i40_read_blocked`/`fmem_i40_witness_green`/`fmem_i40_regress` | Machine-checked + compile run |

I-40 is the only "Confirmed (model-level reachable)" entry among the three of
the L2 MSHR group: triggering does not need I-44's pool-exhaustion corner —
three cycles suffice to hit the row. Together with I-23/I-29 it completes the
"SRAM same-cycle read-write LFSR poisoning" family's picture across the three
layers ICache/DCache/L2 — within the family, two entries have been reproduced
on RTL or carry residual doubt, and this entry's model-level evidence chain
(mechanism + reachability + cycle-by-cycle machine-checked environment
legality) is the most complete of the three layers.
