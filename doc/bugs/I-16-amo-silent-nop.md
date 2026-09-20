> English translation of the Chinese master `doc/bugs/I-16-AMO静默译码NOP.md`. Translated 2026-09-13.

# I-16 Detailed Defect Analysis Report: `IDecodeLUT_A` is dead code — all LR/SC/AMO instructions silently decoded as NOP

| Item | Content |
|---|---|
| ID | I-16 |
| Source location | `ventus/src/pipeline/DecodeUnit.scala:453-468` (`object IDecodeLUT_A`: **definition** of the 11-row AMO decode table) vs `:557-570` (`ctrlSignals` table selection uses only the IMF/V/VL/VC tables; the outer opcode keys do not include `0101111`); default row `:151`; side-effect field bindings `:625-627` |
| Type | Functional bug (ISA-level missing functionality — the entire RISC-V A extension is unusable) |
| Severity | **High** (any A-extension instruction silently NOPs on synthesized hardware: LR never reserves a word, SC is not mutually exclusive, AMO has no atomic semantics; the only line of defense is a simulation-time assertion that vanishes after synthesis) |
| Confirmation status | 【Confirmed】(doc/03 originally marked it "confirmed (mechanism) / impact scope pending"; subsequently reproduced in practice at both ChiselSim module level ×2 and Verilator whole-machine level — the reproduction loop is closed); fixed version modeled and verified + behavior of the trap route verified on the 38-patch merged tree |
| Primary evidence | 【Lean machine-checked proof】`decDecode` maps the AMOADD_W/LR_W/SC_W encodings to `decDefaultRow` (3 decide theorems) + `dec_default_safe` (all 19 side-effect fields of the default row are inactive, zero axioms) + `farith_amo_falls_default` (general form over the entire opcode 0101111 space); 【simulation runs】ChiselSim `DecodeUnitAMORepro` ×2 + Verilator `i16_amo_nop` (the issue-stage assertion fires with UNDEFINED INSTRUCTION); 【direct source reading】key-by-key check of the table-selection keys in DecodeUnit.scala |
| Lean model | Original `lean/Ventus/Arith/DecodeUnit.lean` (mechanical port of the full 265-line table, generator script `lean/scripts/gen_decodeunit.py`); fixed version `lean/VentusF/Arith.lean` (decode-layer illegal flag) + `lean/VentusF/FixI16.lean` (trap routing and scheduler delivery); SM integration `lean/VentusF/SM.lean` |
| Reproduction / patch | `repro/DecodeUnitAMORepro.scala` (ChiselSim); `repro/verilator/` kernel `i16_amo_nop`; adopted patch `i16-decodeunit-amo-trap.patch` (internal fix manifest; not released) (decision D2, 6 files, 11 hunks); alternative `i16-decodeunit-amo-enable.ALTERNATIVE.patch` (not in the default series) |
| Related entries | LSU notes Q14/Q15 (downstream AMO semantics unverified — the reason ALTERNATIVE was not selected); DCache-side corroboration `dc_genControl_amo_noop`/`dc_st1Ready_amo_swallowed`; I-6/I-46 (trap reuse of the ENDPRG channel depends on their ready-gating synchronous extension) |

---

## 0. Abstract

The Ventus decoder `InstrDecodeV2` uses a two-level table-driven structure:
"outer opcode-based table selection + ListLookup inside the table". The source
code defines a complete A-extension (LR/SC/AMO) decode table `IDecodeLUT_A`
(DecodeUnit.scala:453-468, 11 rows), but **the table-selection list of
`ctrlSignals` never references it** (:557-570 uses only the IMF/V/VL/VC four
tables, and the outer opcode keys do not include `0101111`) — the table is
dead code.

Consequence chain: any A-extension instruction falls through the outer table
selection into the IMF table, finds no matching row, and falls back to the
**default row** (`alu_fn = FN_X = 63`, no register write, no memory access,
`atomic = 0`). During simulation, the `alu_fn =/= 63.U` assertion at
pipe.scala:275-286 reports "UNDEFINED INSTRUCTION" at issue time (this is
exactly what fired in the Verilator whole-machine run); **after synthesis the
assertion does not exist, and on hardware it is a silent NOP** — LR always
"succeeds" without reserving a word, SC writes are dropped, AMO has no atomic
semantics at all, and any kernel using gcc atomic builtins silently computes
wrong results.

This entry belongs to the same "inter-module interface semantic mismatch"
family as I-12, but in a simpler form: within a single module, one table was
"defined but never wired in". The evidence chain is fully closed: Lean
machine-checked proof (3 encoding decides pinned down + `dec_default_safe` +
general form over the whole opcode space) → ChiselSim module-level
reproduction ×2 (alu_fn=63 instead of 29/0, atomic=0, mem_cmd=0, wxd=0) →
Verilator whole-machine reproduction (assertion fires) → fix patch (D2,
explicit illegal-instruction trap route, 6 files) turned green in two-level
behavioral verification on the 38-patch merged tree.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **RISC-V A extension (atomic instructions)**: the atomic memory operation
  extension of the standard ISA, in two categories — **LR/SC** (load-reserved /
  store-conditional: a reserved read followed by a conditional write, forming
  the basis of lock-free synchronization primitives) and **AMO** (atomic
  memory operation: AMOADD/AMOSWAP/AMOAND/AMOOR/AMOXOR/AMOMIN(U)/AMOMAX(U),
  whose read-modify-write three steps complete atomically in hardware).
  All 11 instructions share opcode **`0101111`** and are distinguished by the
  funct5 field. Mutexes, counters, and work-stealing queues of multi-threaded
  GPU kernels all depend on them; C/C++ `__atomic_*` builtins are compiled
  into AMO/LR/SC instruction sequences.
- **Table-driven decode**: Ventus decodes each instruction into one row of 27
  control signals (`CtrlSigs`: is-vector, is-memory, alu_fn, write-back enable,
  atomic, etc.). Decode tables are written as arrays of
  `(BitPat, List[control signals])` and looked up with Chisel's `ListLookup` —
  the instruction word is compared element by element against each BitPat
  (`?` bits are wildcards), first match wins; **when no row matches, it falls
  back to the `default` row**.
- **Two-level lookup**: the outer level first selects a table by the low 7
  bits of the instruction (opcode) — vector arithmetic table V, vector memory
  table VL, SIMT custom table VC, or the IMF table for all other instructions —
  then ListLookup runs inside the selected table. The design intent of the
  default row is to catch "instructions this processor does not support".
- **Simulation assertions vs hardware**: Chisel's `assert` exists only in
  simulation; it disappears completely on synthesized silicon (and on the
  synthesized netlist). Relying on an assertion to catch "illegal
  instructions" means there is no catch at all in hardware.

### 1.2 Design intent

The 11-row table of `IDecodeLUT_A` (LR_W/SC_W/9 AMOs, with the atomic flag as
the last column), together with `FN_SWAP(28)`/`FN_AMOADD(29)` defined in
`IDecode` and the AMO datapath in the LSU (selecting the TileLink param by
alu_fn and the opcode by aq/rl, LSU.scala:241-256), form a set of **planned
A-extension support**: the decode table produces `atomic=1` and the memory
command, and the LSU is responsible for translating AMOs into TileLink atomic
operations sent to L1/L2. The design intent clearly exists — only the
table-selection step left this table out.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: definition of the A-extension decode table (intact but never wired in)**
(`DecodeUnit.scala:453-468`):

```scala
object IDecodeLUT_A{ //The last element of the list indicates whether the instruction is atomic.
  import IDecode._
  val table= Array(
    LR_W ->    List(N,N,N,B_N,N,N,CSR.N,N,A3_X,A2_X,A1_RS1,IMM_X,MEM_W,FN_ADD,N,M_XRD,N,N,N,N,N,N,Y,N,N,N,Y),
    SC_W ->    List(N,N,N,B_N,N,N,CSR.N,N,A3_X,A2_RS2,A1_RS1,IMM_X,MEM_W,FN_ADD,N,M_XWR,N,N,N,N,N,N,Y,N,N,N,Y),
    AMOSWAP_W->List(...FN_SWAP,...),
    AMOADD_W ->List(...FN_AMOADD,...),   // …11 rows in total, last column Y = atomic
    ...
    AMOMAXU_W->List(...FN_MAXU,...)
  )
}
```

The content itself is correct (LR goes through read, SC/AMO go through write,
and the alu_fn allocation is consistent with the LSU's param decode chain).
The problem is not inside the table, but outside it.

**Construct 2: the table-selection list leaves this table out** (`DecodeUnit.scala:557-570`, ★ defect point):

```scala
val ctrlSignals = (0 until num_fetch).map( i => {
  val lut = Seq(IDecodeLUT_IMF.table, IDecodeLUT_V.table,
                IDecodeLUT_VL.table, IDecodeLUT_VC.table).map { t =>   // ★ four tables, no IDecodeLUT_A
    ListLookup(io.inst(i), IDecode.default, t)
  }
  ListLookup(io.inst(i)(6, 0), lut(0),
    Array(
      BitPat("b1010111") -> lut(1),
      BitPat("b1111011") -> lut(2),
      BitPat("b0?00111") -> lut(2),
      BitPat("b0101011") -> lut(2),
      BitPat("b1011011") -> lut(3),
      BitPat("b0001011") -> lut(3)       // ★ keys do not include "b0101111" (AMO)
    ))
})
```

Opcode `0101111` matches none of the keys ⇒ the outer level falls back to the
default choice `lut(0)` = IMF table; the IMF table (RV32IMF+CSR/FENCE, 74
rows) has no A-extension rows ⇒ the inner ListLookup misses.

**Construct 3: the default row after a miss is an all-inactive NOP** (`DecodeUnit.scala:151`):

```scala
val default = List(N,X,X,B_N,X,X,X,X,A3_X,A2_X, A1_X, IMM_X, MEM_X, FN_X,
                   N,M_X, X,X,X,X,X,X,X,X,X,X,X)
```

`FN_X = 63.U(6.W)` (:61); write-back / memory / branch / CSR / fence / atomic
flags are all inactive. At the side-effect field bindings (:625-627),
`c.atomic := s(26)`, `c.aq := s(26) & inst(26)`, `c.rl := s(26) & inst(25)`
consequently all become 0 — **even the information that "this instruction is
atomic" is discarded**, and the downstream LSU AMO path is never reachable.

**Construct 4: the only line of defense is a simulation assertion** (`pipe.scala:275-286`, ★ disappears after synthesis):

```scala
// The IOs of the ibuffer2issue module are instructions actually issued but not yet executed; check undefined instructions here
when(ibuffer2issue.io.out_x.fire){
  val ctrl = ibuffer2issue.io.out_x.bits
  assert(ctrl.alu_fn =/= 63.U,
         p"UNDEFINED INSTRUCTION @ SM ${sm_id} warp ${Decimal(ctrl.wid)} " +
         p"PC 0x${Hexadecimal(ctrl.pc)}: 0x${Hexadecimal(ctrl.inst)}")
}
```

(The out_v side has the same pattern.) The assertion exists only under
simulation semantics; in synthesized hardware, an AMO decoded to the default
row is routed by issue's fallback into sALU, fake-executes for one cycle with
FN_X, and retires silently (without any write-back).

**Construct 5: the dangling downstream AMO path** (`LSU.scala:241-256`, becomes dead code):

```scala
param_wire_alt := Mux(reg_save.ctrl.alu_fn===FN_SWAP,16.U,
                  Mux(reg_save.ctrl.alu_fn===FN_AMOADD,0.U,
                  Mux(...FN_XOR/FN_AND/FN_OR/FN_MIN/FN_MAX/FN_MINU/FN_MAXU...)))
when(reg_save.ctrl.atomic){
  when(reg_save.ctrl.aq && reg_save.ctrl.rl){ opcode_wire := ... } ...
}
```

This logic — selecting the TileLink param by alu_fn and the opcode by aq/rl —
is entirely correct, but `c.atomic` is constantly 0 (construct 3), so the
whole `when(atomic)` branch is never entered.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

Defect chain (every link has evidence):

1. An A-extension instruction (opcode `0101111`, LR/SC/9 AMOs) enters
   InstrDecodeV2;
2. The outer table-selection keys do not include `0101111` ⇒ it falls into
   the IMF table (DecodeUnit.scala:561-567);
3. The IMF table has no A-extension rows ⇒ ListLookup falls back to the
   default row (:151): `alu_fn = FN_X = 63`, `atomic = 0`, `mem_cmd = 0`,
   `wxd = 0`, `isvec = 0`, no branch, no fence, no CSR — a machine-level NOP;
4. In simulation: at issue time the `alu_fn =/= 63.U` assertion in
   pipe.scala fires, reporting UNDEFINED INSTRUCTION (observed in the
   Verilator run, see §5);
5. After synthesis: the assertion does not exist, and the AMO instruction
   silently executes as a no-op — **LR does not write back the destination
   register (the program reads a stale value), SC's conditional write does
   not happen (the return value is never stored), and AMO's read-modify-write
   never occurs at all**, with no trap and no observable error.

Trigger surface: **all** A-extension instructions; a single instruction
triggers it, unconditionally, with no timing requirements. On the Lean side,
`farith_amo_falls_default` proves it holds for the **entire opcode 0101111
encoding space** (2^25 instruction words), not just a few witnesses.

### 3.2 Root cause

**An integration omission — "defined but never wired in"** — rather than any
local logic error: the decode table was written, the LSU path was written,
the TileLink param mapping was written; only the wiring list between the two
lookup levels (the `Seq(...)` at :558 and the key array at :562-568) left out
the A extension. Every component is correct under isolated review; the defect
exists only at the unclaimed seam "who wires IDecodeLUT_A into ctrlSignals".

Contributing cause: the default row's design is used simultaneously for two
semantically different situations — "intentionally unsupported instructions"
(FLW/FSD/C extension/ECALL, a design decision of zfinx and no C extension)
and "unintentionally lost instructions" (the A extension). The default row is
a correct catch-all for the former but becomes a silent swallower for the
latter; the two are indistinguishable in the code, and the only alarm
mechanism (the simulation assertion) disappears after synthesis.

### 3.3 Harm and tolerability

- **Harm**: ISA-level missing functionality + silent wrong-data direction.
  Any kernel using synchronization primitives (producer-consumer queues,
  spinlocks, atomic counters) computes wrong results and is extremely hard to
  detect — the program does not deadlock or report errors; the results are
  just quietly wrong. gcc's `__atomic_*` builtins generate AMO instructions,
  so "a software stack that never hand-writes assembly still hits this".
- **Impact scope**: doc/03 originally marked it "impact scope pending".
  Measured facts available at the time of this report: reproduced through
  both ChiselSim and Verilator channels (§5); the trigger surface = the
  entire A-extension encoding space (machine-checked proof); no configuration
  exemption.
- **Tolerability**: the current official test kernels contain no A-extension
  instructions, so neither upstream testing nor FPGA deployment exposed it —
  this is "the mine was not stepped on", not "there is no mine". Once the
  software stack enables atomic operations it is fatal. Rating: **High**.
- **Downstream corroboration (even if decode is fixed there is one more
  layer)**: for the AMO opcode (op=2), the DCache only sets `isAMO` without
  setting any read/write/maintenance bit; the AMO request falls into the
  default branch at st1 and is swallowed by an unconditional ready (Lean
  machine-checked proofs `dc_genControl_amo_noop` /
  `dc_st1Ready_amo_swallowed`). That is, "enabling" the A extension requires
  accompanying LSU/L2 semantic verification — exactly why the alternative
  AMO-enable patch is not in the default series (see §7).

---

## 4. Lean formal evidence

Original side (`lean/Ventus/Arith/DecodeUnit.lean`, full 265-line table
mechanically ported from the two Scala files by `lean/scripts/gen_decodeunit.py`,
cross-checked by an independent Python simulation as a double line of defense
before generation):

- **Three encoding pins** (:639/:641/:643, all `by decide`, kernel-level
  evidence with zero trust axioms): `decDecode 0x0062A22F = decDefaultRow`
  (AMOADD_W x4,x5,x6), `decDecode 0x100423AF = decDefaultRow` (LR_W x7,(x8)),
  `decDecode 0x18B524AF = decDefaultRow` (SC_W x9,x10,x11).
- **`dec_default_safe`** (:496, `by decide`, `#print axioms` depends on no
  axioms): all 19 side-effect fields of the default row are inactive
  (wxd/wvd/branch/csr/atomic/mul/sfu/fence/… all false, memCmd=0,
  aluFn=FN_X) — this is the precise formalization of the word "silent": an
  instruction that lands on the default row has no effect on architectural
  state.
- **Range hub `decDecode_mem`**: the decode output of any 32-bit input must be
  the default row or some row of the four tables — lifting the
  "full-table enumeration" property to arbitrary instructions.
- Incidental audit (same wave, confirmed non-bug): the four tables' BitPats
  are pairwise disjoint (`dec_overlap_imf/v/vl/vc`, native_decide);
  IDecodeLUT_A's absence from the concatenated tables is a faithful
  reproduction, not a model defect (D7).

Fixed-version side (`lean/VentusF/Arith.lean`, decode-layer model of
decision D2):

- **`farith_amo_falls_default`** (**general form**, not just a witness): any
  instruction with `farithAmoIllegal inst = true` (⟺ low 7 bits = 0x2F,
  `farith_amo_opcode`) lands on the default row under the original decode — a
  universal theorem over the entire opcode 0101111 space. Supporting lemmas:
  `farith_amo_imf_all_miss` (the entire IMF table misses on AMO low bits,
  native_decide) + `farith_match_false_of_low7` (low-bit miss ⟹ whole-word
  mismatch) + `farith_lookupEntry_default` (if the whole table misses it
  falls back to the default row, by induction).
- `farith_dec_row_unchanged` (the fixed version's control row is bit-identical
  to the original, rfl-level), `farith_dec_nonamo_regr` (non-AMO instructions
  are completely unaffected), `farith_dec_amo_flagged` (AMOs are explicitly
  flagged illegal=true).
- Witness trio: `farith_i16_witness_amoadd`/`farith_i16_witness_lr`/
  `farith_i16_witness_sc` (native_decide: dual pinning of the original
  default row + the fixed version's (default row, true)); regression spot
  checks `farith_i16_regr_add`/`farith_i16_regr_vsetvli`.

Trap delivery chain (`lean/VentusF/FixI16.lean`, corresponding block by block
to the patch, see §7):

- Routing level: `f16_route_trap` (illegal always routes to warpSched, decide
  over the full Bool space), `f16_trap_no_func_side_effect` (enters no
  functional unit), `f16_route_regr` (when illegal=false, bit-identical
  routing to the original), `f16_default_row_routes_salu` (status-quo pinned:
  the default row goes to sALU for fake execution), `f16_default_row_trap`
  (fixed version: default row + illegal → warpSched).
- Scheduler level (base = the I-5/6/7/46 fixed-version fschWs* model):
  `f16_trap_eq_endprg` (**trap ≡ ENDPRG** — formalization of the design
  point of reusing the termination channel), `f16_trap_clears_active` (after
  the trap is accepted, the warp's active bit is cleared and it no longer
  participates in fetch scheduling), `f16_trap_barData` (barrier bookkeeping
  is not polluted), `f16_trap_reported`/`f16_trap_parked` (the warpRsp trap
  flag is correct in both the pass-through and parked phases),
  `f16_ws_regr` (with no illegal instructions, step-equivalent to the base
  fixed version).
- End to end: `f16_amoadd_end_to_end` (AMOADD_W encoding → (default row,
  illegal=true) → routed to warpSched, native_decide); `f16T_trap_witness`
  (trap after warp3 is allocated: active cleared, trap reported, barData
  unpolluted, endprgCnt proceeds normally through the ENDPRG channel,
  native_decide).

SM integration observation (`lean/VentusF/SM.lean` §8):
`fsmT_i16_amo_flagged` — in the fixed version, at the fetch cycle the illegal
flag of an AMO instruction is raised combinationally (trap delivery itself is
not modeled, I-FSM-6, an ISA-level design decision).

---

## 5. Simulation verification (dual-channel real runs + trap-route verification on the 38-patch merged tree)

All real-run records are in `doc/22-复现执行结果.md`.

**ChiselSim module level** (`repro/DecodeUnitAMORepro.scala`, actually run
2026-09-06/07): AMOADD_W (encoding 0x0020A1AF, amoadd.w x3,x2,(x1)) and LR_W
(0x1000A1AF, lr.w x3,(x1)) each fed once into DecodeUnit — both land on the
default row: measured `alu_fn=63` (expected 29/0), `atomic=0`, `mem_cmd=0`,
`wxd=0`. Verdict: **reproduction succeeded ×2**.

**Verilator whole-machine level** (`repro/verilator/` kernel `i16_amo_nop`,
actually run 2026-09-07): the kernel contains one `amoadd.w x3,x2,(x10)`
(0x002521af). At the issue stage the assertion aborts the simulation (core
dumped):

```
%Error: dut.v:118022: Assertion failed in TOP...pipe:
UNDEFINED INSTRUCTION @ SM 0 warp 0 PC 0x80000014: 0x002521af
```

0x002521af is exactly that amoadd.w, decoded into the default row with
alu_fn=63 — **the simulation assertion is direct evidence of I-16 on RTL**;
after synthesis the assertion does not exist and the same instruction will
flow through silently (the README provides a degraded criterion: "if the
assertion does not abort, judge by readback value 5 vs 12").
Verdict: **reproduction succeeded** (one of 8 reproductions among the 9
target bugs).

**Trap-route behavioral verification on the 38-patch merged tree** (actually
run 2026-09-10, last section of doc/22): the original 2 cases of
DecodeUnitAMORepro encode **ALTERNATIVE (AMO-enable) expectations**
(alu_fn=29/0, atomic=1, mem_cmd=2/1, wxd=1), while i16 actually adopted
decision D2 (the trap route), so those 2 cases remain red (expected,
consistent with the 35-patch tree). The actual fixed behavior was positively
verified by two new cases, both green:

1. **Decode level** (new case in DecodeUnitAMORepro): the three A-extension
   encodings AMOADD_W/LR_W/SC_W decode with `control.illegal=1` (the patch
   sets the bit at the tail of DecodeUnit), no longer taking the silent NOP
   path;
2. **Scheduling level** (new 5th case in WarpSchedulerBugRepro): the
   warp_control event with ctrl.illegal=1 is accepted (ready=1 with fence_end
   all 1s), on the same cycle warpRsp.valid=1 with the correct wid and
   **trap=1**, and after the response fires the wg's flushDCache is issued
   normally — the full chain of trap termination reusing the ENDPRG channel
   works end to end.

---

## 6. Upstream impact analysis

- **Trigger surface**: all A-extension instructions (LR.W/SC.W/AMOSWAP.W/
  AMOADD.W/AMOXOR.W/AMOAND.W/AMOOR.W/AMOMIN.W/AMOMAX.W/AMOMINU.W/AMOMAXU.W,
  the entire opcode 0101111 encoding space — the machine-checked proof
  `farith_amo_falls_default` holds universally). No configuration switch, no
  timing condition.
- **Why upstream did not find it**: the current repository test kernels
  contain no A-extension instructions; simulation has the assertion as a
  catch (if hit, it fires immediately during simulation and a developer would
  notice) — but what the assertion protects is precisely "development-time
  simulation", while the synthesized deployment form (FPGA/silicon) has
  precisely no such protection. The Ventus official software stack's not
  using atomic operations is a usage habit, not a design exemption.
- **Software-stack reachability**: gcc/LLVM's `__atomic_*` builtins and C++
  `std::atomic` are lowered to libcalls only on targets without the A
  extension; if the compile target declares the A extension, the compiler
  generates AMO instructions directly — the software side has no defense.
- **Cost of full support after the fix**: this entry fixes only "decode
  loss". Truly enabling the A extension additionally requires AMO semantic
  verification of LSU/DCache/L2 — known unverified points: LSU note Q14
  (scalar AMO forces mask all-1s → a same-address AMO executes 32 times lane
  by lane) and Q15 (pollution risk when the release-invalidate response of an
  AMO aq&&rl tail arrives late at the MSHR), and on the DCache side
  `dc_st1Ready_amo_swallowed` (AMO swallowed in the L1 default branch). This
  determines that the default fix takes "explicit trap" rather than "enable
  AMO" (§7).

---

## 7. Fix plan and fix verification

**Decision D2 (the internal fix manifest, user approved starting with the recommended
plan)**: A-extension instructions take an explicit **illegal-instruction
trap**, replacing the silent NOP. Note: Ventus originally has **no illegal
instruction handling hardware at all** (mtvec hardwired to 0, no mepc/trap
path; the only protection is the simulation assertion in pipe.scala) — the
trap delivery mechanism is newly built by this patch and is an ISA-level
design.

**Adopted patch** `i16-decodeunit-amo-trap.patch` (internal fix manifest; not released)
(6 files, 11 hunks, designed + verified 2026-09-10):

1. `scoreboard.scala`: add an `illegal` bit to `CtrlSigs`;
2. `DecodeUnit.scala`: set `c.illegal` for opcode=0101111 (the control row
   remains the default row — no functional side effect this cycle, zero
   regression risk); IDecodeLUT_A remains un-merged;
3. `issue.scala`: insert an illegal branch at the head of the routing chain →
   `out_warpscheduler` (illegal instructions enter no functional unit);
4. `warp_schedule.scala`: extend `warp_end` with an illegal disjunct (**trap
   reuses ENDPRG's warp-termination channel**); synchronous extension of the
   I-6/I-46 ready gating (trap likewise waits for fence_end in-flight memory
   drains); barrier bookkeeping excludes illegal (trap does not count as a
   barrier arrival); add a `trap` flag to `warpRsp` (the parked register
   records it synchronously);
5. `CTA2warp.scala`: trap is sampled on response enqueue
   (`CTArspFifoEntry.trap`, same enqueue-sampling rationale as I-25) and
   delivered to the SM boundary via `CTArspData.cu2dispatch_trap`
   (corresponding to RISC-V mcause=2; host-side consumption is follow-up
   contract design, already noted in the patch comments);
6. `pipe.scala`: the issue-level FN_X assertion lets instructions already
   flagged illegal pass.

**Alternative (not in the default series)**
`i16-decodeunit-amo-enable.ALTERNATIVE.patch`: merge `IDecodeLUT_A.table`
into the table-selection Seq and add `0101111` to the outer keys — i.e.,
enable AMO. Reason for not being default: the AMO semantics of LSU/L2 are
unverified (end of §6); enabling it might trade a "silent NOP" for a
"half-working atomic operation", a worse risk direction.

**Fix verification trio**:

- Effectiveness: the Lean fixed-version theorem family (§4:
  `farith_dec_amo_flagged`/`f16_route_trap`/`f16_trap_eq_endprg`/
  `f16_trap_clears_active` + witnesses `farith_i16_witness_amoadd`/
  `f16_amoadd_end_to_end`/`f16T_trap_witness`) + ChiselSim two-level cases
  green on the 38-patch merged tree (§5: decode illegal=1 ×3 encodings +
  scheduling-level warpRsp trap=1/flush follow-up);
- Regression safety: `farith_dec_row_unchanged` (control row bit-unchanged,
  rfl) / `farith_dec_nonamo_regr`/`f16_route_regr`/`f16_ws_regr`
  (step-equivalence on the non-trigger domain); the remaining 9 suites of the
  merged-tree regression stay green (the original 2 red cases of
  DecodeUnitAMO are expected — they encode the unadopted ALTERNATIVE
  expectations);
- Compilation/elaboration: the 38-patch merged tree compiles under mill with
  MILL_EXIT=0, whole-machine elaboration passes (doc/22 / doc/02b R4 closing
  record).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | DecodeUnit.scala:453-468 (table definition)/:557-570 (table selection missing AMO)/:151 (default row)/:625-627 (atomic binding); pipe.scala:275-286 (simulation assertion); LSU.scala:241-256 (dangling AMO path) | Five source locations checked line by line |
| Lean machine-checked proof | 3 encoding decides (DecodeUnit.lean:639/641/643) + `dec_default_safe` (19 fields all inactive, zero axioms) + `farith_amo_falls_default` (general form over the whole opcode 0101111 space) | Combinational universal / full-table enumeration |
| ChiselSim reproduction | AMOADD_W/LR_W both land on the default row (alu_fn=63 instead of 29/0, atomic=0, mem_cmd=0, wxd=0) | Actually run ×2 |
| Verilator whole-machine reproduction | Issue assertion fires UNDEFINED INSTRUCTION (PC 0x80000014, inst=0x002521af i.e. amoadd.w) | Actually run |
| Fix verification | i16 trap patch (6 files, D2); Lean fixed-version theorem family + two-level cases green on the 38-patch merged tree + regression equivalence | Actually run + machine-checked proof |

I-16 is a textbook case of the "integration omission" defect family: the
decode table, the LSU path, and the TileLink mapping are each intact; only
the table-selection seam was left unwired, silently disabling the entire A
extension on synthesized hardware. Together with I-12 it supports this
project's core thesis — **semantic mismatch at inter-module interfaces is the
defect class hardest to find by simulation, and table-level audits (the
`dec_overlap_*` + `decDecode_mem` range theorems) — "universal over the whole
space" formal evidence of this kind — can systematically seal off such
unwired seams**.
