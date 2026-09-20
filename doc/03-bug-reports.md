# Bug Finding Report - Ventus GPGPU Formal Verification Project

> Classification definitions and the disposition process are in the project root
> AGENTS.md. Class I = original Chisel source; Class II = Chisel→Lean
> translation; Class III = spec/proof side. Each entry contains: source location,
> evidence, reproduction method, impact, tolerability conclusion.
> Status tags: [Pending reproduction] [Pending confirmation] [Confirmed] [Excluded].

## Class I (original Chisel source)

### I-1 [Pending confirmation] The `SIMT_STACK` class is dead code as a whole; the live implementation is `branch_join`

- **Location**: `ventus/src/pipeline/SIMT_STACK.scala:126` (`class SIMT_STACK`);
  actual instantiation site `ventus/src/pipeline/pipe.scala:129`:
  `val simt_stack = Module(new branch_join(num_thread))`.
- **Evidence**: a repo-wide search for `SIMT_STACK` finds no instantiation; the
  `simt_stack.io.pc_reconv` port referenced by pipe.scala exists only in
  `branch_join` (SIMT_STACK's io does not have it), i.e. SIMT_STACK cannot
  possibly be instantiated.
- **Impact**: no functional impact (dead code does not participate in
  elaboration); maintenance risk — the two versions have divergent semantics
  (e.g. the complete condition: `!elseOnly` in SIMT_STACK vs `takeif` in
  branch_join), so a later reader who reads the wrong file gets a wrong
  microarchitectural understanding; the file tail also has ~200 lines of
  commented-out old version.
- **Tolerability**: tolerable; suggest upstream delete it or mark it deprecated.
  For the verification project: the verification target is locked to
  `branch_join`; this record prevents mistakenly verifying dead code (a
  lesson carried over from a sister verification project).
- **Reproduction**: non-functional issue; checking the instantiation site
  suffices (the grep evidence above).

### I-2 [Mechanism real / currently unreachable] `branch_join_stack` overflow has no protection, but the stack happens to be sized for the worst case

- **Location**: `ventus/src/pipeline/branch_join.scala:24-63`
  (`branch_join_stack`); instantiation `pipe.scala:129`:
  `depth_stack = num_thread = 32`.
- **Original analysis (incorrect)**: each divergence pushes 2 entries, stack
  depth 32 ⇒ 16 levels of nesting overflow; the worst case of 31 levels of
  unbalanced divergence needs 62 entries.
- **Correction (2026-08-25, Lean model + mask-chain tracing)**:
  1. `pipe.scala:366`: vbranch's mask_init = instruction mask ∧ `out_mask`
     (⊆ current active mask); the mask is monotonically non-increasing along
     nesting.
  2. `branch_join.scala:145`: takeif always chooses the **smaller** side ⇒ after
     divergence |taken| ≤ |mask|/2; :249-256 thread_masks updates to the taken
     mask. Hence consecutive nesting on the taken path at least halves the mask
     per level: 32→16→…→2, **at most 5 levels**.
  3. Thread-by-thread peeling (peeling 1 thread per level) can only happen on
     the pushed **large-side** path, and the large side executes only after the
     taken path reaches the join and **pops the path entry first** (:57-59) —
     peeling occupies **a net 1 entry per level**. At the deepest moment of
     31-level peeling the stack occupancy = 30 (outer RPC entries) + 2 (deepest
     level) = **32 = depth_stack, exactly no overflow**. The original analysis
     wrongly added two mutually exclusive costs (2 entries/level × 31 levels
     deep).
- **Formal evidence** (`lean/Ventus/SIMT/BranchJoinOverflow.lean`, real
  parameter depth=32): the overflow **mechanism** exists — after 17 pushes
  wr=34 (the 6-bit pointer has not wrapped), level 17 writes Mem slots 32/33 →
  mod 32 aliases over level 1 (slots 0/1); witness theorems
  `bjoT5_witness_lost_join` (level-1 join lost: no pop, no jump, mask stuck at
  one thread) and `bjoT6_witness_ghost_pop` (ghost re-entry of level 17). But
  that trace has maskInit constantly all-ones, **violating the mask-halving
  discipline; unreachable under legal execution**.
- **Conclusion**: the stack is precisely sized (worst-case demand is exactly 32
  entries); the hardware has no full detection/stall/exception — a robustness
  risk rather than a functional bug. Reclassified: non-urgent; suggest upstream
  add an overflow assertion.
- **Follow-up task (closed 2026-08-27, `lean/Ventus/SIMT/BranchJoinBounds.lean`)**:
  main theorem **`bjbMain_no_overflow`** fully proved — under legal states (the
  mask discipline / takeif-smaller-side / LIFO peeling encoded as the invariant
  `bjbLegal`), after any event sequence the stack occupancy ≤ 32 = depth_stack,
  and legality is preserved (abstract protocol layer, arbitrary step counts).
  Support: the PopCount bit-level lemma family
  (`bjbPopcount_or_of_disjoint`/`bjbPopcount_partition`/`bjbTakeif_if_half`
  etc., all fully proved), tightness witness `bjbTight_peel_peak` (a 31-level
  peeling trace where wr is exactly 32 — 32 is a tight bound), concrete bridging
  `bjbWr_nop/branch/join`. Declared degradation: the full refinement from the
  concrete model to the abstract model is unproved (the required assumptions
  (1)-(4) are listed item by item in the file header; of these the two popcount
  ones are fully proved, the rest are direct source facts). "Precisely sized"
  has been upgraded from an argument to a theorem.

### I-3 [Excluded] The elseOnly branch does not raise `complete`; the scoreboard beqReg might not be cleared

- **Location**: `ventus/src/pipeline/branch_join.scala:120`:
  `io.complete.valid := (if_mask_buf.fire & opcode === 0.U & branch_ctl_buf.valid & takeif)`;
  `takeif = ((ifCnt < elseCnt) && divOccur) || ifOnly` (:145); under elseOnly
  (if_mask==0) takeif=false. Compare the dead-code SIMT_STACK.scala:211, whose
  complete condition is `!elseOnly`.
- **Related logic**: `scoreboard.scala:113` beqReg is set when a branch/barrier
  instruction is issued; `delay` (:142) contains beqReg — while set, that warp
  is blocked from issuing; one clearing path is `simt_stack.io.complete`
  (pipe.scala:254).
- **Verdict (2026-08-25, decode evidence + clearing-path analysis)**:
  `DecodeUnit.scala:473-479` — VBNE/VBEQ/VBLT/VBLTU/VBGE/VBGEU and JOIN all
  decode to `branch = B_B ≠ 0`, so beqReg is indeed set at issue. But beqReg has
  two complementary clearing paths (pipe.scala:252-254):
  `warp_sche.io.branch.fire` (the branch_back arbiter output;
  `simt_stack.io.fetch_ctl` connects to its in1, pipe.scala:388) and
  `simt_stack.io.complete`. In branch_join, the vbranch fetch_ctl trigger
  condition is exactly `!takeif || elseOnly`, complementary to complete
  (=takeif): under elseOnly, fetch_ctl must fire (jump to PC_branch) → beqReg
  cleared via branch_back; for JOIN, fetch_ctl always fires. I.e. every
  vbranch/join goes through at least one clearing path; the deadlock suspicion
  is excluded (premise: warp_sche accepts branch requests normally).
- **Residual observation**: the complete semantics differ between the two
  versions (!elseOnly vs takeif), and this correctness relies on the implicit
  contract that "fetch_ctl and complete are complementary" — fragile but
  currently holding.

### I-4 [Mechanism real / unreachable in current integration] OpColReg occupancy bit wrongly cleared on same-cycle "dequeue + new occupancy"

- **Location**: `ventus/src/pipeline/scoreboard.scala:115-118`:
  `OpColRegV.set(op_colV_in_fire)` followed by
  `OpColRegV.clear(op_colV_out_fire)` — ScoreboardUtil's same-cycle chained
  semantics is last-write-wins (proved in the Lean model as `sb_clear_wins`),
  so on a same-cycle in_fire and out_fire the occupancy bit is cleared.
- **Mechanism (real)**: same-cycle in_fire+out_fire ⇒ the occupancy bit is
  wrongly cleared; the collector layer has no same-warp deduplication
  (instDemux's widCmp is dead code, :565-568); after clearing, warp w can have
  multiple instructions inside the collector, and an all-immediate instruction
  can issue ahead of a stuck instruction (out of order). Ungated-model witness:
  `ocI4_C_issues_before_B` in `OperandCollector.lean`.
- **Unreachability argument (2026-08-27, independent
  re-review of the source chain)**: same-cycle in+out is **unreachable from reset**. The gating
  chain is fully combinational: pipe.scala:223 `ibuffer2issue.in(i).valid =
  ibuffer.out(i).valid & warp_sche.warp_ready(i)`, warp_schedule.scala:181
  `warp_ready = ~(… | scoreboard_busy | …)`, pipe.scala:161
  `scoreboard_busy = VecInit(scoreb.map(_.delay))`, scoreboard.scala:142 delay ⊇
  read_op_colV (:131, a combinational read of OpColRegV's **current register
  value**). Thus at cycle T: controlV.fire(w) requires occ(w)=0 (the register
  value at the start of T); out_fire(w) requires w's instruction to already be
  inside a CU, and when it entered the CU occ was set and is cleared only by
  out_fire ⇒ at the start of T, occ(w)=1. Both events in the same cycle require
  occ to be both 0 and 1 in that cycle — contradiction. The earlier (2026-08-25)
  reachability analysis only looked at structural possibility on the collector
  side and missed the gating side; corrected hereby (recorded as III-3).
- **Formal evidence** (`lean/Ventus/Schedule/I4Fix.lean`):
  `i4fSys_run_eq_orig` (under the gated system the fixed version is
  cycle-by-cycle equivalent to the original),
  **`i4f_no_two_busy_orig` (under the original gating the "≤1 CU busy" invariant
  holds — out-of-order is unreachable)**,
  `i4f_witness_shape_unreachable` (the I-4 witness shape is unreachable under
  gating).
- **Positioning of the fix (defense in depth, still recommended)**: if a
  pipeline stage is ever inserted into the gating chain (occ reading a stale
  value), the race becomes reachable. The fixed version (set/clear swapped,
  set-wins) has been modeled and verified: `i4f_race_gone` (occupancy bit stays
  1 on the race cycle), `i4f_set_wins` (general form), `i4f_sbRun_equiv`
  (cycle-by-cycle equivalent to the original on race-free input sequences —
  regression safety), `i4f_occ_tracks_busy` (the fixed occ precisely tracks
  collector occupancy). Broken-window control: `i4fT_race_orig` vs
  `i4fT_race_fix` (on the ungated race cycle the original occ wrongly goes to 0,
  the fixed version keeps 1). A gating-independent line of defense is still to
  restore instDemux's wid deduplication (:566).
- **Reproduction**: not reproducible under the current integration (gated
  unreachability); a directed ChiselSim test for the broken-window scenario
  (after adding a pipeline stage to the gating) is ready to be written.

### I-5 [Confirmed] When multiple wgs complete simultaneously, endprg/flush bookkeeping deadlocks (OHToUInt misused on non-one-hot input)

- **Location**: `ventus/src/pipeline/warp_schedule.scala:164-173`.
- **Mechanism**: when multiple bits of `warp_endprg_mask_0` are set (≥2 wgs'
  warp counts successively reaching zero, flush not consumed in time),
  `flush_entry = OHToUInt(mask_0)` on a non-one-hot input outputs the bitwise OR
  of the indices (e.g. wg1|wg2 → 3); `mask_0(3)=false` ⇒ `warp_wg_valid` cannot
  be cleared ⇒ `need_flush` stays true forever, the valid bit is permanently
  stuck.
- **Formal evidence** (`lean/Ventus/Schedule/WarpScheduler.lean`):
  `ws4_flush_entry_avoids` (bv_decide: mask_0 containing bit1∧bit2 ⇒
  flush_entry≠1∧≠2), `ws4_stuck_forever` (the stuck state persists after any
  length of input sequence with no new warpReq, need_flush permanently true),
  T6 concrete-trace witness (two wgs with one warp each endprg in succession;
  flushDCache.ready held for 3 consecutive cycles, valid does not move).
  Triggering does not require the same cycle — adjacent cycles suffice.
- **Impact**: flushDCache is continuously requested (performance/power);
  warp_wg_valid leaks. **Self-healing path**: CTA dispatching a new warp to the
  stuck wg can make mask_0 a singleton and flush_entry fall back to the correct
  index — but that path is blocked by I-6 (see below).
- **Tolerability**: requires multiple wgs to complete in succession within the
  flush consumption window; actual frequency depends on CTA scheduling density.
  Suggested fix: replace OHToUInt with PriorityEncoder, or scan bitwise and
  clear one by one.
- **Reproduction**: directed ChiselSim test (two wgs endprg back-to-back +
  flushDCache.ready delayed a few cycles); ready-to-run code to be added (not
  executed in this environment).

### I-6 [Confirmed] warpRsp handshake violation (valid is a single-cycle pulse, does not wait for ready); bookkeeping cascade deadlock

- **Location**: `ventus/src/pipeline/warp_schedule.scala:55` (`warpRsp.valid :=
  warp_end` is a single-cycle pulse, not satisfying Decoupled's "valid holds
  until ready"); cascade points :131/:161 (belong/cnt cleared on
  `warpRsp.fire`) vs :180 (`warp_active` cleared immediately on `warp_end`).
- **Consequence chain**: when warpRsp is lost, active is already cleared but
  belong/cnt are never cleared → that wg's lock is stuck, exp is never
  re-initialized, mask_0 is never set (flush is never issued); this also blocks
  I-5's self-healing path.
- **Corroborating evidence (known to the developers)**:
  `pipeline/CTA2warp.scala:71-74` original comment
  `TODO: Fix warp_scheduler warpRsp IO logic, which always requires ready=1` +
  the workaround `Queue(io.warpRsp, 16)` + the assertion
  `assert(io.warpRsp.ready, "...FIFO is used to satisfy it, but not enough")`.
  When the FIFO fills up (16 endprgs pile up before CTArsp consumes them),
  responses are dropped — with num_warp=8 a single generation cannot easily fill
  it, but multi-generation accumulation can; the assertion does not exist in
  synthesized hardware, so the loss is silent.
- **Formal evidence**: WarpScheduler.lean T8 witness.
- **Recommendation**: change warpRsp.valid to hold until ready (standard
  Decoupled), or register the pending response inside warp_scheduler.
- **Reproduction**: ChiselSim backpressure test (CTArsp.ready held low for 16+
  cycles while multiple warps endprg); ready-to-run code to be added.
- **Queue(16) workaround fill condition (closed 2026-08-27,
  `Ventus/CTA/CTA2warp.lean`)**: net backlog = #warpRsp.fire − #CTArsp.fire
  reaching 16 means full (`c2w5_fifo_len_delta`, `c2w6_rsp_dropped_iff_full`);
  a single generation produces at most 8 (num_warp=8); **filling requires two
  generations** (the idx_using bit is cleared the very cycle of rsp.fire, so a
  CTAreq can immediately reuse the wid and produce 8 more endprgs); the T6
  witness gives a 24-cycle fill trace (sustained CTArsp backpressure =
  cu_interface stuck in DEALLOC waiting for the host, fully reachable). After
  filling, the assertion exists only in simulation; post-synthesis the drop is
  silent; `c2w4_full_stuck_run`: FIFO full + CTArsp not consuming ⇒ idx_using
  only increases, and once all 8 slots have leaked CTAreq.ready is permanently
  0 (SM dispatch deadlock). The Queue refinement `c2wFifo_simulates`
  (⊑ AQueue 16) is on record.

### I-7 [Confirmed] When same-cycle warpReq+warpRsp target the same wg, the new warp's bookkeeping bits are lost

- **Location**: `ventus/src/pipeline/warp_schedule.scala:123-134` (belong) and
  :157-163 (cnt) — the Rsp clearing is written after the Req setting; Chisel
  last-connect-wins, so on a same-cycle same-wg event the clear overwrites the
  set.
- **Consequence chain**: the new warp's belong/cnt bits are lost → mask_0 is set
  prematurely while the wg still has active warps (premature flushDCache);
  belong lost → lock drops early → exp/cur are re-initialized by the next
  warpReq; if the new warp is already waiting at a barrier, :141 clearing
  warp_bar_data by belong misses it → **that warp is never ready (deadlock)**.
- **Formal evidence**: WarpScheduler.lean T7 witness (wg3: warp4 endprg on the
  same cycle warp5 is dispatched in; belong(3)=cnt(3)=0 while warp5 is active).
- **Trigger condition**: CTA dispatches a new warp into the same wg slot on the
  very cycle the wg's last warp endprgs — reachable when the CTA scheduler's
  slot-reuse cadence is dense.
- **Recommendation**: the same-cycle same-wg merge semantics should be
  "clear-then-set" (set wins), or delay the allocation by one cycle.
- **Reproduction**: directed ChiselSim test (same-cycle fire of warpReq/warpRsp
  on the same wg), ready to run.

### I-8 [Excluded] ibuffer's warp_end flush preempted by a same-cycle branch jump — the two events are structurally mutually exclusive

- **Location**: `ventus/src/pipeline/warp_schedule.scala:73-74` (flush
  single-wid Mux); **exclusion basis :52**:
  `io.warp_control.ready := !io.branch.fire & !io.flushCache.valid`.
- **Mechanism (original analysis)**: on the cycle warp b executes endprg
  (warp_end single-cycle pulse), warp a's taken branch triggers a flush →
  flush.bits = a → b's flush is permanently lost; residual instructions leak and
  execute after wid reuse.
- **Exclusion (2026-08-27, found while constructing the
  reproduction, then confirmed by source re-review)**:
  `warp_control.ready := !io.branch.fire & !io.flushCache.valid` (:52) — on a
  cycle where branch.fire is true, warp_control cannot fire, i.e. warp_end and
  branch jump are **structurally mutually exclusive**; the two flush sources
  never occur in the same cycle, and Mux preemption is unreachable. The original
  analysis (same-family lesson as I-4: only looked at each event's individual
  frequency, missed the enable chain's mutual exclusion) was wrong; recorded as
  the same class as III-3. The I-8 case in repro/WarpSchedulerBugRepro.scala has
  been rewritten as a **premise-check test** (verifying that both wids' flushes
  arrive on separate cycles).
- **Residual observation (note level)**: the preemption mechanism of the flush
  single-wid Mux still exists — if warp_control.ready's mutual-exclusion
  condition is ever relaxed in the future (e.g. flushCache path rework), this
  entry must be re-evaluated; the fix suggestion (change flush to a per-warp
  vector) still stands as defense in depth.

### I-9 [Excluded (bypass unreachable)] FloatRegFileBank bypass forwarding ignores the write mask; masked-off lanes read the new value instead of the old

- **Location**: `ventus/src/pipeline/regfile.scala:57-58`
  (`bypassSignal := RegNext((rsidx===rdidx)&rdwen)`,
  `io.rs := Mux(bypassSignal, RegNext(io.rd), regs.read(io.rsidx))`) vs :63-65
  (`regs.write(rdidx, rd, rdwmask)` writes per-thread mask).
- **Mechanism**: cycle N writes address X with a partial mask (lane t masked
  off, `rd(t)≠mem[X](t)`) → cycle N+1 reads X, the bypass forwards the **whole
  new row rd** (masked-off lane t also gets the new value) → cycle N+2 reads X
  again, lane t gets the old value from mem. The bypass view and the memory view
  diverge.
- **Formal evidence**: `lean/Ventus/Arith/RegFile.lean` theorem
  `rfV_bypass_mem_diverge` + tests V1/V3/V4 (mechanism pinned).
- **Impact assessment**: depends on the consumer — after the operandCollector
  reads out vector operands, whether masked-off lanes are used/written back
  under undisturbed semantics. If the downstream always masks with the same
  execution mask, there is no real impact; if there is a path where "masked-off
  lanes must keep their original value", that lane gets polluted with the newly
  written value. To be discharged when WP2 models operandCollector (same batch
  as I-4).
- **Consumer-side check (2026-08-26 source review of execution.scala)**: the
  collector/crossbar itself does not consume lane values, but the execution
  stage does — `execution.scala:447,540` (vmerge:
  `wb_wvd_rd(x) := Mux(mask(x), in1(x), in2(x))` and `wvd_mask(x):=true.B`
  writing all lanes), and all active-lane ALU consumption uses the read data of
  masked-off lanes. **The divergence, if reachable, is harmful** (not a dead
  value).
- **Reachability narrowing (2026-08-26)**: the bypass window requires "read
  address same cycle as write"; same bank+addr means same warp's same
  architectural register (allocations are disjoint), i.e. a RAW pair — the
  scoreboard busy bit blocks B until the write-back completes. If the busy clear
  cycle = the actual bank write cycle, then B's read request is at the earliest
  the cycle after the write cycle, the bypass window has passed, **unreachable**;
  if the busy clear is one cycle earlier than the bank write, it is reachable.
- **Final resolution (2026-08-27, `lean/Ventus/Schedule/Writeback.lean`)**:
  **unreachable, and under the proved protocol this bypass is dead hardware**.
  The chain is built link by link into theorems: (1) writeback.scala's
  `Queue(_,0)` and Arbiter are purely combinational (verified against chisel
  6.4.0 source); the execution unit fire cycle = the wb out fire cycle = the
  bank write cycle (rdwen=wvd&valid, operandCollector.scala:621) = the busy
  clear cycle (scoreboard.scala:110,112) — no queue/register can make the bank
  write later than the busy clear; (2) `wb_i9_gate_closed`: on the write cycle
  delay reads the register view, so B is still blocked that cycle; (3)
  `wb_i9_timing`: B's read address is presented at the earliest at W+1
  (presented combinationally on the collector accept cycle); (4)
  `wb_i9_bypass_same_cycle`: bypass forwarding happens iff read and write are
  same-cycle same-address — the window has passed; (5) main theorem
  `wb_i9_unreachable`. Control tests S3/S4: a same-cycle read is indeed
  polluted (0xAA05); the actual chain reads the correct old value.
- **Conclusion**: I-9 closed [Excluded — unreachable]. Strengthened conclusion:
  OpCol serialization (same warp) + busy blocking (RAW) make same-cycle
  same-address read-write never happen; the RegFileBank/FloatRegFileBank bypass
  has no trigger path under the current protocol (premises A1-A4 recorded in
  Writeback.lean D6; re-review is needed if collector pipelining ever breaks
  OpCol serialization).

### I-31 [Excluded] branch_join's pc_reconv valid is not gated by fire; the reconvergence point can be enqueued repeatedly

- **Location**: `ventus/src/pipeline/pipe.scala:390`:
  `simt_stack.io.pc_reconv.valid := issueV.io.out_SIMT.valid` — valid passes
  straight through, not gated by fire; pc_reconv's downstream is a
  `Queue(_,1,flow=true)`. The source carries a "todo check this" comment.
- **Mechanism**: during out_SIMT backpressure, pc_reconv.valid stays high →
  whenever the flow queue frees a slot it **re-enqueues the same simt_rpc** →
  duplicated reconvergence points (the same RPC popped multiple times), SIMT
  stack reconvergence bookkeeping corrupted.
- **Formal evidence**: review finding (Q section) in
  `lean/Ventus/Schedule/Issue.lean`; witness to be constructed.
- **TODO**: verify whether out_SIMT backpressure actually occurs (the
  consumption cadence of branch_join's fetch_ctl), and the exact semantics of
  Queue(1,flow); if backpressure exists this escalates to a functional bug.
- **Reproduction**: directed ChiselSim (backpressure out_SIMT for several
  cycles, observe the pc_reconv queue's dequeue count); ready to be written.
- **Exclusion conclusion (2026-08-27, `lean/Ventus/SIMT/PcReconv.lean`)**: two
  mechanisms stacked — (1) vbranch's out_SIMT.valid is combinationally gated by
  ready (issue.scala:121-124), so backpressure is structurally unreachable (the
  idiom itself violates Decoupled, but happens to close off the suspicion); (2)
  on the join side valid can stay high and backpressure is reachable, but
  branch_join.scala:124-138 assigns the same expression to both queues'
  deq.ready (lockstep) + Queue(1,flow=true) when full has enq.ready=!full
  (verified against chisel 6.4.0 Decoupled.scala:243-307) ⇒ the pending entry is
  not overwritten. Theorem chain:
  `pcrT_lockstep`/`pcrT_pending_stable`/`pcrT_count_equal` (enqueue counts 1:1
  on any trace, proved by induction) → main theorem `pcrMain_i31_excluded`;
  witnesses pcrW1-W5 (join backpressured 4 cycles, no duplicate enqueue).
  **Residual fragility**: the lockstep depends on "both queues' deq.ready
  assigned the same value"; a future divergence means duplication/loss —
  suggest upstream add an assertion.

### I-10 [Confirmed] RegFileBank declares SyncReadMem twice, generating an unconnected dead SRAM

- **Location**: `ventus/src/pipeline/regfile.scala:19` (outer `val regs =
  SyncReadMem(...)` in the class body) and :22 (a same-named declaration inside
  the `if (!GVM_ENABLED)` block, shadowing the outer one).
- **Evidence**: Chisel generates a memory node for the outer declaration when
  evaluating the class body; once the outer `regs` is shadowed by the inner one
  it has no connection — under both GVM configurations there is an extra 512×32
  dead SRAM (the GVM branch uses regs_gvm, and the outer one is equally idle).
- **Impact**: pure area/power waste, no functional impact.
- **Tolerability**: tolerable; suggest upstream delete the outer declaration.

### I-11 [Confirmed] Scalar bank address width computed from VGPR; cross-warp register aliasing when sgpr_base ≥ 1024

- **Location**: `ventus/src/pipeline/regfile.scala:10-12` (`rsidx/rdidx` width
  `depth_regBank` = log2Ceil(num_vgpr/num_bank) = log2Ceil(1024/4) = 8 bits) vs
  :21 (scalar bank mem depth `NUMBER_SGPR_SLOTS/num_bank` = 2048/4 = **512**
  entries, needing 9 bits). Address computation: `operandCollector.scala:606`
  (write-back `wbScaBankAddr`, 8-bit UInt addition wraps naturally) and
  `operandCollector.scala:110,122` (same formula on the read side).
- **Mechanism**: address = `(sgpr_base(w) >> 2) + (reg_idx >> 2)`, truncated to
  8 bits. When sgpr_base(w) ≥ 1024 the result ≥ 256 wraps, aliasing into a
  lower warp's register region (example: a warp with base=1792 accessing sgpr0 →
  bank address 448 mod 256 = 192 = sgpr0 of the warp with base=768). At the same
  time the upper 256 of the 512 entries are permanently unreachable (area
  waste).
- **Reachability (confirmed 2026-08-26 + allocation side pinned
  2026-08-27)**: `parameters.scala:181` `NUM_SGPR_MAX = num_sgpr = 2048`; the
  CTA allocator (cta/resource_table.scala:858 `baseaddr_sgpr_reg` → CTA2warp →
  collectorUnit's sgpr_base input) allocates across the entire 2048-slot space;
  NUM_WG_SLOT=8 supports multiple WGs resident concurrently. **Allocation-side
  evidence**: `lean/Ventus/CTA/ResourceTable.lean` T8 (`by decide`) — once the
  low region is occupied, allocation immediately yields base=1792 (right at the
  2048 upper bound); with size=1, base can reach 2047 (`rtI11max`); there is no
  <1024 restriction anywhere on the rt side. Trigger surface = "any high-base
  allocation after the low region is occupied". Contrast: on the vgpr path
  N=1024 ⇒ base≤1023 always holds (`rtV11`); the vector side has no such
  problem.
- **Impact**: cross-warp/cross-WG scalar registers overwrite each other, reading
  out other warps' data — silent data corruption.
- **Fix suggestion**: change `depth_regBank` to take log2Ceil(slots/num_bank)
  separately for SGPR/VGPR (read side, write-back side, and regfile ports
  unified); the vector bank (256 deep = 2^8) happens to have no such problem.
- **Formal evidence (closed 2026-08-26)**:
  `lean/Ventus/Schedule/OperandCollector.lean` `ocI11_witness` (sgpr_base=1792,
  reg=0 → address 192≠mathematical value 448), `ocI11_alias` (bv_decide: bases
  differing by 1024 must alias), **`ocI11_full_alias`** (bv_decide: when warp
  numbers differ by 4, the bank number + address collide completely; two warps'
  write-backs crosstalk into the same physical register), `ocI11_read_witness`
  (read side, same formula same aliasing).
- **ChiselSim reproduction**: allocate two WGs so the latter's sgpr_base ≥ 1024
  (or a single WG with 8 warps × 256 sgprs), do a scalar write-then-read on the
  high-region warp, observe data crosstalk with the low-region warp (ready to
  run).

### I-12 [Confirmed] Masked vector instructions (vm=0 and all vmerge) deadlock in collectorUnit

- **Location**: `operandCollector.scala:214` (mask read request
  `rsTypeWire(3) := 0.U(2.W)`) vs `operandCollector.scala:362-365`
  (operandArbiter only passes `rsType===1` (scalar) and `rsType===2` (vector)
  to the bank arbiters) — mask read requests with rsType=0 are filtered out by
  both arbiters simultaneously, never granted, and the crossbar never returns
  regOrder=3 data.
- **Deadlock chain**: `DecodeUnit.scala:588` `c.mask := ((~inst(25)) |
  alu_fn===FN_VMERGE) & c.isvec & !c.disable_mask` — any vm=0 vector
  instruction, plus VMERGE_VVM/VXM/VIM (DecodeUnit.scala:367-369,
  disable_mask=N forces mask=1) → collectorUnit's `!mask` branch at `:248` does
  not fire → ready(3)=0 → can only wait for bankIn regOrder=3 (:311-315) →
  which never arrives → the CU stays in s_add forever → that CU is permanently
  occupied + that warp's OpColReg is never cleared → warp deadlock.
- **Corroborating evidence (maintenance drift)**: `regfile.scala:59-61` comment
  "v0 mask is not used in the current implementation, remove it to reduce a
  read port" — the vector bank's v0 port has been tied to all-ones (i.e. the v0
  read data path is half-removed), but the decode side and the collect side are
  still designed around "mask read from the v0 register". Even if rsType were
  fixed to 2, the mask would read as all-ones (vmerge degenerates to always
  selecting vs1) — a second layer of functional error.
- **Trigger condition**: any masked vector instruction. The current repo's test
  kernels are mostly unmasked or use branch-assertion-style predicates, so this
  was not exposed; RVV compliance requires vm=0 support.
- **Formal evidence (closed 2026-08-26, two levels chained)**:
  - CU level (`lean/Ventus/Schedule/CollectorUnit.lean`): `cuWmask_deadlock` —
    masked instruction + an input sequence that never carries a regOrder=3
    return ⇒ stuck in s_add forever with control.ready=false; numeric witnesses
    `cuT_deadlock_*`.
  - System level (`lean/Ventus/Schedule/OperandCollector.lean`):
    `ocA_filter_rt0` (rsType=0 filtered by both arbiters across all banks gives
    valid=false), `ocA_no_grant3`, `ocXbar_port3_never_valid`,
    `ocI12_cu_rsType3_run` (reachable state with rsType(3)≡0), closing theorem
    **`ocI12_deadlock_system`** — an instantiation of cuWmask_deadlock under the
    real crossbar drive, with all premises discharged as system facts.
- **ChiselSim reproduction**: any vm=0 vector instruction (e.g. vmerge.vvm
  vd,vs2,vs1,v0) in a single-warp directed test; observe the CU state stuck in
  s_add and OpColReg(w) never cleared (ready to run, not executed in this
  environment).
- **Fix suggestion**: change the mask read request's rsType to 2 (vector
  channel) and restore the v0 data path; or supply the mask directly from the
  SIMT stack and delete the v0 read path (a scheme consistent with the current
  regfile).

### I-13 [Confirmed (currently unreachable)] collectorUnit's regOrder=2 branch mixes old and new control signals

- **Location**: `operandCollector.scala:303-307`: when bankIn returns
  regOrder=2, the fill method is selected by `controlReg.sel_alu3/isvec` (the
  **old** instruction's registered values), but the same cycle's imm input on an
  s_idle accept cycle comes from `io.control.bits` (the **new** instruction,
  :168-171). Within the same function, :268/:288 (rsType) and
  :271-275/:291-295 (regIdx zero test) all have accept-cycle Mux protection —
  only :303 does not; internally inconsistent.
- **Trigger condition**: a regOrder=2 bankIn return arriving on the same cycle a
  new instruction is accepted (s_idle + control.fire). Unreachable inside the
  current system (the response goes through RegNext + SyncReadMem, ≥2 cycles, by
  which time the state is already s_add and takes the registered-value path) —
  a latent bug masked by timing.
- **Evidence**: `lean/Ventus/Schedule/CollectorUnit.lean` theorem
  `cuQ129_bankInRdy_accept` (on the accept cycle bankIn(k).ready =
  !readyWire(k); at the interface level this path is **live**).
- **Impact**: if a timing change (e.g. banks changed to combinational read) made
  accept-cycle returns possible, the fill selection of A3_SD/A3_PC would be
  decoded per the old instruction, silently filling rsReg(2) wrong.
- **Fix suggestion**: change :303's MuxLookup key to the same form as :268:
  `Mux(io.control.fire, rsTypeWire path, registered path)`.

### I-14 [Confirmed] collectorUnit/operandCollector's address lookup tables are dead hardware with no consumer

- **Location**: `operandCollector.scala:89-98` (inside collectorUnit:
  `bankIdLookup` (264-entry ROM), `addrLookupScalar`, `addrLookupVector`) and
  :583-591 (the three same-named tables at the top level).
- **Evidence**: a repo-wide grep finds no reference (addresses are actually
  computed directly by the combinational formulas at :103-126/:603-606); not
  modeled in the Lean model (noted in CollectorUnit D5/D8).
- **Impact**: pure area/power waste (264-entry ROM × 8 CUs + one top-level
  copy), no functional impact.
- **Tolerability**: tolerable; suggest upstream delete them.

### I-25 [Confirmed] CTA2warp completion-response tag read late + wid reused the same cycle → completion bookkeeping misattributed

- **Location**: `ventus/src/pipeline/CTA2warp.scala:77` (`CTArsp.bits :=
  data(fifo.head.wid)` — combinationally reading `data` at dequeue) + :63/:64-66
  (wid is cleared from idx_using on the very cycle of warpRsp.fire, and can be
  reused by a new CTAreq the next cycle, overwriting `data(wid)`).
- **Mechanism**: if the response stays in the internal FIFO for ≥2 cycles
  (cu_interface's gather FSM needs ≥2 cycles per done processed;
  `cu_wf_done.ready=0` during UPDATE/DEALLOC, so residence is the norm), it
  reads the **reused new warp's tag**. Belongs to the I-5/I-6 "wid lifecycle
  bookkeeping" family but with an independent mechanism (does not require the
  FIFO to be full).
- **Consequence chain**: cu_interface takes (cu, wg_slot) by tag
  (cu_interface.scala:161) → the old WG's wf_gather_cnt is permanently short by
  1 (**never completes**: slot/resources/host notification all leak), the new
  WG is over-counted by 1 (**completes prematurely**: resources reclaimed and
  reallocated early, conflicting with warps still running).
- **Formal evidence** (`lean/Ventus/CTA/CTA2warp.lean`): T7 witness
  (native_decide: A's warp ends at wid0, the response stays resident, wid0 is
  reused by B, and at consumption tag=0x11≠0x08); mechanism theorem
  `c2wOut_tag_cons`; safety boundary `c2w7_tag_safe_next_cycle` (consumption
  within one cycle is always correct, under the premise "response wid is
  registered" contract `c2w1_alloc_rsp_no_clash`).
- **Fix suggestion**: enqueue the tag into the FIFO with the response (sample
  `data(wid)` at enqueue), instead of reading it late at dequeue.
- **Reproduction**: directed ChiselSim (CTArsp backpressured 2+ cycles while
  the same wid is re-dispatched), ready to run.
- **Downstream consequence closure (2026-08-27, `lean/Ventus/CTA/CuInterface.lean`)**:
  - T3 `cuifTi25Leak` (native_decide witness): the polluted done makes B (slot5)
    get deallocated with zero completions (resources reclaimed early), while A
    (slot2) has `cntMem=1≠2` and stays resident forever (slot/resources/host
    notification all leak) — the original consequence chain of report 03
    machine-confirmed.
  - T4 `cuifTi25Res` (**new form, residual-count amplifier**): a polluted done
    hitting the **idle** slot 7 → `wf_gather_cnt` keeps a residual 1
    (cu_interface.scala:131-136's load only writes info/valid, **not clearing
    wf_gather_cnt**) → a later WG C (numWf=2) allocated to that slot finishes
    after only 1 real done and gets deallocated early. Fix suggestion: clear the
    corresponding cnt entry at loadNew (zero cost).
  - Aside: on the UPDATE cycle the live write is unconditional — a done hitting
    an idle slot turns the idle slot into a "ghost resident" (under DEBUG the
    :191 assert fires first; post-synthesis silent).
- **Contract discharge (same batch, fully proved)**: cu_interface's
  H-CUIF-SPLIT (splits exactly numWf pieces, tag enumeration correct),
  H-CUIF-DONE (exact completion counting, under premise E2 "the done's tag
  points to a resident slot" — I-25 is exactly what breaks this premise),
  H-CUIF-DEALLOC (timing/content/no duplication); allocator's H-ALLOC-SLOT
  (only idle slots allocated, `alcInv_run`), H-ALLOC-FIT (no overcommit at the
  cache level; cache↔rt consistency is resource_table-side debt, closed by
  `rt_scan_ge_iff` et al.). All eight CtasEventOk contracts are hereby
  discharged.

### I-16 [Confirmed (mechanism) / impact scope TBD] `IDecodeLUT_A` is dead code; all LR/SC/AMO silently decode to NOP

- **Location**: `ventus/src/pipeline/DecodeUnit.scala:453-468` (`object
  IDecodeLUT_A` defines the AMO decode table) vs :556-568 (`ctrlSignals` uses
  only the four tables IMF/V/VL/VC); the outer table-selection opcode keys
  (:561-567) do not include 0101111 (AMO).
- **Mechanism**: any A-extension instruction (LR/SC/AMOADD/AMOSWAP/…, opcode
  0101111) falls into the IMF table at the outer selection, finds no row →
  decodes to the **default row** (all-invalid NOP: no write-back, no memory
  access, alu_fn=63); `c.atomic/c.aq/c.rl` are constantly 0. The AMO data path
  at `LSU.scala:241-243,256` correspondingly becomes dead code. In simulation,
  the `alu_fn =/= 63.U` assertion at pipe.scala:276-287 reports "UNDEFINED
  INSTRUCTION" at issue (**discoverable in simulation**); post-synthesis the
  assertion does not exist → **silent NOP in hardware**: LR always "succeeds",
  SC never truly excludes, AMO has no atomic semantics.
- **Formal evidence**: `lean/Ventus/Arith/DecodeUnit.lean` (full 265-line table
  mechanically ported + independent Python simulation as dual defense lines;
  generator script archived at `lean/scripts/gen_decodeunit.py`): `decDecode` on
  the encodings of AMOADD_W/LR_W/SC_W all yield `decDefaultRow` (3 decide
  pin-downs); `dec_default_safe` (all 19 side-effect fields of the default row
  are invalid).
- **Impact**: any kernel using the A extension is silently wrong in hardware
  (synchronization primitives completely fail and are hard to notice); the
  impact scope depends on whether the Ventus software stack emits AMOs (gcc
  atomic builtins generate them).
- **Tolerability/fix**: the minimal fix is to merge `IDecodeLUT_A.table` into
  the Seq at :558 (add the 0101111 key to the outer selection); if the official
  position is not to support the A extension, illegal-instruction handling
  should be changed to an explicit trap instead of a silent NOP (relying on a
  simulation assertion is dangerous).
- **Reproduction**: directed ChiselSim test of the decode unit (feed the
  AMOADD_W encoding into DecodeUnit, observe output=default row); or triggering
  the issue-level assertion. Ready to run, not executed in this environment.
- **Additional conclusion (same-wave verification, not a bug)**: the four
  tables' BitPats are pairwise disjoint (`dec_overlap_imf/v/vl/vc`, no shadowing,
  no dead rows); illegal instructions (FLW/FSD/C extension/ECALL etc.) falling
  to the default row is intentional (zfinx, no C extension); the low-5-bit
  truncation collisions of FN_* ≥ 32 are discharged item by item as harmless
  (`dec_fn_ge32_implies_vec_or_fp`: FN≥32 rows are necessarily isvec∨fp and do
  not go through the 5-bit consumers; FN_VMERGE(51)→19=FN_MINU but execution
  overrides with the full 6-bit comparison and does not consume vALU's MINU).

### I-17 [Confirmed] IntDivMod `cnt` width truncation: large dividend ÷1 gives a completely wrong quotient

- **Location**: `ventus/src/pipeline/IntDivMod.scala:56` (`cnt :
  UInt(log2Up(xLen).W)` = 5 bits) vs :46 (`iter = dLez-aLez+1`, a 6-bit value,
  up to **32**); :118 `cnt := iter` is a silent wide→narrow truncation.
- **Mechanism**: when aLez=0 (the MSB of |a| is set, i.e. |a|≥2³¹) and dLez=31
  (|d|=1), iter=32; loading it into the 5-bit cnt gives 0 → only 1 iteration
  (should be 32) → q = qSign ? all-ones : 1, r = 0. Trigger set: unsigned
  `a∈[0x80000000,0xFFFFFFFF], d=1`; signed `INT_MIN/1`. (The first review
  conjectured "iter=32 must come with |a|<|d| and be intercepted by zeroQ" —
  **false**: aLez=0 is MSB-set, not |a|=1; |a|≥|d| holds, zeroQ does not
  intercept.)
- **Formal evidence**: `lean/Ventus/Arith/IntDivMod.lean` native_decide
  witnesses: `0x80000000/1 (u) → hardware (1,0), spec (0x80000000,0)`;
  `INT_MIN/1 (s) → (0xFFFFFFFF,0)`; the trigger cones at xLen=4/8 (9/129
  combinations) pinned one by one.
- **Impact**: the DIV(U)/REM(U) instructions of the num_sfu instances at
  execution.scala:846 silently return wrong results on that input domain.
- **Fix suggestion**: widen cnt to `log2Up(xLen)+1` bits, or saturate iter at 31
  (in that case the quotient must be ±1, needing separate handling — plain
  widening is cleanest).
- **Fix verification (wave 23)**: `lean/Ventus/Arith/IntDivModFixed.lean` — a
  fixed model with cnt widened by 1 bit; the original witnesses turn green
  (`dvfT_i17_*`) + `dvf_pre_cnt_full` symbolic pin-down + regression equivalence
  `dvf_exec_eq_orig_of_safe`; the Chisel diff for upstream is in that file's
  header.
- **Reproduction**: directed ChiselSim test (reproduction code ready to run,
  archived with the wave-7 report, not executed in this environment).

### I-18 [WITHDRAWN 2026-09-07 (Class II — our model's mistranslation; the RTL is correct)] IntDivMod remainder recovery

> **Withdrawal notice**: both RTL reproduction channels (module-level ChiselSim
> and whole-chip Verilator) contradicted the model's predictions — the RTL
> produces the spec-correct remainder on all witness inputs. Line-by-line review
> found the single divergence: our Lean model had translated the wrapping add at
> `IntDivMod.scala:70` as a *widening* add, but Chisel 5/6 `+` is wrapping
> (`do_+ = do_+%`). The model has been corrected and the entire development
> re-proved (zero sorry). The analysis below is kept for the record; its
> "formal evidence" holds for the mistranslated model only, not for the RTL.
> Note the toolchain sensitivity: under Chisel ≤3 (`+` widens), the original
> finding would have been real.

- **Location**: `IntDivMod.scala:70`: `recoveryR = Mux(remIsNeg,
  aReg.tail(1).head(xLen)+dReg.tail(1).head(xLen), aReg.tail(1).head(xLen))` —
  the two (xLen+2)-bit addends are **each truncated first** to bits[xLen:1] and
  then added; the negative partial remainder (two's complement) loses its sign
  bit.
- **Mechanism**: algebraic derivation (IntDivMod.lean Q7 full formula): when
  remIsNeg=1, `commonR = |r_true| + 2^(xLen-dLez) (mod 2^xLen)`. The quotient is
  completely correct on all non-I-17 inputs; **the remainder is wrong iff
  remIsNeg=1** (error rate ≈13% at xLen=8).
- **Formal evidence**: all 512 combinations at xLen=4 and all 131,072
  combinations at xLen=8 verified against the formula with zero mismatches
  (native_decide); witnesses: `4/3 → (1,5)`, should be `(1,1)`; `-4/3 → r=-5`,
  should be -1; `0xDEADBEEF/0x1234 (u) → r=0x276B`, should be `0x76B`.
- **Impact**: DIV quotients are right, REM remainders wrong — compilers rely on
  REM when lowering `%`; any modulo that triggers the remIsNeg path is silently
  wrong.
- **Fix suggestion**: add first, then truncate: `Mux(remIsNeg, aReg+dReg,
  aReg).tail(1).head(xLen)`. **Fix pitfall (found during fix verification
  2026-08-29)**: in Chisel you must use `+%` (wrapping add) — `+` widens to
  xLen+3 bits, in which case tail(1).head(xLen) takes bits[xLen+1:2] instead of
  bits[xLen:1], turning the fix itself into a bug.
- **Fixed-version verification (2026-08-29, `lean/Ventus/Arith/IntDivModFixed.lean`)**:
  the three fixes (I-17 cnt widened by one bit, I-18 add-then-truncate, I-19
  clearing zeroQReg in s_idle) are built into the `dvfStep` variant; the
  original witnesses turn green one by one (`dvfT_i17/i18/i19_*`); regression
  safety `dvf_exec_eq_orig_of_safe` (cycle-by-cycle equivalent on the
  non-trigger domain); general correctness is exhaustive at xLen=4/8 + directed
  at 32 bits + symbolic partial lemmas (full invariants left as follow-up).
- **Fix verification (wave 23)**: `lean/Ventus/Arith/IntDivModFixed.lean` — the
  add-then-truncate fixed version; all original witnesses green (`dvfT_i18_*`,
  including 0xDEADBEEF/0x1234 and ±4/3) + exhaustive over all inputs at xLen=4/8
  + regression equivalence; the Chisel diff is in that file's header.
- **Reproduction**: same reproduction file as I-17
  (`assert(txn(c,4,3,false)==(1,1))`, hardware gives (1,5)), ready to run.

### I-19 [Confirmed] IntDivMod stale zeroQReg pollutes the remainder of an overflow transaction

- **Location**: `IntDivMod.scala:54` (`zeroQReg = RegEnable(..., state===s_pre)`,
  no reset) and :77 (`specialR = Mux(divByZeroReg||zeroQReg, rawAReg, 0.U)`).
- **Mechanism**: overflow/divByZero transactions go straight from s_idle to
  s_finish (:88-89), never passing s_pre, so zeroQReg keeps the **previous
  transaction's** old value; a previous transaction with |a|<|d| (zeroQ=1)
  immediately followed by INT_MIN÷(-1) (overflow) → r=rawAReg=0x80000000,
  whereas RISC-V mandates r=0 on overflow. A cross-transaction timing
  dependency; single-transaction tests cannot catch it.
- **Formal evidence**: theorem `div_t1_overflow` characterizes r exactly as
  `if s.zeroQ then a else 0`; `div_test_stale_zeroQ_bug2` two-transaction
  reproduction sequence (3/5 first, then INT_MIN/-1).
- **Impact**: the REM instruction returns a wrong remainder after a specific
  instruction sequence; q is unaffected.
- **Fix suggestion**: change specialR's condition to use the current-cycle
  combinational zeroQ (the transaction's actual
  `unsignedAReg<unsignedDReg`), or explicitly give 0 on the overflow path; or
  clear zeroQReg in the s_idle cycle.
- **Fix verification (wave 23)**: `lean/Ventus/Arith/IntDivModFixed.lean` — the
  chosen scheme is "clear zeroQReg in the s_idle cycle"; the two-transaction
  sequence witness turns green (`dvfT_i19_fixed`: q=INT_MIN and r=0, conforming
  to RISC-V overflow semantics) + the symbolic theorem `dvf_t1_overflow`; the
  Chisel diff is in that file's header.
- **Reproduction**: same reproduction file as I-17 (two-transaction sequence),
  ready to run.

### I-15 [Confirmed] ArrayMultiplier high-word selection misses FN_MULHSU; MULHSU returns the product's low 32 bits

- **Location**: `ventus/src/pipeline/Multiplier.scala:204-205`:
  `res = Mux(isMAC(func), mac_out, Mux(func===FN_MULH | func===FN_MULHU,
  result(2*len-1,len), result(xlen,0)))` — the high-word selection condition has
  only FN_MULH|FN_MULHU, **missing FN_MULHSU(23)**, which falls into the
  low-word branch.
- **Mechanism**: operand formation is correct (:178-179 correctly selects
  sext(a)/zext(b) for MULHSU; the commented-out mulInputFuncTable at :161-177
  proves the design intent included MULHSU high-word); only the result selection
  is wrong. Live decode path: DecodeUnit.scala:223 (scalar MULHSU), :377-378
  (VMULHSU_VV/VX) → issue.scala:110 out_MUL → execution.scala:72,188
  ArrayMultiplier. No downstream compensation.
- **Formal evidence**: `lean/Ventus/Arith/Multiplier.lean`
  `mul_mulhsu_diverges` (per source semantics = low 32 bits) and witness
  `mul_mulhsu_witness`: with a=b=0xFFFFFFFF the source outputs 0x00000001, while
  the correct high 32 bits are 0xFFFFFFFF (product 0x3FFFFFFFF00000001,
  cross-checked against an independent Python replica).
- **Impact**: scalar MULHSU and vector VMULHSU_VV/VX silently return wrong
  results (high word lost). The regular tests not exposing this indicates their
  software stack never exercises MULHSU.
- **Fix suggestion**: add `func===FN_MULHSU` to the high-word condition.
- **Reproduction**: directed ChiselSim test (feed FN_MULHSU + a=b=0xFFFFFFFF
  into ArrayMultiplier, check out.bits.result after two cycles); ready-to-run
  code to be added.

### I-20 [Confirmed (implicit contract, unreachable under current configuration)] The Booth last-row negation correction is lost at general len

- **Location**: `Multiplier.scala:62-69` (the last-row partial product
  `Cat(~s, pp_temp, t)`'s ~s lands in column 2·len, i.e. a discarded result
  bit).
- **Mechanism**: `mulPlacedSum_eq` (fully proved) characterizes it exactly:
  Σ partial products = sext(a)·sext(b) − corr(x_last)·2^(len-1) (mod 2^2len);
  when the last row's 3-bit window falls in a specific interval the correction
  term is nonzero. Exhaustive len=8 confirms that all a with the last-row window
  ∈{4,5,6} (3/8 of them) are wrong.
- **Unreachable under current configuration**: at len=33, reachable inputs
  (32-bit sign/zero extension: bit32=bit31 or bit32=0) always make corr=0
  (`mulCorr_window32_eq0`/`mul_sext33_corr0`/`mul_zext33_corr0` + 3000 groups of
  random reachable inputs all correct in Python).
- **Classification**: the module is correct only under the implicit contract
  "len odd and inputs are (len−1)-bit extended values" (upstream XiangShan has
  the same code and the same contract) — correct within the contract, not a
  current functional bug; reusing this module at other widths/without extension
  would be a landmine. Suggest upstream add a contract comment or an elaboration
  assertion.
- **Aside (Q2 fragility)**: pipeline alignment is correct at len=33
  (`mulPipe_two_cycles`: CSA converges in 4 rounds, depth==4 registers not
  instantiated, data path single stage); at len≥64 the CSA needs 5 rounds, the
  depth==4 register is instantiated, and func/cVec/valid will all be one cycle
  earlier than the product — a parameterization trap.

### I-21 [Confirmed] ShareMem request setIdx is only 8 bits; the upper 96 KB of LDS aliases the lower 32 KB byte-for-byte

- **Location**: `ventus/src/pipeline/LSU.scala:171,216` (`to_shared.setIdx` /
  ShareMemPerLaneAddr use `dcache_SetIdxBits=8` bits) vs
  `L1Cache/ShareMem/ShareMemParameters.scala:22` (SharedMemory
  NSets=sharedmem_depth=**1024**, needing 10 bits); the junction
  `GPGPU_top.scala:488` zero-extends 8→10 directly.
- **Mechanism**: LDS address bits addr(16:15) are discarded — the upper region
  [LDS_BASE+32KB, +128KB) admitted by the `is_shared` bounds check aliases the
  lower 32 KB byte-for-byte; and grouping by tag splits different 32 KB pages
  into different requests carrying the same 8-bit setIdx → **upper-region writes
  silently corrupt the lower region**.
- **Trigger condition**: LDS usage on an SM >32KB (CTA scheduling
  NUM_LDS_MAX=128KB allows it).
- **Formal evidence (closed 2026-08-27, `lean/Ventus/Mem/ShareMem.lean`)**:
  the address chain verified item by item with no interception point (ShareMem
  is a pure scratchpad, direct-mapped, no tags — ShareMem.scala:42 tag field
  commented, :63 L1TagAccess instantiation commented; setIdx's only use is the
  SRAM row address :159-171; LSU same_tag grouping only splits requests, does
  not intercept aliasing).
  - `smI21_alias` (bv_decide): two addresses differing only in addr(16,15)
    produce completely identical ShareMem addressing fields;
  - `smI21_dead_rows` (bv_decide): only the low 256 of each bank's 1024 rows are
    reachable — **of the 128KB silicon only 32KB is addressable, 96KB dead**;
  - **`smI21_witness`** (native_decide end-to-end, through the complete ShareMem
    pipeline model): t0 writes 0x70000040←0x11111111, t3 writes 0x70008040
    (+32KB upper region)←0x22222222, t6 reads 0x70000040 → reads out
    0x22222222≠0x11111111. Upper-region writes silently overwrite the lower
    region — confirmed.
- **Fix suggestion**: widen `ShareMemCoreReq_np.setIdx` to 10 bits (LSU.scala:71/171/216
  and the GPGPU_top.scala:488 junction changed in sync).
- **Reproduction**: ChiselSim/verilator: write the LDS upper region
  (≥LDS_BASE+32KB) then read the lower region, observe the data being
  overwritten (ready to run, not executed in this environment).

### I-22 [Confirmed (mechanism) / harmless in current integration] MSHRv2's to_pipe.valid violates NoWithdraw

- **Location**: `ventus/src/pipeline/MSHR.scala:106` (`to_pipe.valid =
  complete.orR && state===s_out`) and :53/:56/:62 (s_out entry/hold conditions
  all contain the current cycle's to_pipe.ready).
- **Mechanism**: s_out is entered on a cycle with ready=1, and valid rises only
  the next cycle; if ready drops at that point, :62 falls back to s_idle, and
  valid is withdrawn without firing.
- **Formal evidence**: `lean/Ventus/Mem/MSHR.lean`
  **`mshr_noWithdraw_violated : ¬ Handshake.NoWithdraw (mshrTraceOf
  mshrTrWithdraw)`** (concrete-trace witness: cycle 2 valid=1/ready=0/no fire,
  cycle 3 valid=0).
- **Downstream verdict (2026-08-27, full-chain check + machine
  proof)**: the consumption chain LSU2WB (purely combinational pass-through,
  `lsu2wb_rspFire_iff`, `lsu2wb_retract_safe`) → writeback.scala:52-59's
  0-deep Queue → :60-61 count=1 Arbiter (no cross-cycle locking) →
  operandCollector write-back ready constantly 1 — **the whole chain consumes
  only on same-cycle valid&&ready**, used is released only on fire, complete
  is held, and s_idle can re-enter s_out to re-send the same entry: nothing
  lost, nothing duplicated; harmless in the current integration.
- **Tolerability**: currently tolerable; the risk lies in a future insertion of
  a non-transparent register stage or a consumer sampling on valid. Suggested
  fix: make s_out exit fire-triggered only (remove the ready condition at :62),
  or register valid.

### I-23 [Confirmed] ICache probe×refill same-cycle same-set has no mutual exclusion; tag/data reads return LFSR random values (can lead to executing garbage instructions)

- **Location**: `ventus/src/L1Cache/ICache/ICache.scala:262` (`coreReq.ready :=
  true.B` — probe has zero backpressure, the structural root cause) +
  :145/:152/:175/:179 (the refill path `memRsp_Q.deq.fire` has no mutual
  exclusion with probe; the commented-out old code had it); the carrying
  mechanism is in `SRAMTemplate` (with bypassWrite=false, a same-cycle
  same-address read-write returns an LFSR64 value; the tag instance
  `L1TagAccess.scala:451` is configured F,T,F,F, the data instance
  `ICache.scala:84` is configured F,F,F,F).
- **Mechanism**: a missed warp replays via status=01
  (warp_schedule.scala:194-198), so a retry probe landing on the refill cycle
  is normal timing; on same-cycle same-set, st1's tag/data readout = an LFSR
  value (unrelated to the content being written).
- **Formal evidence (`lean/Ventus/Mem/ICache.lean`)**: three structural
  no-mutual-exclusion facts (`ic_coreReq_ready_true` et al.); mechanism theorems
  `ic_tag_collision_lfsr`/`ic_data_collision_lfsr`; reachability witness
  `icTA_collision_reachable` (constructed in 3 cycles from reset). Two
  machine-proved harmful consequences:
  - **False miss**: `icTA_false_miss`+`icTA_duplicate_alloc` — the tag is
    already written but still judged miss; duplicate MSHR entry allocation,
    duplicate memory access (this configuration writes identical data, so
    performance loss without data corruption).
  - **False hit (data corruption)**: `icTB_false_hit`+`ic_false_hit_st1` — when
    the probe's tag happens to match the LFSR's low 17 bits, a HIT + LFSR
    garbage instruction word is returned for an address **never cached**, and
    the warp executes garbage instructions. The LFSR sequence is deterministic,
    so collisions are deterministic (probability depends on the tag value
    distribution). The control group `icTC_clean_hit` proves collision is a
    necessary condition.
- **Impact classification**: instruction data corruption, triggerable under the
  current configuration.
- **Fix suggestion**: restore probe×refill mutual exclusion (backpressure
  coreReq on refill cycles), or change the two SRAMTemplate instances to
  bypassWrite=true (forwarding the correct write data instead of LFSR).
- **Reproduction**: directed ChiselSim (single-warp miss followed by a retry on
  the same set in the same cycle as the refill; observe st1 tag and icRspData),
  ready to run.

### I-24 [Confirmed] ICache ReplacementUnit input missing Reverse; two-way set-associative degenerates to direct-mapped

- **Location**: `ventus/src/L1Cache/L1TagAccess.scala:496` (the ICache version
  of `Cat(way_valid(...))` lacks `Reverse`; compare the DCache version at :297
  which has it).
- **Mechanism**: `indexWhere` scans from bit0 (=way1) — when way0 is occupied
  and way1 is free, the victim is wrongly chosen as way0: the second block in
  the same set always evicts the first, and way1 stays empty forever.
- **Formal evidence**: `icVictimMask_way0_valid_only` (fully symbolic proof) +
  `icTD_victim_thrash` (witness: two same-set blocks alternately refilled always
  miss) + `ic_way1_never_valid` (invariant fully proved: way1 is invalid after
  any input sequence).
- **Impact**: the ICache effectively degenerates to direct-mapped — two same-set
  blocks ping-pong and always miss; instruction-fetch performance degrades (the
  ICache is read-only, so no data corruption).
- **Fix suggestion**: change the `Cat(...)` at :496 to `Reverse(Cat(...))`
  (aligned with the DCache version).
- **Reproduction**: ChiselSim: alternately fetch two same-set addresses; observe
  way1 constantly 0 and the hit rate.

### I-26 [Confirmed (mechanism) / most likely masked in current integration] L1MSHR's missReq.ready is inconsistent with st0 backpressure; a secondary miss can lose the request and pollute targetInfo

- **Location**: `ventus/src/L1Cache/L1MSHR.scala:295` (missReq.ready) vs
  :247-265 (mshrStatus_st0); :274's st1_w recomputation condition only covers
  `st1_r∈{0,1}`, missing the case `SECONDARY_AVAIL(2)` where the matched row's
  subentries are already full; :354's elsewhen only hangs on se=1 (a full row's
  indexWhere defaults seIdx=0); :299-301 targetInfo write has no state gating.
- **Mechanism**: when a secondary miss matches a row whose subentries are full,
  `missReq.ready=1` while `st0=3` (backpressure) — under Decoupled semantics the
  consumer fires upon seeing ready: the subentry set does not take effect
  (**the request never gets a response, lost**), and at the same time the
  targetInfo write overwrites the existing subentry0 (response routing
  information polluted).
- **Formal evidence** (`lean/Ventus/Mem/L1MSHR.lean`): a witness reachable in
  three cycles from the initial state (`l1mT7_ready_inconsistent`/
  `l1mT7_reqLost`/`l1mT7_tiCorrupt`, native_decide) + the symbolic
  `l1m_q1_ready_inconsistent`.
- **Tolerability**: most likely masked under the current DCache integration —
  st0 is predictive (:248/:256 count missReq.valid into full), coreReq
  acceptance is intercepted at st0∈{1,3} (DCache.scala:212-219), coreReq_Q is 1
  deep, and the third same-block request is always blocked first on the st0
  side; but any consumer that "trusts missReq.ready" (legitimate under
  Decoupled) triggers it.
- **Fix suggestion**: widen :274's recomputation condition to any st1_r, or fold
  the negation of `secondaryMiss && subEntryFull` into :295's ready.
- **Counterpart conclusion (good news)**: L1MSHR's missRspOut goes through a
  1-deep pipe queue; NoWithdraw and Stable both hold unconditionally
  (`l1m_rspOut_noWithdraw`/`l1m_rspOut_stable`) — unlike I-22 (MSHRv2
  withdrawal), this module's handshake is compliant.

### I-27 [Confirmed] DCache ReplacementUnit evicts MRU instead of LRU on a full set

- **Location**: `ventus/src/L1Cache/L1TagAccess.scala:426` (minIdxTree
  candidates assembled in reversed order) and :364 (`idxOfMin` is a
  reversed-coordinate value, not mapped back).
- **Mechanism**: when choosing a victim on a full set, candidate indices are
  compared in reversed coordinates and never restored → the one chosen is
  exactly the **most recently used** way (MRU), the opposite of the LRU intent.
- **Formal evidence** (`lean/Ventus/Mem/L1TagAccess.lean`):
  `l1ta_replD2_full_evicts_mru`/`l1ta_replD2_full_ne_lru` (bv_decide, fully
  symbolic) + numeric witnesses; the fixed version `l1ta_i24_fix_correct` is
  verified alongside (victimIdx changed to `(way-1) - idxOfMin`).
- **Impact**: hot sets ping-pong-evict the just-used line; the hit rate
  collapses; no data corruption (performance bug).
- **Fix suggestion**: `victimIdx := (way-1) - idxOfMin` (or fix the candidate
  assembly order).
- **Reproduction**: directed ChiselSim (access in a known LRU order after
  filling a set, then trigger an eviction and observe the victim choice), ready
  to run.

### I-28 [Confirmed] dirtyMaskPerCL_init: multiple lanes of the same blockOffset overwrite each other, dropping earlier lanes' bytes (L2 data loss)

- **Location**: `L1TagAccess.scala:241-245` (dirtyMask initialization written
  lane by lane, overwriting) and DCache.scala:267 (TagAccess uses the un-remapped
  perLaneAddr; whereas DCache.scala:111-133's remapDataPerWord exists precisely
  to merge multiple lanes of the same word).
- **Mechanism**: dirty bytes of multiple lanes at the same blockOffset overwrite
  each other; earlier-written lanes' bytes are lost → the dirty bitmap is too
  small → write-back omits dirty bytes (data-corruption direction).
- **Formal evidence**: `l1taT_dmBuild_overwrite_real` (overwrite witness at the
  real 32-lane × 32-block scale).
- **Reachability (discharged in the DCache wave 2026-08-27: confirmed
  reachable)**: the LSU side emits perLaneAddr straight from the address with no
  same-word merging (LSU.scala:273-279) — a vector SB store at adjacent
  addresses produces two active lanes with "same blockOffset, different bytes";
  DCache.scala:267 feeds the un-remapped perLaneAddr into TagAccess's dirtyMask
  path, while the remap merge (:104-134) only serves the data path
  (:410/:617) — **the data/dirty-bit paths are inconsistent**. Machine proof
  `dcT_i28_asymmetry` (lean/Ventus/Mem/DCache.lean): under the same input, the
  data-path mask has both lanes present (0b0011) while dirtyMask keeps only the
  later lane's byte → replacement/flush writes back to L2 with bytes missing
  from the mask → **stale bytes left in L2, data lost**.
- **Fix suggestion**: reuse the remap merge (OR of multiple lanes of the same
  word) for the dirtyMask path, or make TagAccess use the remapped
  addresses/masks.
- **Reproduction**: ChiselSim: adjacent-address vector SB store followed by
  evict; read back from L2 and compare (ready to run, not executed in this
  environment).

### I-29 [Confirmed] DCache victim write-back data can be polluted by SRAM LFSR random values

- **Location**: `DCache.scala:623` (`probereadAllocateWriteConflict` only
  intercepts "coreReq.fire on the same cycle as allocateWrite") — no
  interception for a write request that **entered st1 the previous cycle and is
  stalled there because missRspOut occupies the response channel** (:445); the
  collision site: :648 (writeHit_st1 write port) × :579-583
  (dataReplaceReadValid read port), same (set,way) in the same cycle, with the
  SRAM instances at :637-659 configured bypassWrite=false.
- **Mechanism**: a write request's stall cycle coincides with a
  memRsp-triggered allocateWrite → same-address SRAM read-write in one cycle →
  the read returns an LFSR random value → `dirtyReplace_st1.a_data` (:764) →
  **the victim write-back data to L2 is polluted with garbage**. Same family as
  I-23 (ICache LFSR), but here it is **write-back data corruption**.
- **Formal evidence**: `dc_fire_excludes_allocWrite` (characterization of the
  original interception scope), `dcT_w1_collision_reachable` (three-cycle
  reachability witness), `dcT_w1_sram_lfsr` (readout = LFSR value 0x43B2A190,
  interfacing with `sram_lfsr_bypass`).
- **Impact**: when evicting a dirty line, L2 receives random data — silent data
  corruption. I-27 (MRU eviction) enlarges its trigger surface (any way can be
  chosen).
- **Fix suggestion**: fold "st1 holds a stalled write" into
  probereadAllocateWriteConflict's interception condition, or change the
  DataAccess instance to bypassWrite=true.
- **Reproduction**: ChiselSim: a "load miss refill + same-set stalled store"
  sequence; observe the victim write-back data (ready to run).

### I-30 [Confirmed] DCache flush/invalidate response metadata confusion (memRspIsFluOrInv lacks a valid qualifier)

- **Location**: `DCache.scala:425` (`memRspIsFluOrInv` lacks a valid qualifier) —
  after memRsp_Q consumes a hintAck, the head-of-queue register keeps
  d_opcode=2 resident; :754 is the only production point of the flush/invalidate
  coreRsp; :695-699 the ghost-entry mechanism.
- **Mechanism**: the second and subsequent flush/invalidate's `waitforL2flush`
  is spuriously cleared for one cycle by the resident queue head
  (`dcT_w2b_early_clear`) → st1 is let through early and ghost presetting stops
  → when the real hintAck arrives, coreRsp_st2 is already occupied by an
  intermediate response → **flush(5)'s response carries load(3)'s instrId**
  (`dcT_w2b_stale_instrId`). Accounted by instrId through the Coalscer
  (pipeline/MSHR.scala:50-71) → pollutes other instructions' entries / the
  target instruction never completes.
- **Related variant (Q2c)**: when hintAck coincides with another response in the
  same cycle, the OR merge at :754 makes the **flush response lost as a whole**
  (`dcT_w2c_rsp_lost`) — if that invalidate is an AMO's trailing release (same
  instrId as the AMO), the AMO never completes in the Coalscer → hang.
- **Tolerability**: flush/invalidate is infrequent (CTA boundaries), but once
  triggered it causes bookkeeping confusion/hang; fix suggestion: add the valid
  qualifier at :425 + make the response arbitration at :754 mutually exclusive.
- **Reproduction**: ChiselSim: two consecutive invalidates; observe the second
  response's instrId (ready to run).

### I-32 [Confirmed] fcsr (0x003) is in the read table but the write chain has no branch; csrrw/csrrs fcsr is silently dropped

- **Location**: `ventus/src/pipeline/CSR.scala` — fcsr(0x003) is in the read
  Lookup table at :254, but the write chain (:257-295) has no corresponding
  branch.
- **Mechanism**: RISC-V requires writing fcsr to update both frm (high 3 bits)
  and fflags (low 5 bits); in this implementation writes to fcsr are silently
  dropped (separate write paths for frm/fflags exist), and reads return the old
  value.
- **Formal evidence**: `lean/Ventus/Arith/CSR.lean` `csr_fcsr_write_ignored`
  pins it down.
- **Impact**: any software that writes the rounding mode/flags via fcsr as a
  whole (glibc math library, debuggers) silently fails.
- **Fix suggestion**: add an fcsr branch to the write chain (splitting the write
  into the frm/fflags fields).

### I-33 [Confirmed] The vector CSR state (vl/vstart/vcsr/vlenb/vxrm/vxsat) is dead state as a whole

- **Location**: `CSR.scala:262-264` — the isvec write branch only changes the
  write-back data to min(AVL,VLMAX); **the vl register is never written**;
  vl/vstart/vcsr/vlenb/vxrm/vxsat addresses are not in the read table.
- **Mechanism**: the effect of vsetvli-class instructions is reduced to writing
  back min(AVL,32); vl is constantly 0 and unreadable — the vector-length state
  does not persist. Ventus's current design fixes num_thread at 32 (VLMAX=32),
  the vector length being fixed in hardware; software reading vl gets 0, an
  "observable violation".
- **Formal evidence**: `csr_vl_write_ignored` + `csr_vl_read_zero` +
  `csr_isvec_no_state` + `csr_step_dead_vcsr`.
- **Impact**: software that depends on reading vl (strip-mining loops of
  standard RVV code) is silently wrong; Ventus's custom flows that do not read
  vl are unaffected.
- **Tolerability**: tolerable under the current Ventus software stack (fixed 32
  lanes); must be fixed for RVV-compatibility goals.
- **Aside (note level)**: CTA-issued registers and vtype CSR writes are silently
  ignored with no illegal-instruction exception (mtvec constantly 0, no trap
  mechanism); seven registers have no reset values; vtype constantly 0x10;
  misa/mcycle read as 0 (no consumer).

### I-34 [Pending confirmation] The AXI product top ties ICache invalidate to false — no hardware flush for same-address reuse across kernels

- **Location**: `ventus/src/top/GPGPU_top.scala:136` (GPGPU_axi_top ties
  `icache_invalidate` to false; only the SimWrapper top exposes this port).
- **Mechanism**: the product-level (AXI) top never flushes the ICache — the
  previous kernel's instructions remain in the ICache, and a new kernel reusing
  the same addresses (same load base) with a tag collision will hit old
  instructions. Against the backdrop of I-23 (LFSR false hit) already confirmed,
  the boundary of instruction-fetch correctness tightens further.
- **Formal evidence**: `lean/Ventus/Top.lean` wiring contract (the tie-down fact
  is rfl-level).
- **To be determined**: whether the host driver avoids this by other means
  before each kernel launch (e.g. rewriting the entire address space / different
  bases); if the host side has no such discipline, escalate to [Confirmed].
- **Fix suggestion**: expose icache_invalidate at the AXI top and drive it at
  kernel boundaries.

### I-35 [Confirmed] L2 Directory flushCount stuck at 1024: the second flush scans out of bounds

- **Location**: `ventus/src/L2cache/Directory_test.scala:144-148`:
  `when(io.flush || io.invalidate || (flush_issue_reg && (io.result.fire || !RegNext(dirty)))) { flushCount := flushCount+1 }.elsewhen(flushDone) { flushCount := 0 }` —
  the increment branch takes priority over the clear branch; on the flushDone
  cycle the increment condition still holds ⇒ flushCount stops at 1024 and never
  resets (the source at :149 carries `//todo not sure`).
- **Mechanism**: a first flush on an all-clean cache always triggers this; the
  first flush appears to complete (last_flush is emitted normally), but **the
  second flush starts scanning from 1024**: flush_set=64..127 is out of bounds
  (status dynamic subscript undefined, SRAM address truncated), and during the
  1024 out-of-bounds cycles dirty lines are not written back.
- **Formal evidence**: `lean/Ventus/L2/Directory.lean` machine-proved witnesses
  `l2dT_flush_count_stuck` / `l2dT_flush_second_outofrange` (re-verified against the source).
- **Impact**: scenarios that rely on flush for coherence maintenance (kernel
  boundaries/coherence windows) leave dirty data stranded in L2.
- **Fix suggestion**: swap the two when branches (flushDone takes priority), or
  add `!flushDone` to the increment condition.

### I-36 [Confirmed] L2 Directory: write.valid pollutes status during flush — false hit

- **Location**: `ventus/src/L2cache/Directory_test.scala:192`: the status write
  branch uses `io.write.valid && ...` (should be `io.write.fire`).
- **Mechanism**: Scheduler.scala:227 holds the MSHR's dir write request with
  valid high waiting for ready; during flush the Directory does not accept
  writes (ready=0) but the status branch only looks at valid ⇒ status is set
  valid while the tag array is not written ⇒ after the flush ends, accesses to
  tag=0 addresses get a **false hit on a line that was never allocated**, and a
  Get returns wrong data.
- **Formal evidence**: `lean/Ventus/L2/Directory.lean` machine-proved witnesses
  `l2dT_write_during_flush_corrupts` / `l2dT_flush_false_hit` (re-verified against the source).
- **Impact**: when flush and miss allocation run concurrently, reads return
  garbage data; same "false hit" family as I-23.
- **Fix suggestion**: change `io.write.valid` to `io.write.fire`.

### I-37 [Confirmed] L2 SourceD `PutFullData && PutPartialData` is always false (should be ||) — mshr_wait disabled

- **Location**: `ventus/src/L2cache/SourceD.scala:142`:
  `when(s1_req.opcode === PutFullData && s1_req.opcode === PutPartialData)` —
  an equality conjunction of two different opcodes, constantly false.
- **Mechanism**: when a write miss does not allocate, `mshr_wait_reg` is never
  set ⇒ the blocking protection of the victim way is lost (Scheduler.scala:133
  broadcasts mshr_wait to all MSHRs as a way-occupancy barrier); compare
  :103/:218 where the same condition is correctly written with `||`.
- **Formal evidence**: `lean/Ventus/L2/SourceD.lean` machine proof
  `l2s_putput_and_false` (constantly false) + witness
  `l2sT_mshr_wait_put_miss` (re-verified against the source).
- **Impact**: when a write miss and a victim eviction run concurrently, an MSHR
  can initiate a new allocation on a way being evicted — a data race (depends on
  concrete scheduling timing; the impact scope awaits quantification by
  Scheduler modeling).
- **Fix suggestion**: change `&&` to `||`.

### I-38 [Confirmed] L2 SourceD stage_8 under backpressure: response payload overwritten (decoupled violation)

- **Location**: `ventus/src/L2cache/SourceD.scala:82` (`s_final_req =
  RegNext(s1_req)` with no enable), :193-196 (the last clean-flush item enters
  stage_8 and the same cycle sets `busy := false.B`), :105 (`io.req.ready :=
  !busy`), :264-269 (the d-channel payload is taken combinationally from
  s_final_req).
- **Mechanism**: while stage_8 waits for d.ready, busy is already cleared ⇒
  req.ready rises ⇒ a new request fires and rewrites s_final_req ⇒ **the pending
  HintAck's payload is rewritten during valid&&!ready**: the HintAck is lost,
  and the new request's response is emitted early and will be re-sent later
  (response both lost and duplicated).
- **Formal evidence**: `lean/Ventus/L2/SourceD.lean` machine-proved witnesses
  `l2sT_stage8_accepts_req` / `l2sT_stage8_payload_clobber` (re-verified the wiring chain :82/:105/:193-196/:264-269 against the source).
- **Impact**: when d-channel backpressure actually exists (arbitration of the
  downstream shared D channel), the flush completion signal is lost, and the
  waiting upper level hangs or its bookkeeping is confused.
- **Fix suggestion**: do not clear busy when entering stage_8 (consistent with
  the about_to_not_busy design at :103), or add an enable to s_final_req so it
  updates only when nothing is pending.

### I-39 [Mechanism real / proven unreachable (Scheduler side)] L2 MSHR allocate×a.fire priority inversion; the new request's Get is never emitted

- **Location**: `ventus/src/L2cache/MSHR.scala:110-115`:
  `when(io.schedule.a.fire) { sche_a_valid := false }.elsewhen(io.allocate.valid) { sche_a_valid := true }` —
  a.fire takes priority over allocate.
- **Mechanism**: when the Scheduler reallocates an MSHR whose sche_a_valid is
  still 1 and a.fire occurs in the same cycle, the new allocation is swallowed
  by the elsewhen: sche_a_valid stays false ⇒ the new request's outgoing Get is
  never emitted, and the MSHR hangs (occupying an entry with no response).
- **Formal evidence**: `lean/Ventus/L2/L2MSHR.lean` witness
  `l2mT_alloc_fire_collision` (re-verified :110-115 against the
  source).
- **Reachability discharge (wave 25, proven unreachable)**:
  `lean/Ventus/L2/Scheduler.lean` `l2sc_i39_no_alloc_afire` — the invariant
  `l2scInv1` (ListBuffer free slot ⇒ scheAValid=0) is preserved by induction
  (`l2sc_inv1_init/preserved/run`, under the environment assumption E3:
  allocate hit ⇒ push accepted); an allocated entry cannot have a.fire in the
  same cycle.
  **Qualification (wave-27 revision): E3 has been falsified (see I-44) — in the
  ListBuffer-pool-exhausted corner this discharge does not hold;
  `l2dc_e3_inv1_broken` machine-proves l2scInv1 broken. Outside E3's validity
  range (pool not exhausted) the conclusion still stands.**
- **Fix suggestion**: swap the two branches (allocate takes priority).

### I-40 [Confirmed (reachable at model level)] L2 BankedStore has no conflict protection for read-write of the same row — LFSR poisoning of read data

- **Location**: `ventus/src/L2cache/BankedStore.scala:101-110`:
  `io.sourceD_radr.ready := true.B` (reads always accepted) + the write port
  `w.req.valid := sourceD_wadr.valid || sinkD_adr.valid` — no protection at all
  for same-cycle "read row = write row"; with SRAMTemplate bypassWrite=false, a
  same-cycle same-address read returns an LFSR64 random value (this semantics
  already pinned down in this project's SRAMTemplate.lean).
- **Mechanism**: a sourceD read (fetching data for eviction/refill) and a sinkD
  write (a memory response landing) hit the same row in the same cycle ⇒ the
  read data is randomly poisoned ⇒ the data written back to memory or refilled
  to L1 is wrong. Same family as I-23/I-29, but what is corrupted here is the
  L2 data path.
- **Formal evidence**: `lean/Ventus/L2/L2MSHR.lean` conflict-detection function
  `l2mBsCollision` + witness `l2mBsT4_collision` (re-verified
  :101-110 against the source).
- **Reachability discharge (wave 25, reachable at model level)**:
  `lean/Ventus/L2/Scheduler.lean` `l2sc_i40_witness` (native_decide 3-cycle
  trace: alloc entry0 (Get, set5, way3) → sinkd refill → the dir write
  sinkD_adr(set5,way3) conflicts with sourceD_radr(set5,way3) in the same
  cycle); Scheduler.scala:276-285 has zero protection for radr; sinkD_adr and
  the sourceD read port are fully independent; mshr_wait blocks only schedule.a,
  not dir writes. Environment legality machine-proved cycle by cycle
  (l2sc_i40_env0/1/2). Residual premise: SourceD-side timing feasibility (the
  l2s model corroborates that bs_radr.valid persists for multiple cycles).
- **Fix suggestion**: gate radr.ready with "not the same row as an in-flight
  write", or change the cc_banks instance to bypassWrite=true.

### I-41 [Mechanism real / proven unreachable (under condition E1)] L2 MSHR same-cycle priority family: allocate×sinkd, merge×sinkd

- **Location**: `ventus/src/L2cache/MSHR.scala:143-147` (when allocate and sinkd
  coincide, sink_d_reg is set to 1 by the later write) and :81-87 (data_reg
  priority allocate>merge>sinkd).
- **Mechanism**: allocate×sinkd in the same cycle ⇒ the new entry gains
  d-response eligibility without having received a memory response (witness
  `l2mT_alloc_sinkd_collision`); merge×sinkd in the same cycle ⇒ the Grant data
  is discarded (witness `l2mT_merge_sinkd_priority`).
- **Reachability discharge (wave 25, proven unreachable)**:
  `lean/Ventus/L2/Scheduler.lean` `l2sc_i41a_no_alloc_sinkd` (alloc ⇒ valids=0,
  E1 (sinkD responses only target active entries) ⇒ contradiction) and
  `l2sc_i41b_no_merge_sinkd` (merge ⇒ sinkDReg=1, E1's first response ⇒
  sinkDReg=0, contradiction).
  **Qualification (wave-27 revision): E1 has been established as a theorem but
  its residual premise contains a per-cycle E3 (Discharge.lean
  `l2dc_e1_step/run`); in the corner where E3 is falsified (I-44), repeated A
  from the same source ⇒ duplicate AccessAckData ⇒ the allocate×sinkd /
  merge×sinkd collisions become reachable again. Outside E3's validity range the
  conclusion still stands.**
- **Fix suggestion**: add a mutual-exclusion assert inside the module; when
  fixing upstream, handle it together with I-39.

### I-42 [Confirmed] L2 Scheduler's mixed flag lacks the tagMatches.orR guard — silent cache-insertion failure

- **Location**: `ventus/src/L2cache/Scheduler.scala:214`:
  `m.io.mixed := directory.io.result.valid && (OHToUInt(tagMatches)===i) && (result.opcode =/= status.opcode)` —
  **the `tagMatches.orR` guard is missing**; OHToUInt(0)=0 ⇒ any directory
  result (hit or no-match miss), as long as its opcode differs from entry 0's,
  wrongly marks entry 0 as mixed.
- **Mechanism**: once mixed_reg is set, only allocate can clear it
  (MSHR.scala:128-132) ⇒ sche_dir_valid can never be set (MSHR.scala:123) ⇒
  that entry's refill **writes neither the directory nor the bankedStore**
  (Scheduler.scala:276 uses schedule.dir.valid as the write enable). Trigger
  sequence: while entry0 holds a Get miss waiting for refill, any Put hit/miss
  result flowing out triggers it (a common overlap).
- **Impact analysis**: data is not corrupted — refill data goes straight to L1
  via sinkd (the data_reg path is correct), and the directory and data arrays
  still hold the victim's old content, self-consistently; the consequence is a
  **silent cache-insertion failure** (subsequent accesses to the same block miss
  repeatedly). Functional correctness is unharmed; performance suffers; if any
  upper layer relies on "L2 hit" for coherence decisions, re-review is needed.
- **Formal evidence**: `lean/Ventus/L2/Discharge.lean` (wave 27) witness
  `l2dc_i42_witness`: after a Get miss allocates entry0, any no-match Put
  result wrongly marks mixed in the same cycle; the refill is received
  (sinkDReg=1) but scheDirValid is permanently 0 ⇒ neither directory nor
  bankedStore is written; the control group (result opcode=Get) writes dir
  normally. Five-cycle environment legality machine-proved cycle by cycle.
- **Fix suggestion**: add the `tagMatches.orR &&` guard at :214.

### I-43 [Confirmed] L2 Scheduler miss-dirty's result.ready lacks drb.enq.ready — dirty victim write-back lost

- **Location**: `ventus/src/L2cache/Scheduler.scala:246-252`:
  `directory.io.result.ready := Mux(hit, dir_result_buffer.enq.ready, requests.io.push.ready)` —
  miss-dirty (hit=0, dirty=1) takes push.ready, **not including
  drb.enq.ready**; while drb.enq.valid does include the dirty condition (:246).
- **Mechanism**: when dir_result_buffer is full, a miss-dirty result is consumed
  normally (allocate is still issued, push still lands) but the enq is dropped ⇒
  the dirty victim's write-back (SourceD takes the victim from drb to write back
  to memory) is lost ⇒ after the refill overwrites the victim way, memory holds
  stale data ⇒ subsequent reads of the victim block get **stale data
  (data-correctness level)**.
- **Formal evidence (wave 27, three legs machine-proved reachable)**:
  `lean/Ventus/L2/Discharge.lean` `l2dc_i43_witness` (Scheduler leg: drb full ×
  miss-dirty result in the same cycle, the enq enable false but push/allocate
  still issued; result2's victim write-back information never enqueued) +
  `l2dc_i43_dir_results` (Directory leg: consecutive miss-dirty results can be
  produced) + `l2dc_i43_sourced_busy` (SourceD leg: under a backpressure the drb
  deq window is blocked for ≥3 cycles).
- **Fix suggestion**: for miss-dirty, add `dir_result_buffer.io.enq.ready` to
  result.ready.

### I-44 [Confirmed] L2 ListBuffer pool exhaustion × allocate using result.valid (not fire) — duplicate refill A for the same source

- **Location**: `ventus/src/L2cache/Scheduler.scala:190` (allocate gating uses
  `directory.io.result.valid` instead of `.fire`) × :225 (read-initiation gating
  `requests.io.push.ready`, one cycle earlier than the result cycle) ×
  :217/:223 (push on the result cycle; the secondary push of the tagMatches
  branch also consumes a freelist entry) × :252 (a miss's
  result.ready=push.ready).
- **Mechanism (E3 falsification chain, wave-27 machine proof)**: at read
  initiation the pool has 1 entry left (push.ready=1, gating passes); on the
  result cycle a same-cycle secondary push (a merged request, occupying no MSHR
  but a freelist entry) exhausts the pool ⇒ that result's push.ready=0 ⇒ the
  miss result is stalled (result.ready=0) ⇒ :190's allocate.valid repeats every
  cycle ⇒ the refill A for the same source is **emitted twice** (in the witness,
  two emissions at cycle 33 and cycle 35, both source=31). ListBuffer pool
  exhaustion itself is machine-proved: `l2dc_lb_pool_exhausted` (31 primary + 1
  secondary push ⇒ used=allOnes).
- **Formal evidence**: `lean/Ventus/L2/Discharge.lean`:
  `l2dc_e3_counterexample` (allocValid ∧ ¬pushReady in the same cycle),
  `l2dc_e3_falsified` (the E3 proposition falsified), `l2dc_e3_inv1_broken` (the
  I-39 invariant broken), duplicate-A witness. Degradation: the 31-cycle prefix
  was not replayed as a whole (a 36-cycle runTrace native_decide takes >600s,
  evaluation blow-up); replaced by an LB-leg machine proof + hand-constructed
  pre-state + per-cycle environment-legality symbolic theorems
  (`l2dc_e3_env_allocs`).
- **Impact**: the outer memory receives two A's with the same source ⇒ two
  AccessAckData ⇒ MSHR bookkeeping confusion (the I-41 family's allocate×sinkd /
  merge×sinkd collisions become reachable again in this corner); correctness
  level (duplicate refill / response pairing confusion).
- **Fix suggestion**: gate allocate.valid with push.ready (change :190 to
  result.fire semantics), or make the read-initiation gating reserve one entry
  for a secondary push (:225's push.ready changed to "free ≥ 2").

- **Downstream discharge (2026-08-30, `lean/Ventus/Mem/DupRsp.lean`): the end-to-end impact chain closes**

- **L1MSHR (C1/C2)**: orphan responses are absorbed but with non-transparent
  side effects (the `releasing_stall` flip is sticky-set,
  `dbr_l1m_orphan_stall_toggle`); **no guard after entry reuse**
  (`dbr_l1m_reused_consumed`: any response carrying that entry number is treated
  as genuine — a duplicate response emits a coreRsp with the new occupant's
  metadata but the old block's data (witness `dbrW2_dup_emits_B_coreRsp`), and
  the tag array is displaced (DCache.scala:621,629's allocateWrite uses the
  frozen d_source)) — silent data corruption.
- **MSHRv2/LSU (C3)**: equally unguarded (`dbr_mshr_no_guard`); witness
  `dbrW3_dup_premature`: **warp5's new load is prematurely fulfilled with
  warp2's stale data and written back to the register file**.
- **End-to-end (C4)**: I-44 trigger × L1 unguarded × LSU unguarded ⇒ unrelated
  warps receive stale data + L1 tag/data array displacement, with no layer of
  the chain reporting an error. When the entry has not been reused it degrades
  to transient backpressure.
- **Residual-risk verdict (2026-08-30, `lean/Ventus/Mem/DupRspTag.lean`):
  harmful (correctness level)**. The conjecture "idempotent if no new miss"
  does not hold — the genuine fill itself sets way_valid
  (L1TagAccess.scala:314), so the dup's replacement choice necessarily changes:
  on a non-full set the dup installs a **second valid line with the same tag**
  (`dbt_notfull_dup_way_diff` full enumeration + witness W1; exactly the state
  the commented-out `PopCount(waymask)<=1` assertion at TA:408 was defending
  against). Two layers of coincidence temporarily mask it (OHToUInt=Log2 always
  selects the way1 copy + hit refreshing the timestamp keeps the two copies
  tied), but it is broken by a full-set tie eviction (`dbt_tie_evicts_way1`):
  trace W1→W4 — the dup copy (way1) holding the new data is evicted and written
  back to L2, **the stale way0 copy revives**, and reading A hits and returns
  old data (the control group without dup is correct). Also: during the dup the
  set's effective capacity halves (W6). Fix suggestions: fold the L1MSHR
  `used≠0` guard into the allocateWrite/dataFill enables
  (`dbt_fix_orphan_noop` has verified that after the fix orphans cause zero
  array writes) + restore the TA:408 assertion as online detection.
- **Fix suggestion**: root fix at L2 (gate allocate.valid with push.ready); L1
  hardening (add an expectation check to missRspIn; fold the used≠0 guard into
  the allocateWrite/dataFill enables).

### I-45 [Confirmed (requires host contract violation)] Alignment and size constraints of register allocation are checked nowhere in hardware

- **Location**: `cta/resource_table.scala:305-311` (allocation granularity = 1
  register, no rounding), `top/GPGPU_top.scala:76-79` (num_vgpr/perWf passed
  straight from the host), `cta/cu_interface.scala:96` (the assertion only
  covers the global NUM_VGPR=1024).
- **Mechanism**: the collector's bank/address mapping formulas (`bankID = wid +
  regIdx(1,0)`, `rsAddr = base>>2 + regIdx>>2`) implicitly assume "bases are
  4-aligned" (hb1 of WB-A1's `dcg2_wba1_bank_disjoint`). But the whole
  allocation chain has zero alignment/zero size checks: when the host gives a
  non-4-aligned size, the next WG's base is non-aligned accordingly
  (counterexample `dcg3T_misalign_base`: first WG size 5 ⇒ next base 5),
  causing two WGs' registers to collide at the same physical address
  (`dcg3_wba1_misalign_collision`); when `numWf×perWf > vgprSize`, the last WF
  runs out of its WG's interval (`dcg3_wba1_fit_violation`), while the assertion
  at :96 passes throughout (`dcg3_wba1_hw_assert_too_weak` — the assertion
  checks the wrong quantity).
- **Impact**: when the host/driver configuration violates the contract, register
  data is trampled across WGs — silent wrong data.
- **Tolerability**: if the existing driver always gives 4-aligned,
  size-matching allocations, it cannot be triggered — this is a robustness gap
  of "the contract not being hardened into hardware"; suggest adding alignment
  assertions on the hardware side or rounding at allocation.
- **Formal evidence**: `lean/Ventus/Spec/Discharge3.lean` (the dcg3 family);
  positive direction: `dcg3_wba1_rt_run_aligned` (host sizes all k-aligned ⇒
  bases along the whole chain k-aligned, proved by induction).

### I-46 [Confirmed] endprg does not wait for in-flight memory accesses + wid reuse → late write-backs pollute the new warp's registers

- **Location**: `pipeline/warp_schedule.scala:47,55,180` (endprg has no
  memory-access condition, warpRsp immediate, active cleared the same cycle; the
  ldst/switch drain interface at :39-40 was commented out and deleted);
  `CTA2warp.scala:56,59,63` (a slot is reused as soon as it is free);
  `CSR.scala:296-301,355` (dispatch overwrites sgpr/vgpr_base);
  `operandCollector.scala:604,606` (write-back addresses computed on the fly
  from the **current** base(wid)); `LSU.scala:572-577` (the fence_end in-flight
  counter exists but connects only to fence, not to endprg).
- **Mechanism**: warp w endprgs with an in-flight load → the slot is released
  the same cycle → a new warp reuses the wid and vgpr_base is overwritten → the
  late write-back lands in the new warp's logical registers per the new base.
- **Formal evidence** (`lean/Ventus/Spec/EndprgInflight.lean`): mechanism facts
  EIF-1~4 + witnesses `eifW_endprg_with_inflight`/`eifW_reuse`/
  `eifW_pollution` (native_decide trace: the pollution lands) + the guard
  theorem (a fixed version with fence_end connected into endprg,
  `eif_guarded_endprg_safe` — fix-and-verify).
- **Impact**: the new warp reads the old warp's load data (silent wrong data);
  two unprotected paths: when the new warp's allocated interval is smaller than
  the old warp's destination register number, the write-back runs out of its own
  allocation (vgpr is variably partitioned); and after the old wg's region is
  reclaimed and reallocated, unrelated live warps are polluted. Scoreboard
  leftover busy bits provide incidental serialization (masking same-number
  overwrites, but the new warp waits in vain for a dead warp's memory latency —
  a performance side effect).
- **Fix suggestion**: connect `fence_end(wid)` (the LSU in-flight counter) into
  the endprg completion condition (delay warpRsp until that wid has no in-flight
  write-backs) — the fixed version has been modeled and proved.
- **Additional observation (filed as a separate candidate)**: wg completion
  reporting to the host does not wait for flushDCache completion — an ordering
  risk of store global visibility vs completion reporting.
- **Reproduction**: ChiselSim end-to-end (a warp endprgs with an in-flight load
  + the slot is reused immediately), ready to be written.

### I-47 [Confirmed] WG completion reporting strictly precedes flushDCache completion (no flush completion signal)

- **Location**: the whole reporting chain has no flush input
  (warp_schedule.scala:47,55 → CTA2warp.scala:63,73 →
  cu_interface.scala:156,179,221 → host_wg_done); the flush chain is initiated
  one-way with no completion loop (warp_schedule.scala:169-170 bookkeeping
  "sent means done"; the DCache's actual flushing — DCache.scala:488-503
  writing lines back to L2 one by one — is inside no bookkeeping).
- **Mechanism**: the WG's last warp endprg enters the reporting FIFO the same
  cycle; flushDCache is initiated at the earliest the next cycle and no
  "completion" signal ever comes back (witness: host_wg_done.fire at cycle 3,
  while in the same cycle the flush has not even issued a DCache request; even
  under the most favorable zero-dirty-line abstraction the flush completes no
  earlier than cycle 5).
- **Formal evidence** (`lean/Ventus/Spec/FlushOrdering.lean`): structural
  `floRun_report_indep` (the reporting chain's evolution is completely
  independent of flush state, pure induction) + end-to-end witnesses (`floW_*`,
  including the rfl-level independence "the reporting cycle is unchanged for any
  dirty-line count") + the fixed-version guard theorem
  `flo_guarded_report_safe`.
- **Impact**: a host that "reads the result buffer upon completion" (the
  standard OpenCL flow) reads stale data — a systematic race (reporting is ≥2
  cycles early + ≥1 cycle per dirty line; in practice tens to hundreds of
  cycles). **When stacked with I-5/I-6 the flush may never happen while the
  report is still emitted.**
- **Tolerability**: invalidate semantics writes back before invalidating (no
  data loss); if the host reads through the shared L2, the window shrinks; no
  explicit flush contract seen at the driver layer.
- **Fix suggestion**: gate host_wg_done.valid on "this CU's flush complete"
  (the completion point can reuse the existing invCoreRsp_st1,
  DCache.scala:484-486).
- **Reproduction**: ChiselSim end-to-end (with the WG having dirty lines,
  observe the order of host_wg_done vs flush completion), ready to be written.

### I-48 [Confirmed — latent / fix-activated] Duplicate response to an invalidate: writeback path and hintAck path both respond (masked by I-30's w2b bug; activated once I-30 is fixed)

> Found 2026-09-07 by patched-RTL regression testing (agent-147). **This is a
> fix-activated latent defect**: the mechanism exists in the original RTL but is
> masked by I-30's w2b bug; it activates as soon as the i30 fix is applied — the
> first case in this project whose breakage condition is "fixing another bug".

- **Location**: `L1Cache/DCache/DCache.scala`: :413 (`memRspIsFluOrInv`, the I-30
  fix point), :511 (dirty-writeback PutPart carries
  `hasCoreRsp=waitforL2flush_st2`), :832 (WSHR push produces a response via the
  memReq path), :766 (the hintAck-path response).
- **Mechanism**: the i30 fix (adding the deq.valid qualifier at :413) stops the
  w2b per-cycle spurious clearing, so `waitforL2flush_st2` survives; an inv's
  dirty-writeback PutPart then carries hasCoreRsp=1, the WSHR push produces a
  response via the memReq path — *before* the L2 flush handshake completes,
  contrary to the intent of waitforL2flush — duplicating the hintAck-path
  response. One invalidate yields two responses.
- **Evidence (patched-RTL)**: the I-30 case of DCacheBugRepro (after fixing the
  test-stub defect): baseline response sequence {7,3,1,5,4,2} (exactly one per
  request); patched tree {7,3,1,5,4,**2,2**}. Bisection: reverting i30 alone
  removes the duplication; reverting i27/i28/i29/i44 does not. See doc/22,
  "I-29/I-30 analysis".
- **Harm**: response-protocol violation — one request receives two responses;
  downstream response bookkeeping (LSU / warp scheduler) may miscount warp
  completions.
- **Tolerability**: unreachable in the original current configuration (masked by
  I-30's w2b spurious clearing); immediately reachable once the i30 patch is
  applied. A must-fix for the fixed version.
- **Fix suggestion (to be refined; new design point)**: exactly one response per
  inv — make the writeback path and the hintAck path mutually exclusive (e.g.
  hasCoreRsp effective only after the final Flush handshake, or a per-inv
  responded flag).
- **Unresolved detail**: the exact cycle on which invalidatenodirty (:430) holds
  in the inv2 flow (store4 has completed, hasDirty should be 1, yet the PutPart
  did carry hasCoreRsp=1) needs waveform-level debugging.

### I-49 [Confirmed] Warp scheduler's fixed-priority selection starves higher-numbered warps (policy-level liveness defect)

> Found 2026-09-10 by the fairness-discharge work (R2, doc/27): the
> disproof of unconditional fairness IS the machine-checked witness of this bug.

- **Location**: `pipeline/warp_schedule.scala:183-186` (selection: descending
  `when` chain with last-write-wins, so the lowest-numbered pc_ready warp always
  wins); :184 (the eligibility mask `pc_ready = pc_ibuffer_ready & warp_active`
  does NOT include the bar/scoreboard/exe stall masks of :181). Note
  `current_warp` (:49-50, :95) is only a hold-value fallback (WireInit), **not**
  a round-robin pointer.
- **Mechanism**: a low-numbered warp spinning indefinitely (the ibuffer stays
  ready as instructions are issued and refetched, and with no endprg the warp
  stays active) permanently wins selection, so higher-numbered warps are never
  selected: fetch stalls, they never halt. With cross-warp dependencies through
  global memory (flag waits / producer-consumer), this escalates to a
  whole-machine deadlock. The issue-level arbiter is round-robin
  (`rra5_no_starvation` proved) but the fetch-level selection is fixed-priority
  — the two levels disagree, and the RR level cannot save the starved fetch.
- **Formal evidence (model level)**: `VentusF/Fairness.lean` —
  `fair_starvation` / `fair_starve_trace`: for every trace length n, warp1 stays
  eligible (active ∧ ibuffer ready) while the selection trace is constantly
  warp0 (induction + native_decide numeric instances). The positive family
  (`fair_selected_of_min` / `fair_mem_trace` / `fair_run_stable_min`) shows a
  warp that becomes the minimal eligible candidate is selected that same cycle.
- **Harm**: zero progress for all higher-numbered warps (hang, not wrong data);
  not maskable upstream.
- **Tolerability**: triggerable in the current configuration (num_warp=8; a
  spinning low-numbered warp suffices); software conventions (no unbounded
  spinning, or yielding inside the spin) avoid it; hardware fix suggestion:
  RR selection (reuse the RRArbiter approach) or age-based priority boost.
- **Reproduction**: Verilator two-warp experiment (warp0 spinning `j self`,
  warp1 any program; observe pc_req.warpid constantly 0) — ready, not yet
  executed in this environment.
- **Side ruling**: the unconditional form of `capeFairSched` (the scheduler
  fairness contract in CapExist.lean) is falsified by this entry; it is
  therefore carried as the explicit premise `hcov` ("every unhalted warp
  eventually becomes the minimal eligible candidate") in `fair_capeFairSched`,
  to be supplied by execution semantics.

### I-50 [Confirmed] vmerge write mask deviates from RVV: lanes with tmask=1 ∧ v0[t]=0 are not written (exposed by the I-12 fix)

> Confirmed 2026-09-10 by the R4 vmerge semantics evaluation (doc/28). A
> follow-up of the I-12 fix: once the mask path works, this second-layer
> deviation becomes observable.

- **Location**: `execution.scala:559` (`wvd_mask := io.in.bits.mask`
  unconditionally overwrites, turning the intent at :541 into dead code) +
  `pipe.scala:366` (`io.in.bits.mask` already fused to v0∧tmask, irreversibly).
- **Mechanism**: RVV (v-spec v1.0 §11.15) requires vmerge to write on **all
  active lanes** (v0 selects data per lane; it is not a write enable); the
  machine writes only lanes with v0∧tmask. Exact gap: lanes with
  **tmask=1 ∧ v0[t]=0** — RVV requires writing vs2[t], the machine does not
  (vd keeps its old value). When v0 ⊇ tmask the two sides agree.
- **Observability**: fully observable when vd≠vs2 (discriminating program:
  v0=0x0000FFFF, vd preset to a sentinel, vmerge then vse32 readback — lanes
  16–31 keep the sentinel); unobservable under vd=vs2 (the LLVM tied-destination
  idiom, i.e. typical compiler output). Same for vmerge.vxm/.vim.
- **Harm**: silent wrong data for hand-written/non-LLVM-idiom code; the RVV
  conformance claim does not hold.
- **Fix suggestion (Option A, recommended in doc/28)**: add a `tmask` field to
  vExeData in `pipe.scala` (tapped at :366 from simt_stack.io.out_mask) and
  conditionalize `execution.scala:559`:
  `wvd_mask := Mux(alu_fn===FN_VMERGE, tmask, io.in.bits.mask)`. Note: simply
  activating the dead code (all-true) would corrupt inactive lanes — worse than
  the status quo.
- **Evidence**: source-level static analysis + Lean-side consistency cross-check
  (IsaSpec D6 golden semantics uses wm=tmask; SMMem's machine-side
  wbVMaskFn=v0∧tmask; the machine-level alignment gap registered at
  CapExist.lean:57-59 is exactly the proof-side projection of this gap). RTL
  reproduction pending (discriminating program designed).
- **Tolerability**: unobservable in compiler output (vd=vs2 idiom);
  triggerable by hand-written kernels.

### I-51 [Confirmed — timing-conditional] Allocator's rtcache mismatches the rt list and can accumulate into resource overestimation → H-ALLOC-FIT fails → overlapping WG resource regions

> 2026-09-10, R4's G2 discharge (`Ventus/CTA/RtCacheConsistency.lean`): the
> contract gap G2 ("rtcache timing-consistency half") was **refuted** — the
> consistency does not merely lack a proof; it does not hold, with a
> decide-certified failure trajectory.

- **Location**: `allocator.scala:86-92` (rtcache deducted by the sel row) +
  :251-262 (checks against rtcache) + `resource_table.scala:560-567` (a SCAN can
  be preempted by a same-CU alloc).
- **Mechanism**: the allocator deducts the cache by the sel row while rt picks
  the best-fit segment — the cache stores no segment IDs, so deductions
  mismatch; when a SCAN is preempted by a same-CU alloc, the mismatch is never
  refreshed and can **accumulate** into overestimation.
- **Formal evidence** (event model, all `by decide`): a complete failure
  trajectory on the sgpr channel (N=2048): alloc 2038/3/1 → dealloc → SCAN →
  alloc 4/1/2 — afterwards cache=(2,0) while the true max gap is 1
  (`rtcc_w_final_cache`/`rtcc_w_gapmax`); the fourth alloc with size=2 passes
  the check (`rtcc_w_checks`) although no gap ≥2 exists (`rtcc_w_nofit`) —
  **H-ALLOC-FIT fails**; the failed FIND inserts at the initial base=0,
  overlapping the resident node [0,2038) (`rtcc_w_corrupt`/`rtcc_w_overlap`).
- **Positive results (same file, fully proved)**: the total-conservation
  invariant `rtccInv_run` (sum of the two cache rows ≤ total free length always
  holds) — the cache never overestimates the *total*; only the top-2 structure
  drifts; and the first alloc after a landed SCAN is always safe
  (`rtcc_fit_after_scan`).
- **Harm**: two WGs receive overlapping SGPR/LDS regions → silent data
  corruption.
- **Reachability (three breakage conditions, all required)**: (a) the best-fit
  segment differs from the sel row's segment; (b) that alloc's SCAN has not
  completed before the next same-CU check; (c) another same-CU alloc passes the
  check on the mismatched cache within the window. Proved at the event-model
  level; RTL-level timing reproduction pending.
- **Fix suggestion**: add a DEBUG assertion on the resource_table WRITE path
  that "an alloc with nonzero size must hit FIND" (the existing :91 assertion
  only guards against deduction wraparound, not overestimation); the root fix
  aligns cache deduction with the best-fit segment (store segment IDs, or block
  alloc checks until the SCAN lands).

### I-53 [Confirmed — latent] Two boundary points in fudian's FMA composite (Q-FM-2 silent drop + Q-FM-1 fragile lockstep) and one misleading comment (Q-FM-3)

> Found 2026-09-11 by the R5-B FMA-composite modeling (FpuFma.lean). All in the
> fudian library (upstream: OpenXiangShan).

- **Q-FM-2 (latent, currently unreachable)**: `FMA.scala:162` +
  `utils/FPUOps.scala:61-86` — op=3 (fu=0 and op(2,0)=3) belongs to no operation
  class, yet in.ready can fire via the else branch: the transaction is accepted
  and **silently dropped** (enters no container). The current decode table has
  no such encoding (fpu_utils.scala:16-43), so it is unreachable; breakage
  condition = adding that encoding without wiring the FMA datapath. A "op=3 must
  not fire" assertion is recommended.
- **Q-FM-1 (fragility, not a bug)**: `FMA.scala:151-158` splits addPipe's
  data/ctrl paths — data from inToAddFIFO/mulToAddFIFO, ctrl/op from the arbiter
  output; safety rests entirely on the lockstep of the two FIFO pairs (proved
  for the current configuration by `ffm_lockstep_*`). Breaks if any queue
  depth/flow parameter changes — re-verification required on such changes.
- **Q-FM-3 (doc-level, harmless)**: the comment at `fpu_utils.scala:20`
  ("FN_FSUB io.(b*1-a)") conflicts with the fpuv2 comment ("io.(a-b)"); the
  implementation matches fpuv2 (a-b). The ventus-side comment is misleading.
- **Disposition**: latent registration + monitoring assertions; Q-FM-3 is a
  comment fix suggestion for upstream.

### I-54 [Confirmed] fpuv2 FCMP wrapper's NaN/±0 handling family (7 sub-items, machine-checked witnesses)

> Found 2026-09-12 by the fudian numeric-core N1 pilot (FpuCmp.lean). The defects
> are in fpuv2's FCMP wrapper (`dependencies/fpuv2/src/main/scala/FCMP.scala:18-30`);
> the fudian comparison core itself is fully proved correct. RISC-V references:
> F-ext §2.2 / vector §13.6 (minNum/maxNum semantics + NV flag rules).

- **W1**: min/max with an sNaN operand → invalid → result zeroed to 0x00000000
  (should return the non-NaN operand, canonical NaN if both, and set NV).
  Witness: `fcW1_min_snan`.
- **W2**: with a single qNaN, one of min/max returns the qNaN bit pattern instead
  of the numeric operand (operand-order asymmetry: lt=false → min=b, max=a).
  Witnesses in FpuCmp.lean §10.
- **W3**: two qNaN inputs are not canonicalized (should return the canonical NaN).
- **W4**: FLT/FLE with a qNaN does not set NV (`FCMP.scala:18-19` hardwires
  signaling to false; the source carries a "TODO: signal logic").
- **W5**: FNE with an sNaN clears to 0 (should be 1 — NaN≠x is always true).
- **W6/W7**: fmin/fmax(-0,+0) get the sign wrong (fmin should give -0, fmax +0;
  root cause: the fudian core's diff-sign zero pair uses `fp_a.sign || bothZero`,
  and the wrapper's Mux(lt,a,b) is operand-order asymmetric). Witness:
  `fcW6_min_negzero` et al.
- **Harm**: silent wrong data for min/max/fne on NaN/±0 boundary inputs; the
  missing NV flag breaks software relying on fflags (strict IEEE compliance
  checks).
- **Tolerability**: requires NaN/±0 boundary inputs, rare in typical numeric
  kernels; but an ISA-conformance defect that upstream should fix. Fix
  direction: rewrite the wrapper's NaN dispatch per RISC-V minNum/maxNum
  semantics (both NaN → canonical NaN; single NaN → the other operand; set NV)
  + implement the NV logic + fix the ±0 sign rules.
- **Reproduction**: the machine-checked witnesses in FpuCmp.lean; ChiselSim /
  Verilator reproduction ready-to-run (min/max(sNaN, x), fne(sNaN, x),
  fmin/fmax(-0,+0)).
- **Note (Class III side-catch)**: F-III-1 (FloatSpec's fsFle double-inf typo)
  was caught by this pilot and already fixed — the independent-expectation
  discipline working again.

### Notes (ISA-level deviations, B1 findings, 2026-09-01)

- **JALR target address does not clear bit0** (operandCollector.scala:243-246
  passes imm+rs1 straight through; PCcontrol only aligns to fetch-group) —
  deviates from the RISC-V manual (JALR should clear bit0); under RV32I legal
  targets are always 4B-aligned so this is unobservable; recorded as a fragility.
- **vbranch comparison direction**: with reverse=true, vblt actually compares
  (rs2)<(rs1) — opposite to RVV intuition; IsaSpec models the machine as built
  (D10).
- **vmv.s.x writes all active lanes** (RVV writes only lane 0) — machine
  deviation, modeled as built (D12).
- **vmerge write mask**: even after I-12 is fixed, execution.scala:559's
  unconditional wvd_mask overwrite makes the effective write only to lanes of
  v0∧tmask — deviating from RVV (vmerge should write all lanes). A follow-up
  item of I-12 pending evaluation (already listed in the internal fix manifest); the expected
  failure point of the capping theorem on vmerge ("failure point = bug list").

- `operandCollector.scala:499-502` (instDemux): the X (scalar) side always
  takes the "second-lowest ready CU" (`ocRdy2` unconditionally drops the lowest
  bit) — when only 1 free CU remains, scalar instructions cannot issue (even if
  that CU is free), and must wait for another CU to be released or for the v
  side to occupy the lowest bit. A performance-level stall risk (not a
  functional bug: a CU will eventually be released); quiesced single-instruction
  scenarios are unaffected. Evidence: the `prg_ocOrR_ocRdy2_of_two` comment and
  analysis in `VentusF/Progress.lean`.

## Class II (translation process)

### II-1 IntDivMod recovery path mistranslated as a widening add (formerly I-18; withdrawn 2026-09-07)

- **Location**: the original `divCommonRNext` in `lean/Ventus/Arith/IntDivMod.lean`
  modeled the wrapping add at `IntDivMod.scala:70` as a widening add
  (zero-extend then add).
- **Discovery**: RTL reproduction (both ChiselSim and Verilator channels)
  contradicted the model's predictions; line-by-line review against two Chisel
  versions (5.3.0 and 6.4.0) pinned the divergence — in Chisel 5/6, `+`/`-` are
  wrapping (`do_+ = do_+%`); a widening add requires an explicit `+&`.
- **Lesson**: any translation point that relies on operator-width semantics must
  carry numeric regression tests whose expected values are derived independently
  of the model (here the tests shared the model's mistake, so they could not
  catch it).
- **Disposition**: the model has been corrected and the whole development
  re-proved (zero sorry); the fixed-variant regression equivalence was re-proved
  as well (pointwise agreement on all 131,072 inputs at xLen=8 outside the I-17
  cone).

## Class III (spec/proof side)

### III-1 IBuffer test/spec written wrong (found during the wave-4 checkpoint fix; all corrected)

- `IBuffer.lean` IbLane test block and `ibT_no_flush_ok`: the test trace assumed
  "an empty lane can issue the cycle after enqueue; loading does not require
  out.ready", but `ibuffer.scala:170` SlowDown's `in.ready = (mask_next==0) &&
  out.ready` (conservative bubble, Q3) gives a 2-cycle latency from empty-lane
  enqueue to first issue. Caught by decide/native_decide counterexamples; the
  trace has been rewritten per the real timing.
- `ibTop_warp_prefix`'s original conclusion form `run.2 ++ tl = run.1.abs ++
  accepted` was itself unprovable (a half-refactored artifact from an
  interruption); changed to the prefix form `run.2 ++ tl = accepted` per the
  comment's intent, and proved.
- The lesson (also seen in a sister verification project): spec/test
  errors are quickly caught by
  decide-family counterexamples; the test-first flow works. The model itself
  (IbQ.step/ibSdInRdy/flush discard) was checked item by item against the
  source — consistent, no Class II issues.

### III-2 Two errors in the DecodeUnit task briefing (corrected during verification)

- The briefing's BitPat intersection criterion `(mA &&& mB &&& ~~~(vA ^^^ vB)) =
  0` was a wrong formula (it judges "no common constrained bits"); the correct
  criterion is `(mA &&& mB &&& (vA ^^^ vB)) = 0` — no value conflict on common
  constrained bits means non-intersecting. The wrong formula would misjudge
  almost all row pairs as intersecting.
- The briefing's assumption "espresso minimization, intersection means
  nondeterministic decode" does not hold: chisel's (6.4.0 and 7.x) `ListLookup`
  is element-wise MuxCase with first-match priority (deterministic shadowing).
  Decode determinism does not depend on disjointness; the value of the
  disjointness audit is "no shadowing / no dead rows". Agent-9's zero-shadowing
  result was adopted accordingly (four tables pairwise disjoint ⇒ match order
  irrelevant; the model's first-match semantics is equivalent to the hardware).
- Version note: build.sc:32 pins chisel 6.4.0; this machine's coursier cache
  only has 7.0.0-RC1 (leftover from another project), and the bytecode
  verification was based on 7.0.0-RC1 — the conclusion holds for 6.4.0 as well
  (espresso has been removed since chisel 3.5).
- Lesson: "factual" briefing content given to subagents can itself be wrong;
  subagents' falsification receipts are a necessary line of defense.

### III-3 I-4 reachability analysis error (wave-3 main-session conclusion, corrected in wave 11)

- The wave-3 "reachability confirmed" conclusion for I-4 argued
  only structural possibility on the collector side (in and out can occur in
  different units in the same cycle), **missing the gating side**: OpColReg is a
  register, the gating chain combinationally reads its current value, and
  same-cycle in+out requires that bit to be both 0 and 1 — a contradiction.
  Found and proved during I4Fix modeling (`i4f_no_two_busy_orig`);
  the source chain was re-reviewed (pipe.scala:223 →
  warp_schedule.scala:181 → pipe.scala:161 → scoreboard.scala:131,142) and
  confirmed.
- Lesson: **a "reachability" argument must cover the complete enable chain
  (including upstream gating); structural possibility ≠ reachability**. This is
  exactly where formalization beats paper review — a combinational-level
  invariant (`i4f_no_two_busy_orig`) turned the gating constraint the paper
  analysis missed into a theorem.
- Same-class risk sweep: I-2 (BranchJoin overflow) has been handled as
  "mechanism real / unreachable under legal execution", a consistent process;
  the remaining [Confirmed] entries' reachability is all supported by witness
  traces, unaffected.

## Review Notes (non-bugs; fragile-idiom records)

- `issue.scala`/`writeback.scala` notes: two inconsistent combinations exist
  between Issue routing and ibuffer2issue's inst_is_vec classification
  (csr∧(mul∨mem), isvec∧barrier — the latter would be sent to a channel with
  ready tied off and deadlock); the current decode table produces neither
  combination (the necessary-and-sufficient criterion `iss_classify_agree` is on
  record) — a decode-table evolution landmine; arbiter_o2m's valid is driven
  backwards from ready (inside dead code; ISS10 proves it can fire fake data);
  Writeback/Branch_back's fixed-priority Arbiter can starve a persistently
  valid low-priority source (performance observation).
- `L1TagAccess.scala` notes: invalidateAll clears valid but not dirty
  (:316-318) and needReplace (:294) does not look at valid — stale dirty can
  cause spurious write-backs (machine proof
  `l1taT_stale_dirty_after_invalidate`), currently masked by the "flush before
  invalidate" protocol; Counter(1000) wraparound breaks LRU order (ultra-long
  run performance item); the :307 comment does not match the code; the I-24
  re-proof chain (independent): `l1ta_i24_mapping` (the selection only looks at
  way1) → `l1ta_i24_way1_never_valid` (way1-never-valid invariant) → two-way
  degenerates to direct-mapped.
- `L1MSHR.scala` notes: :319 ready is dead logic (proved equivalent to the
  simplification); :187/:192 matching is not qualified by valid (stale bits
  participate in st0/almFull, at most transient backpressure); :354's elsewhen
  only hangs on se=1 — exactly correct at S=2, a bug upon changing the
  parameter; the merge-target entry's write address is recomputed at the fire
  cycle while the subscript is frozen at the probe cycle (abnormal timing can
  dislocate them; masked on the DCache side by probereadAllocateWriteConflict);
  instrId_Access/probestatus are dead state; releasing sticks under orphan
  responses (unreachable in normal flows).
- `CTA2warp.scala` notes: `warpReq.valid := CTAreq.fire` (around :54) relies on
  the implicit contract that warp_schedule is always ready; the data table has
  no RegInit (relies on "dispatch before use"); the :74 assertion exists only in
  simulation. `cta_scheduler.scala`: the top level's only self-protection is the
  init_ok gate; no-resource-overcommit and slot-disjointness rest entirely on
  submodule contracts (the eight `CtasEventOk` assumptions, wave-10 discharge
  debt; counterexamples T2/T3: without the contracts, two allocs overcommit
  3000>2048).
- `wg_buffer.scala` notes (2026-08-28, `Ventus/CTA/WgBuffer.lean`): H-WGB
  discharged (`wgb_h_wgb_discharge`). Observations: the :175 assertion checks
  only a three-way AND, weaker than the pairwise mutual exclusion the comment
  claims (silent when rstmask2 and setmask coincide, Q-WGB2, insufficient
  assertion strength); dequeue order ≠ enqueue order (under reject-retry the
  latter dequeues first, Q-WGB6 witness — wg_buffer is not a strict FIFO; the
  consumer CtaScheduler only uses counts, so no impact); :176 accept clears
  valid but not alloc (harmless residue); :68-69/:136-137 the suspected
  Verilator tool bug where wgram2 bit 238 is constantly 1 in simulation, and
  the workaround (simulation-trustworthiness risk); alloc_result has no
  internal duplicate protection (relies on allocator discipline; merged into
  the WgbEnvOk contract).
- `GPGPU_top.scala` notes (2026-08-28, `Ventus/Top.lean` Q section): the
  pc_reset chain is machine-proved (constantly high cycles 0-4, constantly low
  from cycle 5, `top_pcReset_high_first5`/`top_pcReset_low_after5` — closing
  the safety premise for PCcontrol mask having no reset value); I-21's :488
  junction and the ShareMem model are pinned as the same function
  (`top_shared_setIdx_conn`). Observations: GPGPU_axi_adapter_top's AXI
  idBits=5 mismatches the inner 16 (dead module, blows up if enabled,
  `top_axiAdapter_mismatch`); TL size constantly 0.U (the comment admits it
  should be 7; the consumer side awaits the L2 wave); the MMU branch 17→16
  silently truncates the MSB (not instantiated in the current configuration);
  icache request a_param=DontCare passes through; several dead fields such as
  host_kernel_asid.
- `execution.scala` SFU/FPU-side notes (`Ventus/Arith/ExeSFU.lean` Q section;
  all fragilities are contract-dependent/counterfactual, not bugs reachable
  under the current configuration): :865-867 valid uses wvd/wxd while o_ready
  uses isvec — with isvec=1∧wvd=0 an instruction is silently lost
  (`exsSfu_q3_silent_drop` pins it down); :928 scalar takes only arbiter(0),
  taking dummy=1 when mask≠0x1; FPUexe :803's ready mux drops results when
  wvd/wxd is not exactly one; data_buffer with pipe=true would deadlock
  back-to-back. BUG2 (I-19) impact-scope correction: a dummy 1/1 transaction in
  a masked slot flushes zeroQReg to false (a "washing" effect) — under the SFU
  wrapper, I-19 reachability requires two consecutive real transactions in the
  same slot with no dummy in between. The black-box assumption list
  H-FPU/H-FDIV/H-TC/H-DECODE is given in the file header (to be consolidated
  into Spec/Contracts.lean).
- `execution.scala` vALU-side notes (2026-08-27, `Ventus/Arith/ExeVALU.lean` Q
  section): the active equal-width branch (num_lane=num_thread=32,
  pipe.scala:77) is fully closed in modeling; the following all live in the
  **split branch not instantiated under the current configuration** (:573-736)
  or the dead module vALUexe — recorded as evolution landmines: :681 if_mask
  cross-batch concatenation is correct only for maxIter=2 (≥3 loses all earlier
  batches, dual evidence symbolic + end-to-end; the commented-out (12,4) at
  ExtMem_gen.scala:40 is exactly a maxIter=3 configuration); :620-635 batch
  shifting does not shift the mask (batch k≥2 wrongly uses batch 0's mask,
  witness on record); :580 on the drain cycle outFIFOReady selects the queue
  using the already-cleared inReg.ctrl.simt_stack (entry-loss witness on record;
  fix suggestion: use the latched recv_simt_stack); the split branch has no
  cmp_out override (SGE/SGEU get un-inverted slt). Also: the unconditional
  wvd_mask overwrites at :462/:559 make the conditional assignments at
  :448/:453/:541/:548 dead code (VMERGE's all-true intent void; the effective
  mask = the instruction mask — but VMERGE is already blocked upstream by the
  I-12 deadlock, making this a latent item downstream of I-12).
- `execution.scala` multiply-side notes (`Ventus/Arith/ExeMul.lean` Q section):
  send side wvd-priority vs recv side wxd-priority (:244-249 vs :332-336;
  same-batch mutual exclusion relies on decode guarantees, suspected
  unreachable); mid-recv bubbles silently drop data (:343-349/:370-372,
  unreachable under the current configuration, semantically inconsistent with
  vALUv2 :650-652); :406-409 spike_info is taken combinationally from mul(0)
  instead of resultReg (only pollutes the Spike comparison).
- `ICacheMSHR.scala` notes: :104-107/:136/:186-188 — a secondary miss's
  subentry allocation subscript and full test are taken from the rsp-selected
  row rather than the matched row (when rsp is free the subscript is effectively
  arbitrary; `icT_subfull_quirk` has an observable backpressure witness —
  entry1 has space but is rejected because entry0's row is full. No functional
  harm currently: targetInfo is a dead field and warps rely on replay; if
  targetInfo return is ever enabled, this becomes a bug); :214 `0 to
  NMshrEntry` out-of-bounds iteration is constantly-false dead code at
  NMshrEntry=4 (a power of 2), and becomes a Vec dynamic out-of-bounds write
  (UB) upon changing to a non-power-of-2 configuration; `ICache.scala:164`
  targetInfo (3 bits) assigned a 10-bit value, :169 EntryIdx (2 bits) :=
  d_source (5 bits) — the truncations currently have no functional impact (dead
  field / the low 2 bits happen to be the instrId).
- `LSU.scala` review notes (2026-08-27, review Q section; details in the
  `Ventus/Mem/LSU.lean` header notes Q1-Q15): :314,332,349,360 `cnt.value >=
  num_thread.U` is constantly false (Counter(32) ranges over 0..31, machine
  proof `lsuCntDone_false`) — cnt's inc/reset is dead hardware with no
  observable effect; blockOffset 9→5-bit truncation (functionally correct,
  literally misleading); the FN_SWAP branch truncating 16.U into the 4-bit
  param happens to yield TileLink semantics 0 (coincidentally correct);
  :259-261 the fence opcode branch is unreachable (fence=1 ⇒ mem_cmd=0
  intercepts first); :227 flush requests carry a residual entryID (DCache
  returns a coreRsp for flush; mitigation: on the flush cycle activeMask is
  all-zero, nullifying MSHR updates); :520 LSU2WB `ready = isWrite` — with a
  malformed tag (wxd=wfd=isWrite=0) the MSHR entry is never released and they
  exhaust into deadlock (unreachable under normal decode, a latent condition);
  Q14 scalar AMO forces mask all-ones → a same-address AMO executes per lane 32
  times (64-96 cycles each; the semantic verdict awaits ISA documentation
  cross-check); Q15 the AMO aq&&rl trailing release-invalidate response arriving
  late risks polluting the MSHR's data (to be verified in the L1D wave).
- `SRAMTemplate` (NutShell lineage) notes: a dual-port instance with
  bypassWrite=false returns an LFSR64 random value on same-cycle same-address
  read-write (X-probing convention; post-synthesis it is real logic) —
  **the ICache tag/data instances (L1TagAccess:451, ICache.scala:84) have no
  mutual exclusion between probe and refill, same-set same-cycle reachable**
  (tag reading a random value held by holdRead → most likely a false miss,
  small chance of a false hit), to be discharged in the ICache wave; the DCache
  DataAccess similar combination awaits the DCache wave. During reset
  w.req.ready=true but writes are silently dropped (`sramT_reset_drop_write`;
  harmless in current instances). SRAMTemplateWithArbiter has no instantiation
  repo-wide (dead code).
- `operandCollector.scala:366`: `readArbiterIO(j)(k).ready :=
  bankArbiterScalar(i).io...` takes effect in the last iteration (i=3) of the
  num_bank loop — all requests' ready is connected from the bank3 scalar
  arbiter, a cross-bank miswiring. Verified to have **no consumer** (inside
  collectorUnit only outArbiterIO's bits/valid are driven) — dead logic; and it
  would be a wrong value even if consumed. Modeled and pinned as
  `ocArbInReady366`.
- `operandCollector` review exclusions (2026-08-26, all with formal evidence):
  the crossbar scalar/vector double-when blocks writing the same out(j,k) is
  impossible (`ocE3_no_clash`: a same-(j,k) hit would require the same
  request's rsType to be both =1 and =2); the demux bits broadcast does not
  pollute controlX (`ocDemux_controlX_second` + `ocDemux_E4_single_ready`);
  RRArbiter non-Irrevocability is legitimate at both instances in this module
  (no backpressure on the read side; CU outputs stable under DualIssueIO
  backpressure, `ocE1_cu_issue_stable`/`ocE1_dual_stable`) — the "point-by-point
  verification" of the RRArbiter note in report 03 is closed for
  operandCollector; the ibuffer2issue/issue.scala two points remain to be
  checked.
- `chisel3.util.RRArbiter` (chisel 6.4.0 `Arbiter.scala:78-118`, an
  integration-contract risk, modeled in `Ventus/Schedule/RRArbiter.lean`): with
  count=1 the lock register group is not generated and `io.out` is **not
  Irrevocable** — under backpressure lastGrant is frozen but chosen is purely
  combinational, so a newly arrived circularly-higher-priority request changes
  chosen/out.bits in the same cycle (formal witness `rra3_not_stable`; a
  sufficient condition in `rra3_choice_stable`). Not a chisel bug (Irrevocable
  is never promised; the "Locking" name is undeserved at count=1).
  **Per-instance discharge conclusions (all closed 2026-08-27)**: the two
  operandArbiter instances are legitimate (no backpressure on the read side; CU
  outputs stable under DualIssueIO backpressure,
  `ocE1_cu_issue_stable`/`ocE1_dual_stable`); issue.scala:189-190,224-228's
  XVDualIssue/IssueV2 have **zero instantiations repo-wide (dead code)**;
  ibuffer.scala:64-65's rrarbit_x/v are all sampled only on fire downstream
  (`iss_ib2iss_fire_integrity`) — no Irrevocable-violation harm. Also: grant is
  not one-hot (all-true when there is no request), and `in.ready = grant &&
  out.ready`, so an upstream that uses in.ready as "selected" misreads it;
  lastGrant has no reset value (the source admits this is intentional;
  functionally harmless).
- `PCcontrol.scala:27`: `mask` is a Reg with no reset value. Current safety
  relies on an off-chip contract — the top-level pc_reset is high for the first
  5 cycles (GPGPU_top.scala:355-360), during which all warps write a
  deterministic value via PC_src=1, and warpReq dispatch precedes the first
  scheduling (on the Lean side, `pccReset_deterministic`/T4 have formalized
  "one PC_src=1 write eliminates the nondeterminism"). The module itself does
  not guarantee it; reused in a scenario without a reset window, mask_o is
  undefined on the first cycle; suggest `RegInit`. Also: the :39 comment
  "PC_src=0:PC+4" does not match the code (otherwise keeps the value) — a stale
  comment; align drops thread slots for non-4B-aligned New_PC (mask=0b00 when
  pc%8∈{5,6,7}); unobservable under RV32I without the C extension; re-review
  needed if RVC is introduced.
- `Classify.scala`: line-by-line review found no bug (45 pairs of mutual
  exclusion + exhaustiveness + derived consistency all closed by bv_decide).
  Note that `frac.head(1)` is the **most significant bit** (SNaN=0/QNaN=1,
  consistent with RISC-V fclass); repo-wide it is instantiated only in
  FloatDivSqrt.scala:129,132 and only `isSubnormalOrZero` is consumed; the other
  15 outputs are currently dead signals.
- `regfile.scala` other notes: ImmGen's default branch `Iimm & -2` (when
  sel=10-15) is unreachable from the decode table, pinned as a theorem;
  `Imm2 = inst(24,20).asSInt` makes the immediate negative when shamt≥16, but
  ScalarALU only takes the low 5 bits, so harmless; inside the unifiedBank dead
  code, `regs.read(rsidx)(num_thread+1)` indexes out of bounds on
  `Vec(num_thread+1,·)`, 31 lanes of the scalar branch dangle, and the switch
  has no default — the module is dead, recorded to prevent revival (same
  lesson class as I-1).
- `ibuffer.scala` Q1 [verdict: intended semantics, not a bug]: when flush and
  enqueue coincide for the same warp, enq.ready does not look at flush
  (:124/:128), icache_rsp sees fire, but the same-cycle enqueue is overwritten
  and discarded by the Queue's internal flush when-block (InstrBufferV2
  :117-120 + chisel Queue flush semantics). Main session verdict (2026-08-25):
  under both flush sources (taken branch jump / warp_end), an icache response
  arriving in the same cycle can only be from a wrong path (fall-through
  prefetch) or a residual response of a dead warp — discarding is exactly
  flush's design purpose; a fetch of the correct target address is issued only
  after branch resolution and cannot respond in the same cycle; wid reuse is
  many cycles apart and also cannot coincide. On the bookkeeping side
  (pipe.scala:153-155 pc_rsp reporting fetch completion) wrong-path responses
  have no adverse effect. **But** this analysis led to I-8 (flush single-wid
  preemption), see above. On the Lean side, `ibT_flush_enq_drop` is kept as a
  behavioral pin of this semantics.
- `ibuffer.scala` other review notes (IBuffer.lean Q2-Q6): the :129-136
  `when(io.in.fire)` block has no observable effect (suspected debug residue,
  dead logic) and :124/:128 assigns in.ready twice; SlowDown in.ready requires
  out.ready even for an empty group (:170, conservative bubble, performance
  only); when flush and SlowDown in.fire coincide, the queue head being popped
  and discarded is flush's intended semantics; `instbuffer`, `IBuffer2OpC` have
  no instantiations repo-wide (dead code, not modeled).
- `ALU.scala:81,96` (rocket-lineage lazy semantics): for FN_SGE/FN_SGEU, `out`
  = the **un-inverted slt** (i.e. the 0/1 of `<`); the ≥ semantics exists only
  in `cmp_out`. All consumers verified (2026-08-25): scalar BGE/BGEU
  (DecodeUnit.scala:175-176) and vector VMSLE(U) comparisons (:333-338,
  written back via execution.scala:534's cmp_out) all use only cmp_out; out has
  no consumer for func=13/15. Not a bug; if a future path ever consumes
  SGE/SGEU via out, it becomes a landmine. The Lean model pins the source
  status quo (sa_sge_out_spec / sa_sgeu_out_spec state the `<` semantics).
- `SIMT_STACK.scala:79` (inside dead code): `io.d := Mux(io.index,
  dout(width*2-1,width), dout(width,0))` — `dout(width,0)` is width+1 bits
  assigned to a width-bit port, relying on FIRRTL connection truncation
  semantics to happen to take the low width bits (= q_else); functionally
  correct but fragile. Recorded only because it is dead code.
- `branch_join.scala:58-59`: pop unconditionally does `rd_ptr := rd_ptr - 1`;
  after a push+2×pop sequence from an empty stack, rd_ptr wraps out of bounds
  (≥depth), after which `io.newPC/io.newMask` combinationally read undefined
  out-of-bounds Mem values. All current use sites are gated by `jump=0` and
  unobservable — not a bug; the Lean model models it as "mod depth" and notes
  the divergence boundary in BranchJoin.lean D4.
- `execution.scala:36`: `alu.io.func := ctrl.alu_fn(4,0)`; ScalarALU outputs
  constant 0 for FN_MUL/FN_MAC etc. (operations 20–27) (no corresponding case).
  **The convention verified to hold (2026-08-25)**: in `issue.scala:110-112`,
  the `ctrl.mul` routing branch precedes the isvec and sALU fallback branches
  (chain order tc→sfu→fp→csr→mul→mem→isvec→barrier→sALU), so multiply-class
  operations are all routed to out_MUL (Multiplier) and never enter the
  ScalarALU write-back path. The fragility remains (relies on decode not setting
  overlapping bits), but there is currently no bug.
