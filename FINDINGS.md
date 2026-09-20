# Findings Master Table — 52 Machine-Checked Findings on Ventus

Verification target: **THU-DSP-LAB/ventus-gpgpu**, Chisel snapshot commit
[`6811725`](https://github.com/THU-DSP-LAB/ventus-gpgpu) (2025-11-12), plus its
bundled vendor FPU library (`dependencies/fpuv2`, fudian). All findings were
discovered by machine-checked reasoning over a hand-translated, line-anchored
Lean 4 cycle-level model (toolchain v4.31.0, zero `sorry`), and every reported
defect was then traced back to the Chisel source and validated independently at
the RTL level where applicable.

## Disposition taxonomy

The 52 findings are **not** 52 confirmed bugs. Per the disposition discipline
(mechanism → reachability → harm), they decompose as follows:

| Disposition | Count | Entries |
|---|---|---|
| **Confirmed reachable functional/performance bugs** | **32** | I-5, I-6, I-7, I-11, I-12, I-15, I-16, I-17, I-19, I-21, I-23, I-24, I-25, I-27, I-28, I-29, I-30, I-32, I-33, I-35, I-36, I-37, I-38, I-40, I-42, I-43, I-44, I-46, I-47, I-49, I-50, I-51 |
| **Fix-activated defect** (latent in the original, activated by our fix to a companion bug) | **1** | I-48 |
| **Latent / defense-in-depth** (mechanism proved real, unreachable in the current configuration; each carries a breakage condition) | **10** | I-2, I-4, I-13, I-20, I-22, I-26, I-39, I-41, I-52, I-53 |
| **Excluded suspects** (refuted by proof or by RTL precondition falsification; kept as negative results) | **4** | I-3, I-8, I-9, I-31 |
| **Dead code** | **3** | I-1, I-10, I-14 |
| **Host-contract issues** | **2** | I-34, I-45 |
| **Total** | **52** | |

Counting conventions: the finding registry numbers I-1…I-53 (53 numbered slots);
**I-18 was withdrawn** after RTL reproduction falsified it (a Class-II
mistranslation in our own model — see its report), leaving 52 findings on the
original source and its bundled FPU library. I-52/I-53 concern the bundled
vendor FPU library rather than Ventus proper. Three further report-series
entries (I-B1 ISA-level deviation group, II-1 the I-18 mistranslation record,
III-1…III-3 spec/test-side lessons) bring the per-finding detail reports in
`doc/bugs/` to 58.

## Master table

Columns: **Disposition** per the taxonomy above (Reach = confirmed reachable;
FixAct = fix-activated; Latent = defense-in-depth; Excl = excluded; Dead =
dead code; Host = host contract). **Lean evidence** names the key
original-side theorem(s); full statements in `docs-evidence/THEOREMS.md`;
fixed-side efficacy/regression theorems are listed in
`docs-evidence/THEOREM_TO_BUG.md` (the repair-side development is not part of
this release — see the note below). **RTL repro** cites the dual-channel
campaign (`repro/RESULTS.md`): CS = ChiselSim suite, V = Verilator kernel.
**Patch** identifiers refer to our internal fix manifest (not released); each
finding's fix plan is documented in its per-finding report under `doc/bugs/`.
**Upstream** marks independent fixes on the upstream `develop` branch
(details in `UPSTREAM_CORROBORATION.md`).

| ID | Finding | Disposition | Chisel source (file:line) | Lean evidence (original side) | RTL repro | Patch | Upstream |
|---|---|---|---|---|---|---|---|
| I-1 | `SIMT_STACK` class is dead code in its entirety | Dead | `pipeline/SIMT_STACK.scala:126` | — (dead code; verification target locked to `branch_join`) | — | `i01` | — |
| I-2 | `branch_join_stack` has no overflow protection (exactly sized: depth 32 tight) | Latent | `pipeline/branch_join.scala:24-63` | `bjbMain_no_overflow` + tightness witness | — | assertion recommended | — |
| I-3 | elseOnly branch does not raise `complete`; scoreboard beqReg might never clear | Excl | `pipeline/branch_join.scala:120` | `tD_elseOnly` (exclusion test) | — | — | — |
| I-4 | Scoreboard OpColReg occupancy bit wrongly cleared on same-cycle deq+alloc | Latent | `pipeline/scoreboard.scala:115-118` | bit-level mechanism; unreachability chain | — | `i04` | — |
| I-5 | Multi-WG completion bookkeeping stuck (OHToUInt on non-one-hot input) | Reach | `pipeline/warp_schedule.scala:164-173` | `ws4_stuck_forever` | CS ✓ | `i05` | — |
| I-6 | warpRsp handshake violation (valid pulse does not wait for ready) | Reach | `pipeline/warp_schedule.scala:55` | `c2w6_rsp_dropped_iff_full` | CS ✓ | `i06-i07-i46` | — |
| I-7 | Bookkeeping bit lost on same-cycle warpReq+warpRsp to one WG | Reach | `pipeline/warp_schedule.scala:123-134` | `wsStepBelong`/`wsStepCnt` + T7 | CS ✓ | `i06-i07-i46` | — |
| I-8 | ibuffer warp_end flush preempted by same-cycle branch | Excl | `pipeline/warp_schedule.scala:73-74` | source-level mutual-exclusion argument (`:52`) | CS: precondition falsified | — | — |
| I-9 | RegFileBank bypass forward ignores the write mask | Excl | `pipeline/regfile.scala:57-58` | `wb_i9_unreachable` | — | — | — |
| I-10 | RegFileBank declares SyncReadMem twice; unconnected dead SRAM | Dead | `pipeline/regfile.scala:19` | — (dead hardware not modeled) | — | `i10` | — |
| I-11 | Scalar bank address width derived from VGPR size; cross-warp aliasing | Reach | `top/parameters.scala:22` | `ocI11_full_alias`; `rtI11`/`rtI11max` | CS ✓ | `i11` | — |
| I-12 | **All masked vector instructions (vm=0) and vmerge deadlock** | Reach | `pipeline/operandCollector.scala:214` | `cuWmask_deadlock`; `ocI12_deadlock_system` | CS ✓ + V ✓ | `i12` | — |
| I-13 | collectorUnit regOrder=2 branch mixes old/new control signals | Latent | `pipeline/operandCollector.scala:303-307` | `cuQ129_bankInRdy_accept` | — | `i13` | — |
| I-14 | collectorUnit address lookup tables are dead hardware | Dead | `pipeline/operandCollector.scala:89-98` | — (dead hardware not modeled) | — | `i14` | — |
| I-15 | MULHSU returns the low 32 bits (high-half select omits FN_MULHSU) | Reach | `pipeline/Multiplier.scala:204-205` | `mul_mulhsu_witness` | CS ✓ + V ✓ | `i15` | — |
| I-16 | `IDecodeLUT_A` dead: all LR/SC/AMO silently decoded as NOP | Reach | `pipeline/DecodeUnit.scala:453-468` | full 265-line decode table ported; `decide` checks | CS ✓ + V ✓ | `i16` (trap route; ALTERNATIVE included) | — |
| I-17 | IntDivMod `cnt` width truncation: quotients wrong for large dividends | Reach | `pipeline/IntDivMod.scala:46` | witness; fixed `dvfT_i17_eq_spec` | CS ✓ + V ✓ | `i17` | — |
| I-18 | ~~IntDivMod remainder recovery~~ **WITHDRAWN** (Class-II mistranslation; RTL correct) | — | `pipeline/IntDivMod.scala:70` | — | CS ✗ + V ✗ (both channels) | `i18` is a no-op, **not for upstream** | — |
| I-19 | Stale zeroQReg pollutes remainder of overflow transactions | Reach | `pipeline/IntDivMod.scala:54` | witness; fixed `dvfT_i19_eq_spec` | CS ✓ + V ✓ | `i19` | — |
| I-20 | Booth last-row negation correction lost at general len | Latent | `pipeline/Multiplier.scala:62-69` | `mulCorr_window32_eq0` | — | contract comment recommended | — |
| I-21 | **ShareMem setIdx 8 bits: upper 96 KB of LDS aliases lower 32 KB** | Reach | `pipeline/LSU.scala:71` | `smI21_alias`; `smI21_dead_rows`; `smI21_witness` | CS ✓ + V ✓ (bit-exact) | `i21` | ✓ `05503f8b` |
| I-22 | MSHRv2 to_pipe.valid violates NoWithdraw | Latent | `pipeline/MSHR.scala:106` | `mshr_noWithdraw_violated` | — | `i22` | — |
| I-23 | ICache probe × refill not mutually exclusive: false hits execute garbage | Reach | `L1Cache/ICache/ICache.scala:262` | `icTB_false_hit` | CS ✓ | `i23` | (family, see I-29) |
| I-24 | ICache replacement missing `Reverse`: 2-way degrades to direct-mapped | Reach | `L1Cache/L1TagAccess.scala:496` | `ic_way1_never_valid` | CS ✓ | `i24` | — |
| I-25 | **Completion-response tag read one transaction late; recycled warp misattributes WG completion** | Reach | `pipeline/CTA2warp.scala:77` | T7 witness; `c2w7_tag_safe_next_cycle`; `cuifTi25Leak` | CS ✓ (bit-exact) | `i25` | — |
| I-26 | L1MSHR missReq.ready inconsistent with st0 backpressure | Latent | `L1Cache/L1MSHR.scala:295` | `l1mT7_ready_inconsistent` | CS ✓ (mechanism) | `i26` (behavior-preserving guard) | — |
| I-27 | DCache replacement evicts MRU instead of LRU on full set | Reach | `L1Cache/L1TagAccess.scala:364` | replacement witness series | CS ✓ | `i27` | — |
| I-28 | dirtyMask lane overwrite loses bytes (L2 data loss) | Reach | `L1Cache/L1TagAccess.scala:241-245` | `l1taT_dmBuild_overwrite_real`; `dcT_i28_asymmetry` | CS ✓ (bit-exact) | `i28` | ✓ `ef2fb0c9` |
| I-29 | DCache victim writeback polluted by SRAM LFSR | Reach | `L1Cache/DCache/DCache.scala:623` | `dcT_w1_sram_lfsr` | CS ✗ (not observable under simulator SRAM semantics; residual doubt retained) | `i29` | (family `862db08d`) |
| I-30 | Flush/invalidate response metadata disorder and loss | Reach | `L1Cache/DCache/DCache.scala:413` | `dcT_w2b_stale_instrId`; `dcT_w2c_rsp_lost` | CS: initially blocked by a testbench-stub defect; scenario then runs and exposes I-48 | `i30` | ✓ `ed6fb9d1` |
| I-31 | pc_reconv valid not fire-gated; reconvergence point re-enqueued | Excl | `pipeline/pipe.scala:390` | `pcrMain_i31_excluded` | — | — | — |
| I-32 | fcsr in read table but no write branch: csrrw/csrrs fcsr dropped | Reach | `pipeline/CSR.scala:235` | `csr_fcsr_write_ignored` | V ✓ | `i32` | — |
| I-33 | Vector CSR state (vl/vstart/vcsr/vlenb/vxrm/vxsat) entirely dead | Reach | `pipeline/CSR.scala:262-264` | `csr_vl_write_ignored`; `csr_vl_read_zero` | V ✓ | `i33` | — |
| I-34 | ICache invalidate tied off to false at the AXI top level | Host | `top/GPGPU_top.scala:136` | `Top.lean` W11d/W11e | — | — (driver/doc fix recommended) | — |
| I-35 | L2 Directory flushCount stuck at 1024; second flush out of range | Reach | `L2cache/Directory_test.scala:144-148` | `l2dT_flush_count_stuck`; `l2dT_flush_second_outofrange` | — | `i35` | ✓ `d0c8ba1a` |
| I-36 | L2 Directory write.valid (not fire) pollutes status during flush | Reach | `L2cache/Directory_test.scala:192` | `l2dT_flush_false_hit` | — | `i36` | — |
| I-37 | L2 SourceD `PutFullData && PutPartialData` constant-false; mshr_wait off | Reach | `L2cache/SourceD.scala:142` | `l2s_putput_and_false` | — | `i37` | — |
| I-38 | L2 SourceD stage_8 response payload clobbered under backpressure | Reach | `L2cache/SourceD.scala:82` | `l2sT_stage8_payload_clobber` | — | `i38` | — |
| I-39 | L2 MSHR allocate×a.fire priority inversion (Get never sent) | Latent | `L2cache/MSHR.scala:110-115` | `l2sc_i39_no_alloc_afire` (under E3) | — | `i39` | — |
| I-40 | L2 BankedStore same-row read/write unprotected; LFSR poisons data | Reach | `L2cache/BankedStore.scala:101-110` | `l2sc_i40_witness` | — | `i40` | (family `862db08d`) |
| I-41 | L2 MSHR same-cycle priority family (allocate×sinkd, merge×sinkd) | Latent | `L2cache/MSHR.scala:67-72` | `fmem_i41a`/`fmem_i41b` mutex (fixed side) | — | `i41` | — |
| I-42 | L2 Scheduler mixed flag missing tagMatches guard: silent insertion loss | Reach | `L2cache/Scheduler.scala:214` | `l2dc_i42_witness` | — | `i42` | — |
| I-43 | L2 Scheduler miss-dirty result.ready missing drb.enq.ready: writeback lost | Reach | `L2cache/Scheduler.scala:252` | `l2dc_i43_witness` | — | `i43` | ✓ 2026-08-18 commit |
| I-44 | L2 ListBuffer pool exhaustion × allocate gated on valid not fire: duplicate refill | Reach | `L2cache/Scheduler.scala:190` | DupRsp/DupRspTag models; E3 falsification chain | — | `i44` | ✓ `2e1ae642` |
| I-45 | No hardware checks on register-allocation alignment/size | Host | `cta/resource_table.scala:305-311` | `dcg3` series (Discharge3.lean) | — | — (host discipline) | — |
| I-46 | endprg does not wait for in-flight memory ops; late writeback pollutes recycled warp | Reach | `pipeline/warp_schedule.scala:47,55,180` | EndprgInflight.lean checking machine | — | `i06-i07-i46` | ✓ `0cefc242` |
| I-47 | WG completion reported before flushDCache completes | Reach | `pipeline/warp_schedule.scala:47,55` | FlushOrdering.lean checking machine | — | `i47` | ✓ `7864f4c8` |
| I-48 | Duplicate response between invalidate write-back path and hintAck path | FixAct | `L1Cache/DCache/DCache.scala:413` | FixI48.lean (fixed-model verification) | CS ✓ (on merged patch tree) | `i48` | — |
| I-49 | Fetch-level fixed-priority warp selection starves higher-numbered warps | Reach | `pipeline/warp_schedule.scala:183-186` | Fairness.lean starvation witness (found by *falsifying* a fairness proof) | — | — | — |
| I-50 | vmerge write mask deviates from RVV (tmask=1 ∧ v0[t]=0 lanes not written) | Reach | `pipeline/execution.scala:559` | IsaSpec.lean D6; CapExist.lean | — | — (follow-up of the I-12 fix) | — |
| I-51 | Allocator rtcache/rt mismatch overestimates resources: overlapping register ranges to two WGs | Reach | `cta/allocator.scala:86-92` | RtCacheConsistency.lean machine-checked trace | — | — | — |
| I-52 | fudian ScalarFPU out.bits switches under cross-unit interleaving (Decoupled violation) | Latent | `dependencies/fpuv2/.../FPU.scala:8-45` | FpuWrap.lean (elastic-pipeline model) | — | — (report to OpenXiangShan/fudian) | — |
| I-53 | fudian FMA boundary group (silent drop corner + fragile lockstep + misleading comment) | Latent | `dependencies/fpuv2/.../FMA.scala` | FpuFma.lean | — | — (report to OpenXiangShan/fudian) | — |

## Notes

- **Per-finding detail reports**: `doc/bugs/I-*.md` (58 reports including the
  withdrawn I-18 record and the I-B1/II-1/III-1…3 process entries), each with
  metadata, mechanism analysis, reachability/harm analysis, formal evidence,
  reproduction method, fix plan, and upstream impact. The aggregate analysis is
  `doc/bugs/00-comprehensive-defect-report.md`; the full finding registry with
  evidence chains is `doc/03-bug-reports.md`.
- **RTL reproduction**: 22 of 28 executed cases confirm the predicted behavior
  on the actual RTL (six bugs in both channels independently; several
  bit-exact with the Lean witnesses). Per-case verdicts, the full accounting of
  the six non-reproducing cases, and the patched-RTL regression:
  `repro/RESULTS.md`.
- **Fix plans**: repair patches are **not part of this release package** —
  repair is outside the bug-discovery scope of the paper. The **Patch** column
  above carries the identifiers of our internal fix manifest (38 patches
  covering 39 entries, one patch covering I-6/I-7/I-46); each finding's fix
  plan is documented in its per-finding report under `doc/bugs/`.
- **Upstream corroboration**: 8 findings were independently fixed on the
  upstream `develop` branch (I-21, I-28, I-30, I-35, I-43, I-44, I-46, I-47),
  plus one commit related to the I-23/I-29/I-40 LFSR family. Commit mapping:
  `UPSTREAM_CORROBORATION.md`.
