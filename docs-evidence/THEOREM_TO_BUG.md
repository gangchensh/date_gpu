# Theorem-to-Bug Mapping

For every finding, this table names the **original-side evidence theorem(s)**
(the machine-checked witness, invariant, or exclusion on the model of the
original RTL) and, where a fix was modeled, the **fixed-side theorems**
(efficacy = the original witness turns green on the fixed variant; regression
safety = step-wise equivalence off the trigger domain). Full statements of all
3,662 theorems: `THEOREMS.md`. Verbatim proof excerpts for the three flagship
findings: `excerpts/`. The original-side (`Ventus/`) development ships with
this package under `lean/`; the fixed-side (`VentusF/`) theorems are **not
part of this release** and are listed here for indexing purposes only.

| Finding | Original-side evidence (theorem — file) | Fixed-side theorems (file) |
|---|---|---|
| I-1 | — (dead code; the verification target is explicitly locked to `branch_join`) | — |
| I-2 | `bjbMain_no_overflow` (exact-fit bound, arbitrary event sequences) + tightness witness — `Ventus/SIMT/BranchJoinBounds.lean` | — (overflow assertion recommended) |
| I-3 | `tD_elseOnly` (behavior-pinning test, exclusion) — `Ventus/SIMT/BranchJoin.lean` | — |
| I-4 | bit-level mechanism — `Ventus/Schedule/Scoreboard.lean`; unreachability chain via `pipe`/`warp_schedule` composition | `i4f_race_gone` / `i4f_sbRun_equiv` / `i4f_occ_tracks_busy` — `Ventus/Schedule/I4Fix.lean`; `fschCu_i4_dock` / `fschCuInv_run` — `VentusF/Schedule.lean` |
| I-5 | `ws4_stuck_forever` — `Ventus/Schedule/WarpScheduler.lean` | `fschWs_priEnc_hit` / `fschWs_step_clears_selected` / `fschWsT_i5_drains` — `VentusF/Schedule.lean` |
| I-6 | `c2w6_rsp_dropped_iff_full` — `Ventus/CTA/CTA2warp.lean` | `fschWs_rsp_holds` / `fschWsT_i6_rsp_held` / `fschWsT_i6_completes` — `VentusF/Schedule.lean` |
| I-7 | WarpScheduler T7 (`wsStepBelong`/`wsStepCnt` same-cycle loss) — `Ventus/Schedule/WarpScheduler.lean` | `fschWs_belong_req_set` / `fschWs_cnt_req_set` / `fschWsT_i7_req_survives` — `VentusF/Schedule.lean` |
| I-8 | source-level mutual exclusion (`warp_control.ready`, :52); RTL precondition falsification (repro) | — |
| I-9 | `wb_i9_unreachable` — `Ventus/Schedule/Writeback.lean` | — |
| I-10 | — (dead hardware not modeled) | — |
| I-11 | `ocI11_full_alias` — `Ventus/Schedule/OperandCollector.lean`; `rtI11` / `rtI11max` — `Ventus/CTA/ResourceTable.lean` | `farith_i11_alias_gone` / `farith_i11_full_alias_gone` / `farith_i11_regr` — `VentusF/Arith.lean` |
| I-12 | `cuWmask_deadlock` — `Ventus/Schedule/CollectorUnit.lean`; `ocI12_deadlock_system` — `Ventus/Schedule/OperandCollector.lean`; whole-machine stall witness — `Ventus/SMMaskedMem.lean` ([excerpt](excerpts/I-12-masked-vector-deadlock.lean.txt)) | `fschCu_accept_port3_rsType2` / `fschCuT_masked_collects` / `fschCuT_masked_issues` — `VentusF/Schedule.lean`; `fsmT_i12_mask_returns` / `fsmT_i12_cu_collected` / `fsmT_i12_orig_never` — `VentusF/SM.lean` |
| I-13 | `cuQ129_bankInRdy_accept` — `Ventus/Schedule/CollectorUnit.lean` | `fschCu_i13_uses_new_decode` / `fschCuT_i13_fix_fresh` — `VentusF/Schedule.lean` |
| I-14 | — (dead hardware not modeled; non-modeled items recorded in file headers) | — |
| I-15 | `mul_mulhsu_witness` — `Ventus/Arith/Multiplier.lean` | `farith_mul_mulhsu_fixed` / `farith_mulhsu_divergence_gone` / `farith_mul_regr` — `VentusF/Arith.lean`; `fsmT_i15_mulhsu_wb` — `VentusF/SM.lean` |
| I-16 | full 265-line decode table mechanically ported; `decide` checks — `Ventus/Arith/DecodeUnit.lean` | `f16_route_trap` / `f16_trap_eq_endprg` / `f16_trap_clears_active` / `f16_ws_regr` — `VentusF/FixI16.lean` |
| I-17 | witness (cnt truncation) — `Ventus/Arith/IntDivMod.lean` | `dvfT_i17_eq_spec` / `dvf_pre_cnt_full` / `dvf_exec_eq_orig_of_safe` — `Ventus/Arith/IntDivModFixed.lean` |
| I-18 | **withdrawn** — the mistranslation record is `doc/bugs/II-1` | — |
| I-19 | witness (stale zeroQReg) — `Ventus/Arith/IntDivMod.lean` | `dvfT_i19_fixed` / `dvfT_i19_eq_spec` — `Ventus/Arith/IntDivModFixed.lean` |
| I-20 | `mulCorr_window32_eq0` (unreachability at the verified width) — `Ventus/Arith/Multiplier.lean` | — (contract comment recommended) |
| I-21 | `smI21_alias` / `smI21_dead_rows` / `smI21_witness` — `Ventus/Mem/ShareMem.lean` ([excerpt](excerpts/I-21-sharemem-aliasing.lean.txt)) | `fmem_i21_no_dead_rows` / `fmem_i21_witness_green` / `fmem_i21_regress_low32K` — `VentusF/Mem.lean`; `fsmm_shSetIdx_regr` / `fsmm_shSetIdx_hi_witness` — `VentusF/SMMem.lean` |
| I-22 | `mshr_noWithdraw_violated` — `Ventus/Mem/MSHR.lean`; LSU2WB pass-through verdict — `Ventus/Mem/LSU.lean` | `fschMshrB_no_withdraw` / `fschMshrBT_withdraw_blocked` / `fschMshrB_run_eq_orig` — `VentusF/Schedule.lean` |
| I-23 | `icTB_false_hit` (with SRAMTemplate LFSR-semantics hookup) — `Ventus/Mem/ICache.lean` | `fmem_i23_false_hit_gone` / `fmem_i23_retry_hit_correct` / `fmem_i23_step_regress` — `VentusF/Mem.lean` |
| I-24 | `ic_way1_never_valid` (invariant) — `Ventus/Mem/ICache.lean`; independent re-proof — `Ventus/Mem/L1TagAccess.lean` | `fmem_i24_way1_used` / `fmem_i24_way1_reachable` / `fmem_i24_regress` — `VentusF/Mem.lean` |
| I-25 | T7 witness (tag 0x11 ≠ 0x08) + `c2w7_tag_safe_next_cycle` (safety boundary) — `Ventus/CTA/CTA2warp.lean`; `cuifTi25Leak` (consequence closure) — `Ventus/CTA/CuInterface.lean` ([excerpt](excerpts/I-25-cta2warp-tag-late-read.lean.txt)) | `fschC2w_enq_tag_sampled` / `fschC2w_no_late_read` / `fschC2wT_i25_tag_correct` — `VentusF/Schedule.lean` |
| I-26 | `l1mT7_ready_inconsistent` — `Ventus/Mem/L1MSHR.lean` | `fschL1m_q1_ready_consistent` / `fschL1mT_i26_noFire` / `fschL1mRun_eq_orig` — `VentusF/Schedule.lean` |
| I-27 | replacement witness series — `Ventus/Mem/L1TagAccess.lean`; `l1ta_i24_fix_correct` (in-file numbering) | `fmem_i27_fix_eq_lru` / `fmem_i27_witness_gone` / `fmem_i27_regress` — `VentusF/Mem.lean` |
| I-28 | `l1taT_dmBuild_overwrite_real` — `Ventus/Mem/L1TagAccess.lean`; `dcT_i28_asymmetry` — `Ventus/Mem/DCache.lean` | `fmem_i28_two_lane_merge` / `fmem_i28_witness_fixed` / `fmem_i28_step_regress` — `VentusF/Mem.lean` |
| I-29 | `dcT_w1_sram_lfsr` — `Ventus/Mem/DCache.lean` | `fmem_i29_guard` / `fmem_i29_collision_blocked` / `fmem_i29_ready_regress` — `VentusF/Mem.lean` |
| I-30 | `dcT_w2b_stale_instrId` / `dcT_w2c_rsp_lost` — `Ventus/Mem/DCache.lean` | `fmem_i30a_eq_hintAck` / `fmem_i30_w2b_green` / `fmem_i30_w2c_status` — `VentusF/Mem.lean` |
| I-31 | `pcrMain_i31_excluded` — `Ventus/SIMT/PcReconv.lean` | — |
| I-32 | `csr_fcsr_write_ignored` — `Ventus/Arith/CSR.lean` | `farith_csr_fcsr_write_mask` / `farith_csr_fcsr_write_frm` / `farith_csr_step_regr` — `VentusF/Arith.lean` |
| I-33 | `csr_vl_write_ignored` / `csr_vl_read_zero` — `Ventus/Arith/CSR.lean` | `farith_csr_vl_rw` / `farith_csr_vl_read` / `farith_csr_read_regr` — `VentusF/Arith.lean` |
| I-34 | hardwired-false fact — `Ventus/Top.lean` (W11d/W11e) | — (host contract) |
| I-35 | `l2dT_flush_count_stuck` / `l2dT_flush_second_outofrange` — `Ventus/L2/Directory.lean` | `fmem_i35_fix_vs_orig` / `fmem_i35_count_returns_zero` / `fmem_i35_second_flush_in_range` — `VentusF/MemL2.lean` |
| I-36 | `l2dT_flush_false_hit` — `Ventus/L2/Directory.lean` | `fmem_i36_no_corrupt` / `fmem_i36_false_hit_gone` / `fmem_i36_regress` — `VentusF/MemL2.lean` |
| I-37 | `l2s_putput_and_false` — `Ventus/L2/SourceD.lean` | `fmem_i37_fix_faithful` / `fmem_i37_witness_green` — `VentusF/MemL2.lean` |
| I-38 | `l2sT_stage8_payload_clobber` — `Ventus/L2/SourceD.lean` | `fmem_i38_fix_faithful` / `fmem_i38_witness_green` — `VentusF/MemL2.lean` |
| I-39 | witness — `Ventus/L2/L2MSHR.lean`; `l2sc_i39_no_alloc_afire` (holds under E3) — `Ventus/L2/Scheduler.lean` | `fmem_i39_witness_green` / `fmem_i39_regress` — `VentusF/MemL2.lean` |
| I-40 | `l2sc_i40_witness` — `Ventus/L2/L2MSHR.lean`; reachability trace — `Ventus/L2/Scheduler.lean` | `fmem_i40_read_blocked` / `fmem_i40_witness_green` / `fmem_i40_regress` — `VentusF/MemL2.lean` |
| I-41 | mechanism + witness — `Ventus/L2/L2MSHR.lean`; E1 discharge — `Ventus/L2/Discharge.lean` | `fmem_i41a_alloc_sinkd_mutex` / `fmem_i41b_merge_sinkd_mutex` — `VentusF/MemL2.lean` |
| I-42 | `l2dc_i42_witness` — `Ventus/L2/Discharge.lean`; combinational invariants — `Ventus/L2/Scheduler.lean` | `fmem_i42_guard` / `fmem_i42_witness_green` / `fmem_i42_regress` — `VentusF/MemL2.lean` |
| I-43 | `l2dc_i43_witness` — `Ventus/L2/Discharge.lean` | `fmem_i43s_no_leak` / `fmem_i43_witness_green` / `fmem_i43s_regress` — `VentusF/MemL2.lean` |
| I-44 | duplicate-refill witness — `Ventus/Mem/DupRsp.lean` / `Ventus/Mem/DupRspTag.lean`; E3 falsification chain — `Ventus/L2/Discharge.lean` | `dbt_fix_orphan_noop` — `Ventus/Mem/DupRspTag.lean`; `fmem_i44_alloc_imp_fire` / `fmem_i44_e3_by_construction` / `fmem_i44_e3_witness_green` / `fmem_i44_regress` — `VentusF/MemL2.lean` |
| I-45 | `dcg3` series + `dcg3_wba1_rt_run_aligned` (positive invariant) — `Ventus/Spec/Discharge3.lean` | `farith_i45_guard_iff` / `farith_i45_guard_accept_witness` — `VentusF/Arith.lean` |
| I-46 | cross-module risk-chain checking machine — `Ventus/Spec/EndprgInflight.lean` | `fschWs_endprg_gated` / `fschWsT_i46_blocked` / `fschWsT_i46_released` — `VentusF/Schedule.lean`; `fsmmT_i46_endprg_after_drain` — `VentusF/SMMem.lean` |
| I-47 | cross-module risk-chain checking machine — `Ventus/Spec/FlushOrdering.lean` | `fmem_i47_report_safe` / `fmem_i47_witness_green` / `fmem_i47_regress` — `VentusF/MemL2.lean` |
| I-48 | witness reuses `dcStep`/`dcRun`/`rspLog` — `Ventus/Mem/DCache.lean` | `f48_fix_at_most_one` / `f48_fix_exactly_one` / `f48T_fix_single` / `f48T_no_early_rsp` — `VentusF/FixI48.lean` |
| I-49 | `fair_starvation` / `fair_starve_trace` (witness, found by *falsifying* a fairness proof); `fair_selected_of_min` / `fair_mem_trace` (conditional positive forms) — `VentusF/Fairness.lean` | — (policy change; to be discussed upstream) |
| I-50 | RVV deviation pinned — `VentusF/IsaSpec.lean` (D6); `VentusF/CapExist.lean`; `VentusF/RefineVec.lean` | — (fix designed; model + fix-verify pending) |
| I-51 | `rtcc_w_corrupt` / `rtcc_w_overlap` (failure witnesses); `rtccInv_run` (total-conservation invariant) — `Ventus/CTA/RtCacheConsistency.lean` | — (fix direction recorded in the report) |
| I-52 | `fwSfpu_stable_violation` (witness); `fwSfpu_out_irrevocable_of_singleFu` (conditional positive form) — `VentusF/FpuWrap.lean` | — (vendor library; report to OpenXiangShan/fudian) |
| I-53 | boundary-point witnesses — `VentusF/FpuFma.lean` | — (vendor library; report to OpenXiangShan/fudian) |

## Notes

- Naming conventions: original-side witnesses carry the finding number
  (`smI21_*`, `ocI12_*`, `l2dc_i42_*`, `rtcc_*`) or the module prefix of their
  file; fixed-side theorems carry an `f` prefix (`fmem_*`, `fsch*` , `farith_*`,
  `fsm*`/`fsmm*` for SM-level integration). A small number of in-file names
  predate the finding registry (e.g., `l1ta_i24_fix_correct` concerns I-27);
  such cases are annotated inline.
- `#print axioms` certificates for every theorem: `AXIOM_AUDIT.md` (index) and
  `AXIOM_AUDIT_OUTPUT.txt` (full output).
