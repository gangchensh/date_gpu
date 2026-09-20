# Axiom Audit Index (`#print axioms`, auto-extracted)

> Every verification module file ends with a `#print axioms` audit block.
> This index lists, per file, exactly which theorems are audited (the audit
> command lines, verbatim).
>
> **The actual audit output is archived in `AXIOM_AUDIT_OUTPUT.txt`** (same
> directory): all 94 `.lean` files re-elaborated with `lake env lean`
> (exit=0 for every file), yielding 1,077 audit outputs (1,057
> "depends on axioms" + 20 "does not depend on any axioms"), with **zero
> `sorryAx` and zero errors**. The entire corpus depends only on
> `propext`/`Quot.sound`/`Classical.choice` (Lean kernel standard), plus
> per-theorem decision-procedure trust axioms where used:
> `_native.bv_decide.ax_*` (1,887 references, native LRAT certificates) and
> `_native.native_decide.ax_*` (397 references, compiled-evaluation trust,
> the `Lean.ofReduceBool` family).

### `Ventus/Arith/CSR.lean`

- line 1020: `#print axioms csrWdata_s`
- line 1021: `#print axioms csr_read_mstatus_bits`
- line 1022: `#print axioms csr_read_fcsr_bits`
- line 1023: `#print axioms csr_mscratch_rw`
- line 1024: `#print axioms csr_mstatus_write_mask`
- line 1025: `#print axioms csr_frm_set_narrow`
- line 1026: `#print axioms csr_fcsr_write_ignored`
- line 1027: `#print axioms csr_vl_write_ignored`
- line 1028: `#print axioms csr_isvec_no_state`
- line 1029: `#print axioms csr_custom0_rpc`
- line 1030: `#print axioms csr_write_preserves_cta_regs`
- line 1031: `#print axioms csr_step_dead_vcsr`
- line 1032: `#print axioms csr_cta_threadid`
- line 1033: `#print axioms csrLdsCat_eq`
- line 1034: `#print axioms csr_lsu_tid_mul`
- line 1035: `#print axioms csrExe_untouched`

### `Ventus/Arith/Classify.lean`

- line 453: `#print axioms cls_t1_negInf_pairwise`
- line 454: `#print axioms cls_t1_sNaN_pairwise`
- line 455: `#print axioms cls_t2_exhaustive`
- line 456: `#print axioms cls_t3_isInfOrNaN`
- line 457: `#print axioms cls_t3_isSubnormalOrZero`
- line 458: `#print axioms cls_t4_isPosNormal`
- line 459: `#print axioms cls_t4_isSNaN`
- line 460: `#print axioms cls_t4_isQNaN`

### `Ventus/Arith/DecodeUnit.lean`

- line 773: `#print axioms dec_overlap_imf`
- line 774: `#print axioms dec_overlap_v`
- line 775: `#print axioms dec_overlap_vl`
- line 776: `#print axioms dec_overlap_vc`
- line 777: `#print axioms dec_default_safe`
- line 778: `#print axioms decDecode_mem`
- line 779: `#print axioms dec_fn_ge32_implies_vec_or_fp`
- line 780: `#print axioms dec_mul_fn_lt32`
- line 781: `#print axioms dec_regidx1_noext`
- line 782: `#print axioms dec_force_rm_rtz_spec`

### `Ventus/Arith/DecodeUnitProps.lean`

- line 177: `#print axioms decH1aRows_all`
- line 178: `#print axioms decH1cRows_all`
- line 179: `#print axioms decH1a`
- line 180: `#print axioms decH1b`
- line 181: `#print axioms decH1c`
- line 182: `#print axioms decH1_sfu_specOk`

### `Ventus/Arith/ExeMul.lean`

- line 1116: `#print axioms exmQStep_pipe`
- line 1117: `#print axioms exmPipe2_two_cycles`
- line 1118: `#print axioms exmPipe2_stall_hold`
- line 1119: `#print axioms exmAluExe_latency_bN`
- line 1120: `#print axioms exmAluExe_latency_bB`
- line 1121: `#print axioms exmAluExe_latency_bJ`
- line 1122: `#print axioms exmMulExec_prep`
- line 1123: `#print axioms exmMulLaneOut_mulhsu`
- line 1124: `#print axioms exmMulLaneOut_mulhsu_witness`
- line 1125: `#print axioms exmVMulExe_latency_wvd`
- line 1126: `#print axioms exmVMulExe_latency_wxd`
- line 1127: `#print axioms exmShiftN_spec`
- line 1128: `#print axioms exmRRAssembleN_spec`
- line 1129: `#print axioms exmV2_result_spec`
- line 1130: `#print axioms exmV2_test_continuous`

### `Ventus/Arith/ExeSFU.lean`

- line 1274: `#print axioms exsGrpSeqMg_nodup`
- line 1275: `#print axioms exsGrpSeqMg_complete`
- line 1276: `#print axioms exsGrpSeqMg_sound`
- line 1277: `#print axioms exsGrpSeqMg_sorted`
- line 1278: `#print axioms exsGrpSeq_lane_exactly_once`
- line 1279: `#print axioms exsSfu_vec_lane_correct`
- line 1280: `#print axioms exsSfu_mask_fidelity`
- line 1281: `#print axioms exsSfu_vec_terminates`
- line 1282: `#print axioms exsSfu_finish_stable`
- line 1283: `#print axioms exsSfu_q3_silent_drop`
- line 1284: `#print axioms exsFpu_q12_drop`
- line 1285: `#print axioms exsTc_wvdMask_allOnes`
- line 1286: `#print axioms exs_test_vec_lane3`
- line 1287: `#print axioms exs_test_bug1_lane3`
- line 1288: `#print axioms exs_test_reverse`

### `Ventus/Arith/ExeVALU.lean`

- line 883: `#print axioms exv_vmandnot_spec`
- line 884: `#print axioms exv_vmerge_spec`
- line 885: `#print axioms exv_sge_cmp_spec`
- line 886: `#print axioms exv_v1_sge_out_spec`
- line 887: `#print axioms exv_ifmask_two_batch_correct`
- line 888: `#print axioms exv_ifmask_maxIter3_broken`
- line 889: `#print axioms exvSplit_add_trace`
- line 890: `#print axioms exvSplit_simt_ifMask_broken_trace`
- line 891: `#print axioms exvSplit_vmerge_mask_not_shifted_trace`
- line 892: `#print axioms exvSplit_simt_drop_witness_trace`

### `Ventus/Arith/IntDivMod.lean`

- line 791: `#print axioms div_t1_divByZero`
- line 792: `#print axioms div_t1_overflow`
- line 793: `#print axioms div_t1_zeroQ`
- line 794: `#print axioms div_compute_finish`
- line 795: `#print axioms div_terminates`
- line 796: `#print axioms div_finish_stable`
- line 797: `#print axioms div_test_xlen4_exhaustive`
- line 798: `#print axioms div_test_xlen8_exhaustive`
- line 799: `#print axioms div_test_32_bug1_unsigned`
- line 800: `#print axioms div_test_32_bug3_unsigned`
- line 801: `#print axioms div_test_stale_zeroQ_bug2`

### `Ventus/Arith/IntDivModFixed.lean`

- line 781: `#print axioms dvfT_i17_unsigned`
- line 782: `#print axioms dvfT_i18_unsigned`
- line 783: `#print axioms dvfT_i18_random_s`
- line 784: `#print axioms dvfT_i19_fixed`
- line 785: `#print axioms dvf_t1_divByZero`
- line 786: `#print axioms dvf_t1_overflow`
- line 787: `#print axioms dvf_t1_zeroQ`
- line 788: `#print axioms dvf_pre_cnt_full`
- line 789: `#print axioms dvf_compute_finish`
- line 790: `#print axioms dvf_terminates`
- line 791: `#print axioms dvf_selPos_ne_selNeg`
- line 792: `#print axioms dvf_test_xlen4_exhaustive`
- line 793: `#print axioms dvf_test_xlen8_exhaustive`
- line 794: `#print axioms dvf_commonR_eq_orig_of_not_neg`
- line 795: `#print axioms dvf_step_match`
- line 796: `#print axioms dvf_run_match`
- line 797: `#print axioms dvf_exec_eq_orig_of_safe`
- line 798: `#print axioms dvf_test_regr_xlen4`
- line 799: `#print axioms dvf_test_regr_xlen8`
- line 800: `#print axioms dvfT_regr_multitxn`

### `Ventus/Arith/Multiplier.lean`

- line 2236: `#print axioms mulC53_spec`
- line 2237: `#print axioms mulFidRow0`
- line 2238: `#print axioms mulFidMid`
- line 2239: `#print axioms mulFidLast`
- line 2240: `#print axioms mulBaseRow0`
- line 2241: `#print axioms mulBaseMid`
- line 2242: `#print axioms mulBaseLast`
- line 2243: `#print axioms mulTelescope`
- line 2244: `#print axioms mulWindow32_eq6`
- line 2245: `#print axioms mulCorr_window32_eq0`
- line 2246: `#print axioms mul_sext33_corr0`
- line 2247: `#print axioms mul_zext33_corr0`
- line 2248: `#print axioms mulPlacedSum_eq`
- line 2249: `#print axioms mulPlacedSum_eq_of_corr0`
- line 2250: `#print axioms mulPlacedSum_quirk`
- line 2251: `#print axioms mulRes_mulhsu`
- line 2252: `#print axioms mul_mulhsu_diverges`
- line 2253: `#print axioms mul_mulhsu_witness`
- line 2254: `#print axioms mul_wrap_macc`
- line 2255: `#print axioms mul_wrap_nmsub`
- line 2256: `#print axioms mulPipe_two_cycles`
- line 2257: `#print axioms mul_dataModule8_exhaustive`
- line 2258: `#print axioms mul_dm33_sext_zext_witness`

### `Ventus/Arith/MultiplierCSA.lean`

- line 1410: `#print axioms mcsaDataModule33_eq_placedSum`
- line 1411: `#print axioms mcsaDataModule33_eq_placedSum'`

### `Ventus/Arith/RegFile.lean`

- line 528: `#print axioms rfS_read_after_write`
- line 529: `#print axioms rfS_write_preserves`
- line 530: `#print axioms rfV_mem_masked_merge`
- line 531: `#print axioms rfV_bypass_mem_diverge`
- line 532: `#print axioms rfImm_U_spec`
- line 533: `#print axioms rfImm_default_quirk`

### `Ventus/Arith/ScalarALU.lean`

- line 388: `#print axioms sa_add_spec`
- line 389: `#print axioms sa_sra_spec`
- line 390: `#print axioms sa_slt_cmp_spec`
- line 391: `#print axioms sa_sgeu_cmp_spec`
- line 392: `#print axioms sa_min_spec`
- line 393: `#print axioms sa_mul_family_out_zero`

### `Ventus/CTA/Allocator.lean`

- line 857: `#print axioms alc_h_alloc_slot`
- line 858: `#print axioms alc_h_alloc_fit`
- line 859: `#print axioms alc_assert91`
- line 860: `#print axioms alcInv_step`
- line 861: `#print axioms alcInv_run`
- line 862: `#print axioms alc_hold_alloc`

### `Ventus/CTA/CTA2warp.lean`

- line 592: `#print axioms c2w1_alloc_idx_clear`
- line 593: `#print axioms c2w1_alloc_rsp_no_clash`
- line 594: `#print axioms c2w2_rsp_clears`
- line 595: `#print axioms c2w3_step_full_idx_mono`
- line 596: `#print axioms c2w4_full_stuck_run`
- line 597: `#print axioms c2w6_rsp_dropped_iff_full`
- line 598: `#print axioms c2w7_tag_safe_next_cycle`
- line 599: `#print axioms c2wFifo_simulates`

### `Ventus/CTA/CtaScheduler.lean`

- line 951: `#print axioms ctas_tag_roundtrip`
- line 952: `#print axioms ctas_step_inv`
- line 953: `#print axioms ctas_no_oversubscribe`
- line 954: `#print axioms ctas_dealloc_only_when_complete`
- line 955: `#print axioms ctas_dealloc_frees`

### `Ventus/CTA/CuInterface.lean`

- line 1344: `#print axioms cuif_split_tag`
- line 1345: `#print axioms cuif_split_deq_last`
- line 1346: `#print axioms cuif_split_countdown`
- line 1347: `#print axioms cuif_split_load`
- line 1348: `#print axioms cuif_finish_exact`
- line 1349: `#print axioms cuif_done_read`
- line 1350: `#print axioms cuif_cnt_update`
- line 1351: `#print axioms cuif_dealloc_exact`
- line 1352: `#print axioms cuif_dealloc_wgId`
- line 1353: `#print axioms cuif_dealloc_no_double`
- line 1354: `#print axioms cuifInv_step`
- line 1355: `#print axioms cuifInv_run`

### `Ventus/CTA/ResourceTable.lean`

- line 1780: `#print axioms rt_alloc_base_bounds`
- line 1781: `#print axioms rt_alloc_disjoint`
- line 1782: `#print axioms rt_step_wf`
- line 1783: `#print axioms rt_alloc_used`
- line 1784: `#print axioms rt_dealloc_used`
- line 1785: `#print axioms rt_sum_le_N`
- line 1786: `#print axioms rtScan_max`
- line 1787: `#print axioms rt_scan_ge_iff`
- line 1788: `#print axioms rt_find_of_scan`
- line 1789: `#print axioms rt_dealloc_notin`
- line 1790: `#print axioms rt_sort3_out`
- line 1791: `#print axioms rt_bw_empty_size_sgpr`

### `Ventus/CTA/WgBuffer.lean`

- line 705: `#print axioms wgb_h_wgb_discharge`
- line 706: `#print axioms wgb_step_count`
- line 707: `#print axioms wgbInv_step`
- line 708: `#print axioms wgb_alloc_capture`
- line 709: `#print axioms wgb_cuif_capture`
- line 710: `#print axioms wgb_no_double_clear`
- line 711: `#print axioms wgb_rrPick_mem`
- line 712: `#print axioms wgbT7_reorder_witness`

### `Ventus/L2/Directory.lean`

- line 679: `#print axioms l2d_lfsr_orbit_stable`
- line 680: `#print axioms l2d_lfsr_reach`
- line 681: `#print axioms l2d_lfsr_cycle`
- line 682: `#print axioms l2d_lfsr_victim_cover`
- line 683: `#print axioms l2d_hit_mutual`
- line 684: `#print axioms l2dT_wipe`
- line 685: `#print axioms l2dT_write_then_read_hit`
- line 686: `#print axioms l2dT_miss_victim_lfsr`
- line 687: `#print axioms l2dT_flush_count_stuck`
- line 688: `#print axioms l2dT_flush_second_outofrange`
- line 689: `#print axioms l2dT_write_during_flush_corrupts`
- line 690: `#print axioms l2dT_flush_false_hit`

### `Ventus/L2/Discharge.lean`

- line 718: `#print axioms l2dc_i42_witness`
- line 719: `#print axioms l2dc_i43_witness`
- line 720: `#print axioms l2dc_i43_dir_results`
- line 721: `#print axioms l2dc_i43_sourced_busy`
- line 722: `#print axioms l2dc_lb_pool_exhausted`
- line 723: `#print axioms l2dc_e3_counterexample`
- line 724: `#print axioms l2dc_e3_falsified`
- line 725: `#print axioms l2dc_e3_inv1_broken`
- line 726: `#print axioms l2dc_e3_env_allocs`
- line 727: `#print axioms l2dc_e1_step`
- line 728: `#print axioms l2dc_e1_init`
- line 729: `#print axioms l2dc_e1_run`

### `Ventus/L2/L2Channels.lean`

- line 803: `#print axioms parse_expand`
- line 804: `#print axioms expand_parse`
- line 805: `#print axioms lbLowestOne_spec`
- line 806: `#print axioms lbPushReady_iff`
- line 807: `#print axioms sinkA_listsSet_iff`
- line 808: `#print axioms sinkA_hint_gated`
- line 809: `#print axioms sinkA_step_idle`
- line 810: `#print axioms lbT_sim_pushpop`
- line 811: `#print axioms sinkAT_put_pop_reuse`
- line 812: `#print axioms sinkAT_hint_gate`
- line 813: `#print axioms hold_holds`

### `Ventus/L2/L2MSHR.lean`

- line 979: `#print axioms l2m_step_alloc`
- line 980: `#print axioms l2m_scheA_noWithdraw`
- line 981: `#print axioms l2m_sinkd_effect`
- line 982: `#print axioms l2m_sinkd_dir_set`
- line 983: `#print axioms l2m_dirValid_get`
- line 984: `#print axioms l2mByteLanes_getLsbD`
- line 985: `#print axioms l2mFullMask_getLsbD`
- line 986: `#print axioms l2mMergeData_getLsbD`
- line 987: `#print axioms l2mMergeData_byte`
- line 988: `#print axioms l2mFullMask_allOnes`
- line 989: `#print axioms l2mMergeData_allOnes`
- line 990: `#print axioms l2mMergeData_zero`
- line 991: `#print axioms l2mBsRowAddr_inj`
- line 992: `#print axioms l2mBsWriteLanes_read`
- line 993: `#print axioms l2mBsWriteRow_read_same`
- line 994: `#print axioms l2mBsWriteRow_read_diff`
- line 995: `#print axioms l2mBsReadRow_byte`
- line 996: `#print axioms l2mBsStep_rdata`
- line 997: `#print axioms l2mT6_trace`
- line 998: `#print axioms l2mBsT2_byte_mask`

### `Ventus/L2/Scheduler.lean`

- line 983: `#print axioms l2sc_i39_no_alloc_afire`
- line 984: `#print axioms l2sc_inv1_preserved`
- line 985: `#print axioms l2sc_inv1_run`
- line 986: `#print axioms l2sc_i41a_no_alloc_sinkd`
- line 987: `#print axioms l2sc_i41b_no_merge_sinkd`
- line 988: `#print axioms l2sc_q4_sinkd_always_accepted`
- line 989: `#print axioms l2sc_alloc_exclusive`
- line 990: `#print axioms l2sc_alloc_exists_unique`
- line 991: `#print axioms l2sc_sinkd_unique`
- line 992: `#print axioms l2sc_i40_witness`

### `Ventus/L2/SourceD.lean`

- line 531: `#print axioms l2s_putput_and_false`
- line 532: `#print axioms l2sT_mshr_wait_put_miss`
- line 533: `#print axioms l2sT_d_get_hit`
- line 534: `#print axioms l2sT_d_addr`
- line 535: `#print axioms l2sT_trace_read_hit`
- line 536: `#print axioms l2sT_trace_write_hit`
- line 537: `#print axioms l2sT_trace_miss_dirty`
- line 538: `#print axioms l2sT_trace_write_miss_noalloc`
- line 539: `#print axioms l2sT_stage8_accepts_req`
- line 540: `#print axioms l2sT_stage8_payload_clobber`

### `Ventus/Mem/DCache.lean`

- line 1064: `#print axioms dc_blockAddr_roundtrip`
- line 1065: `#print axioms dc_genControl_onehot`
- line 1066: `#print axioms dcRemapMask_includes`
- line 1067: `#print axioms dcWriteMissMask_complete`
- line 1068: `#print axioms dcT_i28_asymmetry`
- line 1069: `#print axioms dcwDistinct_push`
- line 1070: `#print axioms dc_fire_excludes_allocWrite`
- line 1071: `#print axioms dcT_w1_collision_reachable`
- line 1072: `#print axioms dcT_w1_sram_lfsr`
- line 1073: `#print axioms dcT_w2a_normal`
- line 1074: `#print axioms dcT_w2b_stale_instrId`
- line 1075: `#print axioms dcT_w2c_rsp_lost`

### `Ventus/Mem/DupRsp.lean`

- line 408: `#print axioms dbr_l1m_guard_exact`
- line 409: `#print axioms dbr_l1m_orphan_no_coreRsp`
- line 410: `#print axioms dbr_l1m_orphan_absorbed_ready`
- line 411: `#print axioms dbr_l1m_orphan_subValid_kept`
- line 412: `#print axioms dbr_l1m_orphan_tables_kept`
- line 413: `#print axioms dbr_l1m_orphan_stall_toggle`
- line 414: `#print axioms dbr_l1m_orphan_statusR`
- line 415: `#print axioms dbr_l1m_reused_consumed`
- line 416: `#print axioms dbrW1_genuine_drains`
- line 417: `#print axioms dbrW1_orphan_absorbed`
- line 418: `#print axioms dbrW1_sole_effect_stall`
- line 419: `#print axioms dbrW2_realloc`
- line 420: `#print axioms dbrW2_dup_emits_B_coreRsp`
- line 421: `#print axioms dbrW2_genuine_orphaned`
- line 422: `#print axioms dbr_mshr_no_guard`
- line 423: `#print axioms dbr_mshr_orphan_cm_kept`
- line 424: `#print axioms dbr_mshr_orphan_tag_kept`
- line 425: `#print axioms dbr_mshr_orphan_complete8_kept`
- line 426: `#print axioms dbr_mshr_rsp_premature_complete`
- line 427: `#print axioms dbrW3_normal_flow`
- line 428: `#print axioms dbrW3_realloc`
- line 429: `#print axioms dbrW3_dup_premature`
- line 430: `#print axioms dbrW3_genuine_blocked`
- line 431: `#print axioms dbrW3_genuine_orphan`

### `Ventus/Mem/DupRspTag.lean`

- line 422: `#print axioms dbtT_oh2`
- line 423: `#print axioms dbt_notfull_dup_way_diff`
- line 424: `#print axioms dbt_fill_idempotent_of_same`
- line 425: `#print axioms dbt_fill_makes_dup_tags`
- line 426: `#print axioms dbt_dup_twohot`
- line 427: `#print axioms dbt_dup_hit_reads_dup_copy`
- line 428: `#print axioms dbt_storeHit_times_tie`
- line 429: `#print axioms dbt_tie_evicts_way1`
- line 430: `#print axioms dbt_fix_orphan_noop`
- line 431: `#print axioms dbtW1_dup_installed`
- line 432: `#print axioms dbtW2_storeHit_dup_copy`
- line 433: `#print axioms dbtW3_evict_fresh_copy`
- line 434: `#print axioms dbtW_stale_read_contrast`
- line 435: `#print axioms dbtW5_idempotent_full_mru`
- line 436: `#print axioms dbtW_capacity`

### `Ventus/Mem/ICache.lean`

- line 1645: `#print axioms ic_tag_collision_lfsr`
- line 1646: `#print axioms ic_data_collision_lfsr`
- line 1647: `#print axioms ic_false_hit_st1`
- line 1648: `#print axioms ic_deqFire_indep_probe`
- line 1649: `#print axioms icMshr_primary_alloc`
- line 1650: `#print axioms icMshr_secondary_merge`
- line 1651: `#print axioms icMshr_rsp_fire`
- line 1652: `#print axioms icMshr_rsp_last_frees`
- line 1653: `#print axioms icMshrStep_inv`
- line 1654: `#print axioms icMshr_no_loss`
- line 1655: `#print axioms icVictimMask_way0_valid_only`
- line 1656: `#print axioms ic_way1_never_valid`
- line 1657: `#print axioms icDataSt1_of_onehot`
- line 1658: `#print axioms icTB_false_hit`
- line 1659: `#print axioms icTA_false_miss`

### `Ventus/Mem/L1MSHR.lean`

- line 923: `#print axioms l1m_rspInReady_simplify`
- line 924: `#print axioms l1m_reqFire_not_rspInFire`
- line 925: `#print axioms l1m_rspOut_noWithdraw`
- line 926: `#print axioms l1m_rspOut_stable`
- line 927: `#print axioms l1m_st0_primary_full`
- line 928: `#print axioms l1m_st0_secondary_full`
- line 929: `#print axioms l1mEntryNext_invalid`
- line 930: `#print axioms l1mFirstOne2_spec`
- line 931: `#print axioms l1mPriEnc4_hit`
- line 932: `#print axioms l1m_primary_alloc`
- line 933: `#print axioms l1m_secondary_merge`
- line 934: `#print axioms l1m_rsp_consume`
- line 935: `#print axioms l1mMatchProbe_cpop_le_one`
- line 936: `#print axioms l1mDistinct_step_primary`
- line 937: `#print axioms l1m_q1_ready_inconsistent`

### `Ventus/Mem/L1TagAccess.lean`

- line 650: `#print axioms l1ta_tagHit2_iff`
- line 651: `#print axioms l1ta_replD2_full_evicts_mru`
- line 652: `#print axioms l1ta_replD2_full_ne_lru`
- line 653: `#print axioms l1ta_i24_mapping`
- line 654: `#print axioms l1ta_i24_way1_never_valid`
- line 655: `#print axioms l1taT_two_refill_contrast`
- line 656: `#print axioms l1taT_stale_dirty_after_invalidate`
- line 657: `#print axioms l1taT_dmBuild_overwrite_real`
- line 658: `#print axioms l1taT_refill_then_hit`

### `Ventus/Mem/LSU.lean`

- line 1742: `#print axioms lsuBex_byte`
- line 1743: `#print axioms lsuBex_half`
- line 1744: `#print axioms lsuBex_default`
- line 1745: `#print axioms lsuCntDone_false`
- line 1746: `#print axioms lsuPrioEncF_spec_set`
- line 1747: `#print axioms lsuMaskNext_pe`
- line 1748: `#print axioms lsuT_progress`
- line 1749: `#print axioms lsuT_progress_dcache`
- line 1750: `#print axioms lsuT_progress_shared`
- line 1751: `#print axioms lsuT_dcache_hold`
- line 1752: `#print axioms lsuT_dcache_irrevocable`
- line 1753: `#print axioms lsuT_shared_hold`
- line 1754: `#print axioms lsuT_ssave_hold`
- line 1755: `#print axioms lsuT_ssave_fire`
- line 1756: `#print axioms lsuT_ssave_entry`
- line 1757: `#print axioms lsuT_accept_mask_scalar`
- line 1758: `#print axioms lsuT_accept_aq`
- line 1759: `#print axioms lsuT_flush_accept`
- line 1760: `#print axioms lsuT_flush_opcode`
- line 1761: `#print axioms lsuT_entryID_hold`
- line 1762: `#print axioms lsuT_state_legal_step`
- line 1763: `#print axioms lsuT_state_legal_run`
- line 1764: `#print axioms lsu2wb_rspFire_iff`
- line 1765: `#print axioms lsu2wb_retract_safe`
- line 1766: `#print axioms lsuSbInv_step`
- line 1767: `#print axioms lsuSbFull_iff`
- line 1768: `#print axioms lsuSbStep_push_count`
- line 1769: `#print axioms lsuSbStep_pop_count`
- line 1770: `#print axioms lsuSbEmpty_iff`
- line 1771: `#print axioms lsuSbStepAll_other`
- line 1772: `#print axioms lsuReqReady_blocked`

### `Ventus/Mem/MSHR.lean`

- line 713: `#print axioms mshrPriEnc_bit`
- line 714: `#print axioms mshr_out_entry_needs_ready`
- line 715: `#print axioms mshr_withdraw`
- line 716: `#print axioms mshr_sadd_alloc_consistent`
- line 717: `#print axioms mshr_addrFire_entry_free`
- line 718: `#print axioms mshr_outFire_entry_cleared`
- line 719: `#print axioms mshr_fastpath_complete_next`
- line 720: `#print axioms mshr_noWithdraw_violated`

### `Ventus/Mem/SRAMTemplate.lean`

- line 687: `#print axioms sram_read_clean`
- line 688: `#print axioms sram_read_after_write`
- line 689: `#print axioms sram_bypass_forward`
- line 690: `#print axioms sram_lfsr_bypass`
- line 691: `#print axioms sram_hold_holds`
- line 692: `#print axioms sram_resetStep_mem`
- line 693: `#print axioms sramT_lfsr_bypass`

### `Ventus/Mem/ShareMem.lean`

- line 675: `#print axioms smI21_alias`
- line 676: `#print axioms smI21_dead_rows`
- line 677: `#print axioms smI21_witness`
- line 678: `#print axioms smPrioOH_onehot`
- line 679: `#print axioms sm_bytes_word_roundtrip`
- line 680: `#print axioms smT1_read_rsp`
- line 681: `#print axioms smT4_serialized_mem`
- line 682: `#print axioms smT6_read_pipelined`

### `Ventus/MultiSM.lean`

- line 312: `#print axioms msmT_sm0_wire`
- line 313: `#print axioms msmT_sm1_wire`
- line 314: `#print axioms msmT_view_same`
- line 315: `#print axioms msmT_wbUpd_spec`
- line 316: `#print axioms msmT_merge_priority`
- line 317: `#print axioms msmTraceA_ok`

### `Ventus/MultiSMCTA.lean`

- line 1038: `#print axioms mctTraceA_evt`
- line 1039: `#print axioms mctTraceA_ok`
- line 1040: `#print axioms mctTraceB_ok`
- line 1041: `#print axioms mctRtB_disjoint`

### `Ventus/MultiSML2.lean`

- line 641: `#print axioms mslTraceA_ok`
- line 642: `#print axioms mslTraceB_ok`

### `Ventus/Pipe.lean`

- line 576: `#print axioms pipeScoreboardBusy_bit`
- line 577: `#print axioms pipe_w2_full_blocks_enq`
- line 578: `#print axioms pipe_sb_ifFire_spec`
- line 579: `#print axioms pipe_sb_brCtrl_spec`
- line 580: `#print axioms pipe_vmask_sub_outMask`
- line 581: `#print axioms pipe_issue_partition`
- line 582: `#print axioms pipe_i2_mask_chain`
- line 583: `#print axioms pipe_i2_first_link`
- line 584: `#print axioms pipe_i3_branch_complete_or_fetch`
- line 585: `#print axioms pipe_i3_vbranch_clears`
- line 586: `#print axioms pipe_i3_join_clears`
- line 587: `#print axioms pipe_sb_beqReg_cleared`
- line 588: `#print axioms pipe_i4_gate_chain`
- line 589: `#print axioms pipe_i4_gate_chain_beq`
- line 590: `#print axioms pipe_i31_witness`

### `Ventus/SIMT/BranchJoin.lean`

- line 630: `#print axioms bjT1_ptr_conserve`
- line 631: `#print axioms bjT2_mask_restore`
- line 632: `#print axioms bjT3_underflow_safe`
- line 633: `#print axioms bjT4_mask_partition`
- line 634: `#print axioms bjT5_push_priority`

### `Ventus/SIMT/BranchJoinBounds.lean`

- line 693: `#print axioms bjbPopcount_or_of_disjoint`
- line 694: `#print axioms bjbPopcount_partition`
- line 695: `#print axioms bjbTakeif_if_half`
- line 696: `#print axioms bjbTakeif_else_half`
- line 697: `#print axioms bjbLegal_step`
- line 698: `#print axioms bjbWr_le_32`
- line 699: `#print axioms bjbMain_no_overflow`
- line 700: `#print axioms bjbWr_branch`
- line 701: `#print axioms bjbWr_join`
- line 703: `#print axioms bjbTight_peel_peak`
- line 704: `#print axioms bjbTight_peel_drain`
- line 705: `#print axioms pcB5_peak`
- line 706: `#print axioms ha_halve_level5`

### `Ventus/SIMT/BranchJoinOverflow.lean`

- line 194: `#print axioms bjoT5_witness_lost_join`
- line 195: `#print axioms bjoT6_witness_ghost_pop`

### `Ventus/SIMT/PCcontrol.lean`

- line 287: `#print axioms pccT1a_align`
- line 288: `#print axioms pccT1b_mask_bit0`
- line 289: `#print axioms pccT1b_mask_bit1`
- line 290: `#print axioms pccT1c_mask_contiguous`
- line 291: `#print axioms pccT1c_mask_word_aligned`
- line 292: `#print axioms pccT2_replay`
- line 293: `#print axioms pccT2_seq`
- line 294: `#print axioms pccT2_src1`
- line 295: `#print axioms pccT2_src3`
- line 296: `#print axioms pccT2_hold`
- line 297: `#print axioms pccT3_seq_advance`
- line 298: `#print axioms pccT4_src1_determines`
- line 299: `#print axioms pccReset_deterministic`

### `Ventus/SIMT/PcReconv.lean`

- line 306: `#print axioms pcrQ1FStep_correct`
- line 307: `#print axioms pcrT_lockstep`
- line 308: `#print axioms pcrT_enqFire_eq`
- line 309: `#print axioms pcrT_deqFire_eq`
- line 310: `#print axioms pcrT_pending_stable`
- line 311: `#print axioms pcrT_count_equal`
- line 312: `#print axioms pcrT_vbranch_valid_gated`
- line 313: `#print axioms pcrMain_i31_excluded`
- line 315: `#print axioms pcrW2_stall_no_dup`
- line 316: `#print axioms pcrW5_count`

### `Ventus/SM.lean`

- line 674: `#print axioms smT1_fetch_enq`
- line 675: `#print axioms smT3_ib_queue`
- line 676: `#print axioms smT4_cu_accept`
- line 677: `#print axioms smT5_cu_collect`
- line 678: `#print axioms smT6_wb_x1`

### `Ventus/SMCSR.lean`

- line 776: `#print axioms smcsrT_csrWbData_wire`
- line 777: `#print axioms smcsrT_wbXData_sel`
- line 778: `#print axioms smcsrT_step_csrF`
- line 779: `#print axioms smcsrT_i33_vl_dead`
- line 780: `#print axioms smcsrTrace_ok`

### `Ventus/SMICache.lean`

- line 513: `#print axioms smicT1_first_miss_replay`
- line 514: `#print axioms smicT2_fetch_stall`
- line 515: `#print axioms smicT3_false_miss_replay`
- line 516: `#print axioms smicT3b_no_duplicate_memreq`
- line 517: `#print axioms smicT4_hit_enq`
- line 518: `#print axioms smicT5_wb_refine`
- line 519: `#print axioms smicT6_endprg`
- line 520: `#print axioms smicT7_all_hit`
- line 521: `#print axioms smicT7b_q2_forced_replay`
- line 522: `#print axioms smicT8_warm_refine`

### `Ventus/SMMaskedMem.lean`

- line 206: `#print axioms smmmDlTrace_deadlock`

### `Ventus/SMMem.lean`

- line 1146: `#print axioms smmT_shreq_setidx_wire`
- line 1147: `#print axioms smmT_mshr_addrTag_wire`
- line 1148: `#print axioms smmT_mshr_dcvalid_wire`
- line 1149: `#print axioms smmT_wbValids_bit2`
- line 1150: `#print axioms smmT_wbVValids_bit2`
- line 1151: `#print axioms smmT_wbVValids_lsu_wire`
- line 1152: `#print axioms smmT_wbXValids_lsu_wire`
- line 1153: `#print axioms smmT_lsuRspRdy_wire`
- line 1154: `#print axioms smmT_boards_step_wire`
- line 1155: `#print axioms smmT_fenceEnd_wire`
- line 1156: `#print axioms smmTraceA_ok`
- line 1157: `#print axioms smmTraceB_ok`

### `Ventus/SMMemDc.lean`

- line 1702: `#print axioms smdT_dcacheReady_wire`
- line 1703: `#print axioms smdT_shRspRdy_wire`
- line 1704: `#print axioms smdT_arb_mux_wire`
- line 1705: `#print axioms smdT_dcstep_wire`
- line 1706: `#print axioms smdT_mergeWord`
- line 1707: `#print axioms smdT_micro`
- line 1708: `#print axioms smdTraceC_ok`
- line 1709: `#print axioms smdTraceD_ok`

### `Ventus/SMMemMask.lean`

- line 281: `#print axioms smmmTrace_ok`

### `Ventus/SMTrace.lean`

- line 406: `#print axioms smtA_ok`
- line 407: `#print axioms smtB_ok`

### `Ventus/SMVec.lean`

- line 785: `#print axioms smvT_bj_step_wire`
- line 786: `#print axioms smvT_mask_partition`
- line 787: `#print axioms smvT_complete_or_fetch`
- line 788: `#print axioms smvTrace_ok`
- line 789: `#print axioms smvT_module_replay`
- line 790: `#print axioms smvT_mask_restore_scene`

### `Ventus/SMVecWb.lean`

- line 817: `#print axioms smwT_wbData_fidelity`
- line 818: `#print axioms smwT_rfInV_rd_wire`
- line 819: `#print axioms smwT_rfInV_wen_wire`
- line 820: `#print axioms smwT_sbIn_wbV_wire`
- line 821: `#print axioms smwT_wbV_fire_eq_valid`
- line 822: `#print axioms smwT_wb_value_fidelity`
- line 823: `#print axioms smwT_wb_value_fidelity_sm`
- line 824: `#print axioms smwT_wb_clears_busy`
- line 825: `#print axioms smwTrace_ok`

### `Ventus/Schedule/CollectorUnit.lean`

- line 1170: `#print axioms cuT1_run`
- line 1171: `#print axioms cuT1_sout_valid_eq_ready`
- line 1172: `#print axioms cuT2_controlReg_accept`
- line 1173: `#print axioms cuT2_issue_control`
- line 1174: `#print axioms cuT3_imm_shortcut`
- line 1175: `#print axioms cuT4_sout_fire`
- line 1176: `#print axioms cuWmask_accept`
- line 1177: `#print axioms cuWmask_step`
- line 1178: `#print axioms cuWmask_run`
- line 1179: `#print axioms cuWmask_deadlock`
- line 1180: `#print axioms cuQ129_bankInRdy_accept`
- line 1181: `#print axioms cuT_deadlock_state`

### `Ventus/Schedule/I4Fix.lean`

- line 693: `#print axioms i4f_set_wins`
- line 694: `#print axioms i4f_clear_works`
- line 695: `#print axioms i4f_race_gone`
- line 696: `#print axioms i4f_orig_race_loses`
- line 697: `#print axioms i4f_occFix_spec`
- line 698: `#print axioms i4f_occOrig_spec`
- line 699: `#print axioms i4f_swap_irrelevant`
- line 700: `#print axioms i4f_orig_eq_fix_of_no_race`
- line 701: `#print axioms i4f_sbStepFix_eq_orig`
- line 702: `#print axioms i4f_sbRun_equiv`
- line 703: `#print axioms i4f_cuStep_busy`
- line 704: `#print axioms i4fSys_step_inv_fix`
- line 705: `#print axioms i4fSys_run_inv_fix`
- line 706: `#print axioms i4f_occ_tracks_busy`
- line 707: `#print axioms i4f_no_two_busy_fix`
- line 708: `#print axioms i4f_witness_shape_unreachable`
- line 709: `#print axioms i4fSys_step_eq_orig`
- line 710: `#print axioms i4fSys_run_eq_orig`
- line 711: `#print axioms i4f_no_two_busy_orig`
- line 712: `#print axioms i4fT_gated_C_blocked`
- line 713: `#print axioms i4fT_race_orig`
- line 714: `#print axioms i4fT_race_fix`
- line 715: `#print axioms i4fT_ungated_fix_still_oob`
- line 716: `#print axioms i4fT_B_issues_first`
- line 717: `#print axioms i4fT_C_after_B`

### `Ventus/Schedule/IBuffer.lean`

- line 642: `#print axioms ibLane_run_abs`
- line 643: `#print axioms ibLane_step_abs`
- line 644: `#print axioms ibLane_irrevocable`
- line 725: `#print axioms ibTop_warp_prefix`

### `Ventus/Schedule/Issue.lean`

- line 557: `#print axioms issRoute_shape`
- line 558: `#print axioms iss_valid_routed`
- line 559: `#print axioms iss_mutex`
- line 560: `#print axioms iss_dual_valid_coupled`
- line 561: `#print axioms iss_classify_agree`
- line 562: `#print axioms iss_split_fire_iff`
- line 563: `#print axioms issV2_route_agree`
- line 564: `#print axioms issO2m_mutex`
- line 565: `#print axioms issO2m_fire_without_valid`
- line 566: `#print axioms iss_ib2iss_fire_integrity`

### `Ventus/Schedule/OperandCollector.lean`

- line 1450: `#print axioms ocA_filter_rt0`
- line 1451: `#print axioms ocA_grant_sca`
- line 1452: `#print axioms ocA_no_grant3`
- line 1453: `#print axioms ocD_bank_addr_wiring`
- line 1454: `#print axioms ocE1_read_fire_of_valid`
- line 1455: `#print axioms ocXbar_valid_iff`
- line 1456: `#print axioms ocXbar_route_sca`
- line 1457: `#print axioms ocXbar_route_vec`
- line 1458: `#print axioms ocXbar_port3_never_valid`
- line 1459: `#print axioms ocE3_no_clash`
- line 1460: `#print axioms ocI12_slot3_rt0`
- line 1461: `#print axioms ocI12_cu_rsType3_run`
- line 1462: `#print axioms ocI12_xbar_hyp_of_arb`
- line 1463: `#print axioms ocI12_closure`
- line 1464: `#print axioms ocI12_deadlock_system`
- line 1465: `#print axioms ocRdy2_prio_ne`
- line 1466: `#print axioms ocDemux_controlV_lowest`
- line 1467: `#print axioms ocDemux_controlX_second`
- line 1468: `#print axioms ocDemux_E4_single_ready`
- line 1469: `#print axioms ocI11_witness`
- line 1470: `#print axioms ocI11_alias`
- line 1471: `#print axioms ocI11_full_alias`
- line 1472: `#print axioms ocI11_read_witness`
- line 1473: `#print axioms ocD_wb_x0_suppress`
- line 1474: `#print axioms ocD_wb_wen_of_ne0`
- line 1475: `#print axioms ocE1_cu_issue_stable`
- line 1476: `#print axioms ocE1_dual_stable`
- line 1477: `#print axioms ocI4_demux_T`
- line 1478: `#print axioms ocI4_demux_T1`
- line 1479: `#print axioms ocI4_T_alloc_B`
- line 1480: `#print axioms ocI4_T1_alloc_C`
- line 1481: `#print axioms ocI4_C_issues_before_B`

### `Ventus/Schedule/RRArbiter.lean`

- line 1125: `#print axioms rraChoiceHw_eq`
- line 1126: `#print axioms rraGrant_eq_true_iff`
- line 1127: `#print axioms rra1_mutex`
- line 1128: `#print axioms rra1_choice_granted`
- line 1129: `#print axioms rra1_grant_valid_eq_choice`
- line 1130: `#print axioms rra2_choice_valid`
- line 1131: `#print axioms rra2_choice_first`
- line 1132: `#print axioms rra2_choice_default`
- line 1133: `#print axioms rra3_choice_stable`
- line 1134: `#print axioms rra3_not_stable`
- line 1135: `#print axioms rra4_step_of_fire`
- line 1136: `#print axioms rra5_no_starvation`

### `Ventus/Schedule/Scoreboard.lean`

- line 505: `#print axioms sb1_run_scalar_x0`
- line 506: `#print axioms sb2_raw`
- line 507: `#print axioms sb2_raw_scalar`
- line 508: `#print axioms sb3_wb_clear`
- line 509: `#print axioms sb4_clear_priority`
- line 510: `#print axioms sb5_delay_complete`

### `Ventus/Schedule/WarpScheduler.lean`

- line 701: `#print axioms ws1_ready_spec`
- line 702: `#print axioms ws2_release_clears`
- line 703: `#print axioms ws2_barred_not_ready`
- line 704: `#print axioms ws3_next_warp_min`
- line 705: `#print axioms ws4_flush_entry_avoids`
- line 706: `#print axioms ws4_stuck_forever`

### `Ventus/Schedule/Writeback.lean`

- line 496: `#print axioms wb_arb_mutex`
- line 497: `#print axioms wb_arb_choice_valid`
- line 498: `#print axioms wb_arb_fire_integrity`
- line 499: `#print axioms wb_arb_progress`
- line 500: `#print axioms wb_i9_gate_closed`
- line 501: `#print axioms wb_i9_clear_visible`
- line 502: `#print axioms wb_i9_unreachable`
- line 503: `#print axioms wb_i9_scalar`
- line 504: `#print axioms wb_i9_chain`

### `Ventus/Spec/Contracts.lean`

- line 447: `#print axioms specXrefRtDisjoint`
- line 448: `#print axioms specXrefAllocFit`
- line 449: `#print axioms specXrefCuifFinishExact`
- line 450: `#print axioms specXrefWbI9Unreachable`
- line 451: `#print axioms specXrefBjbNoOverflow`
- line 452: `#print axioms specXrefI4fNoTwoBusyFix`
- line 453: `#print axioms spec_count_partition`

### `Ventus/Spec/Discharge1.lean`

- line 480: `#print axioms dcg1_hIb2i_ready_closed`
- line 481: `#print axioms dcg1_hDelay_gate_closed`
- line 482: `#print axioms dcg1_hWid_event`
- line 483: `#print axioms dcg1_wbA3_serialization`
- line 484: `#print axioms dcg1_wbA3_next_blocked`
- line 485: `#print axioms dcg1_allocRegInv_run`
- line 486: `#print axioms dcg1_hAllocPending_fire`
- line 487: `#print axioms dcg1_wsM7_counterexample`
- line 488: `#print axioms dcg1_wsM7_assumption_false`
- line 489: `#print axioms dcg1_pcc_run_aligned`
- line 490: `#print axioms dcg1_icD8_align_assert`
- line 491: `#print axioms dcg1_icD8_rsp_consumes_env`

### `Ventus/Spec/Discharge2.lean`

- line 789: `#print axioms dcg2_wba2_prefix`
- line 790: `#print axioms dcg2_wba2_getElem`
- line 791: `#print axioms dcg2_wba2_chain`
- line 792: `#print axioms dcg2_bjb1_consume`
- line 793: `#print axioms dcg2_hbb_grant`
- line 794: `#print axioms dcg2_hbb_fire`
- line 795: `#print axioms dcg2_hbb_no_fire_iff`
- line 796: `#print axioms dcg2_hbb_bounded_wait`
- line 797: `#print axioms dcg2_wba1_stride_disjoint`
- line 798: `#print axioms dcg2_wba1_bank_disjoint`
- line 799: `#print axioms dcg2_wba1_vgpr_bank_addr_unique`
- line 800: `#print axioms dcg2_cuif_splitVgpr_step`
- line 801: `#print axioms dcg2_cuif_splitVgpr_run`
- line 802: `#print axioms dcg2_cuif_split_base`
- line 803: `#print axioms dcg2_ctaA1`
- line 804: `#print axioms dcg2_ctaE1`

### `Ventus/Spec/Discharge3.lean`

- line 716: `#print axioms dcg3_bjb1_chain_wid`
- line 717: `#print axioms dcg3_bjb1_inputWid_same_source`
- line 718: `#print axioms dcg3_bjb1_wid_pair_gate`
- line 719: `#print axioms dcg3_queue_hist_fidelity`
- line 720: `#print axioms dcg3_bjb1_flow_through`
- line 721: `#print axioms dcg3_bjb1_consumed_entry`
- line 722: `#print axioms dcg3_bjb1_end_to_end`
- line 723: `#print axioms dcg3_wba1_csrExe_write_point`
- line 724: `#print axioms dcg3_wba1_dispatch_consistent`
- line 725: `#print axioms dcg3_wba1_capstone`
- line 726: `#print axioms dcg3_rt_alloc_base_aligned`
- line 727: `#print axioms dcg3_rt_alloc_step_aligned`
- line 728: `#print axioms dcg3_rt_dealloc_step_aligned`
- line 729: `#print axioms dcg3_wba1_rt_run_aligned`
- line 730: `#print axioms dcg3_wba1_next_alloc_aligned`
- line 731: `#print axioms dcg3_wba1_fit_violation`
- line 732: `#print axioms dcg3_wba1_hw_assert_too_weak`

### `Ventus/Spec/EndprgInflight.lean`

- line 323: `#print axioms eif_endprg_preserves_inflight`
- line 324: `#print axioms eif_step_endprg_clears_active`
- line 325: `#print axioms eif_step_endprg_frees_slot`
- line 326: `#print axioms eif_lateWb_uses_current_base`
- line 327: `#print axioms eifW_endprg_with_inflight`
- line 328: `#print axioms eifW_reuse`
- line 329: `#print axioms eifW_pollution`
- line 330: `#print axioms eif_guarded_endprg_safe`
- line 331: `#print axioms eifW_guarded_blocks`

### `Ventus/Spec/FlushOrdering.lean`

- line 459: `#print axioms flo_flush_done_src`
- line 460: `#print axioms flo_flush_two_steps`
- line 461: `#print axioms floRun_report_indep`
- line 462: `#print axioms flo_report_chain_no_flush_input`
- line 463: `#print axioms floW_report_precedes_flush`
- line 464: `#print axioms floW_report_any_dirty`
- line 465: `#print axioms floW_dirty_delays_flush`
- line 466: `#print axioms flo_guarded_report_safe`
- line 467: `#print axioms floWG_blocked_then_safe`

### `Ventus/Top.lean`

- line 757: `#print axioms top_pcReset_high_first5`
- line 758: `#print axioms top_pcReset_low_after5`
- line 759: `#print axioms top_sm_memReq_source_chain`
- line 760: `#print axioms top_rsp_route_exactly_one`
- line 761: `#print axioms top_cluster_rsp_lossless`
- line 762: `#print axioms top_shared_setIdx_high_zero`
- line 763: `#print axioms top_src_layout`
- line 764: `#print axioms top_rsp_route_home`
- line 765: `#print axioms top_rsp_ready_mux`
- line 766: `#print axioms top_rsp_dsource_roundtrip`
- line 767: `#print axioms top_cluster_rsp_packed_lossless`
- line 768: `#print axioms top_i21_dead_rows_conn`
- line 769: `#print axioms top_c2w_zext_lossless`
- line 770: `#print axioms top_axiAdapter_mismatch`

### `VentusF/Arith.lean`

- line 430: `#print axioms farith_mulres_eq_orig_of_ne_mulhsu`
- line 431: `#print axioms farith_mul_mulhsu_fixed`
- line 432: `#print axioms farith_i15_witness`
- line 433: `#print axioms farith_mulhsu_divergence_gone`
- line 434: `#print axioms farith_mul_regr`
- line 435: `#print axioms farith_amo_opcode`
- line 436: `#print axioms farith_dec_row_unchanged`
- line 437: `#print axioms farith_dec_nonamo_regr`
- line 438: `#print axioms farith_amo_imf_all_miss`
- line 439: `#print axioms farith_match_false_of_low7`
- line 440: `#print axioms farith_lookupEntry_default`
- line 441: `#print axioms farith_amo_falls_default`
- line 442: `#print axioms farith_i16_witness_amoadd`
- line 443: `#print axioms farith_i16_regr_add`
- line 444: `#print axioms farith_csr_vl_read`
- line 445: `#print axioms farith_csr_read_regr`
- line 446: `#print axioms farith_csr_vl_write`
- line 447: `#print axioms farith_csr_vl_rw`
- line 448: `#print axioms farith_i33_witness`
- line 449: `#print axioms farith_csr_fcsr_write_mask`
- line 450: `#print axioms farith_csr_fcsr_write_frm`
- line 451: `#print axioms farith_i32_witness`
- line 452: `#print axioms farith_csr_step_regr`
- line 453: `#print axioms farith_csr_regr_frm`
- line 454: `#print axioms farith_i11_witness`
- line 455: `#print axioms farith_i11_alias_gone`
- line 456: `#print axioms farith_i11_full_alias_gone`
- line 457: `#print axioms farith_i11_regr`
- line 458: `#print axioms farith_i45_guard_iff`

### `VentusF/Audit.lean`

- line 213: `#print axioms audXrefCapstone`
- line 214: `#print axioms audXrefCapMain`
- line 215: `#print axioms audXrefCapEpisodeSalu`
- line 216: `#print axioms audXrefCapEpisodeValu`
- line 217: `#print axioms audXrefRf3StmtSaluOfProgress`
- line 218: `#print axioms audXrefPrgStmtSalu`
- line 219: `#print axioms audXrefPrjStmtSalu`
- line 220: `#print axioms audXrefMwfSimStepOfCuQW`
- line 221: `#print axioms audXrefRfvStmtValuOfProgress`
- line 222: `#print axioms audXrefRfvStmtVloadOfProgress`
- line 223: `#print axioms audXrefRfvStmtVstoreOfProgress`
- line 224: `#print axioms audXrefPrjStmtJoinOfProgress`
- line 225: `#print axioms audXrefBjbMainNoOverflow`
- line 226: `#print axioms aud_count_partition`

### `VentusF/Capstone.lean`

- line 250: `#print axioms cap_memCmd0_of_salu`
- line 251: `#print axioms cap_stmt_salu`
- line 252: `#print axioms cap_pack_fields_of_head`
- line 604: `#print axioms cap_salu_beat_iso`
- line 605: `#print axioms cap_valu_beat_iso`
- line 606: `#print axioms cap_episode_salu`
- line 607: `#print axioms cap_episode_valu`
- line 815: `#print axioms cap_main`
- line 816: `#print axioms ventusF_capstone`

### `VentusF/IsaSpec.lean`

- line 1013: `#print axioms isa_cls_add`
- line 1014: `#print axioms isa_cls_endprg`
- line 1015: `#print axioms isa_coverage_audit`
- line 1016: `#print axioms isa_step_default_nop`
- line 1017: `#print axioms isa_lane_vadd_match`
- line 1018: `#print axioms isa_lane_vmerge_match`
- line 1019: `#print axioms isa_alu_add_sa`
- line 1020: `#print axioms isa_cmp_bge_sa`
- line 1021: `#print axioms isa_div_fn_q_signed`
- line 1022: `#print axioms isa_mulhsu_fixed`
- line 1023: `#print axioms isaT_scalar_arith`
- line 1024: `#print axioms isaT_branch_jump`
- line 1025: `#print axioms isaT_scalar_mem`
- line 1026: `#print axioms isaT_muldiv_golden`
- line 1027: `#print axioms isaT_csr`
- line 1028: `#print axioms isaT_vec_alu`
- line 1029: `#print axioms isaT_vec_mem`
- line 1030: `#print axioms isaT_simt_diverge_reconverge`
- line 1031: `#print axioms isaT_simt_final`
- line 1032: `#print axioms isaT_edge`
- line 1033: `#print axioms isaT_halted_idem`

### `VentusF/Mem.lean`

- line 697: `#print axioms fmem_i21_witness_rows_differ`
- line 698: `#print axioms fmem_i21_no_dead_rows`
- line 699: `#print axioms fmem_i21_regress_low32K`
- line 700: `#print axioms fmem_i21_grouping_equiv`
- line 701: `#print axioms fmem_i21_witness_green`
- line 702: `#print axioms fmem_i23_stall_mechanism`
- line 703: `#print axioms fmem_i23_no_false_verdict`
- line 704: `#print axioms fmem_i23_step_regress`
- line 705: `#print axioms fmem_i23_false_hit_gone`
- line 706: `#print axioms fmem_i23_retry_hit_correct`
- line 707: `#print axioms fmem_i24_victim_correct`
- line 708: `#print axioms fmem_i24_regress`
- line 709: `#print axioms fmem_i24_way1_reachable`
- line 710: `#print axioms fmem_i24_way1_used`
- line 711: `#print axioms fmem_i27_fix_eq_lru`
- line 712: `#print axioms fmem_i27_witness_gone`
- line 713: `#print axioms fmem_i27_regress`
- line 714: `#print axioms fmem_i28_witness_fixed`
- line 715: `#print axioms fmem_i28_two_lane_merge`
- line 716: `#print axioms fmem_i28_step_regress`
- line 717: `#print axioms fmem_i28_regress`
- line 718: `#print axioms fmem_i29_guard`
- line 719: `#print axioms fmem_i29_collision_blocked`
- line 720: `#print axioms fmem_i29_write_proceeds`
- line 721: `#print axioms fmem_i29_ready_regress`
- line 722: `#print axioms fmem_i30a_eq_hintAck`
- line 723: `#print axioms fmem_i30_w2b_green`
- line 724: `#print axioms fmem_i30_w2c_status`
- line 725: `#print axioms fmem_i30_step_regress`
- line 726: `#print axioms fmem_i47_report_safe`
- line 727: `#print axioms fmem_i47_witness_green`
- line 728: `#print axioms fmem_i47_regress`

### `VentusF/MemL2.lean`

- line 796: `#print axioms fmem_i35_fix_vs_orig`
- line 797: `#print axioms fmem_i35_regress`
- line 798: `#print axioms fmem_i35_flushCount_regress`
- line 799: `#print axioms fmem_i35_count_returns_zero`
- line 800: `#print axioms fmem_i35_second_flush_in_range`
- line 801: `#print axioms fmem_i36_regress`
- line 802: `#print axioms fmem_i36_status_regress`
- line 803: `#print axioms fmem_i3536_step_regress_others`
- line 804: `#print axioms fmem_i36_no_corrupt`
- line 805: `#print axioms fmem_i36_false_hit_gone`
- line 806: `#print axioms fmem_i37_fix_faithful`
- line 807: `#print axioms fmem_i37_witness_green`
- line 808: `#print axioms fmem_i38_fix_faithful`
- line 809: `#print axioms fmem_i38_witness_green`
- line 810: `#print axioms fmem_i3738_regress`
- line 811: `#print axioms fmem_i3738_step_regress`
- line 812: `#print axioms fmem_i39_witness_green`
- line 813: `#print axioms fmem_i39_regress`
- line 814: `#print axioms fmem_i40_read_blocked`
- line 815: `#print axioms fmem_i40_regress`
- line 816: `#print axioms fmem_i40_witness_green`
- line 817: `#print axioms fmem_i41a_alloc_sinkd_mutex`
- line 818: `#print axioms fmem_i41b_merge_sinkd_mutex`
- line 819: `#print axioms fmem_i42_guard`
- line 820: `#print axioms fmem_i42_witness_green`
- line 821: `#print axioms fmem_i42_regress`
- line 822: `#print axioms fmem_i43_witness_green`
- line 823: `#print axioms fmem_i43_push_leak_residual`
- line 824: `#print axioms fmem_i43s_regress`
- line 825: `#print axioms fmem_i43s_no_leak`
- line 826: `#print axioms fmem_i44_alloc_imp_fire`
- line 827: `#print axioms fmem_i44_e3_by_construction`
- line 828: `#print axioms fmem_i44_e3_witness_green`
- line 829: `#print axioms fmem_i44_regress`

### `VentusF/MultiWarp.lean`

- line 1545: `#print axioms mwf_cu_wid_stable_run`
- line 1546: `#print axioms mwf_demux_two_valid`
- line 1547: `#print axioms mwf_cuQW_of_quiesce`
- line 1548: `#print axioms mwf_cuQW_all`
- line 1549: `#print axioms mwf_addrS_ne_bv`
- line 1550: `#print axioms mwf_addrV_ne_bv`
- line 1551: `#print axioms mwf_rdX_iso`
- line 1552: `#print axioms mwf_rdV_iso`
- line 1553: `#print axioms mwf_pcOk_step_iso`
- line 1554: `#print axioms mwf_wsStepActive_bit`
- line 1555: `#print axioms mwf_sim_step_iso`
- line 1556: `#print axioms mwf_sim_run_iso`
- line 1557: `#print axioms mwf_wbArbChoice_set`
- line 1558: `#print axioms mwf_wbX_not_w`
- line 1559: `#print axioms mwf_wbV_not_w`
- line 1560: `#print axioms mwf_brM_not_w`
- line 1561: `#print axioms mwf_warpEnd_not_w`
- line 1562: `#print axioms mwf_sim_step_of_cuQW`
- line 1563: `#print axioms mwf_silent_step_all`
- line 1564: `#print axioms mwf_silent_run_all`
- line 1565: `#print axioms mwf_sep_step`
- line 1566: `#print axioms mwfT_dual_pre`
- line 1567: `#print axioms mwfT_dual_post`
- line 1568: `#print axioms mwfT_dual_stable`
- line 1569: `#print axioms mwfT_iso_differential`
- line 1570: `#print axioms mwfT_cu_wid_stable`
- line 1571: `#print axioms mwfT_cu_occupied_dual`

### `VentusF/Progress.lean`

- line 852: `#print axioms prg_saluBeat_of_issue`
- line 853: `#print axioms prg_stmt_salu`
- line 854: `#print axioms prg_cu_full_cycle`
- line 855: `#print axioms prg_cu_add_collect`
- line 856: `#print axioms prg_i2iX_accept`
- line 857: `#print axioms prg_ib_deq_head`
- line 858: `#print axioms prg_rra_no_starvation`
- line 859: `#print axioms prg_eventual`

### `VentusF/ProgressJoin.lean`

- line 315: `#print axioms prj_join_step`
- line 316: `#print axioms prj_stmt_join_of_progress`
- line 457: `#print axioms prj_isaAlu_saAlu`
- line 458: `#print axioms prj_aluRes_eq_of_collect`
- line 956: `#print axioms prj_fsch_collect_terminates`
- line 957: `#print axioms prj_machine_accept`
- line 958: `#print axioms prj_reach_cu_sOut`
- line 959: `#print axioms prj_issueState_of_pack`
- line 960: `#print axioms prj_stmt_salu`

### `VentusF/Refine.lean`

- line 573: `#print axioms rf1_rdX_write_hit`
- line 574: `#print axioms rf1_rdX_write_miss`
- line 575: `#print axioms rf1_mapS_inj`
- line 576: `#print axioms rf1SimB_sound`
- line 577: `#print axioms rf1T_salu_addi_post`
- line 578: `#print axioms rf1T_sbr_beq_resolve`
- line 579: `#print axioms rf1T_sbr_beq_flush`
- line 580: `#print axioms rf1T_jal_post`
- line 581: `#print axioms rf1T_jalr_post`
- line 582: `#print axioms rf1T_mul_post`
- line 583: `#print axioms rf1T_endprg_post`
- line 584: `#print axioms rf1T_nop_post`

### `VentusF/RefineGen.lean`

- line 775: `#print axioms rf2_quiesce_step_sim`
- line 776: `#print axioms rf2_quiesce_run_sim`
- line 777: `#print axioms rf2_nop_no_wbXFire`
- line 778: `#print axioms rf2_nop_no_brFire`
- line 779: `#print axioms rf2_nop_no_fireWs`
- line 780: `#print axioms rf2_cuQ_of_rf1Quiesce`
- line 781: `#print axioms rf2QuiesceB_sound`
- line 782: `#print axioms rf2_stmt_inst`
- line 783: `#print axioms rf2_stmt_inst_salu`
- line 784: `#print axioms rf2T_salu_addi_grid`
- line 785: `#print axioms rf2T_salu_itype_grid`
- line 786: `#print axioms rf2T_salu_rtype_grid`
- line 787: `#print axioms rf2T_mul_grid`
- line 788: `#print axioms rf2T_sbr_beq_grid`
- line 789: `#print axioms rf2T_jal_grid`
- line 790: `#print axioms rf2T_jalr_grid`
- line 791: `#print axioms rf2T_endprg_grid`
- line 792: `#print axioms rf2T_nop_grid`

### `VentusF/RefineMem.lean`

- line 2359: `#print axioms rf3_salu_wb_step`
- line 2360: `#print axioms rf3_salu_advance`
- line 2361: `#print axioms rf3_isaStep_salu`
- line 2362: `#print axioms rf3_stmt_salu_of_progress`
- line 2363: `#print axioms rf3_mapS_inj_bv`
- line 2364: `#print axioms rf3_rdMemB_step`
- line 2365: `#print axioms rf3_silent_step`
- line 2366: `#print axioms rf3_silent_run`
- line 2367: `#print axioms rf3_dcStep_freeze`
- line 2368: `#print axioms rf3_memQ_step`
- line 2369: `#print axioms rf3_progOk_single`
- line 2370: `#print axioms rf3_memOk_pre`
- line 2371: `#print axioms rf3_stmt_inst_addi`
- line 2372: `#print axioms rf3T_salu_addi_grid`
- line 2373: `#print axioms rf3T_salu_itype_grid`
- line 2374: `#print axioms rf3T_salu_rtype_grid`
- line 2375: `#print axioms rf3T_mul_grid`

### `VentusF/RefineVec.lean`

- line 2392: `#print axioms rfv_rdV_write_hit`
- line 2393: `#print axioms rfv_mapV_inj_bv`
- line 2394: `#print axioms rfv_mapV_inj`
- line 2395: `#print axioms rfv_isaStep_valu`
- line 2396: `#print axioms rfv_stmt_valu_of_progress`
- line 2397: `#print axioms rfv_isaStep_vload`
- line 2398: `#print axioms rfv_stmt_vload_of_progress`
- line 2399: `#print axioms rfv_isaStep_vstore`
- line 2400: `#print axioms rfv_stmt_vstore_of_progress`
- line 2401: `#print axioms rfv_bjSys_branch_list`
- line 2402: `#print axioms rfv_bjSys_join_list`
- line 2403: `#print axioms rfv_isaStep_vbr`
- line 2404: `#print axioms rfv_isaStep_join`
- line 2405: `#print axioms rfv_silent_run`
- line 2406: `#print axioms rfv_mask_split`
- line 2407: `#print axioms rfv_vbr_step`

### `VentusF/SM.lean`

- line 748: `#print axioms fsmT1_fetch_enq`
- line 749: `#print axioms fsmT3_ib_queue`
- line 750: `#print axioms fsmT4_cu_accept`
- line 751: `#print axioms fsmT5_cu_collect`
- line 752: `#print axioms fsmT6_wb_x1`
- line 753: `#print axioms fsm_regr_obs`
- line 754: `#print axioms fsmT_i12_mask_returns`
- line 755: `#print axioms fsmT_i12_orig_never`
- line 756: `#print axioms fsmT_i12_cu_collected`
- line 757: `#print axioms fsmT_i15_mulhsu_wb`
- line 758: `#print axioms fsm_mulhsu_correct`
- line 759: `#print axioms fsmT_i16_amo_flagged`

### `VentusF/SMMem.lean`

- line 1434: `#print axioms fsmmT_shreq_setidx_wire`
- line 1435: `#print axioms fsmmT_shreq_only_setIdx`
- line 1436: `#print axioms fsmm_shSetIdx_regr`
- line 1437: `#print axioms fsmm_shSetIdx_hi_witness`
- line 1438: `#print axioms fsmmT_mshr_step_wire`
- line 1439: `#print axioms fsmm_mshrStep_regr`
- line 1440: `#print axioms fsmmT_dcacheReady_wire`
- line 1441: `#print axioms fsmmT_arb_mux_wire`
- line 1442: `#print axioms fsmmT_dcstep_wire`
- line 1443: `#print axioms fsmm_dcCore_regr`
- line 1444: `#print axioms fsmmT_fenceEnd_wire`
- line 1445: `#print axioms fsmmT_sbFence_wire`
- line 1446: `#print axioms fsmmT_boards_step_wire`
- line 1447: `#print axioms fsmmT_wbValids_bit2`
- line 1448: `#print axioms fsmmT_wbXValids_lsu_wire`
- line 1449: `#print axioms fsmmTraceA_ok`
- line 1450: `#print axioms fsmmTraceB_ok`
- line 1451: `#print axioms fsmmTraceC_ok`
- line 1452: `#print axioms fsmm_regr_orig_chainA`
- line 1453: `#print axioms fsmm_regr_orig_chainC`
- line 1454: `#print axioms fsmmT_i46_endprg_after_drain`

### `VentusF/Schedule.lean`

- line 2249: `#print axioms fschCu_accept_port3_rsType2`
- line 2250: `#print axioms fschCu_mask_req_admissible`
- line 2251: `#print axioms fschCuT_masked_collects`
- line 2252: `#print axioms fschCuT_masked_issues`
- line 2253: `#print axioms fschCuRun_mod3`
- line 2254: `#print axioms fschCu_outArb_eq_orig_of_ne3`
- line 2256: `#print axioms fschCu_i13_uses_new_decode`
- line 2257: `#print axioms fschCuT_i13_fix_fresh`
- line 2259: `#print axioms fschCu_i4_dock`
- line 2260: `#print axioms fschCuInv_run`
- line 2262: `#print axioms fschWs_priEnc_hit`
- line 2263: `#print axioms fschWs_priEnc_eq_oh_of_onehot`
- line 2264: `#print axioms fschWs_step_clears_selected`
- line 2265: `#print axioms fschWsT_i5_drains`
- line 2267: `#print axioms fschWs_rsp_holds`
- line 2268: `#print axioms fschWs_rsp_stable`
- line 2269: `#print axioms fschWsT_i6_rsp_held`
- line 2270: `#print axioms fschWsT_i6_completes`
- line 2272: `#print axioms fschWs_belong_req_set`
- line 2273: `#print axioms fschWs_cnt_req_set`
- line 2274: `#print axioms fschWsT_i7_req_survives`
- line 2276: `#print axioms fschWs_endprg_gated`
- line 2277: `#print axioms fschWs_i46_gate_clean`
- line 2278: `#print axioms fschWsT_i46_blocked`
- line 2279: `#print axioms fschWsT_i46_released`
- line 2281: `#print axioms fschWs_step_equiv`
- line 2282: `#print axioms fschWs_run_equiv`
- line 2283: `#print axioms fschWs_out_equiv`
- line 2285: `#print axioms fschC2w_abs_step`
- line 2286: `#print axioms fschC2w_no_late_read`
- line 2287: `#print axioms fschC2w_enq_tag_sampled`
- line 2288: `#print axioms fschC2wT_i25_tag_correct`
- line 2289: `#print axioms fschC2w_out_abs`
- line 2291: `#print axioms fschMshrA_no_withdraw`
- line 2292: `#print axioms fschMshrB_no_withdraw`
- line 2293: `#print axioms fschMshrA_sink`
- line 2294: `#print axioms fschMshrA_sink_run`
- line 2295: `#print axioms fschMshrAT_deadlock`
- line 2296: `#print axioms fschMshrBT_normal_flow`
- line 2297: `#print axioms fschMshrBT_withdraw_blocked`
- line 2298: `#print axioms fschMshrB_no_sink_entry`
- line 2299: `#print axioms fschMshrB_step_eq_orig`
- line 2300: `#print axioms fschMshrB_run_eq_orig`
- line 2301: `#print axioms fschMshrA_step_eq_orig`
- line 2302: `#print axioms fschMshrA_run_eq_orig`
- line 2304: `#print axioms fschL1m_q1_ready_consistent`
- line 2305: `#print axioms fschL1mT_i26_noFire`
- line 2306: `#print axioms fschL1m_fire_eq_iff`
- line 2307: `#print axioms fschL1mStep_eq_orig`
- line 2308: `#print axioms fschL1mRun_eq_orig`
- line 2309: `#print axioms fschL1m_noFire_ti_preserved`
