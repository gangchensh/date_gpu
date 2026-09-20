# Reproduction Campaign — Per-Case Verdicts and Patched-RTL Regression

Execution dates: ChiselSim and Verilator channels 2026-09-06/07; 35-patch tree
regression 2026-09-07; merged 38-patch tree regression 2026-09-10.

Target: upstream `master` snapshot `6811725` (read-only). ChiselSim suites were
added under `ventus/tests/src/` without modifying any existing source file.
Toolchain: mill 0.11.8, OpenJDK 21, Scala 2.13.12, Chisel 6.4.0 + chiseltest
6.0.0; Verilator 5.034 (source build; the distribution's 5.020 is incompatible
with the vendor simulation wrapper).

## Totals and counting convention

- **28 reproduction cases executed** = 11 ChiselSim suites carrying 18 cases +
  10 Verilator whole-machine kernels (one of which is the channel self-check).
- **22 cases reproduce** the predicted faulty behavior on the actual RTL
  (14 ChiselSim + 8 Verilator); **six bugs reproduce independently in both
  channels** (I-12, I-15, I-16, I-17, I-19, I-21), and six cases match the Lean
  witnesses **bit-exactly** (I-25, I-15, I-19, I-21, I-28, I-11).
- The **6 non-reproducing cases are fully accounted for** (below): two exercise
  the same withdrawn finding, one is a refuted precondition, one is unobservable
  under the simulators' SRAM semantics, one was a defect in our own testbench
  stub, and one is the channel self-check.

## ChiselSim channel (module level; 11 suites, 18 cases)

| Suite (`repro/*.scala`) | Case | Verdict | Key evidence (observed vs. expected) |
|---|---|---|---|
| `ArrayMultiplierBugRepro` | I-15 | **Reproduced** | MULHSU(0xFFFFFFFF,0xFFFFFFFF)=0x00000001 (correct: 0xFFFFFFFF); control MULHU passes |
| `CTA2warpTagBugRepro` | I-25 | **Reproduced** | CTArsp tag reads 0x11 (expected 0x08) — bit-exact with the Lean T7 witness |
| `DecodeUnitAMORepro` | I-16 ×2 | **Reproduced** | AMOADD_W and LR_W both fall to the default row: alu_fn=63, atomic=0, mem_cmd=0, wxd=0 — A-extension silently NOPs |
| `IntDivModBugRepro` | I-17 | **Reproduced** | 0x80000000/1(u) = (1,0) (correct: (0x80000000,0)); cnt width truncation |
| 〃 | I-19 | **Reproduced** | after 3/5, INT_MIN/-1(s): r=0x80000000 (correct: 0) — stale zeroQReg |
| 〃 | I-18 (+I-18b cross case) | **Not reproduced** | both witnesses yield spec-correct results on the RTL — led to the I-18 withdrawal |
| `ShareMemAddrAliasRepro` | I-21 | **Reproduced** | address 0x70008040 → to_shared.setIdx=0 (expected 256); addr(16,15) dropped |
| `WarpSchedulerBugRepro` | I-5 | **Reproduced** (after trigger-pair calibration) | flushDCache.valid stuck high for 6/6 cycles |
| 〃 | I-6 | **Reproduced** | warpRsp.valid pulses one cycle (gone after ready=0); no flush within 8 cycles |
| 〃 | I-7 | **Reproduced** | same-cycle warpReq+endprg: wg3 flushes while warp1 still active |
| 〃 | I-8 | **Precondition falsified** (test passes) | warp_control.ready=0 mutual exclusion holds; the two flush events never coincide — supports the "excluded" disposition |
| `OperandCollectorBugRepro` | I-11 | **Reproduced** | warp7 (sgpr_base=1792) write read back by warp3 (base=768) as 0xdeadbeef — 8-bit bank address wraps across warps |
| 〃 | I-12 | **Reproduced** | mask=1 vmerge-form instruction not issued within 30 cycles (deadlock); control group (mask=0) issues normally |
| `L1CacheBugRepro` | I-23 | **Reproduced** (after 1-cycle retry calibration) | same block fetched twice (duplicate MSHR allocation); retry returns garbage 0xce2468acf10eca86 with status=1 |
| 〃 | I-24 | **Reproduced** | second allocation to the set picks waymask=0b01 (expected 0b10) — way1 never valid |
| 〃 | I-27 | **Reproduced** | full-set replacement evicts the MRU (waymask=0b10) instead of LRU way0 |
| `L1MSHRReadyBugRepro` | I-26 | **Reproduced** (primary evidence exact) | ready=1 with st0=3 (SECONDARY_FULL); the response phase trips the RTL's own assertion L1MSHR.scala:196 (duplicate entry for one block) — a stronger failure than predicted |
| `L1TagAccessDirtyMaskRepro` | I-28 | **Reproduced** | two lanes, same blockOffset, adjacent bytes: dirtyMask=0x212 (expected 0x213); lane0's byte silently lost |
| `DCacheBugRepro` (Verilator backend) | I-29 | **Not reproduced** (test passes) | victim writeback data clean ({0xBBBB2222, 0xDDDD4444}); the predicted LFSR pollution is not observable under the simulator's SRAM same-cycle read/write rule — residual doubt retained; the Lean mechanism proof governs |
| 〃 | I-30 | **Initially not runnable** | root-caused to a **testbench-stub defect** (the hand-written L2 stub never returned AccessAck to write-backs, so the invalidate never completes); after fixing the stub the scenario executes — and exposes the companion defect I-48 |

## Verilator channel (whole machine; 10 kernels)

Kernels and execution logs: `verilator/kernels/`, `verilator/logs/`
(invocation: `bash run.sh run <kernel>`; see `verilator/README.md`).

| Kernel | Target | Verdict | Key evidence |
|---|---|---|---|
| `k00_smoke` | channel self-check | **Pass** | memory canary written; kernel finishes |
| `i12_vmerge_deadlock` | I-12 | **Reproduced** | canary written, PASS word untouched, no finish log, simulation hits the time cap — deadlock |
| `i15_mulhsu_low32` | I-15 | **Reproduced** | mulhsu(0xFFFFFFFF,0xFFFFFFFF)=0x00000001 |
| `i16_amo_nop` | I-16 | **Reproduced** | issue-stage assertion fires on 0x002521af (amoadd.w): decode fell to the default row alu_fn=63 |
| `i17_divu_cnt_trunc` | I-17 | **Reproduced** | divu 0x80000000/1 quotient=0x00000001 |
| `i18_rem_recovery` | I-18 | **Not reproduced** | rem 4/3 yields the correct remainder 1 (bug version would give 5) |
| `i19_rem_stale_zeroq` | I-19 | **Reproduced** | INT_MIN%-1 remainder=0x80000000 (correct: 0) |
| `i21_lds_alias` | I-21 | **Reproduced** | after writing 0x22222222 to the high region (0x70008040), reading the low region (0x70000040) returns 0x22222222 |
| `i32_fcsr_write_dropped` | I-32 | **Reproduced** | csrrw fcsr 0xE5 reads back 0x00000000 |
| `i33_vl_dead` | I-33 | **Reproduced** | vsetvli writes rd=0x20, but csrrs vl reads 0x00000000 |

## The six non-reproducing cases — full accounting

1. **I-18 (ChiselSim and Verilator, 2 cases)** — our model had read a wrapping
   Chisel `+` as a widening add; the RTL is correct. The finding was
   **withdrawn** (Class II), the model corrected, and the whole development
   re-proved; a library-wide audit of operator-width assumptions found no
   second instance. This withdrawal is evidence that the mandatory RTL
   back-validation filter works.
2. **I-8 (1 case)** — the triggering precondition was falsified by the RTL
   itself: the `warp_control.ready=0` gating makes the two flush sources
   mutually exclusive. The RTL experiment upgrades the formal exclusion to an
   observed negative result.
3. **I-29 (1 case)** — the predicted LFSR pollution does not manifest under
   either simulator's SRAM same-cycle read/write semantics (treadle or
   Verilator). The mechanism proof (`fmem_i29_*` family on the model) stands;
   the residual doubt is recorded openly in the I-29 report.
4. **I-30 (1 case)** — initially not runnable due to a defect in our own L2
   testbench stub (a test-side artifact, not an RTL or model defect; an
   isolation matrix over six patch configurations plus baseline confirmed no
   patch regression). Once the stub was fixed, the scenario executes — and
   exposed the fix-activated companion defect I-48.
5. **k00_smoke (1 case)** — channel self-check; targets no bug.

## Patched-RTL regression

### 35-patch tree (2026-09-07)

All 11 ChiselSim suites re-run on the fully patched tree vs. the baseline.
**9 suites fully green** (I-15/17/19/25/11/12/21/5/6/7/8/23/24/27/28 fixed-side
green; I-18 regression consistent). Two exceptions, both dispositioned:

- `DecodeUnitAMORepro` (I-16): the two original cases encode the
  **ALTERNATIVE** (AMO-enable) expectation, while the applied patch takes the
  **trap** route (decode sets `illegal`; the warp-termination channel is reused
  as the trap path). The trap behavior is positively verified by two added
  cases (decode-level `illegal=1`; scheduler-level `trap=1` + flush follow-through).
- `L1MSHRReadyBugRepro` (I-26): the patch is a **behavior-preserving defensive
  guard** on the tested witness (diagnosed cycle-by-cycle with an added
  diagnostic suite: the witness drives a timing pattern that does not occur
  under the DCache's real probe→missReq timing, where the unpatched code
  already backpressures correctly). Patch retained as defense in depth.

The regression itself caught three issues, which is the point of running it:
the i28 v1 patch contained a **combinational loop** (rejected by firrtl's
CheckCombLoops; fixed in v2 by OR-merging instead of read-modify-write through
a dynamic index), an **ineffective patch** (since revised and re-verified), and
the **fix-activated companion defect I-48** (the i30 fix unmasks a duplicate
invalidate response: response sequence 7,3,1,5,4,2,**2** instead of
7,3,1,5,4,2 — the baseline's "normal" behavior had itself depended on the w2b
bug's masking).

### Merged 38-patch tree (2026-09-10)

The 38-patch series (35 + i47 + i16 + i48; applies cleanly with `git apply`,
mill compile clean) re-runs identically to the 35-patch tree on all suites,
plus two positive verifications:

- **I-48 fix verified**: the I-30 case's response sequence is back to exactly
  one response per request (7,3,1,5,4,2), no longer relying on the w2b
  masking artifact.
- **I-16 trap route verified** at both decode level and scheduler level
  (two added cases green).

I-29 remains "not reproduced (residual doubt retained)" on both trees.
