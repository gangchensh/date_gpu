> English translation of the Chinese master `doc/bugs/I-6-warpRsp握手违规.md`. Translated 2026-09-13.

# I-6 Detailed Defect Report: warpRsp handshake violation (valid is a single-cycle pulse that does not wait for ready), cascading bookkeeping deadlock

| Item | Content |
|---|---|
| ID | I-6 |
| Source location | `ventus/src/pipeline/warp_schedule.scala:55` (`warpRsp.valid := warp_end` single-cycle pulse); cascade points `:131-133`/`:160-162` (belong/cnt cleared on `warpRsp.fire`) vs `:180` (`warp_active` cleared immediately on `warp_end`); corroborating evidence `CTA2warp.scala:71-74` (developer TODO + Queue(16) workaround + assertion) |
| Type | Functional bug (Decoupled handshake contract violation → response silently lost → WG bookkeeping deadlock) |
| Severity | **High** (response loss is silent (no assertion after synthesis); consequences include SM dispatch deadlock; and it blocks I-5's self-healing path) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + ChiselSim reproduction successful + 38-patch merged tree regression 5/5 green |
| Primary evidence | [Lean machine-checked proof] T8 witness + the CTA2warp-side fill-condition theorem family; [simulation run] ChiselSim reproduction successful; [direct source reading] line-by-line check against line numbers + the developer's own TODO as corroboration |
| Lean model | `lean/Ventus/Schedule/WarpScheduler.lean` (original); `lean/Ventus/CTA/CTA2warp.lean` (downstream Queue fill-condition closure); fixed version `lean/VentusF/Schedule.lean` |
| Reproduction/patch | `repro/WarpSchedulerBugRepro.scala` (ChiselSim, I-6 case); patch `i06-i07-i46-warp-schedule-endprg.patch` (internal fix manifest; not released) |
| Related entries | I-5 (its self-healing path is blocked by this entry), I-7 (fixed by the same patch), I-46 (fixed by the same patch), I-25 (downstream late tag read; its workaround could only be removed after I-6 was fixed) |

---

## 0. Summary

warp_scheduler's warpRsp is the completion-response channel that sends a warp's completion (endprg) back to the CTA layer, declared as Decoupled (`Decoupled(new warpRspData)`). Chisel's Decoupled contract requires that **once valid is raised it must be held until ready** (when the receiver is not ready, the sender must keep the request asserted). But source `:55` directly writes `io.warpRsp.valid := warp_end` — warp_end is a **single-cycle pulse** of warp_control.fire, so valid exists for only one cycle, and the comment "always ready." shows the developer assumed the downstream is always ready.

That assumption is wrong: the CTA2warp side uses a `Queue(io.warpRsp, 16)` as a workaround (CTA2warp.scala:71-74, with its own TODO comment and assertion); when the FIFO is full, ready goes low and the single-cycle-valid response is **silently dropped** (the assertion exists only in simulation; it does not exist after synthesis). After the response is lost, the bookkeeping tears apart: `warp_active` is already cleared in the same cycle by `warp_end` (:180), while the clearing of `warp_bar_belong`/`warp_endprg_cnt` waits for `warpRsp.fire` (:131-133/:160-162) — active is cleared but belong/cnt never clear ⇒ the WG's lock is stuck, the barrier expectation set is never re-initialized, mask_0 is never set (flush is never issued), and I-5's only self-healing path is blocked.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **Decoupled handshake**: Chisel's standard valid/ready channel. Contract: once the sender raises valid it **must hold it** with bits unchanged, until both sides are valid&ready in the same cycle (fire) and the transfer completes. Violating "hold-until-ready" is the most common handshake bug type.
- **warpRsp's responsibility**: after a warp endprg's, the scheduler notifies CTA2warp via warpRsp that "this warp slot (wid) has been released"; CTA2warp clears the idx_using bit and forwards the completion event through a 16-deep FIFO as CTArsp to cu_interface (WG completion bookkeeping and host notification).
- **Three bookkeeping sites for the same event**: a warp's completion triggers three kinds of state updates inside warp_scheduler — `warp_active` (:180, clear the active bit), `warp_bar_belong` (:133, clear the WG membership bit), `warp_endprg_cnt` (:162, clear the not-yet-finished count). By design all three should happen synchronously for the same event.
- **CTA2warp's workaround**: the developers already knew warpRsp was non-compliant — the original comment at CTA2warp.scala:71-74 reads `TODO: Fix warp_scheduler warpRsp IO logic, which always requires ready=1`, with `Queue(io.warpRsp, 16)` buffering plus `assert(io.warpRsp.ready, "...FIFO is used to satisfy it, but not enough")`. The workaround postpones the consequence of the violation from "lost immediately" to "lost only when the FIFO fills up", and delegates detection to a simulation assertion.

### 1.2 Design intent

warp endprg → warpRsp.fire → CTA2warp releases the wid + enqueues the completion event → cu_interface counts WG completions. The whole chain relies on "each endprg produces exactly one warpRsp.fire".

---

## 2. Construct-by-construct reading of the original code

**Construct 1: the violating valid** (warp_schedule.scala:47, :55, ★ hazard):

```scala
val warp_end = io.warp_control.fire & io.warp_control.bits.ctrl.simt_stack_op  // :47
...
io.warpRsp.valid := warp_end // always ready.                                  // :55 ★
io.warpRsp.bits.wid := warp_end_id
```

warp_end is a combinational single-cycle pulse; valid is not held. The comment "always ready." shifts the contract responsibility onto the downstream.

**Construct 2: the split of bookkeeping update conditions** (★ hazard, three clears not synchronized):

```scala
when(io.warpRsp.fire){                                                          // :131
  warp_bar_belong(end_wg_id) := warp_bar_belong(end_wg_id) & (~(1.U<<io.warpRsp.bits.wid)).asUInt  // :133
}
...
when(io.warpRsp.fire){                                                          // :160
  warp_endprg_cnt(end_wg_id) := warp_endprg_cnt(end_wg_id) & (~(1.U<<io.warpRsp.bits.wid)).asUInt  // :162
}
...
warp_active := (warp_active | (req set bits...)) &
  (~(Fill(num_warp, warp_end) & (1.U<<warp_end_id))).asUInt                     // :180 ★
```

The clear condition for belong/cnt is `warpRsp.fire` (= warp_end && warpRsp.ready), while the clear condition for active is `warp_end` (ignoring ready). On a cycle where ready is low: valid disappears after its single cycle (the response is lost), but active has already been cleared — **the same event produced inconsistent effects on different registers**.

**Construct 3: the downstream workaround and its limit** (CTA2warp.scala:63, :71-74):

```scala
// TODO: Fix warp_scheduler warpRsp IO logic, which always requires ready=1
val CTArsp_fifo = Queue(io.warpRsp, 16)                                          // :73
assert(io.warpRsp.ready, "...FIFO is used to satisfy it, but not enough")        // :74
```

The Queue's enq.ready is warpRsp.ready; when the FIFO is full (16 entries), ready=0. Fill condition (Lean closure, see §4): net backlog = #warpRsp.fire − #CTArsp.fire reaching 16. With num_warp=8, a single generation produces at most 8 endprgs, so **filling the FIFO requires two generations** — idx_using is cleared on the very cycle of warpRsp.fire (CTA2warp.scala:63), so CTAreq can immediately reuse the wid and produce 8 more endprgs. The real source of CTArsp back-pressure: cu_interface's gather FSM stops in DEALLOC waiting for the host, during which CTArsp.ready=0 — entirely reachable.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

The consequence chain (after a response is lost):

1. warpRsp lost (FIFO full or any ready-low cycle): active(w) already cleared (:180 by warp_end);
2. belong/cnt never cleared (:131/:160 wait for fire, which never comes again) ⇒ the WG's `warp_bar_lock` (belong.orR, :135) is stuck, and the barrier expectation set exp is never re-initialized;
3. `warp_endprg_cnt` nonzero ⇒ mask_0 never set ⇒ **flushDCache is never issued** (the WG's dirty data is never flushed out via this bookkeeping path);
4. **Blocks I-5's self-healing path**: I-5's stuck state escapes via "CTA dispatches another warp so mask_0 falls back to a singleton", and this entry corrupts the cnt/belong bookkeeping so the escape premise no longer holds;
5. When the FIFO is full and CTArsp keeps not being consumed, the situation escalates further: idx_using only grows and never shrinks; once all 8 slots leak away, CTAreq.ready is permanently 0 (CTA2warp.scala:56) — **SM dispatch deadlock** (Lean: `c2w4_full_stuck_run`).

### 3.2 Root cause

**The sender violates the Decoupled contract + the downstream replaces the fix with an exhaustible buffering workaround**. Three layers stacked: (a) :55's valid not held (the violation); (b) the split clear conditions of :180 vs :131/:160 (two different criteria for the same event; once the violation triggers, the bookkeeping tears); (c) detection relies on a simulation assertion and is silent after synthesis. At the root-cause level, (b) amplifies the cost of the violation from "one response lost" to "WG bookkeeping permanently stuck".

### 3.3 Harm and tolerability

- **Harm**: WG bookkeeping stuck (flush never issued, lock stuck, slot/resource leak), and in the extreme case SM dispatch deadlock; the loss is silent, with no runtime signal at all.
- **Tolerability**: with num_warp=8, a single generation does not easily fill the FIFO (16 backlog entries needed), but multi-generation accumulation + CTArsp back-pressure (cu_interface waiting for the host) is reachable — a real, load-dependent trigger surface, not a purely theoretical corner. Rating: **High** (the combined effect of deadlock-level consequences + silence + the blocked self-healing path).
- **Fix recommendation**: make warpRsp.valid hold until ready (standard Decoupled: pending-register scheme), or register the pending response inside warp_scheduler. The former was adopted (§7).

---

## 4. Lean formal evidence

**WarpScheduler side** (`lean/Ventus/Schedule/WarpScheduler.lean`):

- `wsStepActive` (modeling item M7): explicitly lists warpRsp.ready as an input — the "always ready" of source :55 is an assumption, not a guarantee, and the model must be able to characterize behavior when ready is low; this is the prerequisite for formalizing I-6;
- **T8 witness** (decide + native_decide, `wsD2`/`wsD5` series): at endprg with warpRspReady=false → active already cleared, `endprgCnt(1)=8` not cleared; after 3 more cycles of idle inputs, cnt/belong remain stuck, flushDCacheValid=false (flush never issued), and warpRspValid never rises again (the response is permanently lost).

**CTA2warp side (fill-condition closure, `lean/Ventus/CTA/CTA2warp.lean`)**:

- `c2w5_fifo_len_delta`: cycle-by-cycle characterization of FIFO net backlog = #warpRsp.fire − #CTArsp.fire;
- `c2w6_rsp_dropped_iff_full`: a response is dropped ⟺ the FIFO is full (precise iff criterion);
- T6 witness: a 24-cycle fill trace (CTArsp continuously back-pressured, an entirely reachable scenario);
- `c2w4_full_stuck_run`: FIFO full + CTArsp not consumed ⇒ idx_using only grows and never shrinks; once all 8 slots leak away, CTAreq.ready is permanently 0 (SM dispatch deadlock);
- `c2wFifo_simulates`: Queue refinement (⊑ AQueue 16) on record.

**Fixed-version verification** (`lean/VentusF/Schedule.lean`): `fschWs_rsp_holds` (after the fix, valid holds until ready), `fschWsT_i6_rsp_held` (in the original witness scenario the response is held instead of lost), `fschWsT_i6_completes` (after back-pressure is released the response completes normally).

---

## 5. Simulation verification (ChiselSim measurements + patch-tree regression)

**ChiselSim module-level reproduction** (`repro/WarpSchedulerBugRepro.scala` I-6 case, actually run 2026-09-06/07, doc/22): pull warpRsp.ready low on the endprg cycle; measured **warpRsp.valid for only 1 cycle** (disappears after ready=0; the handshake violation is directly observed), followed by **flushDCache.valid never rising within 8 cycles** (the downstream manifestation of the stuck bookkeeping). Verdict: **reproduction successful**.

**Patch-tree regression**: 35-patch tree 4/4 green after fence_end adaptation; 38-patch merged tree 5/5 green (doc/22) — after the fix the response holds until ready and completes normally once back-pressure is released; no regressions.

---

## 6. Upstream impact analysis

- **Trigger surface**: any cycle that pulls warpRsp.ready low — in the current implementation that is CTA2warp's Queue(16) filling up. Filling requires two generations of endprg accumulation (16 entries) plus continuous CTArsp back-pressure; CTArsp back-pressure is the norm when the host does not consume completion events promptly. **Small kernels with a single generation of 8 warps do not trigger; long-running / multi-kernel scenarios are reachable**.
- **Known upstream but not cured**: the TODO comment at CTA2warp.scala:71-74 proves upstream was aware that warpRsp "always requires ready=1" is a violation, but chose a FIFO workaround + a simulation assertion instead of fixing the sender. This entry's incremental contribution: pinning down as theorems both "the exact conditions under which the FIFO fills" (two generations, 16 entries of net backlog, CTArsp back-pressure scenarios) and "the precise consequence chain after filling" (bookkeeping tear → flush never issued → SM dispatch deadlock in the extreme).
- **Coupling with I-25**: only after I-6's fix made warpRsp a standard Decoupled could I-25's CTA2warp fix (tag enqueued together with the response) remove the original assert workaround (the internal fix manifest note) — the fix side has a dependency order too.
- **Silence after synthesis**: the assertion at :74 exists only in simulation; the only observable symptom on silicon is a kernel that never completes / resource exhaustion, and root-causing it is extremely hard.

---

## 7. Fix and fix verification

**Patch** (`i06-i07-i46-warp-schedule-endprg.patch` (internal fix manifest; not released), same patch as I-7 and I-46; the warpRsp-related edit points):

1. Add three registers `warp_rsp_valid_reg`/`warp_rsp_wid_reg`/`warp_rsp_wg_reg` — the response is registered on the endprg accept cycle, and valid holds until ready (pending-register scheme);
2. `io.warpRsp.valid := warp_rsp_valid_reg || warp_end` (pass-through + pending, two paths);
3. Add gating to `warp_control.ready`: when a response is pending and the downstream is not ready, reject new endprgs (preventing response overflow);
4. Change `wg_id_lookup` to look up warp_end_id on warp_control active cycles and the response header on idle cycles (a companion change allowing the response to be issued several cycles later).

**Fix verification trio**:

- Effectiveness: Lean fixed-version theorems `fschWs_rsp_holds`/`fschWsT_i6_rsp_held`/`fschWsT_i6_completes`;
- Regression safety: 38-patch merged tree ChiselSim regression 5/5 green (doc/22);
- Linked unblocking: I-25's assert workaround can be removed once this fix lands (the internal fix manifest note).

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | warp_schedule.scala:55/:131-133/:160-162/:180, CTA2warp.scala:63/:71-74 checked line by line; developer TODO as corroboration | Consistent |
| Lean machine-checked proof | T8 witness (response lost → bookkeeping-stuck trace); `c2w5_fifo_len_delta`/`c2w6_rsp_dropped_iff_full`/`c2w4_full_stuck_run` (fill-condition and deadlock closure) | Concrete trace + iff criterion |
| ChiselSim reproduction | warpRsp.valid for only 1 cycle (violation directly observed) + flushDCache.valid not rising within 8 cycles | Measured |
| Fix verification | i06-i07-i46 patch; Lean fixed-version hold theorems + 38-patch tree regression 5/5 green | Measured + machine-checked |

I-6 is a "handshake-contract violation + workaround instead of fix" defect: one line of comment on the sender side ("always ready.") outsources the contract responsibility to the downstream, and the downstream buries the landmine with a finite-depth FIFO that only explodes "when it fills up". Formal methods pinned down both the fill condition (two generations, 16 entries) and the consequence chain (bookkeeping tear → flush never issued → dispatch deadlock), while simulation directly observed the violating valid pulse at module level — the two evidence channels corroborate each other at the numerical level.
