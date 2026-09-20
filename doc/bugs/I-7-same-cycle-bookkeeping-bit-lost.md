> English translation of the Chinese master `doc/bugs/I-7-同拍簿记位丢失.md`. Translated 2026-09-13.

# I-7 Detailed Defect Report: new warp's bookkeeping bit lost when warpReq+warpRsp target the same WG in the same cycle

| Item | Content |
|---|---|
| ID | I-7 |
| Source location | `ventus/src/pipeline/warp_schedule.scala:123-134` (`warp_bar_belong`: Req set at `:124` written first, Rsp clear at `:133` written later) and `:157-163` (`warp_endprg_cnt`: Req set at `:158`, Rsp clear at `:162`); downstream harm point `:141` (barrier release clears `warp_bar_data` by belong) |
| Type | Functional bug (same-cycle clear-then-set race → bookkeeping bit lost → premature flush / barrier deadlock) |
| Severity | **High** (can cause a deadlock in which a warp never becomes ready; premature flush is a consistency risk) |
| Confirmation status | 【Confirmed】, fixed version modeled and verified + ChiselSim reproduction successful + 38-patch merged tree regression 5/5 green |
| Primary evidence | [Lean machine-checked proof] T7 witness + M4 semantic characterization; [simulation run] ChiselSim reproduction successful; [direct source reading] line-by-line check against line numbers |
| Lean model | `lean/Ventus/Schedule/WarpScheduler.lean` (`wsStepBelong`/`wsStepCnt` + T7); fixed version `lean/VentusF/Schedule.lean` |
| Reproduction/patch | `repro/WarpSchedulerBugRepro.scala` (ChiselSim, I-7 case); patch `i06-i07-i46-warp-schedule-endprg.patch` (internal fix manifest; not released) |
| Related entries | I-5, I-6 (same family, same patch), I-46 (same patch); I-4 (the same "same-cycle clear-then-set" race pattern in the scoreboard, proven unreachable via gating — a comparison case) |

---

## 0. Summary

warp_scheduler's per-WG bookkeeping bitmaps (`warp_bar_belong`: which warps belong to the WG; `warp_endprg_cnt`: which warps in the WG have not yet endprg'd) each have two update blocks: on warpReq.fire they **set** bits (a new warp is enrolled), and on warpRsp.fire they **clear** bits (a finished warp is removed). In the source, the clear block is written **after** the set block (belong: :123-134; cnt: :157-163). Chisel follows last-connect-wins semantics for multiple `:=` to the same register — the later write overrides the earlier one, and the read side of every write sees the **old value** from before the clock edge.

So when "warpReq dispatches a new warp to wg3" and "the warpRsp.fire of wg3's last old warp" happen in the same cycle: the set write (belong(3) | 1<<new wid) is written first, and the clear write (belong(3) & ~(1<<old wid), reading the old belong) is written later and **overrides it wholesale** — the new warp's belong/cnt bits are lost even though the warp is already active.

The consequences come in two layers: (a) the lost cnt bit ⇒ mask_0 is set prematurely while the WG still has an active warp ⇒ **premature flushDCache** (the cache is flushed before the WG has truly completed — a consistency risk); (b) the lost belong bit ⇒ the lock drops prematurely and the barrier expectation set is re-initialized by the next warpReq; if the new warp has already entered barrier waiting, the release at :141 clears `warp_bar_data` by belong and **misses it** ⇒ **that warp never becomes ready (deadlock)**.

---

## 1. Module function and design intent

### 1.1 Background concepts

- **last-connect-wins**: Chisel semantics — among multiple `:=` assignments to the same register within one clock cycle, the one appearing later in the source wins; the right-hand side of every assignment reads the register's old value as of the beginning of the cycle (before the clock edge). Equivalent to a sequence of non-blocking assignments within one Verilog always block.
- **WG slot reuse**: a WG's 8 slots (num_block=8) are dynamically allocated by the CTA scheduler. Once a WG's last warp endprg's, the slot can immediately be reused by the next WG — "the old WG wrapping up" and "the new WG moving in" happening in the same cycle is a normal rhythm under dense scheduling, not a pathological corner.
- **The dual identity of the bookkeeping bitmaps**: `warp_bar_belong` both identifies "which warps belong to this wg" (barrier release clears waiting bits by it, :141) and derives `warp_bar_lock` (belong.orR, :135, indicating whether the wg is occupied); `warp_endprg_cnt` directly determines mask_0 (the WG-completion pending-flush criterion, :165). Both bitmaps must track precisely "which warps are currently active in this wg".

### 1.2 Design intent

warpReq.fire adds the new warp into its wg's belong/cnt; warpRsp.fire removes the finished warp. The correct merge semantics for same-cycle same-wg should be "clear first, then set" (net effect = old bitmap − old warp + new warp), i.e. **the set wins**. The source's block order is exactly the opposite.

---

## 2. Construct-by-construct reading of the original code

**Construct 1: belong's set block** (warp_schedule.scala:123-128):

```scala
when(io.warpReq.fire){                                                          // :123
  warp_bar_belong(new_wg_id) := warp_bar_belong(new_wg_id) | (1.U<<io.warpReq.bits.wid).asUInt  // :124
  when(!warp_bar_lock(new_wg_id)) {                                             // :126
    warp_bar_cur(new_wg_id) := 0.U
    warp_bar_exp(new_wg_id) := (1.U << new_wg_wf_count).asUInt - 1.U            // :128
  }
}
```

**Construct 2: belong's clear block** (warp_schedule.scala:131-133, ★ hazard — wrong block order):

```scala
when(io.warpRsp.fire){                                                          // :131
  warp_bar_belong(end_wg_id) := warp_bar_belong(end_wg_id) & (~(1.U<<io.warpRsp.bits.wid)).asUInt  // :133 ★
}
```

On a same-cycle same-wg event (new_wg_id = end_wg_id): the set at :124 is written first, and the clear at :133 is written later and reads the old belong (which does not contain the bit just set at :124) — under last-connect-wins, the new warp's bit is lost.

**Construct 3: the isomorphic problem in cnt** (warp_schedule.scala:157-162, ★ hazard):

```scala
when(io.warpReq.fire){                                                          // :157
  warp_endprg_cnt(new_wg_id) := warp_endprg_cnt(new_wg_id) | (1.U<<io.warpReq.bits.wid).asUInt  // :158
  warp_wg_valid(new_wg_id) := true.B                                            // :159
}
when(io.warpRsp.fire){                                                          // :160
  warp_endprg_cnt(end_wg_id) := warp_endprg_cnt(end_wg_id) & (~(1.U<<io.warpRsp.bits.wid)).asUInt  // :162 ★
}
```

Structurally fully isomorphic to constructs 1/2. Consequence: the lost cnt bit ⇒ mask_0(i) = (cnt(i)==0) && valid(i) (:165) is set prematurely while the wg still has an active warp ⇒ premature flush (I-5's mask_0 mechanism triggered spuriously).

**Construct 4: the harm amplifier on the barrier side** (warp_schedule.scala:138-141):

```scala
warp_bar_data := warp_bar_data | (1.U<<io.warp_control.bits.ctrl.wid).asUInt    // :138 arrival registration
when((warp_bar_cur(end_wg_id) | ...) === warp_bar_exp(end_wg_id)){              // :139 release when complete
  ...
  warp_bar_data := warp_bar_data & (~warp_bar_belong(end_wg_id)).asUInt         // :141 ★ clear waiting bits by belong
}
```

Barrier release clears waiting bits based on belong — after the new warp's belong bit is lost, if it is waiting at the barrier, the clear at :141 misses it ⇒ that warp's waiting bit in `warp_bar_data` persists forever ⇒ `warp_ready` (:181, `~(bar_data | ...)`) is permanently false for that warp ⇒ **deadlock**.

---

## 3. Defect analysis

### 3.1 Precise description of the defect

Trigger condition: the CTA dispatches a new warp (warpReq.fire) to the same wg slot **in the same cycle** as the wg's last warp endprg's (warpRsp.fire). Consequence chain:

1. The new warp's belong(wid) and cnt(wid) bits are lost (last-connect-wins: the clear overrides the set);
2. Lost cnt bit ⇒ mask_0 set prematurely ⇒ **premature flushDCache** (a flush is initiated before the WG has truly completed; dirty data is written back too early — a consistency risk);
3. Lost belong bit ⇒ `warp_bar_lock` (=belong.orR) drops prematurely ⇒ the next warpReq hits the `!lock` branch at :126 ⇒ `warp_bar_cur/exp` are re-initialized (the barrier progress of resident warps is zeroed);
4. If the new warp whose bit was lost has already entered barrier waiting ⇒ the release at :141 misses its clear ⇒ **never ready (deadlock)**.

### 3.2 Root cause

**The same-cycle "clear first, then set" semantics was written backwards**. The source order of the two update blocks makes the clear write later and the set write earlier, and Chisel's last-connect-wins lets the later write win — the correct merge semantics (set wins) requires swapping the block order. This is the **same defect pattern** as I-4 (the same-cycle set/clear race at scoreboard.scala:115-118): same project, same semantic trap, different module; I-4 was proven unreachable via the gating chain (the III-3 lesson: reachability arguments must cover the complete enable chain), while I-7 was confirmed **genuinely reachable** by ChiselSim measurement — the same pattern with different fates, which exactly illustrates why "mechanism confirmed ≠ reachable" must be adjudicated case by case.

### 3.3 Harm and tolerability

- **Harm**: three forms — premature flush (consistency risk), barrier bookkeeping re-initialization (progress corruption), and barrier waiting-bit clear miss (deadlock). Triggering only needs a dense CTA slot-reuse rhythm (back-to-back WG scheduling), within the scheduler's normal operating range.
- **Tolerability**: the trigger condition depends on CTA scheduling timing (same-cycle same-wg slot reuse); not every WG switch hits it, but there is no structural protection and the frequency rises with load. The existence of a deadlock form makes the rating **High**.
- **Fix recommendation**: change the same-cycle same-wg merge semantics to "clear first, then set" (set wins) — swapping the two when blocks suffices (exploiting last-connect-wins so the later-written set wins); or delay the allocation by one cycle. The block-order swap was adopted (§7).

---

## 4. Lean formal evidence

All in `lean/Ventus/Schedule/WarpScheduler.lean`:

**Mechanism characterization (M4 semantics)**: `wsStepBelong` and `wsStepCnt` model Chisel's "read old value + last-connect-wins" strictly — the req set is written first, the rsp clear is written later, and the later write's right-hand side reads the old belong/cnt (the model comments state the :123-134 correspondence explicitly). For same-cycle same-wg, the clear overriding the set wholesale is the model's definitional behavior, requiring no extra assumptions.

**T7 witness** (native_decide, `wsC2` series): same-cycle warpReq (warp5→wg3) and warpRsp (warp4 endprg, wg3) → `barBelong(3)=0`, `endprgCnt(3)=0` while `warpActive(5)=1` — wg3 still has an active warp (warp5 active) yet mask_0(3)=1 (flush requested prematurely); both consequences — the lost bit and the premature mask_0 — are pinned down on the same trace.

**Fixed-version verification** (`lean/VentusF/Schedule.lean`): `fschWs_belong_req_set`/`fschWs_cnt_req_set` (after the fix, the new warp's bookkeeping bits are always set on same-cycle same-wg), `fschWsT_i7_req_survives` (the new warp's bookkeeping survives the original witness scenario on the fixed version).

---

## 5. Simulation verification (ChiselSim measurements + patch-tree regression)

**ChiselSim module-level reproduction** (`repro/WarpSchedulerBugRepro.scala` I-7 case, actually run 2026-09-06/07, doc/22): same-cycle fire of warpReq (warp1→wg3) + endprg (warp0 of wg3); measured **wg3 issuing a premature flush while warp1 is still active** — the consequence chain of lost bookkeeping bit and premature mask_0 was directly observed on RTL. Verdict: **reproduction successful**.

**Patch-tree regression**: 35-patch tree 4/4 green after fence_end adaptation; 38-patch merged tree **5/5 green** (doc/22) — after the fix the new warp's bookkeeping survives the same-cycle scenario; no regressions.

---

## 6. Upstream impact analysis

- **Trigger surface**: back-to-back WG scheduling (slot reuse in the same cycle as the old WG's last warp endprg's) — a normal rhythm when the CTA scheduler runs at full load, not dependent on pathological inputs.
- **Why upstream did not find it**: the same-cycle window is only one cycle wide; the consequences (premature flush / barrier corruption / occasional deadlock) are temporally separated from the trigger, and a simulation regression without a targeted checkpoint ("does the wg still have an active warp when the flush is issued?") will not raise an alarm.
- **Significance of the contrast with I-4**: the same "same-cycle clear-then-set" semantic trap is structurally masked by the gating chain in the scoreboard (I-4) and genuinely reachable in the warp scheduler (this entry) — validating the necessity of the project's discipline that "every mechanism-level finding must undergo its own reachability adjudication" (the original lesson of doc/03 III-3).
- **Fix dependency**: this entry's fix sits in the same patch as I-6 (warpRsp hold-until-ready) and they are mutually dependent — after the fix, the Rsp can be issued several cycles late, so the clear block must use `warp_rsp_fire_wg` (the wg tag at the response's actual fire cycle) instead of the combinational `end_wg_id`, and the block-order swap is done on top of that.

---

## 7. Fix and fix verification

**Patch** (`i06-i07-i46-warp-schedule-endprg.patch` (internal fix manifest; not released), same patch as I-6 and I-46; the edit points relevant to this entry):

The Rsp clear blocks of `warp_bar_belong` and `warp_endprg_cnt` are **moved before** the Req set blocks — under Chisel last-connect-wins, the same-cycle same-wg merge semantics becomes "clear first, then set" (set wins), and the new warp's bookkeeping bit survives. The clear blocks' wg tag switches to `warp_rsp_fire_wg` (matching I-6's delayed response: on the pass-through cycle the combinationally looked-up end_wg_id is used; on pending cycles the registered value).

**Fix verification trio**:

- Effectiveness: Lean fixed-version theorems `fschWs_belong_req_set`/`fschWs_cnt_req_set`/`fschWsT_i7_req_survives`;
- Regression safety: 38-patch merged tree ChiselSim regression 5/5 green (doc/22);
- No follow-up items: the block-order swap is a pure bookkeeping-semantics correction and does not change any interface timing.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | warp_schedule.scala:123-134/:157-163/:138-141 checked line by line; last-connect-wins semantics cross-checked against Chisel conventions | Consistent |
| Lean machine-checked proof | `wsStepBelong`/`wsStepCnt` (M4 semantic characterization) + T7 witness (lost bit + premature mask_0 pinned on the same trace) | Concrete-trace level |
| ChiselSim reproduction | Same-cycle Req+Rsp: wg3 flushes prematurely while warp1 is active | Measured |
| Fix verification | i06-i07-i46 patch (block-order swap); Lean fixed-version set-survival theorems + 38-patch tree regression 5/5 green | Measured + machine-checked |

I-7 is a "same-cycle clear-then-set written backwards" race, same pattern as I-4 but with the opposite fate (I-4 proven unreachable via gating; this entry measured reachable) — together they are the best footnote for this project's methodology of "mechanism confirmed ≠ reachable; adjudicate case by case". The fix (block-order swap) is only a few lines, but locating the precise semantics of "the clear overrides the set" requires bitmap-level cycle-by-cycle reasoning — a typical case where the Lean model witness (T7) pins the shape down first and ChiselSim then confirms it on RTL.
