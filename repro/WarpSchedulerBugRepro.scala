// repro/WarpSchedulerBugRepro.scala — ChiselSim reproduction of
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// I-5/I-6/I-7/I-8 (ready-to-run, not executed in this environment: no
// mill/scala dependencies on this machine). Follows the ventus/tests/ style
// (ChiselScalatestTester) and the sibling file IntDivModBugRepro.scala.
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.WarpSchedulerBugRepro
//
// Bugs covered (see doc/03-bug-reports.md for details):
//   I-5  [confirmed] warp_schedule.scala:164-173: when multiple wg finish
//        simultaneously, the endprg/flush bookkeeping deadlocks (OHToUInt
//        bitwise-ORs a non-one-hot input; flush_entry lands on a
//        non-existent wg and valid gets stuck forever).
//        Lean witnesses: WarpScheduler.lean T6 / ws4_flush_entry_avoids /
//        ws4_stuck_forever.
//        Trigger: two wg with one warp each endprg in succession (adjacent
//        cycles suffice), flushDCache.ready held high.
//        Expected: flushDCache.valid returns to 0 after each wg's flush
//        completes; actual: valid stuck forever (fires every cycle).
//   I-6  [confirmed] warp_schedule.scala:55 warpRsp handshake violation
//        (valid is a single-cycle pulse that does not wait for ready); after
//        the response is lost, belong/cnt are never cleared and the flush is
//        never issued.
//        Trigger: warpRsp.ready=0 on the endprg cycle. Expected: the
//        response holds until ready / the flush is eventually issued;
//        actual: valid rises for only one cycle and is lost,
//        flushDCache.valid is never asserted.
//   I-7  [confirmed] warp_schedule.scala:123-134 vs :157-163: when
//        warpReq+warpRsp point at the same wg in the same cycle, the clear
//        overwrites the set (last-connect-wins); the new warp's bookkeeping
//        bit is lost → flushDCache fires early while the wg still has an
//        active warp. Lean witness: WarpScheduler.lean T7.
//        Trigger: wg3's warp0 endprg and warp1 dispatched in the same cycle.
//        Expected: no flush (wg3 still has an active warp); actual:
//        flushDCache.valid rises immediately.
//   I-8  [unconfirmed → this test doubles as a check of the triggering
//        precondition] warp_schedule.scala:73-74 flush serves a single wid;
//        when warp_end and a branch jump collide in the same cycle only the
//        branch is served. Note: at :51-52 warp_control.ready =
//        !branch.fire & !flushCache.valid, i.e. endprg and branch are
//        structurally mutually exclusive — if this test passes (both flushes
//        are delivered), the same-cycle precondition does not hold and I-8
//        should be downgraded/closed accordingly; if it fails (warp b's
//        flush is lost), I-8 is confirmed.
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class WarpSchedulerBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  // ---- helper: poke all CtrlSigs fields to deterministic values (with spike_info when SPIKE_OUTPUT=true) ----
  def pokeCtrlSigsZero(c: CtrlSigs): Unit = {
    c.inst.poke(0.U); c.wid.poke(0.U); c.fp.poke(false.B); c.branch.poke(0.U)
    c.simt_stack.poke(false.B); c.simt_stack_op.poke(false.B); c.barrier.poke(false.B)
    c.csr.poke(0.U); c.reverse.poke(false.B); c.sel_alu2.poke(0.U); c.sel_alu1.poke(0.U)
    c.isvec.poke(false.B); c.sel_alu3.poke(0.U); c.mask.poke(false.B); c.sel_imm.poke(0.U)
    c.mem_whb.poke(0.U); c.mem_unsigned.poke(false.B); c.alu_fn.poke(0.U)
    c.force_rm_rtz.poke(false.B); c.is_vls12.poke(false.B); c.mem.poke(false.B)
    c.mul.poke(false.B); c.tc.poke(false.B); c.disable_mask.poke(false.B)
    c.custom_signal_0.poke(false.B); c.mem_cmd.poke(0.U); c.mop.poke(0.U)
    c.reg_idx1.poke(0.U); c.reg_idx2.poke(0.U); c.reg_idx3.poke(0.U); c.reg_idxw.poke(0.U)
    c.wvd.poke(false.B); c.fence.poke(false.B); c.sfu.poke(false.B)
    c.readmask.poke(false.B); c.writemask.poke(false.B); c.wxd.poke(false.B)
    c.pc.poke(0.U); c.imm_ext.poke(0.U)
    c.atomic.poke(false.B); c.aq.poke(false.B); c.rl.poke(false.B)
    if (SPIKE_OUTPUT) {
      c.spike_info.get.sm_id.poke(0.U); c.spike_info.get.pc.poke(0.U); c.spike_info.get.inst.poke(0.U)
    }
  }

  // ---- helper: construct one warpReq (CTA dispatch). tag high 3 bits = wg slot, low 3 bits = wf id ----
  def pokeWarpReq(dut: warp_scheduler, wid: Int, tag: Int, wfCount: Int): Unit = {
    val d = dut.io.warpReq.bits.CTAdata
    d.dispatch2cu_wg_wf_count.poke(wfCount.U)
    d.dispatch2cu_wf_size_dispatch.poke(num_thread.U)
    d.dispatch2cu_sgpr_base_dispatch.poke(0.U)
    d.dispatch2cu_vgpr_base_dispatch.poke(0.U)
    d.dispatch2cu_lds_base_dispatch.poke(0.U)
    d.dispatch2cu_wf_tag_dispatch.poke(tag.U)
    d.dispatch2cu_start_pc_dispatch.poke(0x1000.U)
    d.dispatch2cu_pds_base_dispatch.poke(0.U)
    d.dispatch2cu_gds_base_dispatch.poke(0.U)
    d.dispatch2cu_csr_knl_dispatch.poke(0.U)
    d.dispatch2cu_wgid_x_dispatch.poke(0.U)
    d.dispatch2cu_wgid_y_dispatch.poke(0.U)
    d.dispatch2cu_wgid_z_dispatch.poke(0.U)
    d.dispatch2cu_wg_id.poke(0.U)
    dut.io.warpReq.bits.wid.poke(wid.U)
    dut.io.warpReq.valid.poke(true.B)
  }

  // ---- helper: endprg event (warp_control.fire & simt_stack_op) ----
  def pokeEndprg(dut: warp_scheduler, wid: Int, tagOfWid: Int): Unit = {
    pokeCtrlSigsZero(dut.io.warp_control.bits.ctrl)
    dut.io.warp_control.bits.ctrl.wid.poke(wid.U)
    dut.io.warp_control.bits.ctrl.simt_stack_op.poke(true.B)
    dut.io.warp_control.valid.poke(true.B)
    // wg_id_tag is an input (actually produced by CTA2warp's lookup); the
    // test directly presents this warp's tag
    dut.io.wg_id_tag.poke(tagOfWid.U)
  }

  def pokeIdle(dut: warp_scheduler): Unit = {
    dut.io.pc_reset.poke(false.B)
    dut.io.warpReq.valid.poke(false.B)
    dut.io.warp_control.valid.poke(false.B)
    dut.io.branch.valid.poke(false.B)
    dut.io.branch.bits.wid.poke(0.U)
    dut.io.branch.bits.jump.poke(false.B)
    dut.io.branch.bits.new_pc.poke(0.U)
    if (SPIKE_OUTPUT) {
      dut.io.branch.bits.spike_info.get.sm_id.poke(0.U)
      dut.io.branch.bits.spike_info.get.pc.poke(0.U)
      dut.io.branch.bits.spike_info.get.inst.poke(0.U)
    }
    dut.io.pc_rsp.valid.poke(false.B)
    dut.io.pc_rsp.bits.addr.poke(0.U)
    dut.io.pc_rsp.bits.data.poke(0.U)
    dut.io.pc_rsp.bits.mask.poke(0.U)
    dut.io.pc_rsp.bits.warpid.poke(0.U)
    dut.io.pc_rsp.bits.status.poke(0.U)
    dut.io.pc_req.ready.poke(true.B)
    dut.io.scoreboard_busy.poke(0.U)
    dut.io.exe_busy.poke(0.U)
    dut.io.pc_ibuffer_ready.foreach(_.poke(0.U))
    dut.io.issued_warp.valid.poke(false.B)
    dut.io.issued_warp.bits.poke(0.U)
    dut.io.warpRsp.ready.poke(true.B)
    dut.io.flushDCache.ready.poke(false.B)
  }

  "I-5: two wg endprg in succession + flushDCache.ready held high; flushDCache.valid should return to 0 after the flushes complete" in {
    // [2026-09-06 execution calibration] The original stimulus used wg0(tag
    // 0x00)+wg1(tag 0x08): OHToUInt(0b011)=0|1=1 still points at a real wg
    // (wg1), so the two flushes are consumed one by one and the bug does NOT
    // trigger (the first run passed). Per the mechanism at
    // warp_schedule.scala:164-173, the stuck case requires flush_entry to
    // land on a wg whose mask_0 bit is 0: use wg1(tag 0x08)+wg2(tag 0x10),
    // OHToUInt(0b110)=1|2=3, mask_0(3)=false => never cleared, stuck forever.
    test(new warp_scheduler) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // T0: warp1 -> wg1 (tag=0b001_000), 1 wf in the wg
      pokeWarpReq(dut, wid = 1, tag = 0x08, wfCount = 1)
      dut.clock.step()
      // T1: warp2 -> wg2 (tag=0b010_000)
      pokeWarpReq(dut, wid = 2, tag = 0x10, wfCount = 1)
      dut.clock.step()
      pokeIdle(dut)
      // T2: warp1 endprg (warpRsp.ready=1, cnt(wg1) cleared)
      pokeEndprg(dut, wid = 1, tagOfWid = 0x08)
      dut.clock.step()
      // T3: warp2 endprg (cnt(wg2) cleared) — afterwards mask_0 = 0b110 (non-one-hot)
      pokeEndprg(dut, wid = 2, tagOfWid = 0x10)
      dut.clock.step()
      pokeIdle(dut)
      // From T4 on mask_0=0b110, flush_entry=OHToUInt(0b110)=3, mask_0(3)=false => never cleared
      dut.io.flushDCache.ready.poke(true.B)
      var stuckCnt = 0
      for (_ <- 0 until 6) {
        if (dut.io.flushDCache.valid.peek().litToBoolean) stuckCnt += 1
        dut.clock.step()
      }
      // Expected: after the flush is consumed once per wg, valid returns to
      // 0 (at most 2 valid cycles within 6).
      // Actual (bug): valid is 1 every cycle (need_flush stays true), stuckCnt==6.
      assert(stuckCnt <= 2,
        s"I-5: flushDCache.valid stuck, valid in $stuckCnt of 6 cycles (expected <=2)")
    }
  }

  "I-6: with warpRsp.ready=0 on the endprg cycle, the response is silently dropped and this wg's flush is never issued" in {
    test(new warp_scheduler) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // T0: warp2 -> wg2 (tag=0b010_000), 1 wf
      pokeWarpReq(dut, wid = 2, tag = 0x10, wfCount = 1)
      dut.clock.step()
      pokeIdle(dut)
      // T1: warp2 endprg, but warpRsp.ready=0 — warp_control.fire still
      //     happens (active cleared the same cycle), while warpRsp.fire=0
      //     (belong/cnt not cleared)
      pokeEndprg(dut, wid = 2, tagOfWid = 0x10)
      dut.io.warpRsp.ready.poke(false.B)
      // Decoupled contract: valid should hold until ready. Check the
      // handshake violation itself:
      assert(dut.io.warpRsp.valid.peek().litToBoolean, "precondition: warpRsp.valid should be 1 on the endprg cycle")
      dut.clock.step()
      pokeIdle(dut)
      // T2: the single-cycle valid pulse is gone (direct observation of the
      // contract violation) — record it first, assert together at the end
      val validAtT2 = dut.io.warpRsp.valid.peek().litToBoolean
      // From T2 on for several cycles: cnt(wg2) is never cleared =>
      // mask_0(wg2) never set => the flush is never issued
      dut.io.flushDCache.ready.poke(true.B)
      var flushSeen = false
      for (_ <- 0 until 8) {
        if (dut.io.flushDCache.valid.peek().litToBoolean) flushSeen = true
        dut.clock.step()
      }
      // Evidence 1 (Decoupled compliance): valid should hold after ready=0
      // — actual: gone by T2 (response lost)
      // Evidence 2 (bookkeeping consequence): after all of a wg's warps
      // finish, a flushDCache request should be issued — actual: never issued
      assert(validAtT2 && flushSeen,
        s"I-6: warpRsp handshake violation and bookkeeping deadlock — T2 valid=$validAtT2 (expected true: hold until ready), " +
          s"flushDCache.valid seen within 8 cycles=$flushSeen (expected true). After the response is lost, belong/cnt " +
          "are never cleared and the flush is never issued (the developer comment/assertion at CTA2warp.scala:71-74 corroborates this problem)")
    }
  }

  "I-7: same-cycle warpReq(warp1->wg3)+endprg(warp0 of wg3); the new warp's bookkeeping is overwritten by the clear and wg3 flushes early" in {
    test(new warp_scheduler) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // T0: warp0 -> wg3 (tag=0b011_000), wg3 has 2 wf total
      pokeWarpReq(dut, wid = 0, tag = 0x18, wfCount = 2)
      dut.clock.step()
      pokeIdle(dut)
      // T1: same cycle — warp0 endprg (wg_id_tag=0x18 points at wg3) +
      //     warp1 dispatched into wg3 (tag=0b011_001)
      //     In :123-134 (belong) and :157-163 (cnt) the Rsp clear is written
      //     after the Req set; last-connect-wins => the new warp1's
      //     belong/cnt bits are lost
      pokeEndprg(dut, wid = 0, tagOfWid = 0x18)
      pokeWarpReq(dut, wid = 1, tag = 0x19, wfCount = 2)
      dut.io.warpRsp.ready.poke(true.B)
      dut.clock.step()
      pokeIdle(dut)
      // From T2 on: cnt(wg3)=0 and wg_valid(wg3)=1 => mask_0(wg3)=1 =>
      // premature flush, but warp1 is still active (warp_active(1)=1)
      var prematureFlush = false
      for (_ <- 0 until 4) {
        if (dut.io.flushDCache.valid.peek().litToBoolean) prematureFlush = true
        dut.clock.step()
      }
      // Expected: wg3 still has the active warp1, no flushDCache should be
      // issued.
      // Actual (bug): mask_0 is set early, flushDCache.valid rises.
      assert(!prematureFlush,
        "I-7: same-cycle Req+Rsp clear overwrote the set; wg3 flushed early while warp1 is still active")
    }
  }

  "I-8 precondition check: when a branch jump and an endprg collide in the same cycle, does flush serve only the branch" in {
    test(new warp_scheduler) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // warp0(a) -> wg4, warp1(b) -> wg5
      pokeWarpReq(dut, wid = 0, tag = 0x20, wfCount = 1)
      dut.clock.step()
      pokeWarpReq(dut, wid = 1, tag = 0x28, wfCount = 1)
      dut.clock.step()
      pokeIdle(dut)
      // T: drive branch(wid=0, jump=1) and endprg(wid=1) in the same cycle
      dut.io.branch.valid.poke(true.B)
      dut.io.branch.bits.jump.poke(true.B)
      dut.io.branch.bits.wid.poke(0.U)
      dut.io.branch.bits.new_pc.poke(0x2000.U)
      pokeEndprg(dut, wid = 1, tagOfWid = 0x28)
      // warp_schedule.scala:52: warp_control.ready := !io.branch.fire & !flushCache.valid
      // => when branch.fire=1, warp_control.ready=0 and the endprg does not happen that cycle
      val warpCtrlReady = dut.io.warp_control.ready.peek().litToBoolean
      val flushValidT = dut.io.flush.valid.peek().litToBoolean
      val flushBitsT = dut.io.flush.bits.peek().litValue
      dut.clock.step()
      // T+1: branch withdrawn; the endprg (warp_control.valid still held) fires this cycle
      dut.io.branch.valid.poke(false.B)
      pokeEndprg(dut, wid = 1, tagOfWid = 0x28)
      val flushValidT1 = dut.io.flush.valid.peek().litToBoolean
      val flushBitsT1 = dut.io.flush.bits.peek().litValue
      dut.clock.step()
      pokeIdle(dut)
      // Two readings:
      //  (a) if warpCtrlReady==false (the :52 mutual exclusion works): cycle
      //      T flushes only wid0, cycle T+1 flushes wid1, both flushes are
      //      delivered — I-8's same-cycle precondition does not hold; I-8
      //      should be closed/downgraded.
      //  (b) if warpCtrlReady==true (the mutual exclusion is bypassed):
      //      cycle T has flush.bits=0 and wid1's flush is permanently lost —
      //      I-8 confirmed.
      // The assertion below is written per the contract "the flush of both
      // wids must be delivered"; its failure confirms I-8:
      val bFlushed = (flushValidT && flushBitsT == 1) || (flushValidT1 && flushBitsT1 == 1)
      assert(flushValidT && flushBitsT == 0,
        s"I-8 precondition: on cycle T flush should serve branch(wid=0), actual valid=$flushValidT bits=$flushBitsT")
      assert(bFlushed,
        "I-8 confirmed: warp b(wid=1)'s warp_end flush was preempted by the branch flush and permanently lost; " +
          "if warpCtrlReady=false this assertion should not fail (the two events are serialized by the :52 mutual exclusion)." +
          s" Scene: warpCtrlReady=$warpCtrlReady T(valid=$flushValidT,bits=$flushBitsT) " +
          s"T+1(valid=$flushValidT1,bits=$flushBitsT1)")
    }
  }
}
