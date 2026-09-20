// repro/CTA2warpTagBugRepro.scala — ChiselSim reproduction of I-25
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.CTA2warpTagBugRepro
//
// I-25 [confirmed] CTA2warp.scala:77 completion-response tag read late +
// wid reused in the same cycle → completion bookkeeping attributed to the
// wrong warp.
//   Mechanism: CTArsp.bits := data(fifo.head.wid) combinationally reads the
//   data table at dequeue time; while at :63-66 wid is cleared from
//   idx_using in the very cycle of warpRsp.fire, so the next cycle it can be
//   reused by a new CTAreq, overwriting data(wid). If the response stays in
//   the FIFO for >=2 cycles (CTArsp backpressure, the normal state of the
//   cu_interface gather FSM), it reads the new warp's tag.
//   Lean witness: CTA2warp.lean T7 (tag=0x11 ≠ 0x08).
//   Trigger: after warp0 (tag=0x08) endprg, backpressure CTArsp for >=2
//   cycles, during which the same wid is re-dispatched (tag=0x11).
//   Expected: CTArsp.bits.cu2dispatch_wf_tag_done == 0x08 (the old warp's tag).
//   Actual: reads 0x11 (the new warp's tag) — the old WG never completes and
//   the new WG completes early (see the consequence chain in the report).
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec

class CTA2warpTagBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  def pokeCTAreq(dut: CTA2warp, tag: Int): Unit = {
    val d = dut.io.CTAreq.bits
    d.dispatch2cu_wg_wf_count.poke(1.U)
    d.dispatch2cu_wf_size_dispatch.poke(32.U)
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
    dut.io.CTAreq.valid.poke(true.B)
  }

  "I-25: wid reused during CTArsp backpressure; the stranded response's tag is polluted by the new warp" in {
    test(new CTA2warp) { dut =>
      // initial: downstream (warp_scheduler) and CTA side ready
      dut.io.warpReq.ready.poke(true.B)
      dut.io.warpRsp.valid.poke(false.B)
      dut.io.warpRsp.bits.wid.poke(0.U)
      dut.io.CTAreq.valid.poke(false.B)
      dut.io.CTArsp.ready.poke(false.B) // CTArsp backpressure
      dut.io.wg_id_lookup.poke(0.U)
      dut.clock.step()

      // T0: CTAreq(tag=0x08) fire -> wid0 allocated, data(0):=0x08; warpReq fires the same cycle
      pokeCTAreq(dut, tag = 0x08)
      assert(dut.io.CTAreq.ready.peek().litToBoolean, "precondition: CTAreq should be acceptable")
      dut.clock.step()
      dut.io.CTAreq.valid.poke(false.B)

      // T1: warp0's endprg response comes back (warpRsp.fire, enters the
      //     internal FIFO; idx_using(0) cleared the same cycle -> wid0
      //     reusable from the next cycle). CTArsp remains backpressured.
      dut.io.warpRsp.valid.poke(true.B)
      dut.io.warpRsp.bits.wid.poke(0.U)
      assert(dut.io.warpRsp.ready.peek().litToBoolean, "precondition: warpRsp FIFO empty, ready should be 1")
      dut.clock.step()
      dut.io.warpRsp.valid.poke(false.B)

      // T2: wid0 reused — a new CTAreq(tag=0x11) fires; data(0) is overwritten to 0x11 at end of cycle
      pokeCTAreq(dut, tag = 0x11)
      assert(dut.io.CTAreq.ready.peek().litToBoolean, "precondition: wid0 should have been reclaimed and be re-allocatable")
      dut.clock.step()
      dut.io.CTAreq.valid.poke(false.B)

      // T3: the old response is still at the FIFO head (CTArsp.valid=1,
      //     backpressure not lifted), but bits combinationally reads
      //     data(0) — which is already the new warp's tag
      assert(dut.io.CTArsp.valid.peek().litToBoolean, "precondition: the stranded response should still be pending")
      val tagObserved = dut.io.CTArsp.bits.cu2dispatch_wf_tag_done.peek().litValue
      // hold backpressure one more cycle before consuming, to confirm this
      // is not a transient phenomenon
      dut.clock.step()
      dut.io.CTArsp.ready.poke(true.B)
      val tagAtFire = dut.io.CTArsp.bits.cu2dispatch_wf_tag_done.peek().litValue

      // Expected: 0x08 (warp0's tag); actual (bug): 0x11 (the new warp's tag after wid reuse)
      assert(tagObserved == 0x08 && tagAtFire == 0x08,
        s"I-25: stranded response's tag polluted, read 0x${tagObserved.toString(16)}/0x${tagAtFire.toString(16)}, expected 0x08")
    }
  }
}
