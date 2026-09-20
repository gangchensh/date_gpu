// repro/DCacheBugRepro.scala — ChiselSim reproduction of I-29/I-30
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/L1Cache/DCache/) and run:
//   mill ventus.test.testOnly L1Cache.DCache.DCacheBugRepro
//
// I-29 [confirmed] DCache.scala:623 probereadAllocateWriteConflict only
//   blocks "a coreReq.fire in the same cycle as allocateWrite"; it does not
//   block a write request stranded in st1 because missRspOut occupies the
//   response channel (:445) — the stranded write and the memRsp-triggered
//   allocateWrite write/read the same (set,way) of the data SRAM in the same
//   cycle (instantiated at :637-659 with bypassWrite=false) => the victim
//   writeback data is polluted by the LFSR random value (:764
//   dirtyReplace_st1.a_data).
//   Lean witnesses: DCache.lean dcT_w1_collision_reachable / dcT_w1_sram_lfsr.
//   Construction (see comments for the cycle-by-cycle correspondence; the
//   timing is derived from the source — if it does not trigger on the first
//   run, calibrate the relative position of the collision cycle first):
//     1. load A(tag=1,set=0) miss -> refill -> way0; store A(hit, dirty, data=0xAAAA1111)
//     2. load B(tag=2,set=0) miss -> refill -> way1; store B(hit, dirty, data=0xBBBB2222)
//        (B is touched last => under the coexisting MRU behavior of I-27, the
//        next allocation evicts way1=B)
//     3. load C(tag=3,set=0) miss -> memReq Get (do not answer; hold it)
//     4. same cycle: store B'(hit way1, data=0xDDDD4444)'s coreReq + C's memRsp
//        — B' is backpressured by missRspOut and stranded in st1 for one
//        cycle; the cycle it is released it writes (set0,way1), exactly the
//        same cycle as victim B's replace read (set0,way1) => the SRAM reads
//        out LFSR data
//     5. observe the victim writeback memReq (a_opcode=1 PutPart, a_addr=B's
//        block base) a_data(0): expected ∈ {0xBBBB2222, 0xDDDD4444} (old or
//        new data both acceptable); actual = LFSR garbage.
//   Note: the victim landing on way1 relies on the coexisting I-27 (MRU
//   eviction); if I-27 is fixed first, the victim becomes way0(A) — retarget
//   step 4's stranded store at A (tag=1) and retest.
//
// I-30 [confirmed] DCache.scala:425 memRspIsFluOrInv has no valid qualifier
//   — after memRsp_Q consumes a hintAck, the queue-head register retains
//   d_opcode=2, and the second and subsequent flush/invalidate's
//   waitforL2flush is erroneously cleared for one cycle -> st1 is released
//   early; when the real hintAck arrives, the OR merge at :754 makes the
//   response carry a wrong instrId or be lost entirely
//   (dcT_w2b_stale_instrId / dcT_w2c_rsp_lost).
//   Construction: invalidate(instrId=1) -> L2 hintAck ->
//   load(tag=5,set=1,instrId=5) -> invalidate(instrId=2) -> L2 hintAck;
//   collect all coreRsp.
//   Expected: exactly 3 responses, instrIds {1,5,2} in order (the criterion
//   may be adjusted for the actual pipeline ordering, but every request must
//   have exactly one response carrying its own instrId).
//   Actual (bug): the second invalidate's response carries the load's
//   instrId (or is lost/duplicated).
//   Note: this case crosses many state-machine paths; if no disorder appears
//   on the first run, print the actual response sequence first and then
//   tighten the assertions against the report.
package L1Cache.DCache

import L1Cache._
import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec

class DCacheBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  val param = (new MyConfig).toInstance

  // [2026-09-06 execution adaptation] Run on the Verilator backend:
  // DCache's coreReq_st1_ready defaults to false when coreReqControl_st1_Q is
  // empty, and the queue's content registers are not reset — under treadle
  // (random initialization) tagready_st1 gets stuck at 0 and coreReq.ready
  // never rises (both tests failed their first-request precondition within 50
  // cycles). Verilator zero-initializes these registers, matching the real
  // hardware/verilator flow used by sim-verilator (and the repo's own
  // tests.scala, which uses VerilatorBackendAnnotation for the same reason).

  // ---- helpers ----
  def pokeIdle(dut: DataCache): Unit = {
    dut.io.coreReq.valid.poke(false.B)
    dut.io.coreReq.bits.instrId.poke(0.U)
    dut.io.coreReq.bits.opcode.poke(0.U)
    dut.io.coreReq.bits.param.poke(0.U)
    dut.io.coreReq.bits.tag.poke(0.U)
    dut.io.coreReq.bits.setIdx.poke(0.U)
    dut.io.coreReq.bits.perLaneAddr.foreach { l =>
      l.activeMask.poke(false.B); l.blockOffset.poke(0.U); l.wordOffset1H.poke(0.U)
    }
    dut.io.coreReq.bits.data.foreach(_.poke(0.U))
    dut.io.coreReq.bits.spike_info.get.pc.poke(0.U)
    dut.io.coreReq.bits.spike_info.get.vaddr.poke(0.U)
    dut.io.coreRsp.ready.poke(true.B)
    dut.io.memRsp.valid.poke(false.B)
    dut.io.memRsp.bits.d_opcode.poke(0.U)
    dut.io.memRsp.bits.d_source.poke(0.U)
    dut.io.memRsp.bits.d_addr.poke(0.U)
    dut.io.memRsp.bits.d_data.foreach(_.poke(0.U))
    dut.io.memReq.get.ready.poke(true.B)
  }

  // Send one coreReq (only lane0 active; wordOffset1H=0b1111 full word) and
  // wait for fire
  def sendCoreReq(dut: DataCache, opcode: Int, param: Int, instrId: Int,
                  tag: BigInt, setIdx: Int, data: BigInt = 0): Unit = {
    dut.io.coreReq.bits.instrId.poke(instrId.U)
    dut.io.coreReq.bits.opcode.poke(opcode.U)
    dut.io.coreReq.bits.param.poke(param.U)
    dut.io.coreReq.bits.tag.poke(tag.U)
    dut.io.coreReq.bits.setIdx.poke(setIdx.U)
    dut.io.coreReq.bits.perLaneAddr(0).activeMask.poke(true.B)
    dut.io.coreReq.bits.perLaneAddr(0).blockOffset.poke(0.U)
    dut.io.coreReq.bits.perLaneAddr(0).wordOffset1H.poke(15.U)
    dut.io.coreReq.bits.data(0).poke(data.U)
    dut.io.coreReq.valid.poke(true.B)
    var t = 0
    while (!dut.io.coreReq.ready.peek().litToBoolean && t < 500) { dut.clock.step(); t += 1 } // [2026-09-07] 50 -> 500: post-invalidate settling exceeds 50 cycles
    assert(dut.io.coreReq.ready.peek().litToBoolean,
      s"precondition: coreReq(instrId=$instrId) was not accepted within 500 cycles")
    dut.clock.step() // this cycle fires
    clearCoreReq(dut)
  }

  def clearCoreReq(dut: DataCache): Unit = {
    dut.io.coreReq.valid.poke(false.B)
    dut.io.coreReq.bits.perLaneAddr(0).activeMask.poke(false.B)
  }

  // Wait for a memReq satisfying the condition and return (a_opcode, a_addr, a_source, a_data)
  def waitMemReq(dut: DataCache, opcode: Int, timeout: Int = 60): (BigInt, BigInt, BigInt, BigInt) = {
    var t = 0
    var got: Option[(BigInt, BigInt, BigInt, BigInt)] = None
    while (got.isEmpty && t < timeout) {
      if (dut.io.memReq.get.valid.peek().litToBoolean &&
          dut.io.memReq.get.bits.a_opcode.peek().litValue == opcode) {
        got = Some((dut.io.memReq.get.bits.a_opcode.peek().litValue,
          dut.io.memReq.get.bits.a_addr.get.peek().litValue,
          dut.io.memReq.get.bits.a_source.peek().litValue,
          dut.io.memReq.get.bits.a_data(0).peek().litValue))
      }
      dut.clock.step(); t += 1
    }
    assert(got.isDefined, s"precondition: timed out waiting for memReq(opcode=$opcode)")
    got.get
  }

  // Feed one L2 read response (AccessAckData, d_opcode=1), with d_source
  // filled from the captured a_source
  def sendFillRsp(dut: DataCache, dsource: BigInt, base: BigInt): Unit = {
    dut.io.memRsp.bits.d_opcode.poke(1.U)
    dut.io.memRsp.bits.d_source.poke(dsource.U)
    dut.io.memRsp.bits.d_addr.poke(0.U)
    dut.io.memRsp.bits.d_data.zipWithIndex.foreach { case (w, i) => w.poke((base + i).U) }
    dut.io.memRsp.valid.poke(true.B)
    dut.clock.step()
    dut.io.memRsp.valid.poke(false.B)
  }

  // Feed one hintAck (d_opcode=2, corresponding to a_opcode=5 Flush)
  def sendHintAck(dut: DataCache): Unit = {
    dut.io.memRsp.bits.d_opcode.poke(2.U)
    dut.io.memRsp.bits.d_source.poke(0.U)
    dut.io.memRsp.bits.d_addr.poke(0.U)
    dut.io.memRsp.bits.d_data.foreach(_.poke(0.U))
    dut.io.memRsp.valid.poke(true.B)
    dut.clock.step()
    dut.io.memRsp.valid.poke(false.B)
  }

  // Collect the instrIds of all coreRsp within n cycles
  def collectRsps(dut: DataCache, cycles: Int): Seq[BigInt] = {
    val buf = scala.collection.mutable.ArrayBuffer[BigInt]()
    for (_ <- 0 until cycles) {
      if (dut.io.coreRsp.valid.peek().litToBoolean)
        buf += dut.io.coreRsp.bits.instrId.peek().litValue
      dut.clock.step()
    }
    buf.toSeq
  }

  "I-29: load miss refill + same-set stranded store colliding in one cycle; the victim writeback-to-L2 data is polluted by LFSR" in {
    test(new DataCache()(param)).withAnnotations(Seq(VerilatorBackendAnnotation, chiseltest.internal.CachingAnnotation, chiseltest.simulator.CachingDebugAnnotation)) { dut =>
      pokeIdle(dut)
      // [2026-09-07 execution fix] dirtyMaskAccess (L1TagAccess.scala:209-213,
      // shouldReset=true) clears 256 sets after reset, during which probeRead
      // is routed through dirtyMaskArb (:228) whose target SRAMTemplate holds
      // r.req.ready=0 (!resetState) => DCache coreReq.ready stays 0 for ~256
      // cycles. The original 2-cycle wait + 50-cycle timeout was too short.
      dut.clock.step(300)

      // 1. load A(tag=1,set=0) miss -> Get -> refill(way0); store A hit -> dirty
      sendCoreReq(dut, opcode = 0, param = 0, instrId = 0, tag = 1, setIdx = 0)
      dut.clock.step()
      val (_, _, srcA, _) = waitMemReq(dut, opcode = 4) // Get
      sendFillRsp(dut, srcA, BigInt("A0000000", 16))
      dut.clock.step(4)
      sendCoreReq(dut, opcode = 1, param = 0, instrId = 1, tag = 1, setIdx = 0,
        data = BigInt("AAAA1111", 16))
      dut.clock.step(4)

      // 2. load B(tag=2,set=0) miss -> Get -> refill(way1); store B hit -> dirty (MRU=way1)
      sendCoreReq(dut, opcode = 0, param = 0, instrId = 2, tag = 2, setIdx = 0)
      dut.clock.step()
      val (_, _, srcB, _) = waitMemReq(dut, opcode = 4)
      sendFillRsp(dut, srcB, BigInt("B0000000", 16))
      dut.clock.step(4)
      sendCoreReq(dut, opcode = 1, param = 0, instrId = 3, tag = 2, setIdx = 0,
        data = BigInt("BBBB2222", 16))
      dut.clock.step(4)

      // 3. load C(tag=3,set=0) miss -> Get (hold memRsp unanswered)
      sendCoreReq(dut, opcode = 0, param = 0, instrId = 4, tag = 3, setIdx = 0)
      dut.clock.step()
      val (_, _, srcC, _) = waitMemReq(dut, opcode = 4)

      // 4. Same cycle: store B'(hit way1) coreReq.fire + C's refill entering
      //    memRsp_Q (memRsp_Q pipe=false, deq fires the next cycle; B' is
      //    backpressured by missRspOut and stranded in st1, and the cycle it
      //    is released its write to (set0,way1) collides with the victim
      //    replace read (set0,way1))
      //    Method: hold B''s valid until the cycle ready is seen, and in the
      //    same cycle also raise memRsp.valid, so that coreReq.fire and the
      //    memRsp enqueue happen in the same cycle.
      dut.io.coreReq.bits.instrId.poke(5.U)
      dut.io.coreReq.bits.opcode.poke(1.U)
      dut.io.coreReq.bits.param.poke(0.U)
      dut.io.coreReq.bits.tag.poke(2.U)
      dut.io.coreReq.bits.setIdx.poke(0.U)
      dut.io.coreReq.bits.perLaneAddr(0).activeMask.poke(true.B)
      dut.io.coreReq.bits.perLaneAddr(0).blockOffset.poke(0.U)
      dut.io.coreReq.bits.perLaneAddr(0).wordOffset1H.poke(15.U)
      dut.io.coreReq.bits.data(0).poke(BigInt("DDDD4444", 16).U)
      dut.io.coreReq.valid.poke(true.B)
      var tw = 0
      while (!dut.io.coreReq.ready.peek().litToBoolean && tw < 50) { dut.clock.step(); tw += 1 }
      assert(dut.io.coreReq.ready.peek().litToBoolean, "I-29 precondition: B' coreReq not ready within 50 cycles")
      dut.io.memRsp.bits.d_opcode.poke(1.U)
      dut.io.memRsp.bits.d_source.poke(srcC.U)
      dut.io.memRsp.bits.d_data.zipWithIndex.foreach { case (w, i) => w.poke((BigInt("C0000000", 16) + i).U) }
      dut.io.memRsp.valid.poke(true.B)
      dut.clock.step() // collision choreography cycle: coreReq(B') fire + memRsp(C) enqueue
      clearCoreReq(dut)
      dut.io.memRsp.valid.poke(false.B)

      // 5. Wait for the victim writeback (PutPart=1, a_addr = B's block base = tag=2,set=0 => 2<<15 = 0x10000)
      val t0 = 60
      var wb: Option[(BigInt, BigInt)] = None // (a_addr, a_data(0))
      var t = 0
      while (wb.isEmpty && t < t0) {
        if (dut.io.memReq.get.valid.peek().litToBoolean &&
            dut.io.memReq.get.bits.a_opcode.peek().litValue == 1) {
          val addr = dut.io.memReq.get.bits.a_addr.get.peek().litValue
          if (addr == BigInt(2) << 15)
            wb = Some((addr, dut.io.memReq.get.bits.a_data(0).peek().litValue))
        }
        dut.clock.step(); t += 1
      }
      assert(wb.isDefined,
        "I-29 precondition: no victim(B) writeback memReq observed — if I-27 is already fixed, the victim is way0(A); " +
          "retarget step 4's stranded store at tag=1 and retest")
      val wbData = wb.get._2
      // Expected: B's old value 0xBBBB2222 or B''s new value 0xDDDD4444
      // (the two reasonable outcomes of a same-cycle read/write);
      // actual (bug): LFSR garbage (a same-address read/write with
      // bypassWrite=false returns a random value)
      assert(wbData == BigInt("BBBB2222", 16) || wbData == BigInt("DDDD4444", 16),
        f"I-29: victim(B)'s writeback-to-L2 data word0=0x$wbData%08x, neither 0xBBBB2222 nor " +
          "0xDDDD4444 — the writeback data was polluted by the LFSR random value of the SRAM collision (silent data corruption)")
    }
  }

  "I-30: two consecutive invalidates (with a load in between); the response instrIds should correspond one-to-one" in {
    test(new DataCache()(param)).withAnnotations(Seq(VerilatorBackendAnnotation, chiseltest.internal.CachingAnnotation, chiseltest.simulator.CachingDebugAnnotation)) { dut =>
      pokeIdle(dut)
      // [2026-09-07 execution fix] dirtyMaskAccess (L1TagAccess.scala:209-213,
      // shouldReset=true) clears 256 sets after reset, during which probeRead
      // is routed through dirtyMaskArb (:228) whose target SRAMTemplate holds
      // r.req.ready=0 (!resetState) => DCache coreReq.ready stays 0 for ~256
      // cycles. The original 2-cycle wait + 50-cycle timeout was too short.
      dut.clock.step(300)
      val rsps = scala.collection.mutable.ArrayBuffer[BigInt]()

      // [2026-09-07 execution calibration] DCache only sends the L2 Flush
      // (a_opcode=5) when the invalidate/flush actually finds DIRTY lines
      // (InvOrFluMemReqValid_st1 = ... && coreReqTagHasDirty_st1,
      // DCache.scala:488). The original sequence invalidated a clean cache,
      // so no flush memReq was ever issued and the test timed out waiting
      // for it. Now: before each invalidate, refill a line and store to it
      // so the flush round-trip (flush memReq -> hintAck) really happens.
      // The dirty-making load/store responses are included in the accounting
      // (a store hit also produces a coreRsp, DCache.scala:729-731).

      // d1: load (tag=7,set=2,instrId=7) -> refill; store (instrId=3) -> dirty
      sendCoreReq(dut, opcode = 0, param = 0, instrId = 7, tag = 7, setIdx = 2)
      dut.clock.step()
      val (_, _, srcD1, _) = waitMemReq(dut, opcode = 4)
      sendFillRsp(dut, srcD1, BigInt("70000000", 16))
      rsps ++= collectRsps(dut, 8)
      sendCoreReq(dut, opcode = 1, param = 0, instrId = 3, tag = 7, setIdx = 2,
        data = BigInt("EEEE5555", 16))
      rsps ++= collectRsps(dut, 6)

      // inv1: instrId=1 (opcode=3, param=0 => isInvalidate) — dirty exists,
      // so the L2 flush round-trip really happens
      sendCoreReq(dut, opcode = 3, param = 0, instrId = 1, tag = 0, setIdx = 0)
      rsps ++= collectRsps(dut, 2)
      waitMemReq(dut, opcode = 5) // Flush request to L2
      sendHintAck(dut) // after memRsp_Q consumes it, the queue head retains d_opcode=2 (:425 has no valid qualifier)
      rsps ++= collectRsps(dut, 8)

      // load L: tag=5,set=1,instrId=5 -> miss -> Get -> refill -> coreRsp(5);
      // then store (instrId=4) -> dirty again for inv2
      sendCoreReq(dut, opcode = 0, param = 0, instrId = 5, tag = 5, setIdx = 1)
      dut.clock.step()
      val (_, _, srcL, _) = waitMemReq(dut, opcode = 4)
      sendFillRsp(dut, srcL, BigInt("50000000", 16))
      rsps ++= collectRsps(dut, 8)
      sendCoreReq(dut, opcode = 1, param = 0, instrId = 4, tag = 5, setIdx = 1,
        data = BigInt("CCCC3333", 16))
      rsps ++= collectRsps(dut, 6)

      // inv2: instrId=2 — waitforL2flush is erroneously cleared for one
      // cycle by the stale queue head (dcT_w2b_early_clear), st1 is released
      // early; when the real hintAck arrives, coreRsp_st2 is already
      // occupied -> the response carries a wrong instrId or is lost
      sendCoreReq(dut, opcode = 3, param = 0, instrId = 2, tag = 0, setIdx = 0)
      rsps ++= collectRsps(dut, 4)
      waitMemReq(dut, opcode = 5) // inv2's Flush
      sendHintAck(dut)
      rsps ++= collectRsps(dut, 10)

      // Expected: every request has exactly one response carrying its own
      // instrId — {7,3,1,5,4,2} once each, 6 total.
      // Actual (example buggy shapes): inv2's response carries 5 (the load's
      // instrId), or a response is lost/duplicated.
      val counts = rsps.groupBy(identity).mapValues(_.size)
      val eachOnce = Seq(7, 3, 1, 5, 4, 2).forall(i => counts.getOrElse(BigInt(i), 0) == 1)
      assert(eachOnce && rsps.size == 6,
        s"I-30: flush/invalidate response metadata disorder — actual response sequence=${rsps.mkString(",")}, " +
          "expected {7,3,1,5,4,2} exactly once each (the Coalscer accounts by instrId; disorder pollutes other instructions' entries)")
    }
  }
}
