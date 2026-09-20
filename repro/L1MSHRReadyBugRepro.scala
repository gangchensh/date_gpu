// repro/L1MSHRReadyBugRepro.scala — ChiselSim reproduction of I-26
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/L1Cache/) and run:
//   mill ventus.test.testOnly L1Cache.L1MSHRReadyBugRepro
//
// I-26 [confirmed (mechanism)] the missReq.ready at L1MSHR.scala:295 is
// inconsistent with the st0 backpressure:
//   the st1_w recomputation condition at :274 only covers st1_r∈{0,1},
//   missing the case SECONDARY_AVAIL(2) with the secondary-matched entry's
//   subentries full — then missReq.ready=1 (fire holds) while in the same
//   cycle st0=3 (SECONDARY_FULL backpressure). Consequence: this secondary
//   miss is not recorded by any subentry (the elsewhen at :354 only latches
//   se=1; for a full entry indexWhere defaults seIdx=0), so the request is
//   lost and never answered; meanwhile the targetInfo write at :299-301 has
//   no state gating and overwrites the response routing information of the
//   existing subentry0.
//   Lean witnesses (reachable from the initial state in three cycles):
//   L1MSHR.lean l1mT7_ready_inconsistent / l1mT7_reqLost / l1mT7_tiCorrupt.
//
//   Trace (cycle-by-cycle correspondent to the Lean witness,
//   blockAddr=0x10, NMshrSubEntry=2):
//     C1: probe+missReq (instrId=5, ti=0xBEEF) — primary miss, allocate entry0 sub0
//     C2: probe+missReq (instrId=6, ti=0xCAFE) — secondary merge, entry0 sub1 (subentries full afterwards)
//     C3: probe+missReq (instrId=7, ti=0xDEAD) — st0=3 (backpressure) but ready=1 (fire):
//         request lost + targetInfo(0,0) overwritten by 0xDEAD (should be 0xBEEF)
//   Observation 1 (in C3): mshrStatus_st0==3 while missReq.ready==1 —
//     ready/st0 inconsistent.
//   Observation 2 (afterwards): feed missRspIn for entry0; the first
//     missRspOut's targetInfo should be 0xBEEF, hardware gives 0xDEAD
//     (polluted by C3); and the instrId=7 request is never answered.
package L1Cache

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec

class L1MSHRReadyBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  // Same parameters as DCache (instantiation at DCache.scala:178):
  // bABits=TagBits+SetIdxBits=17+8=25,
  // tIWidth=tIBits=WIdBits+NLanes*(BlockOffsetBits+1+BytesOfWord)=3+32*10=323,
  // WIdBits=3, NMshrEntry=4, NMshrSubEntry=2. AsidBits is unused when
  // MMU_ENABLED=false.
  val BA = BigInt("10", 16) // blockAddr

  "I-26: secondary miss meeting full subentries gets ready=1/st0=3 inconsistency -> request lost + targetInfo pollution" in {
    test(new MSHR(bABits = 25, tIWidth = 323, WIdBits = 3,
      NMshrEntry = 4, NMshrSubEntry = 2, AsidBits = 9)) { dut =>
      // idle defaults
      dut.io.probe.valid.poke(false.B)
      dut.io.probe.bits.blockAddr.poke(0.U)
      dut.io.missReq.valid.poke(false.B)
      dut.io.missReq.bits.blockAddr.poke(0.U)
      dut.io.missReq.bits.instrId.poke(0.U)
      dut.io.missReq.bits.targetInfo.poke(0.U)
      dut.io.missRspIn.valid.poke(false.B)
      dut.io.missRspIn.bits.instrId.poke(0.U)
      dut.io.missRspOut.ready.poke(true.B)
      dut.io.stage1_ready.poke(true.B)
      dut.io.stage2_ready.poke(true.B)
      dut.clock.step()

      def cycle(probeV: Boolean, reqV: Boolean, ii: Int, ti: BigInt): Unit = {
        dut.io.probe.valid.poke(probeV.B)
        dut.io.probe.bits.blockAddr.poke(BA.U)
        dut.io.missReq.valid.poke(reqV.B)
        dut.io.missReq.bits.blockAddr.poke(BA.U)
        dut.io.missReq.bits.instrId.poke(ii.U)
        dut.io.missReq.bits.targetInfo.poke(ti.U)
      }

      // C1: primary miss allocates entry0 sub0
      cycle(probeV = true, reqV = true, ii = 5, ti = BigInt("BEEF", 16))
      assert(dut.io.missReq.ready.peek().litToBoolean, "C1 precondition: PRIMARY_AVAIL should be ready")
      dut.clock.step()
      // C2: secondary merge -> entry0 sub1 (subentries full afterwards)
      cycle(probeV = true, reqV = true, ii = 6, ti = BigInt("CAFE", 16))
      assert(dut.io.missReq.ready.peek().litToBoolean, "C2 precondition: SECONDARY_AVAIL should be ready")
      dut.clock.step()
      // C3: third request to the same block — subentries full. st0 reports
      //     SECONDARY_FULL(3) (backpressure semantics), but missReq.ready is
      //     still 1 (the :274 recomputation condition misses st1_r=2).
      //     Do not assert on the spot; record the scene first and judge
      //     together after the response phase (obtaining both pieces of
      //     evidence).
      cycle(probeV = true, reqV = true, ii = 7, ti = BigInt("DEAD", 16))
      val st0AtC3 = dut.io.mshrStatus_st0.peek().litValue
      val readyAtC3 = dut.io.missReq.ready.peek().litToBoolean
      dut.clock.step()
      cycle(probeV = false, reqV = false, ii = 0, ti = 0)

      // [2026-09-06 execution adaptation] Assert the C3 evidence BEFORE the
      // response phase: on the first run the response phase triggered the
      // DUT's own assertion at L1MSHR.scala:196 (PopCount(entryMatchProbe)<=1
      // — duplicate entries for the same block), preempting the designed
      // observations. The response phase is now wrapped in Try so that the
      // hardware assertion is recorded as evidence instead of aborting early.
      assert(st0AtC3 == 3, s"C3 precondition: st0 should be SECONDARY_FULL(3), actual $st0AtC3")

      // Afterwards check the targetInfo pollution: feed missRspIn for
      // entry0; the first missRspOut should carry subentry0's
      // targetInfo=0xBEEF (instrId=5's routing information)
      var ti0: Option[BigInt] = None
      var rspNote = "response phase completed without hardware assertion"
      try {
        dut.io.missRspIn.valid.poke(true.B)
        dut.io.missRspIn.bits.instrId.poke(0.U) // entry0
        var t = 0
        while (ti0.isEmpty && t < 10) {
          if (dut.io.missRspOut.valid.peek().litToBoolean)
            ti0 = Some(dut.io.missRspOut.bits.targetInfo.peek().litValue)
          dut.clock.step(); t += 1
        }
        dut.io.missRspIn.valid.poke(false.B)
      } catch {
        case e: Throwable => rspNote = s"HARDWARE ASSERTION/EXCEPTION in response phase: $e"
      }
      // Evidence 1 (in C3): expected (consistent backpressure) ready=0;
      //   actual (bug) ready=1 — fire holds but the request is recorded by
      //   no subentry, so it is lost (never answered).
      // Evidence 2 (afterwards): subentry0's targetInfo expected 0xBEEF;
      //   actual (bug) 0xDEAD — C3's ungated write (:299-301) overwrote the
      //   response routing information. If the response phase tripped the
      //   DUT's own assertion (L1MSHR.scala:196, duplicate entries for the
      //   same block), that is recorded in rspNote as further evidence.
      assert(!readyAtC3 && ti0.contains(BigInt("BEEF", 16)),
        s"I-26: C3 ready=$readyAtC3 (expected false, consistent with st0=SECONDARY_FULL); " +
          s"subentry0 targetInfo=${ti0.map(t => f"0x$t%x")} (expected Some(0xBEEF)); rspNote: $rspNote. " +
          "ready=1 => the secondary miss is silently dropped after firing; targetInfo=0xDEAD => routing information overwritten.")
    }
  }
}
