// repro/L1CacheBugRepro.scala — ChiselSim reproduction of I-23/I-24/I-27
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/L1Cache/) and run:
//   mill ventus.test.testOnly L1Cache.L1CacheBugRepro
//
// I-23 [confirmed] ICache.scala:262 (coreReq.ready constantly 1, probes see
//   zero backpressure) + :145/:152/:175/:179 (no mutual exclusion between
//   refill and probe) — when a retry after a miss and a refill hit the same
//   set in the same cycle, SRAMTemplate (tag instantiated at
//   L1TagAccess.scala:451 with bypassWrite=false; data instantiated at
//   ICache.scala:84, same) returns LFSR garbage for the same-address
//   read/write. One consequence is a false miss: the tag has been written
//   yet a miss is still judged, allocating a duplicate MSHR entry and
//   refetching from L2. This test observes that deterministic consequence:
//   the same address should produce only 1 memReq.
//   Lean witnesses: ICache.lean icTA_collision_reachable / icTA_duplicate_alloc.
//
// I-24 [confirmed] L1TagAccess.scala:496 (L1TagAccess_ICache):
//   ReplacementUnit_ICache's validbits_of_set is missing a Reverse (compare
//   the DCache variant at :297, which has it) — indexWhere scans from bit0
//   (=way1), so when way0 is occupied and way1 is free it still selects
//   way0: the second block of a set evicts the first, way1 stays invalid
//   forever, and the 2-way set-associative cache degenerates to direct
//   mapped. Lean: ic_way1_never_valid / icTD_victim_thrash.
//
// I-27 [confirmed] L1TagAccess.scala:426/:364 (DCache variant
//   ReplacementUnit): minIdxTree's candidates are assembled in reversed
//   coordinates and never mapped back — a full-set eviction selects the MRU
//   instead of the LRU.
//   Lean: l1ta_replD2_full_evicts_mru / l1ta_replD2_full_ne_lru.
package L1Cache

import L1Cache.ICache._
import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class L1CacheBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  val param = (new MyConfig).toInstance

  // ---------------- I-23 ----------------
  "I-23: miss retry and refill in the same cycle on the same set -> tag reads LFSR garbage -> false miss -> duplicate fetch" in {
    test(new InstructionCache()(param)) { c =>
      c.io.invalidate.poke(false.B)
      c.io.externalFlushPipe.valid.poke(false.B)
      c.io.externalFlushPipe.bits.warpid.poke(0.U)
      c.io.coreRsp.ready.poke(true.B)
      c.io.memReq.ready.poke(true.B)
      c.io.memRsp.valid.poke(false.B)
      c.io.memRsp.bits.d_source.poke(0.U)
      c.io.memRsp.bits.d_addr.poke(0.U)
      c.io.memRsp.bits.d_data.foreach(_.poke(0.U))
      c.io.coreReq.valid.poke(false.B)
      c.clock.step(2)

      // Address A: setIdx = A(14,7) = 1, tag = A(31,15) = 0, blockOffset=0
      // (8B-aligned, satisfying the num_fetch alignment assertion at
      // ICache.scala:185)
      val A = BigInt("00000080", 16)
      val blockA = A >> 7 // blockAddr = 1
      def pokeCoreReq(): Unit = {
        c.io.coreReq.bits.addr.poke(A.U)
        c.io.coreReq.bits.mask.poke(3.U) // num_fetch=2
        c.io.coreReq.bits.warpid.poke(0.U)
        if (SPIKE_OUTPUT) {
          c.io.coreReq.bits.spike_info.get.pc.poke(0.U)
          c.io.coreReq.bits.spike_info.get.vaddr.poke(0.U)
        }
        c.io.coreReq.valid.poke(true.B)
      }

      // T0: first probe — miss, MSHR allocates entry0, producing a memReq (fetch from L2)
      pokeCoreReq()
      c.clock.step()
      c.io.coreReq.valid.poke(false.B)
      var memReqCount = 0
      var t = 0
      // wait for the first memReq (miss -> miss2mem)
      while (memReqCount == 0 && t < 30) {
        if (c.io.memReq.valid.peek().litToBoolean) {
          memReqCount += 1
          val aaddr = c.io.memReq.bits.a_addr.get.peek().litValue
          assert(aaddr == (A & ~BigInt(0x7F)),
            f"precondition: memReq address 0x$aaddr%x should be the base of A's block, 0x${A & ~BigInt(0x7F)}%x")
        }
        c.clock.step(); t += 1
      }
      assert(memReqCount == 1, "precondition: the first miss should produce one memReq")

      // [2026-09-06 execution calibration] First-run diagnostics showed:
      // poking memRsp and the retry coreReq in the SAME cycle makes the
      // retry's tag read happen one cycle BEFORE the refill's tag write
      // (memRsp_Q is consumed one cycle after the poke). The retry then sees
      // a legitimate miss, the MSHR's ReqConflictWithRsp rule (ICacheMSHR
      // missReq.ready := ... && !ReqConflictWithRsp) rejects the missReq, and
      // the core receives coreRsp status=3 (retry later) — the bug is masked.
      // To make the retry's tag READ coincide with the refill's tag WRITE,
      // fire the retry ONE CYCLE AFTER the memRsp poke: the read-during-write
      // on the tag SRAM (L1TagAccess.scala:451, bypassWrite=false; and the
      // ICache drives w.req.bits.waymask=0.U so the internal bypass_mask is 0
      // and the read returns stale/garbage data) is judged a MISS even though
      // the refill has completed and the MSHR entry was freed — a duplicate
      // MSHR allocation and a second memReq for the same block follow.
      // T: L2 refill enters memRsp_Q
      c.io.memRsp.valid.poke(true.B)
      c.io.memRsp.bits.d_source.poke(0.U) // entry 0
      c.io.memRsp.bits.d_addr.poke(A.U)
      c.io.memRsp.bits.d_data.zipWithIndex.foreach { case (w, i) => w.poke((0x1000 + i).U) }
      c.clock.step()
      c.io.memRsp.valid.poke(false.B)
      // T+1: memRsp_Q deq fires (tag/data write, MSHR entry0 freed); the
      // retry's coreReq fires the same cycle — its tag read collides with
      // the refill's tag write on the same set.
      pokeCoreReq()
      c.clock.step() // collision cycle
      c.io.coreReq.valid.poke(false.B)

      // Observe the following 20 cycles (memReq/coreRsp events are printed as
      // the evidence trace):
      //  - correct behavior: the refill has written the tag, the retry
      //    should HIT and produce no further memReq;
      //  - bug: on the collision cycle the tag reads stale/garbage data ->
      //    false miss -> duplicate MSHR entry allocation -> memReq issued a
      //    second time for the same block.
      var falseHit = false
      for (i <- 0 until 20) {
        val mrq = c.io.memReq.valid.peek().litToBoolean
        val crsp = c.io.coreRsp.valid.peek().litToBoolean
        if (mrq) memReqCount += 1
        if (mrq || crsp) {
          val status = if (crsp) c.io.coreRsp.bits.status.peek().litValue else BigInt(-1)
          val addr = if (crsp) c.io.coreRsp.bits.addr.peek().litValue else BigInt(-1)
          val data = if (crsp) c.io.coreRsp.bits.data.peek().litValue else BigInt(-1)
          println(s"I-23 diag cycle+$i: memReq=$mrq coreRsp=$crsp status=$status addr=0x${addr.toString(16)} data=0x${data.toString(16)}")
        }
        if (c.io.coreRsp.valid.peek().litToBoolean &&
            c.io.coreRsp.bits.status.peek().litValue == 0 &&
            c.io.coreRsp.bits.addr.peek().litValue == A &&
            c.io.coreRsp.bits.data.peek().litValue != ((BigInt("1001", 16) << 32) | BigInt("1000", 16)))
          falseHit = true
        c.clock.step()
      }
      assert(memReqCount == 1,
        s"I-23: the same block was fetched $memReqCount times (expected 1) — the probe on the refill cycle read " +
          "LFSR garbage causing a false miss and a duplicate MSHR entry allocation")
      assert(!falseHit, "I-23: false hit — a HIT was returned for the just-refilled address but the instruction word is LFSR garbage")
    }
  }

  // ---------------- I-24 ----------------
  "I-24: L1TagAccess_ICache's second allocation to the same set still selects way0 (way1 stays empty forever, degenerating to direct mapped)" in {
    test(new L1TagAccess_ICache(set = 256, way = 2, tagBits = 17, AsidBits = 9)) { dut =>
      dut.io.invalidate.poke(false.B)
      dut.io.coreReqReady.poke(false.B)
      dut.io.tagFromCore_st1.poke(0.U)
      dut.io.r.req.valid.poke(false.B)
      dut.io.r.req.bits.setIdx.poke(0.U)
      dut.io.w.req.valid.poke(false.B)
      dut.io.w.req.bits.setIdx.poke(0.U)
      dut.io.w.req.bits.data.foreach(_.poke(0.U))
      dut.io.w.req.bits.waymask.foreach(_.poke(0.U))
      dut.clock.step(2)

      val tagA = BigInt("12345", 16)
      val tagB = BigInt("0ABCD", 16)
      // T0: first block (tagA) allocated to set5 — empty set, should select way0 (waymask=0b01)
      dut.io.w.req.bits.setIdx.poke(5.U)
      dut.io.w.req.bits.data.foreach(_.poke(tagA.U))
      dut.io.w.req.valid.poke(true.B)
      val wm1 = dut.io.waymaskReplacement.peek().litValue
      assert(wm1 == 1, f"precondition: the first allocation into an empty set should select way0(0b01), actual waymask=$wm1%x")
      dut.clock.step()
      // T1: second block (tagB) allocated to set5 — way0 occupied, should select way1 (waymask=0b10)
      dut.io.w.req.bits.data.foreach(_.poke(tagB.U))
      val wm2 = dut.io.waymaskReplacement.peek().litValue
      // expected 0b10; actual (bug, L1TagAccess.scala:496 missing Reverse) still 0b01 — tagA is evicted
      assert(wm2 == 2,
        f"I-24: second allocation to the same set waymask=$wm2%x, expected 0b10(way1); way1 stays empty forever => degenerated to direct mapped")
      dut.clock.step()
      dut.io.w.req.valid.poke(false.B)

      // T2/T3: probe tagA back — with a correct design tagA is still in way0
      // and should HIT; with the bug it was overwritten by tagB -> MISS
      dut.io.r.req.bits.setIdx.poke(5.U)
      dut.io.r.req.valid.poke(true.B)
      dut.io.coreReqReady.poke(true.B) // make way_valid(5) visible to tagChecker at T3
      dut.clock.step()
      dut.io.r.req.valid.poke(false.B)
      dut.io.coreReqReady.poke(false.B)
      dut.io.tagFromCore_st1.poke(tagA.U) // st1: tag compare
      dut.clock.step()
      val hitA = dut.io.hit_st1.peek().litToBoolean
      assert(hitA, "I-24: both blocks of the same set should remain resident (2-way set associative); tagA was evicted by the second allocation => MISS")
    }
  }

  // ---------------- I-27 ----------------
  "I-27: DCache ReplacementUnit evicts the MRU instead of the LRU on a full set" in {
    // timeOfSet_st1(i) corresponds to way i (DCache connection:
    // L1TagAccess.scala:298, SRAM resp data(i)=way i); accessCount increases
    // monotonically => smaller time value = least recently used (LRU).
    // minIdxTree's reversed coordinates are never mapped back => the one
    // selected has the largest time value (MRU).
    test(new ReplacementUnit(timeLength = 10, way = 2)) { dut =>
      // case 1: way0 least recently used (time=10), way1 most recently used (time=500). Full set.
      dut.io.validOfSet.poke(3.U) // both ways valid
      dut.io.timeOfSet_st1(0).poke(10.U)
      dut.io.timeOfSet_st1(1).poke(500.U)
      val wm1 = dut.io.waymask_st1.peek().litValue
      // expected to evict way0 (0b01); actual (bug) evicts way1 (0b10, MRU)
      assert(wm1 == 1, f"I-27: LRU=way0, victim waymask=$wm1%x, expected 0b01 — evicted the MRU")

      // case 2: way1 least recently used (time=10), way0 most recently used (time=500)
      dut.io.timeOfSet_st1(0).poke(500.U)
      dut.io.timeOfSet_st1(1).poke(10.U)
      val wm2 = dut.io.waymask_st1.peek().litValue
      // expected to evict way1 (0b10); actual (bug) evicts way0 (0b01, MRU)
      assert(wm2 == 2, f"I-27: LRU=way1, victim waymask=$wm2%x, expected 0b10 — evicted the MRU")
    }
  }
}
