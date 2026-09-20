// repro/L1TagAccessDirtyMaskRepro.scala — ChiselSim reproduction of I-28
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/L1Cache/) and run:
//   mill ventus.test.testOnly L1Cache.L1TagAccessDirtyMaskRepro
//
// I-28 [confirmed] L1TagAccess.scala:241-245 dirtyMaskPerCL_init: multiple
//   lanes with the same blockOffset overwrite each other, losing the earlier
//   lane's bytes: two active lanes at the same blockOffset overwrite each
//   other and the first-written lane's bytes are lost
//   -> the dirty bitmap is smaller than it should be -> on replacement/flush
//   writeback to L2, dirty bytes are skipped (data-corruption direction).
//   Reachability (per the report): LSU perLaneAddr comes straight from the
//   address with no same-word merging; an SB vector store of adjacent
//   addresses produces two active lanes with "same blockOffset, different
//   bytes"; the remap merge (DCache.scala:111-133) only serves the data
//   path — the dirtyMask path uses the un-remapped perLaneAddr
//   (DCache.scala:267).
//   Lean witness: L1TagAccess.lean l1taT_dmBuild_overwrite_real.
//
//   Reproduction level: L1TagAccess (the DCache variant, readOnly=false,
//   instantiated at DCache.scala:184).
//   Construction: pre-allocate tagA at set0 way0; one write-hit probe with
//   lane0/lane1 in perLaneAddr sharing blockOffset=0, wordOffset1H
//   0b0001/0b0010 (adjacent bytes);
//   expected dirtyMask word0 = 0b0011 (both lanes' bytes merged), actual =
//   0b0010 (lane1 overwrote lane0).
//   Read-back path: dirtyMaskAccess re-reads set0 via dirtyMaskArb; observe
//   io.dirtyMask_st1.
//   Note: dirtyMaskAccess has shouldReset=true; after reset you must wait
//   256 cycles for the SRAM clear sequence.
package L1Cache

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class L1TagAccessDirtyMaskRepro extends AnyFreeSpec with ChiselScalatestTester {

  val param = (new MyConfig).toInstance

  // One-cycle write-hit probe transaction: T0 probeRead.fire (tagready_st1=0
  // keeps probeReadBuf), T1 st1 presents tag/isWrite/perLaneAddr
  // (tagready_st1=1 lets it through)
  def probeWriteHit(dut: L1TagAccess, setIdx: Int, tag: BigInt,
                    lanes: Seq[(Int, Int, Int)]): Unit = {
    // lanes: (laneIdx, blockOffset, wordOffset1H)
    dut.io.probeRead.bits.setIdx.poke(setIdx.U)
    dut.io.probeRead.valid.poke(true.B)
    dut.io.tagready_st1.poke(false.B)
    dut.clock.step()
    dut.io.probeRead.valid.poke(false.B)
    // st1
    dut.io.tagFromCore_st1.poke(tag.U)
    dut.io.probeIsWrite_st1.get.poke(true.B)
    dut.io.perLaneAddr_st1.foreach { l =>
      l.activeMask.poke(false.B); l.blockOffset.poke(0.U); l.wordOffset1H.poke(0.U)
    }
    lanes.foreach { case (i, bo, wo) =>
      dut.io.perLaneAddr_st1(i).activeMask.poke(true.B)
      dut.io.perLaneAddr_st1(i).blockOffset.poke(bo.U)
      dut.io.perLaneAddr_st1(i).wordOffset1H.poke(wo.U)
    }
    dut.io.tagready_st1.poke(true.B)
    dut.clock.step()
    dut.io.probeIsWrite_st1.get.poke(false.B)
    dut.io.perLaneAddr_st1.foreach(_.activeMask.poke(false.B))
  }

  // Read probe (probeIsWrite_st1=0), then re-read dirtyMask via dirtyMaskArb
  // and observe dirtyMask_st1
  def probeReadForDirtyMask(dut: L1TagAccess, setIdx: Int, tag: BigInt): BigInt = {
    dut.io.probeRead.bits.setIdx.poke(setIdx.U)
    dut.io.probeRead.valid.poke(true.B)
    dut.io.tagready_st1.poke(false.B)
    dut.clock.step()
    dut.io.probeRead.valid.poke(false.B)
    dut.io.tagFromCore_st1.poke(tag.U)
    dut.io.tagready_st1.poke(true.B)
    dut.clock.step() // this cycle the dirtyMask SRAM resp is ready and dirtyMask_st1 is combinationally output
    dut.io.dirtyMask_st1.peek().litValue
  }

  "I-28: two lanes writing adjacent bytes at the same blockOffset hit; dirtyMask loses the earlier lane's bytes" in {
    test(new L1TagAccess(set = 256, way = 2, tagBits = 17, AsidBits = 9,
      readOnly = false)(param)) { dut =>
      // default inputs
      dut.io.probeRead.valid.poke(false.B)
      dut.io.probeRead.bits.setIdx.poke(0.U)
      dut.io.tagFromCore_st1.poke(0.U)
      dut.io.probeIsWrite_st1.get.poke(false.B)
      dut.io.allocateWrite.valid.poke(false.B)
      dut.io.allocateWrite.bits.setIdx.poke(0.U)
      dut.io.allocateWriteData_st1.poke(0.U)
      dut.io.allocateWriteTagSRAMWValid_st1.poke(false.B)
      dut.io.flushChoosen.get.valid.poke(false.B)
      dut.io.flushChoosen.get.bits.poke(0.U)
      dut.io.invalidateAll.poke(false.B)
      dut.io.tagready_st1.poke(true.B)
      dut.io.perLaneAddr_st1.foreach { l =>
        l.activeMask.poke(false.B); l.blockOffset.poke(0.U); l.wordOffset1H.poke(0.U)
      }
      // The clear sequence of dirtyMaskAccess (shouldReset=true):
      // Counter(set=256) — wait 260 cycles
      dut.clock.step(260)

      val tagA = BigInt("12345", 16)
      // T0/T1: allocate set0 way0 = tagA (allocateWrite.fire -> tag SRAM written next cycle)
      dut.io.allocateWrite.bits.setIdx.poke(0.U)
      dut.io.allocateWrite.valid.poke(true.B)
      dut.clock.step()
      dut.io.allocateWrite.valid.poke(false.B)
      dut.io.allocateWriteData_st1.poke(tagA.U)
      dut.io.allocateWriteTagSRAMWValid_st1.poke(true.B)
      dut.clock.step()
      dut.io.allocateWriteTagSRAMWValid_st1.poke(false.B)

      // Control group: lane0->blockOffset=1(0b0001), lane1->blockOffset=2(0b0010), different words
      // expected/actual both word1=0001|word2=0010 => (2<<8)|(1<<4) = 0x210
      probeWriteHit(dut, setIdx = 0, tag = tagA, lanes = Seq((0, 1, 0x1), (1, 2, 0x2)))
      val dmCtrl = probeReadForDirtyMask(dut, 0, tagA)
      assert((dmCtrl & 0xFFF) == 0x210,
        f"control group failed: two lanes at different blockOffsets should merge normally, dirtyMask low 12 bits=${dmCtrl & 0xFFF}%x, expected 0x210")

      // Test group: lane0->blockOffset=0(0b0001), lane1->blockOffset=0(0b0010), same word adjacent bytes
      // expected word0 = 0b0001|0b0010 = 0b0011; actual (bug, :243 overwrites lane by lane) = 0b0010
      // read-back value = control group's existing 0x210 | this round's word0 => expected 0x213, actual 0x212
      probeWriteHit(dut, setIdx = 0, tag = tagA, lanes = Seq((0, 0, 0x1), (1, 0, 0x2)))
      val dmTest = probeReadForDirtyMask(dut, 0, tagA)
      assert((dmTest & 0xFFF) == 0x213,
        f"I-28: the dirtyMask of two lanes at the same blockOffset with adjacent bytes should merge (low 12 bits expected 0x213), " +
          f"actual ${dmTest & 0xFFF}%x — lane0's byte 0b0001 was overwritten and lost by lane1, " +
          "and the writeback to L2 will skip that byte (data corruption)")
    }
  }
}
