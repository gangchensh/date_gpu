// repro/ShareMemAddrAliasRepro.scala — ChiselSim reproduction of I-21
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.ShareMemAddrAliasRepro
//
// I-21 [confirmed] the ShareMem request setIdx is only 8 bits; the upper
// 96KB of the LDS aliases the low 32KB byte by byte.
//   LSU.scala:171,216 (inside AddrCalculate): setIdx takes addr(14,7)
//   (dcache_SetIdxBits=8 bits); while ShareMemParameters.scala:22
//   NSets=sharedmem_depth=1024 (needs 10-bit setIdx=addr(16,7)).
//   The connection point GPGPU_top.scala:488 zero-extends the 8 bits
//   directly into 10 bits — addr(16,15) is dropped.
//   Lean witness: ShareMem.lean smI21_witness (writing 0x70008040 overwrote
//   the content of 0x70000040).
//
//   Reproduction level: AddrCalculate (the module at LSU.scala:113,
//   instantiated at LSUexe:554).
//   The observation point is closest to the bug's origin: the ShareMem
//   itself with 1024 rows is not wrong; the error is that the setIdx sent by
//   the LSU is truncated. For address 0x70008040 (LDS_BASE+32KB+0x40):
//     correct 10-bit setIdx = addr(16,7) = 0x100 = 256
//     hardware 8-bit setIdx = addr(14,7) = 0x00 — exactly the same as
//     0x70000040 (including blockOffset), i.e. a high-region write silently
//     corrupts the low region.
//   Note: to cover the entire 128KB LDS space, pass sharedmemory_maxsize =
//   131072 (128KB, consistent with the CTA side's
//   NUM_LDS_MAX=sharemem_size; the default parameter 4096 would classify
//   the high region as non-shared).
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class ShareMemAddrAliasRepro extends AnyFreeSpec with ChiselScalatestTester {

  val LdsMax = 0x20000 // 128KB = sharemem_size (sharedmem_depth 1024 * 32 words * 4B)

  def pokeIdle(dut: AddrCalculate): Unit = {
    dut.io.from_fifo.valid.poke(false.B)
    dut.io.flush_dcache.valid.poke(false.B)
    dut.io.flush_dcache.bits.poke(false.B)
    dut.io.to_mshr.ready.poke(true.B)
    dut.io.to_shared.ready.poke(false.B) // do not consume yet; stop in s_shared to observe bits
    dut.io.to_dcache.ready.poke(true.B)
    dut.io.idx_entry.poke(0.U)
    dut.io.csr_pds.poke(0.U)
    dut.io.csr_numw.poke(0.U)
    dut.io.csr_tid.poke(0.U)
  }

  // Issue a single-lane scalar store to addr, stop in s_shared and return
  // (setIdx, blockOffset, wordOffset1H)
  def issueSharedStore(dut: AddrCalculate, addr: BigInt): (BigInt, BigInt, BigInt) = {
    val v = dut.io.from_fifo.bits
    // scalar (isvec=0) store: addr = in1(0)+in2(0) (LSU.scala:159)
    v.in1.foreach(_.poke(0.U)); v.in2.foreach(_.poke(0.U)); v.in3.foreach(_.poke(0.U))
    v.in1(0).poke(addr.U)
    v.mask.foreach(_.poke(false.B)); v.mask(0).poke(true.B)
    val c = v.ctrl
    c.inst.poke(0.U); c.wid.poke(0.U); c.fp.poke(false.B); c.branch.poke(0.U)
    c.simt_stack.poke(false.B); c.simt_stack_op.poke(false.B); c.barrier.poke(false.B)
    c.csr.poke(0.U); c.reverse.poke(false.B); c.sel_alu2.poke(0.U); c.sel_alu1.poke(0.U)
    c.isvec.poke(false.B); c.sel_alu3.poke(0.U); c.mask.poke(false.B); c.sel_imm.poke(0.U)
    c.mem_whb.poke(3.U) // MEM_W
    c.mem_unsigned.poke(false.B); c.alu_fn.poke(0.U)
    c.force_rm_rtz.poke(false.B); c.is_vls12.poke(false.B); c.mem.poke(true.B)
    c.mul.poke(false.B); c.tc.poke(false.B); c.disable_mask.poke(false.B)
    c.custom_signal_0.poke(false.B)
    c.mem_cmd.poke(2.U) // M_XWR: mem_cmd(1)=1 means write
    c.mop.poke(0.U)
    c.reg_idx1.poke(0.U); c.reg_idx2.poke(0.U); c.reg_idx3.poke(0.U); c.reg_idxw.poke(0.U)
    c.wvd.poke(false.B); c.fence.poke(false.B); c.sfu.poke(false.B)
    c.readmask.poke(false.B); c.writemask.poke(false.B); c.wxd.poke(false.B)
    c.pc.poke(0.U); c.imm_ext.poke(0.U)
    c.atomic.poke(false.B); c.aq.poke(false.B); c.rl.poke(false.B)
    if (SPIKE_OUTPUT) {
      c.spike_info.get.sm_id.poke(0.U); c.spike_info.get.pc.poke(0.U)
      c.spike_info.get.inst.poke(0.U)
    }
    dut.io.from_fifo.valid.poke(true.B)
    assert(dut.io.from_fifo.ready.peek().litToBoolean, "precondition: s_idle should accept the request")
    dut.clock.step() // -> s_save
    dut.io.from_fifo.valid.poke(false.B)
    // s_save: to_mshr.fire (ready=1) -> s_shared
    var t = 0
    while (!dut.io.to_shared.valid.peek().litToBoolean && t < 10) { dut.clock.step(); t += 1 }
    assert(dut.io.to_shared.valid.peek().litToBoolean,
      "precondition: an all-shared write request should enter s_shared (to_shared.valid=1)")
    (dut.io.to_shared.bits.setIdx.peek().litValue,
      dut.io.to_shared.bits.perLaneAddr(0).blockOffset.peek().litValue,
      dut.io.to_shared.bits.perLaneAddr(0).wordOffset1H.peek().litValue)
  }

  "I-21: the setIdx of the LDS high-region address 0x70008040 is truncated to 0 (should be 256), aliasing the low region 0x70000040 byte by byte" in {
    test(new AddrCalculate(LdsMax.U(32.W))) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // high region: LDS_BASE + 32KB + 0x40 (within the 128KB LDS space;
      // should land on ShareMem row 256)
      val (setHi, boHi, woHi) = issueSharedStore(dut, BigInt("70008040", 16))
      // consume this one and return to s_idle
      dut.io.to_shared.ready.poke(true.B)
      dut.clock.step()
      dut.io.to_shared.ready.poke(false.B)
      // low region: LDS_BASE + 0x40 (row 0)
      val (setLo, boLo, woLo) = issueSharedStore(dut, BigInt("70000040", 16))

      // Direct evidence 1: the high-region request's setIdx should be 256
      // (addr(16,7)); hardware gives 0
      assert(setHi == 256,
        s"I-21: to_shared.setIdx of addr=0x70008040 is $setHi, expected 256 — addr(16,15) was dropped")
      // Direct evidence 2: two addresses 32KB apart produce exactly the same
      // (setIdx, blockOffset, wordOffset1H) — the ShareMem side cannot
      // distinguish them, so a high-region write necessarily overwrites the
      // low region (the head of the chain in ShareMem.lean smI21_witness)
      assert(!(setHi == setLo && boHi == boLo && woHi == woLo),
        s"I-21: 0x70008040 and 0x70000040 alias to the same ShareMem row: " +
          s"setIdx=$setHi blockOffset=$boHi wordOffset1H=$woHi (expected different setIdx)")
    }
  }
}
