// repro/OperandCollectorBugRepro.scala — ChiselSim reproduction of
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// I-11/I-12 (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.OperandCollectorBugRepro
//
// I-11 [confirmed] the scalar bank address width is computed as for VGPR
//   (depth_regBank=8 bits); with sgpr_base>=1024 registers alias across
//   warps. regfile.scala:10-12 (ports 8 bits) vs :21 (the scalar mem is 512
//   deep, needing 9 bits); address computation at
//   operandCollector.scala:598-606 (8-bit UInt addition wraps naturally).
//   Lean witnesses: OperandCollector.lean ocI11_witness / ocI11_full_alias.
//   Construction: warp3 sgpr_base=768 (>>2 =192), warp7 sgpr_base=1792
//   (>>2 =448, truncated to 192 in 8 bits). The same scalar register of both
//   warps (reg_idxw=4 -> +1) lands on bank3 row 193.
//   Expected: warp7's write does not affect warp3; actual: warp3 reads back
//   the value written by warp7.
//
// I-12 [confirmed] masked vector instructions (vm=0 and all vmerge)
//   deadlock in collectorUnit.
//   operandCollector.scala:214 the mask read request has rsType=0 and is
//   filtered out by both arbiters at :362-365 (they only pass rsType==1/2),
//   so the crossbar never returns regOrder=3 -> the CU is stuck in s_add
//   forever.
//   Lean closure: CollectorUnit.lean cuWmask_deadlock +
//   OperandCollector.lean ocI12_deadlock_system.
//   Construction: feed controlV a mask=1 vmerge-shaped instruction.
//   Expected: an issue output after a few cycles; actual: never issues (and
//   subsequent instructions on the same CU are blocked).
//   Control group: a same-shape mask=0 vadd issues normally (verifies the
//   testbench itself works).
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class OperandCollectorBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  // poke all CtrlSigs fields (with spike_info when SPIKE_OUTPUT=true)
  def pokeCtrlSigs(c: CtrlSigs, wid: Int = 0, isvec: Boolean = false, mask: Boolean = false,
                   selAlu1: Int = 0, selAlu2: Int = 0, selAlu3: Int = 0,
                   regIdx1: Int = 0, regIdx2: Int = 0, aluFn: Int = 0,
                   branch: Int = 0, inst: BigInt = 0): Unit = {
    c.inst.poke(inst.U); c.wid.poke(wid.U); c.fp.poke(false.B); c.branch.poke(branch.U)
    c.simt_stack.poke(false.B); c.simt_stack_op.poke(false.B); c.barrier.poke(false.B)
    c.csr.poke(0.U); c.reverse.poke(false.B)
    c.sel_alu2.poke(selAlu2.U); c.sel_alu1.poke(selAlu1.U)
    c.isvec.poke(isvec.B); c.sel_alu3.poke(selAlu3.U); c.mask.poke(mask.B); c.sel_imm.poke(0.U)
    c.mem_whb.poke(0.U); c.mem_unsigned.poke(false.B); c.alu_fn.poke(aluFn.U)
    c.force_rm_rtz.poke(false.B); c.is_vls12.poke(false.B); c.mem.poke(false.B)
    c.mul.poke(false.B); c.tc.poke(false.B); c.disable_mask.poke(false.B)
    c.custom_signal_0.poke(false.B); c.mem_cmd.poke(0.U); c.mop.poke(0.U)
    c.reg_idx1.poke(regIdx1.U); c.reg_idx2.poke(regIdx2.U); c.reg_idx3.poke(0.U)
    c.reg_idxw.poke(0.U)
    c.wvd.poke(false.B); c.fence.poke(false.B); c.sfu.poke(false.B)
    c.readmask.poke(false.B); c.writemask.poke(false.B); c.wxd.poke(false.B)
    c.pc.poke(0.U); c.imm_ext.poke(0.U)
    c.atomic.poke(false.B); c.aq.poke(false.B); c.rl.poke(false.B)
    if (SPIKE_OUTPUT) {
      c.spike_info.get.sm_id.poke(0.U); c.spike_info.get.pc.poke(0.U)
      c.spike_info.get.inst.poke(0.U)
    }
  }

  def pokeIdle(dut: operandCollector): Unit = {
    dut.io.controlX.valid.poke(false.B)
    dut.io.controlV.valid.poke(false.B)
    pokeCtrlSigs(dut.io.controlX.bits)
    pokeCtrlSigs(dut.io.controlV.bits)
    dut.io.out(0).ready.poke(true.B) // out_v
    dut.io.out(1).ready.poke(true.B) // out_x
    dut.io.writeScalarCtrl.valid.poke(false.B)
    dut.io.writeScalarCtrl.bits.wb_wxd_rd.poke(0.U)
    dut.io.writeScalarCtrl.bits.wxd.poke(false.B)
    dut.io.writeScalarCtrl.bits.reg_idxw.poke(0.U)
    dut.io.writeScalarCtrl.bits.warp_id.poke(0.U)
    if (SPIKE_OUTPUT) {
      dut.io.writeScalarCtrl.bits.spike_info.get.sm_id.poke(0.U)
      dut.io.writeScalarCtrl.bits.spike_info.get.pc.poke(0.U)
      dut.io.writeScalarCtrl.bits.spike_info.get.inst.poke(0.U)
    }
    dut.io.writeVecCtrl.valid.poke(false.B)
    dut.io.writeVecCtrl.bits.wb_wvd_rd.foreach(_.poke(0.U))
    dut.io.writeVecCtrl.bits.wvd_mask.foreach(_.poke(false.B))
    dut.io.writeVecCtrl.bits.wvd.poke(false.B)
    dut.io.writeVecCtrl.bits.reg_idxw.poke(0.U)
    dut.io.writeVecCtrl.bits.warp_id.poke(0.U)
    if (SPIKE_OUTPUT) {
      dut.io.writeVecCtrl.bits.spike_info.get.sm_id.poke(0.U)
      dut.io.writeVecCtrl.bits.spike_info.get.pc.poke(0.U)
      dut.io.writeVecCtrl.bits.spike_info.get.inst.poke(0.U)
    }
    // sgpr_base/vgpr_base default to all 0
    dut.io.sgpr_base.foreach(_.poke(0.U))
    dut.io.vgpr_base.foreach(_.poke(0.U))
  }

  // One scalar writeback (writeScalarCtrl.ready is constantly 1, a
  // single-cycle valid suffices)
  def pokeWbScalar(dut: operandCollector, warp: Int, regIdxw: Int, data: BigInt): Unit = {
    dut.io.writeScalarCtrl.bits.warp_id.poke(warp.U)
    dut.io.writeScalarCtrl.bits.reg_idxw.poke(regIdxw.U)
    dut.io.writeScalarCtrl.bits.wb_wxd_rd.poke(data.U)
    dut.io.writeScalarCtrl.bits.wxd.poke(true.B)
    dut.io.writeScalarCtrl.valid.poke(true.B)
    dut.clock.step()
    dut.io.writeScalarCtrl.valid.poke(false.B)
    dut.io.writeScalarCtrl.bits.wxd.poke(false.B)
  }

  // Issue a scalar read instruction via controlX (sel_alu1=A1_RS1), wait for
  // out(1) (out_x) and return alu_src1(0)
  def readScalarViaIssue(dut: operandCollector, warp: Int, regIdx1: Int, timeout: Int = 30): Option[BigInt] = {
    pokeCtrlSigs(dut.io.controlX.bits, wid = warp, isvec = false, mask = false,
      selAlu1 = 1 /*A1_RS1*/, selAlu2 = 0 /*A2_SIZE, ready immediately*/, selAlu3 = 0 /*A3_PC, ready immediately when branch!=B_R*/,
      regIdx1 = regIdx1)
    dut.io.controlX.valid.poke(true.B)
    // wait for the demux to accept
    var t = 0
    while (!dut.io.controlX.ready.peek().litToBoolean && t < timeout) { dut.clock.step(); t += 1 }
    dut.clock.step() // fire
    dut.io.controlX.valid.poke(false.B)
    // wait for issue
    var res: Option[BigInt] = None
    t = 0
    while (res.isEmpty && t < timeout) {
      if (dut.io.out(1).valid.peek().litToBoolean)
        res = Some(dut.io.out(1).bits.alu_src1(0).peek().litValue)
      dut.clock.step(); t += 1
    }
    res
  }

  "I-11: scalar registers of a warp with sgpr_base>=1024 alias a low-region warp's (cross-warp data interference)" in {
    test(new operandCollector) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // allocation: warp3 base=768 (low region), warp7 base=1792 (high region, >=1024 triggers 8-bit wraparound)
      dut.io.sgpr_base(3).poke(768.U)
      dut.io.sgpr_base(7).poke(1792.U)
      // first write warp3's sgpr1 (reg_idxw=4 => bank3 row (768>>2)+(4>>2)=193)
      pokeWbScalar(dut, warp = 3, regIdxw = 4, data = BigInt("12345678", 16))
      // then write warp7's sgpr1 (bank3 row (1792>>2)+1 = 449, truncated to 193 in 8 bits — the same physical row)
      pokeWbScalar(dut, warp = 7, regIdxw = 4, data = BigInt("DEADBEEF", 16))
      // read back warp3's sgpr1 via the full read path (CU->arbiter->scalarBank->crossbar->issue)
      val got = readScalarViaIssue(dut, warp = 3, regIdx1 = 4)
      assert(got.isDefined, "precondition: the read instruction should issue normally")
      // Expected: 0x12345678 (warp3's own value); actual (bug): 0xDEADBEEF (overwritten by warp7)
      assert(got.get == BigInt("12345678", 16),
        f"I-11: warp3's sgpr1 read back 0x${got.get}%08x, expected 0x12345678 — high-region warp7's write wrapped around and overwrote it")
    }
  }

  "I-12: a masked vector instruction (vmerge shape, mask=1) never issues after entering the CU (deadlock)" in {
    test(new operandCollector) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // vmerge.vvm shape: isvec=1, mask=1 (needs to read the mask from v0),
      // sel_alu1=A1_VRS1(2), sel_alu2=A2_VRS2(2), alu_fn=FN_VMERGE(51)
      pokeCtrlSigs(dut.io.controlV.bits, wid = 0, isvec = true, mask = true,
        selAlu1 = 2, selAlu2 = 2, selAlu3 = 0, regIdx1 = 2, regIdx2 = 4, aluFn = 51,
        inst = BigInt("5e2200d7", 16))
      dut.io.controlV.valid.poke(true.B)
      var t = 0
      while (!dut.io.controlV.ready.peek().litToBoolean && t < 10) { dut.clock.step(); t += 1 }
      assert(dut.io.controlV.ready.peek().litToBoolean, "precondition: an empty CU should accept the instruction")
      dut.clock.step() // fire -> the CU enters s_add waiting for the regOrder=3 v0 return (never arrives)
      dut.io.controlV.valid.poke(false.B)
      // Observe 30 cycles: neither out_v nor out_x should assert valid
      // (actual); expected: issue within a few cycles (after the fix)
      var issued = false
      for (_ <- 0 until 30) {
        if (dut.io.out(0).valid.peek().litToBoolean || dut.io.out(1).valid.peek().litToBoolean)
          issued = true
        dut.clock.step()
      }
      assert(issued,
        "I-12: masked vector instruction deadlocked — the CU did not issue within 30 cycles (the rsType=0 mask read request is " +
          "filtered out by the dual arbiters at operandCollector.scala:362-365, so the crossbar never returns regOrder=3)")
    }
  }

  "I-12 control group: a same-shape unmasked vector instruction (mask=0) should issue normally" in {
    test(new operandCollector) { dut =>
      pokeIdle(dut)
      dut.clock.step()
      // vadd.vv shape: isvec=1, mask=0 (does not take the v0 read path), sel_alu1/2 = vector registers
      pokeCtrlSigs(dut.io.controlV.bits, wid = 0, isvec = true, mask = false,
        selAlu1 = 2, selAlu2 = 2, selAlu3 = 0, regIdx1 = 2, regIdx2 = 4, aluFn = 0)
      dut.io.controlV.valid.poke(true.B)
      var t = 0
      while (!dut.io.controlV.ready.peek().litToBoolean && t < 10) { dut.clock.step(); t += 1 }
      dut.clock.step()
      dut.io.controlV.valid.poke(false.B)
      var issued = false
      for (_ <- 0 until 30) {
        if (dut.io.out(0).valid.peek().litToBoolean) issued = true // vadd -> out_v
        dut.clock.step()
      }
      assert(issued, "control group failed: an unmasked vector instruction should issue normally (something is wrong with the testbench/environment)")
    }
  }
}
