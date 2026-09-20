// repro/ArrayMultiplierBugRepro.scala — ChiselSim reproduction of I-15
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.ArrayMultiplierBugRepro
//
// I-15 [confirmed] Multiplier.scala:204-205 high-half select misses
// FN_MULHSU — MULHSU returns the low 32 bits of the product.
//   res = Mux(isMAC, mac_out, Mux(func===FN_MULH | func===FN_MULHU, result(2*len-1,len),
//         result(xlen,0))) — the high-half branch condition only has
//         FN_MULH|FN_MULHU, missing FN_MULHSU(23).
//   Operand formation (:178-179) is correct for MULHSU (sext(a)*zext(b));
//   only the result select is wrong.
//   Instantiation: execution.scala:72,188 (new ArrayMultiplier(num_thread, xLen), len=32).
//   Lean witness: Multiplier.lean mul_mulhsu_witness (a=b=0xFFFFFFFF yields 1
//   from the source; the correct high 32 bits are 0xFFFFFFFF; product =
//   -1 * 0xFFFFFFFF = 0xFFFFFFFF00000001).
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._
import IDecode._

class ArrayMultiplierBugRepro extends AnyFreeSpec with ChiselScalatestTester {

  // Feed a single-cycle transaction, wait for out.valid, return result.
  // ArrayMultiplier latency=2.
  def txn(c: ArrayMultiplier, func: Int, a: BigInt, b: BigInt): BigInt = {
    c.io.in.bits.ctrl.alu_fn.poke(func.U)
    c.io.in.bits.a.poke(a.U)
    c.io.in.bits.b.poke(b.U)
    c.io.in.bits.c.poke(0.U)
    c.io.in.bits.mask.foreach(_.poke(true.B))
    // The remaining CtrlSigs fields do not affect the multiply result path;
    // zero them to avoid X
    val ct = c.io.in.bits.ctrl
    ct.inst.poke(0.U); ct.wid.poke(0.U); ct.fp.poke(false.B); ct.branch.poke(0.U)
    ct.simt_stack.poke(false.B); ct.simt_stack_op.poke(false.B); ct.barrier.poke(false.B)
    ct.csr.poke(0.U); ct.reverse.poke(false.B); ct.sel_alu2.poke(0.U); ct.sel_alu1.poke(0.U)
    ct.isvec.poke(false.B); ct.sel_alu3.poke(0.U); ct.mask.poke(false.B); ct.sel_imm.poke(0.U)
    ct.mem_whb.poke(0.U); ct.mem_unsigned.poke(false.B)
    ct.force_rm_rtz.poke(false.B); ct.is_vls12.poke(false.B); ct.mem.poke(false.B)
    ct.mul.poke(true.B); ct.tc.poke(false.B); ct.disable_mask.poke(false.B)
    ct.custom_signal_0.poke(false.B); ct.mem_cmd.poke(0.U); ct.mop.poke(0.U)
    ct.reg_idx1.poke(0.U); ct.reg_idx2.poke(0.U); ct.reg_idx3.poke(0.U); ct.reg_idxw.poke(0.U)
    ct.wvd.poke(false.B); ct.fence.poke(false.B); ct.sfu.poke(false.B)
    ct.readmask.poke(false.B); ct.writemask.poke(false.B); ct.wxd.poke(false.B)
    ct.pc.poke(0.U); ct.imm_ext.poke(0.U)
    ct.atomic.poke(false.B); ct.aq.poke(false.B); ct.rl.poke(false.B)
    if (SPIKE_OUTPUT) {
      ct.spike_info.get.sm_id.poke(0.U); ct.spike_info.get.pc.poke(0.U)
      ct.spike_info.get.inst.poke(0.U)
    }
    c.io.in.valid.poke(true.B)
    c.io.out.ready.poke(true.B)
    var t = 0
    while (!c.io.in.ready.peek().litToBoolean && t < 10) { c.clock.step(); t += 1 }
    c.clock.step() // in fire
    c.io.in.valid.poke(false.B)
    t = 0
    while (!c.io.out.valid.peek().litToBoolean && t < 20) { c.clock.step(); t += 1 }
    assert(c.io.out.valid.peek().litToBoolean, "precondition: the multiplier should produce a result within latency=2")
    c.io.out.bits.result.peek().litValue
  }

  "I-15: MULHSU(0xFFFFFFFF, 0xFFFFFFFF) should return the high 32 bits 0xFFFFFFFF, hardware gives the low 32 bits 0x00000001" in {
    test(new ArrayMultiplier(num_thread, xLen)) { c =>
      // sext(a=-1) * zext(b=0xFFFFFFFF) = 0xFFFFFFFF_FFFFFFFF * ... =
      // -0xFFFFFFFF = 0xFFFFFFFF00000001 (64 bits) => high 32 bits 0xFFFFFFFF
      val got = txn(c, FN_MULHSU.litValue.intValue, BigInt("FFFFFFFF", 16), BigInt("FFFFFFFF", 16))
      assert(got == BigInt("FFFFFFFF", 16),
        f"I-15: MULHSU returned 0x${got}%08x, expected 0xFFFFFFFF (high 32 bits); returning 0x00000001 confirms the missed high-half select")
    }
  }

  "I-15 control group: MULHU with the same operands takes the high-half branch and should return 0xFFFFFFFE" in {
    test(new ArrayMultiplier(num_thread, xLen)) { c =>
      // 0xFFFFFFFF * 0xFFFFFFFF = 0xFFFFFFFE00000001 => high 32 bits 0xFFFFFFFE
      val got = txn(c, FN_MULHU.litValue.intValue, BigInt("FFFFFFFF", 16), BigInt("FFFFFFFF", 16))
      assert(got == BigInt("FFFFFFFE", 16),
        f"control group failed: MULHU returned 0x${got}%08x, expected 0xFFFFFFFE (the high-half path itself works)")
    }
  }
}
