// repro/DecodeUnitAMORepro.scala — ChiselSim reproduction of I-16
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine).
// Usage: drop into the ventus project test source set (e.g.
// ventus/tests/src/pipeline/) and run:
//   mill ventus.test.testOnly pipeline.DecodeUnitAMORepro
//
// I-16 [confirmed] the IDecodeLUT_A (AMO decode table) at
// DecodeUnit.scala:453-468 is dead code:
//   the ctrlSignals at :556-568 only use the IMF/V/VL/VC four tables, and
//   the keys of the outer opcode-based table select do not include 0101111
//   (AMO). Any A-extension instruction (LR/SC/AMOADD/...) falls into the
//   IMF table, which has no such row, and decodes to the default row
//   (alu_fn=63/FN_X, no writeback, no memory access, atomic=0) — a silent
//   NOP after synthesis.
//   Lean evidence: DecodeUnit.lean decides the encodings of
//   AMOADD_W/LR_W/SC_W to decDefaultRow.
//   Expected: AMOADD_W decodes to atomic=1, mem_cmd=M_XWR(2),
//   alu_fn=FN_AMOADD(29), wxd=1;
//   actual: the default row (alu_fn=63, atomic=0, mem_cmd=0, wxd=0).
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import top.parameters._

class DecodeUnitAMORepro extends AnyFreeSpec with ChiselScalatestTester {

  // Encoding of amoadd.w x3, x2, (x1): funct5=00000 aq=0 rl=0 rs2=00010
  // rs1=00001 funct3=010 rd=00011 opcode=0101111 => 0x0020A1AF
  val AMOADD_W_ENC = BigInt("0020A1AF", 16)
  // lr.w x3, (x1): funct5=00010 rs2=00000 rs1=00001 funct3=010 rd=00011 => 0x1000A1AF
  val LR_W_ENC = BigInt("1000A1AF", 16)

  def pokeAndGet(dut: InstrDecodeV2, inst: BigInt): (BigInt, Boolean, BigInt, Boolean) = {
    dut.io.inst(0).poke(inst.U)
    dut.io.inst(1).poke(0.U)
    dut.io.inst_mask(0).poke(true.B)
    dut.io.inst_mask(1).poke(false.B)
    dut.io.pc.poke(0.U)
    dut.io.wid.poke(0.U)
    dut.io.sm_id.poke(0.U)
    dut.io.flush_wid.valid.poke(false.B)
    dut.io.flush_wid.bits.poke(0.U)
    dut.io.ibuffer_ready.foreach(_.poke(true.B))
    dut.clock.step() // let the combinational/registered paths settle (scratchPads do not update because mask(1)=0)
    val c0 = dut.io.control(0)
    (c0.alu_fn.peek().litValue, c0.atomic.peek().litToBoolean,
      c0.mem_cmd.peek().litValue, c0.wxd.peek().litToBoolean)
  }

  "I-16: AMOADD_W through DecodeUnit should decode to FN_AMOADD/atomic/memory-write, but actually falls to the default row (silent NOP)" in {
    test(new InstrDecodeV2) { dut =>
      val (aluFn, atomic, memCmd, wxd) = pokeAndGet(dut, AMOADD_W_ENC)
      // Expected (if IDecodeLUT_A were wired in): alu_fn=29(FN_AMOADD),
      //   atomic=true, mem_cmd=2(M_XWR), wxd=true
      // Actual (bug): default row alu_fn=63(FN_X), atomic=false, mem_cmd=0, wxd=false
      assert(aluFn == 29 && atomic && memCmd == 2 && wxd,
        s"I-16: AMOADD_W decoded to the default row: alu_fn=$aluFn(expected 29) atomic=$atomic(expected true) " +
          s"mem_cmd=$memCmd(expected 2) wxd=$wxd(expected true) — the A extension silently decodes to NOP")
    }
  }

  "I-16: LR_W also falls to the default row" in {
    test(new InstrDecodeV2) { dut =>
      val (aluFn, atomic, memCmd, wxd) = pokeAndGet(dut, LR_W_ENC)
      // Expected: alu_fn=0(FN_ADD), atomic=true, mem_cmd=1(M_XRD), wxd=true
      assert(aluFn == 0 && atomic && memCmd == 1 && wxd,
        s"I-16: LR_W decoded to the default row: alu_fn=$aluFn atomic=$atomic mem_cmd=$memCmd wxd=$wxd")
    }
  }
}
