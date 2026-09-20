// repro/IntDivModBugRepro.scala — ChiselSim reproduction of I-17/I-18/I-19
// [2026-09-07] 已实跑，结果见 doc/22-复现执行结果.md（ChiselSim 通道）。
// (ready-to-run, not executed in this environment: no mill/scala
// dependencies on this machine). Follows the ventus/tests/ style
// (ChiselScalatestTester). Drop into the ventus project and run:
//   mill ventus.test.testOnly pipeline.IntDivModBugRepro
package pipeline

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec

class IntDivModBugRepro extends AnyFreeSpec with ChiselScalatestTester {
  // [2026-09-06 execution fix] The original txn() did not wait for in.ready
  // and did not consume out.fire; with back-to-back transactions the second
  // input was never accepted (state=s_finish at poke time, in.ready=0), and
  // the test read the FIRST transaction's stale output (I-19's "r=3" was
  // txn1's remainder, not the I-19 mechanism). Now: wait for in.ready before
  // the firing step, and step once after reading to consume the response.
  def txn(c: IntDivMod, a: BigInt, d: BigInt, sgn: Boolean): (BigInt, BigInt) = {
    c.io.in.bits.a.poke(a.U); c.io.in.bits.d.poke(d.U); c.io.in.bits.signed.poke(sgn.B)
    c.io.out.ready.poke(true.B)
    c.io.in.valid.poke(true.B)
    var t = 0
    while (!c.io.in.ready.peek().litToBoolean && t < 100) { c.clock.step(); t += 1 }
    assert(t < 100, "precondition: in was not accepted within 100 cycles")
    c.clock.step(); c.io.in.valid.poke(false.B)
    t = 0; while (!c.io.out.valid.peek().litToBoolean && t < 100) { c.clock.step(); t += 1 }
    assert(t < 100, "precondition: out.valid timeout")
    val res = (c.io.out.bits.q.peek().litValue, c.io.out.bits.r.peek().litValue)
    c.clock.step() // consume the response (out.fire -> s_idle)
    res
  }

  "I-17: cnt width truncation, 0x80000000/1 (u) should give (0x80000000,0), hardware gives (1,0)" in {
    test(new IntDivMod(32)) { c =>
      assert(txn(c, BigInt("80000000", 16), 1, false) == (BigInt("80000000", 16), 0))
    }
  }

  "I-19: stale zeroQReg, first 3/5 then INT_MIN/-1, r should be 0, hardware gives 0x80000000" in {
    test(new IntDivMod(32)) { c =>
      txn(c, 3, 5, false) // zeroQReg <- 1
      assert(txn(c, BigInt("80000000", 16), BigInt("FFFFFFFF", 16), true)._2 == 0)
    }
  }

  "I-18: remainder recovery truncates before adding, 4/3 should give (1,1), hardware gives (1,5)" in {
    test(new IntDivMod(32)) { c =>
      assert(txn(c, 4, 3, false) == (1, 1))
    }
  }

  // [2026-09-06 execution cross-check] The 4/3 stimulus did NOT reproduce on
  // RTL (hardware returned the correct (1,1)). Cross-check with the model's
  // second BUG3 witness (IntDivMod.lean div_test_32_random_u):
  // 0xDEADBEEF/0x1234 (u), spec (q=0xC3BA5, r=0x76B), model predicts r=0x276B.
  "I-18b: model witness 0xDEADBEEF/0x1234 (u), spec (0xC3BA5,0x76B); model predicts (0xC3BA5,0x276B)" in {
    test(new IntDivMod(32)) { c =>
      val (q, r) = txn(c, BigInt("DEADBEEF", 16), BigInt("1234", 16), false)
      println(s"I-18b actual: q=0x${q.toString(16)} r=0x${r.toString(16)} (spec q=0xc3ba5 r=0x76b; model-predicted buggy r=0x276b)")
      assert((q, r) == ((BigInt("C3BA5", 16), BigInt("76B", 16))))
    }
  }
}
