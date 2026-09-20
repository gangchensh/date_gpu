> English translation of the Chinese master `doc/bugs/I-9-旁路前递不看写掩码.md`. Translated 2026-09-13.

# I-9 Detailed Defect Report: the FloatRegFileBank bypass forward ignores the write mask (mechanism confirmed / bypass unreachable, excluded)

| Item | Content |
|---|---|
| ID | I-9 |
| Source location | `ventus/src/pipeline/regfile.scala:57-58` (the bypass forward ignores the write mask) vs `:63-65` (`regs.write` writes per the thread mask); the exclusion chain involves `writeback.scala:52-61` (0-depth Queue + Arbiter, all combinational), `operandCollector.scala:621` (bank write enable), `scoreboard.scala:110,112` (busy clear), `scoreboard.scala:131,142` + `warp_schedule.scala:181` + `pipe.scala:222-224` (issue gating) |
| Type | Functional bug (masked-lane readout pollution) — unreachable of the exactly-masked-by-timing type (doc/14 §2) |
| Severity | High at the mechanism level (when reachable = masked lanes read new values, which the execution stage consumes — not dead values); under the current protocol the bypass is dead hardware, rated latent |
| Confirmation status | 【Excluded — bypass unreachable】 (final write-off 2026-08-27); strengthened conclusion: under the proven protocol the bypass has no trigger path |
| Primary evidence | [Lean machine-checked proof] mechanism theorem `rfV_bypass_mem_diverge` + the five-ring exclusion-chain theorems (`wb_i9_gate_closed`/`wb_i9_clear_visible`/`wb_i9_timing`/`wb_i9_bypass_same_cycle`/**`wb_i9_unreachable`**) + control tests S3/S4; [direct source reading] line-by-line verification that the writeback chain is all combinational |
| Lean model | `lean/Ventus/Arith/RegFile.lean` (mechanism), `lean/Ventus/Schedule/Writeback.lean` (exclusion chain, 506 lines) |
| Reproduction/patch | No patch (the internal fix manifest: I-9 "No fix (excluded)", VentusF has no corresponding fix model); no simulation reproduction (excluded entry, see §5) |
| Related entries | I-12 (maintenance drift in the same regfile file), doc/14-不可达缺陷分析 §2, doc/modules/14-Schedule-Issue与Writeback.md §3.3, doc/modules/07-Arith-RegFile与CSR.md |

---

## 0. Abstract

A vector register-file bank (FloatRegFileBank) has a bypass forward: when the
read address equals the previous cycle's write address and the write enable
holds, the read data is forwarded directly from the previous cycle's write
data, bypassing the SyncReadMem read latency. The problem: **the write lands
in mem per the thread mask (32 lanes independently enabled), while the bypass
forwards the complete new row** — a masked lane (not written this cycle) reads
the new value via the bypass, diverging from the old value retained in mem.

The mechanism itself is real and pinned down by a Lean theorem
(`rfV_bypass_mem_diverge`); the consumer-side check further confirms the
divergence **would be harmful if reachable** (execution-stage paths such as
vmerge consume the read data of masked lanes — not dead values). But a
ring-by-ring reachability check found: the bypass window requires "the read
address presented in the same cycle as the write", and a read and write of
the same bank at the same address must be a same-warp RAW dependent pair,
blocked by the scoreboard busy bit — the busy clear and the bank write happen
in the **same cycle** (the writeback chain is combinational throughout; no
queue/register can make the write later than the clear), the clear is a
register visible only the next cycle, the dependent instruction issues at the
earliest one cycle after the write cycle, and its read address reaches the
bank one cycle after that — **the bypass window has always already expired**.

The main theorem `wb_i9_unreachable` closes this exclusion; the control tests
S3/S4 pin it down in both directions: a same-cycle read is indeed polluted
(the mechanism exists), while the actual chain reads the correct old value
(unreachable). **This bypass is dead hardware under the currently proven
protocol**. The exclusion premises (A1-A4) are on record; if "collector
serialization" among them is broken by a future pipelining rework, this entry
needs re-examination.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **Register-file banks and SyncReadMem**: Ventus's vector register file is
  organized by banks; each bank is a `SyncReadMem` row of 32 lanes
  (num_thread=32) — a synchronous-read SRAM whose read data comes out one
  cycle later.
- **Write mask**: a vector write carries a 32-bit thread mask (`rdwmask`);
  only mask-enabled lanes land in mem (`regs.write(rdidx, rd, rdwmask)`,
  regfile.scala:63-65). Masked lanes keep their old values — this is the
  storage-side implementation of the SIMT mask semantics (undisturbed).
- **Bypass forward**: the classic optimization for synchronous-read SRAM — if
  address X is written at cycle N and the same address X is read at cycle
  N+1, the read port forwards the write data registered at cycle N directly,
  instead of waiting for the mem readout (the mem does hold the new value at
  this point, but under SRAM timing/structural constraints a direct read is
  unreliable or one wants to save a cycle). Design intent: what is forwarded
  is "the row of data written at cycle N".
- **RAW and the scoreboard**: read-after-write (RAW) dependences are blocked
  by the scoreboard — when an instruction writing register a is issued, a's
  busy bit is set, and it is cleared at writeback; while busy, any
  instruction reading a is held by the issue gating.

### 1.2 Design intent

The bypass addresses the one-cycle hole of "a read immediately after a
write". The designer's implicit assumption is that a write is a full-row
write — in which case forwarding the complete new row agrees with the mem
semantics. Vector masked writes break this assumption, and the bypass logic
was not updated to look at the mask.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the bypass forward ignores the write mask**
(regfile.scala:57-58, ★ hazard):

```scala
val bypassSignal = Wire(Bool())
bypassSignal := RegNext((io.rsidx === io.rdidx) & io.rdwen)  // :57 looks only at address + write enable
io.rs := Mux(bypassSignal, RegNext(io.rd), regs.read(io.rsidx)) // :58 forwards the complete new row
```

`RegNext((rsidx===rdidx)&rdwen)`: cycle N's "read/write same address and
write enabled" is registered to cycle N+1 as the bypass switch; the forwarded
data is `RegNext(io.rd)` — **the complete 32-lane new row, carrying no mask
information whatsoever**.

**Construct 2: writes land in mem per the mask** (regfile.scala:63-65):

```scala
when (io.rdwen) {
  regs.write(io.rdidx, io.rd, internalMask)  // internalMask = io.rdwmask
}
```

**Construct 3: the writeback chain is all combinational (the foundation of
the exclusion chain)**:

- The `Queue.apply(_, 0)` at writeback.scala:52-59 is a zero-depth queue =
  a purely combinational direct connection; the `Arbiter` at :60-61 is a
  stateless fixed-priority arbiter — the whole Writeback module has no
  registers;
- operandCollector.scala:621: the bank write enable
  `rdwen := wvd & writeVecCtrl.valid` (combinational);
- scoreboard.scala:110,112: the busy clear is in the same cycle as the
  writeback (`vectorReg.clear(wb_v_fire…)` etc.), and the clear writes a
  register, becoming visible in the read view only the next cycle;
- Issue gating (scoreboard.scala:131,142 → pipe.scala:161 →
  warp_schedule.scala:181 → pipe.scala:222-224): busy reads the current
  register value and gates issue fully combinationally.

Hence: **execution-unit fire cycle = wb out fire cycle = bank write cycle =
busy clear cycle** — no queue/register makes the bank write later than the
busy clear (Queue/Arbiter semantics verified against the Chisel 6.4.0
source).

---

## 3. Defect Analysis: Mechanism and Exclusion Argument

### 3.1 Precise description of the mechanism (confirmed)

Write address X at cycle N with a partial mask (suppose lane t's mask is off
and the new data `rd(t)≠mem[X](t)`):

1. On the mem side: lane t retains its old value (construct 2);
2. Reading X at cycle N+1: the bypass switch holds (construct 1), and the
   readout is the **complete new row** — the masked lane t also reads the new
   value;
3. Reading X again at cycle N+2: the bypass window has passed, and lane t
   gets the old value from mem.

The bypass view and the memory view diverge (pinned down by the Lean
mechanism theorem `rfV_bypass_mem_diverge` + numeric corroboration V1/V3/V4).

**Harm pre-assessment (if reachable)**: the collector/crossbar themselves do
not consume lane values, but the execution stage does — vmerge's
`wb_wvd_rd(x) := Mux(mask(x), in1(x), in2(x))` together with
`wvd_mask(x):=true.B` writes all lanes (execution.scala:447,540), and every
active lane's ALU consumption uses the read data of masked lanes. **The
divergence is harmful if reachable — not a dead value.**

### 3.2 Exclusion argument (ring by ring, machine-checked end to end)

The bypass window requires "the read address presented to the bank in the
**same cycle** as the write" (construct 1's RegNext structure: the same
address is judged at cycle N and forwarded at cycle N+1, requiring the read
address to already be on `rsidx` at cycle N). Ring-by-ring exclusion:

1. **Same address ⇒ a same-warp RAW pair**: same bank and same address = the
   same architectural register of the same warp (register allocation across
   warps is disjoint — premise A1), i.e. a read-after-write dependence;
2. **At the write cycle W the dependent instruction is gated off**: busy(a)
   is still 1 in the current register value at write cycle W (the clear is
   only registered that cycle and becomes visible at W+1), and the issue
   gating is all combinational ⇒ the dependent instruction B cannot issue
   that cycle (theorem `wb_i9_gate_closed`);
3. **The clear is visible the next cycle**: B issues at the earliest at W+1
   (`wb_i9_clear_visible`);
4. **The read address is presented at the earliest after W+1**: the collector
   presents the read address combinationally in the accept cycle
   (`wb_i9_timing`: tRead ≥ tFire ≥ W+1);
5. **The same-cycle requirement is contradictory**: the bypass triggers if
   and only if the read and write are same-cycle and same-address
   (`wb_i9_bypass_same_cycle`), which conjoined with ring 4 is a
   contradiction.

Main theorem **`wb_i9_unreachable`** (vector bank): when a is written with an
arbitrary mask at cycle W and a is read at cycle R≥W+1 (no write that cycle),
(1) the bypass does not trigger; (2) what is read is the mask-merged value in
mem (masked-enabled lanes take the new value, masked-off lanes retain the
old) — the correct semantics. The scalar version `wb_i9_scalar` is analogous.
The capstone `wb_i9_chain` composes the two facts "gated off at the write
cycle + clear visible the next cycle" into a single theorem.

**Control tests (pinned down in both directions)**: S3 — if the read address
is presented in the same cycle as write cycle W (the scenario excluded by
rings 2-4), the bypass indeed triggers and the masked lane reads the new
value (0xAA05) — the mechanism exists; S4 — in the actual chain, writing at
cycle W and reading at cycle W+1, the bypass does not trigger and the masked
lane reads the correct old value (0).

### 3.3 Harm and tolerability

- **Under the current protocol**: the bypass has no trigger path and is dead
  hardware; no realistic harm whatsoever.
- **Premises and broken-window conditions**: the exclusion chain relies on
  four system-level premises (recorded in Writeback.lean D6, assumptions
  rather than theorems inside this file) — A1 same physical bank address ⇒
  same warp; A2 within-warp issue order = program order; A3 **OpCol
  serialization** (at most one instruction per warp in the collector,
  excluding WAR/out-of-order reads); A4 the writeback path is all
  combinational. Broken-window conditions: **collector pipelining** (breaks
  A3) or moving the busy clear one cycle earlier (breaks ring 2).
- **Conclusion**: excluded (bypass unreachable). No fix needed (the internal fix manifest
  "No fix (excluded)"); the residual value is the registration of the
  broken-window conditions.

---

## 4. Lean Formal Evidence

All machine-checked (zero sorry; Writeback.lean's proofs use only
simp/decide/rfl/omega/manual terms, with no bv_decide/native_decide trust
axioms; audit see doc/modules/14 §6).

**Mechanism side** (`lean/Ventus/Arith/RegFile.lean`):

- `rfV_bypass_mem_diverge` (:407): after a same-cycle same-address partial-
  mask write, the bypass readout and the mem view diverge — the mechanism is
  pinned down; tests V1/V3/V4 corroborate numerically.

**Exclusion chain** (`lean/Ventus/Schedule/Writeback.lean`, premises A1-A4
recorded in D6):

- `wb_i9_gate_closed` (:365): at the write cycle, delay reads the register
  view, and the dependent instruction is still blocked that cycle;
- `wb_i9_clear_visible` (:375): the writeback clear is visible the next cycle
  (a restatement of `sb3_wb_clear` from Scoreboard.lean);
- `wb_i9_timing` (:385): the read address is presented at the earliest at W+1
  (timing inequality);
- `wb_i9_bypass_same_cycle` (:393): bypass triggering ⇒ same cycle and same
  address (necessary condition);
- **`wb_i9_unreachable`** (:406): the main theorem, a two-cycle symbolic
  theorem for the vector bank — for arbitrary register-file state and
  arbitrary address/data/mask, the bypass does not trigger and the mask-
  merged correct value is read;
- `wb_i9_scalar` (:416): the scalar-bank version;
- `wb_i9_chain` (:423): capstone — the simultaneity composition of the
  same-cycle bank write enable and the busy-clear registration.

**Numeric controls** (same file, example + `by decide`): S3 (same-cycle read
pollution 0xAA05), S4 (the actual chain's masked lane reads the old value 0)
— mechanism existence and unreachability pinned down in both directions.

---

## 5. Simulation Verification

【Not applicable / excluded】This entry is an unreachability exclusion; no
simulation reproduction is planned (simulation can only falsify
unreachability, not confirm it; confirmation rests on the invariant-level
theorems of §4). doc/22-复现执行结果.md has no record for this entry,
consistent with the exclusion status. The two-way pinning at the mechanism
level is borne by the Lean control tests S3/S4 (the same-cycle-read pollution
shape 0xAA05 has been decide-verified).

---

## 6. Upstream Impact and Fix Disposition

- **No patch**: the internal fix manifest registers I-9 as "No fix (excluded)", and VentusF
  has no corresponding fix model — an excluded entry does not change RTL.
- **Recommendation to upstream** (note level): the bypass logic hard-codes the
  implicit assumption "writes are full-row writes" into the hardware. If
  upstream ever reworks the collector (pipelining, or allowing multiple
  in-flight instructions per warp) or adjusts the scoreboard clear timing,
  this bypass immediately turns from dead hardware into a data-pollution
  source — recommend adding an assertion (whenever the bypass triggers, the
  write mask is all-ones) to fix the contract in place.
- **Registered broken-window conditions**: collector pipelining (breaks A3)
  or moving the busy clear one cycle earlier — when either occurs, this entry
  must be re-examined per the harm assessment of §3.1 (execution-stage paths
  such as vmerge consume masked lanes — wrong-data level).

---

## 7. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Mechanism (Lean machine-checked proof) | `rfV_bypass_mem_diverge` + V1/V3/V4: the bypass forwards the complete new row; masked lanes diverge | two cycles, fully symbolic + numeric |
| Harm pre-assessment (direct source reading) | execution.scala:447,540 and other execution-stage paths consume masked lanes — harmful if reachable | source line by line |
| Exclusion (Lean machine-checked proof) | `wb_i9_gate_closed`/`wb_i9_clear_visible`/`wb_i9_timing`/`wb_i9_bypass_same_cycle` → **`wb_i9_unreachable`** (+`wb_i9_scalar`/`wb_i9_chain`) | fully symbolic, premises A1-A4 on record |
| Controls (Lean machine-checked proof) | S3 same-cycle read pollution (0xAA05) vs S4 actual chain correct (old value 0) | decide numeric |
| Direct source reading | line-by-line check of regfile.scala:57-58/:63-65, writeback.scala:52-61, operandCollector.scala:621, scoreboard.scala:110,112,131,142 | five files consistent |
| Simulation | not applicable (excluded entry) | — |
| Fix | No fix (excluded); an assertion to fix the contract is recommended | direct source reading + recommendation |

I-9 is a paradigmatic case of "**a real mechanism precisely excluded by a
proven protocol**": the bypass hardware objectively exists and its semantics
is wrong, but the three protocol layers — scoreboard blocking, the
all-combinational writeback chain, and collector serialization — stack up to
leave it with no trigger window ever; the exclusion is not "not observed in
testing" but a reachability denial composed of five ring theorems. Together
with I-4 it supports doc/14's methodological argument: the value of an
exclusion conclusion lies in attributing safety precisely to concrete
contracts (A1-A4 and the broken-window conditions), and these contracts
themselves become review checkpoints for subsequent design changes.
