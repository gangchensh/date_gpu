> English translation of the Chinese master `doc/bugs/I-34-ICache冲刷绑死.md`. Translated 2026-09-13.

# I-34 Detailed Defect Analysis Report: ICache invalidate Tied Off to false at the AXI Production Top Level — No Hardware Flush for Multi-Kernel Same-Address Reuse

| Item | Content |
|---|---|
| ID | I-34 |
| Source location | `ventus/src/top/GPGPU_top.scala:136` (GPGPU_axi_top ties `icache_invalidate` off to false.B, ★ landmine); downstream chain `:162` (GPGPU_top port declaration) → `:184` (broadcast to all SM_wrappers in the cluster) → `:347`/`:370` (SM_wrapper → ICache `io.invalidate`) → `L1Cache/ICache/ICache.scala:71,93` (→ tagAccess.invalidate) |
| Type | Environment-contract defect (triggered only when host discipline is violated) — doc/14 §4 classification |
| Severity | Conditional: when the host reuses an address to load a new kernel and a tag collision occurs, this is **instruction-level data corruption** (executing the old kernel's instructions); not triggerable under proper host discipline |
| Confirmation status | 【Pending】 — the hardware-side "tied off" fact has been pinned by the Lean wiring contract (rfl level); **the item awaiting adjudication = whether the host driver avoids the issue in some other way before every kernel launch** (doc/03:760-761) |
| Primary evidence | [Lean machine-checked proof] `top_icacheInv_never` (Top.lean:542, rfl level: under the AXI top level, no SM's ICache ever receives invalidate); [Direct source reading] the tie-off point and the four-level downstream chain checked line by line |
| Lean model | `lean/Ventus/Top.lean` (W11d/W11e, Top.lean:535-543) |
| Repro/patch | No patch (the internal fix manifest classification "No fix (host contract)", recommending hardware assertion + driver contract documentation); no repro case (doc/13 class C: not reproducible under the current configuration in either simulation or FPGA) |
| Related entries | I-23 (no mutual exclusion between ICache probe/refill — the boundary of fetch correctness tightens further against a backdrop of stale entries); I-45 (also a host-contract type); Q4 (the original suspicion case from the Top.lean source review) |

---

## 0. Summary

Ventus has two top levels: `GPGPU_SimWrapper` (for simulation, exposing
`icache_invalidate` as a port, GPGPU_SimWrapper.scala:83,111) and
**`GPGPU_axi_top` (the production-grade AXI top level)**. The latter, at
GPGPU_top.scala:136, **ties off** the inner GPGPU_top's `icache_invalidate` input to
**false.B** — meaning that on a chip deployed through the AXI top level, the ICache
invalidate signal is false at all times, and **the previous kernel's instruction
lines remain resident in the ICache across kernel boundaries**.

Consequence chain: if a new kernel reuses the same load base address and a tag
collision occurs, instruction fetch will hit the old kernel's stale instruction
lines — the whole machine executes the wrong program with no error raised. This
correctness is entirely outsourced to implicit host-side discipline ("each kernel
owns its address space / base addresses are not reused"); the hardware itself has no
protection whatsoever.

This entry's status is 【Pending】 rather than 【Confirmed】 precisely because of
this outsourcing: **the mechanism (hardware never flushes) has been pinned by
machine-checked proof, but "whether it constitutes an actual bug" depends on host
driver discipline** — if the driver always uses non-reused load base addresses for
every kernel (or otherwise guarantees no stale hits), it cannot be triggered. The
adjudication criteria are in §3.3.

---

## 1. Module Function and Design Intent

### 1.1 Background concepts

- **ICache and kernel switching**: a GPU executes in units of kernels; the host
  writes the new kernel's instruction binary into memory and then starts CTA
  scheduling. The ICache caches instruction lines by address; if a new kernel is
  loaded **at the same physical address as an old kernel**, stale lines may remain
  in the ICache — on general-purpose CPUs this is handled by `fence.i` / cache
  maintenance instructions, and on GPUs typically by the driver issuing an
  "invalidate" flush at kernel boundaries.
- **The `icache_invalidate` port**: Ventus's ICache (`ICache.scala:71`) has an
  `invalidate: Input(Bool())`, internally wired to `tagAccess.io.invalidate`
  (ICache.scala:93) — raising it clears the valid bits of the tag array, so all
  subsequent fetches miss and the new kernel's instructions are re-fetched from
  memory.
- **Two top levels**: `GPGPU_top` is the core logic; `GPGPU_SimWrapper` is the
  simulation wrapper (exposing `icache_invalidate` as an io port; the companion
  sim-verilator C++ host driver has a `ventus_rtlsim_icache_invalidate()` API);
  `GPGPU_axi_top` is the production-grade wrapper (externally it has only an
  AXI4-Lite control port `io.s` and an AXI4 master port `io.m`), and the host can
  only interact with it via MMIO registers.

### 1.2 Design intent

The invalidate path is clearly **designed for kernel-boundary flushing**: the port
is broadcast from GPGPU_top all the way to every SM's ICache. The SimWrapper top
level exposing this port shows the designers expected the host/driver to drive it at
appropriate times. The defect is that the production top level cut this path.

---

## 2. Construct-by-Construct Reading of the Original Code

**Construct 1: the tie-off point** (`GPGPU_top.scala:116-137`, the whole of GPGPU_axi_top; ★ landmine at :136):

```scala
class GPGPU_axi_top extends Module{
  ...
  val gpgpu_top=Module(new GPGPU_top()(l1param,true))
  ...
  gpgpu_top.io.cycle_cnt:=0.U                    // :135 (Q5, separate case: cycle counter tied to 0)
  gpgpu_top.io.icache_invalidate:=false.B        // :136 ★ ICache invalidate permanently false
}
```

The AXI top level's io has only two ports, `s` (AXI4-Lite 32×32) and `m` (AXI4
master) (:120-123) — **no field can carry a "flush ICache" request in from the
host**.

**Construct 2: inner port and broadcast** (`GPGPU_top.scala:162,:184`):

```scala
val icache_invalidate = Input(Bool())                              // :162 GPGPU_top port
...
sm_wrapper(i * NSmInCluster + j).icache_invalidate := io.icache_invalidate  // :184 broadcast to every SM
```

**Construct 3: landing point inside the SM** (`GPGPU_top.scala:347,:370`):

```scala
val icache_invalidate = Input(Bool())            // :347 SM_wrapper port
val icache = Module(new InstructionCache(SV)(param))
icache.io.invalidate := io.icache_invalidate     // :370 wired into the ICache
```

**Construct 4: consumption inside the ICache** (`ICache.scala:71,:93`):

```scala
val invalidate = Input(Bool())                   // :71
tagAccess.io.invalidate := io.invalidate         // :93 clears the tag array's valid bits
```

**Contrasting construct: the simulation top level exposes it** (`GPGPU_SimWrapper.scala:83,:111`):

```scala
val icache_invalidate = Input(Bool())            // :83 SimWrapper port
GPU.io.icache_invalidate := io.icache_invalidate // :111 passed straight into GPGPU_top
```

And sim-verilator's C++ driver provides a host API
(`ventus_rtlsim_icache_invalidate()` at `sim-verilator/ventus_rtlsim.h:126`,
implemented at ventus_rtlsim.cpp:49 / ventus_rtlsim_impl.cpp:298-299: after the host
calls it, `io_icache_invalidate` is raised on the next cycle). **That is: the flush
capability exists in full on the simulation channel, while the production channel
was cut by the single line at :136.**

---

## 3. Defect Analysis

### 3.1 Precise description of the defect

When deployed via the AXI top level, the ICache's invalidate signal is permanently
false (the chain of constructs 1–4 was read directly end to end; no other driving
source). Therefore:

1. After kernel K1 executes, its instruction lines remain resident, valid, in each
   SM's ICache;
2. The host loads kernel K2 and launches it — if K2 reuses the same load base
   address as K1 (same-address reuse is a common pattern in real production
   deployments, doc/14:112) and the address tags collide with the resident lines;
3. Instruction fetch hits the resident lines and **the warps execute the old
   kernel's instructions** — silently executing the wrong program.

Read together with I-23 (no mutual exclusion between ICache probe/refill, which can
return LFSR garbage instructions): I-23 already established the first layer of risk
that "ICache hit ≠ correct instruction", and I-34 further removes the cleanup means
at kernel boundaries on top of that — the boundary of fetch correctness tightens
further (doc/03:758).

### 3.2 Root cause

When the host interface surface of the production wrapper (GPGPU_axi_top) was
designed, `icache_invalidate` was not incorporated into the MMIO register map — the
AXI4-Lite port (axi_lite_adapter → AXI4Lite2CTA) only handles kernel
dispatch/completion reporting, leaving no path for a flush signal. The root cause is
that **the contract "the ICache must be cleared at kernel boundaries" is implemented
only on the simulation channel and is missing on the production channel**. It
belongs to the "environment-contract" defect class of doc/14 §4: safety is
outsourced to host discipline, with zero hardware protection.

### 3.3 Harm and tolerability (including the pending-adjudication criteria)

- **Harm (when the conditions hold)**: the most severe tier of instruction-level
  data corruption — what executes is not a program with wrong results but **the
  wrong program**; no trap, no assertion; from the host's perspective it appears as
  "wrong results with an extremely hard-to-locate cause".
- **Tolerability**: if the host driver always allocates non-reused load base
  addresses for every kernel (or rewrites the entire address space before loading so
  resident lines cannot be hit), it cannot be triggered. doc/14:111 records "the
  current driver gives each kernel an exclusive load address or does not reuse";
  repro/verilator/README.md:184-186 records that the sim-verilator driver "runs an
  exclusive load procedure for every kernel; I-34 is not among the targets of that
  repro package" — consistent with this assessment.
- **Pending-adjudication criteria** (verbatim from doc/03:760-761): **whether the
  host driver avoids the issue in some other way before every kernel launch (e.g.,
  rewriting the entire address space / using different base addresses); if the host
  side has no such discipline, upgrade to 【Confirmed】**. The object that must be
  examined for adjudication is the source of the host driver/runtime used in
  production deployment (the base-address allocation policy on the kernel loading
  path); this project's snapshot does not contain that software stack, so the ruling
  is left to upstream/deployers.

---

## 4. Lean Formal Evidence

The wiring contract in `lean/Ventus/Top.lean` pins the "tied off" fact as an
rfl-level theorem (Top.lean:535-543):

```lean
/-- W11d (:136, Q4): icache_invalidate tied off to false -/
def topAxiTopIcacheInv : Bool := false

/-- W11e (:184): icache_invalidate broadcast to all SMs in the cluster (same value for each SM, W0) -/
def topIcacheInvBroadcast (b : Bool) (_sm : Fin 2) : Bool := b

/-- Composition of Q4: under GPGPU_axi_top, no SM's ICache ever receives invalidate -/
theorem top_icacheInv_never (sm : Fin 2) :
    topIcacheInvBroadcast topAxiTopIcacheInv sm = false := rfl
```

[Lean machine-checked proof] `top_icacheInv_never`: for any SM (Fin 2; current
configuration num_sm=2), the invalidate via the AXI top level is permanently false.
An rfl-level proof — the conclusion is just unfolding definitions, with no axiom
burden (Top.lean is entirely zero-sorry, no native_decide; audit in
doc/modules/32-集成-顶层连线契约.md §6).

Nature of the evidence: this is **structural/wiring-check evidence** (doc/13:25
classifies I-34 in the "structural evidence" family), pinning that "the hardware has
no such path"; it neither proves nor refutes that "same-address reuse will happen" —
the latter is a host-side question, which is exactly the boundary of this entry's
【Pending】 status.

---

## 5. Simulation Verification

**Not executed in this environment, and the current reproduction channels
structurally do not cover this entry** (recorded as-is):

- doc/13-复现分析报告 §2.2 places I-34 in **class C** ("unreachable or masked under
  the current configuration; can only be proved/refuted at the model level"): under
  the existing host discipline, neither simulation nor FPGA can reproduce it; its
  "reproduction would require modifying the configuration in the first place"
  (doc/13:28).
- repro/verilator/README.md:184-186 states explicitly: I-34 is **relevant** to the
  verilator channel (the multi-kernel same-address-reuse scenario), but the
  sim-verilator driver runs an exclusive load procedure for every kernel, so it is
  not among that repro package's targets.
- If a directed reproduction is ever wanted in the future, the path is ready: the
  sim-verilator driver already has the `ventus_rtlsim_icache_invalidate()` API and
  the `io_icache_invalidate` port; construct "execute K1 → load K2 at the same base
  address (without calling invalidate) → observe fetch hitting resident lines" — but
  the reproduction target would be the **SimWrapper channel** (the port exists, and
  whether to raise it is the host's decision), which happens to demonstrate "no
  flush → wrong execution"; the AXI top level's tie-off is a wiring fact, already
  covered by the §4 machine-checked proof, needing no simulation.

---

## 6. Upstream Impact Analysis

- **Trigger surface**: all scenarios deployed via GPGPU_axi_top where the host
  reuses load base addresses. The SimWrapper/FPGA demo channel (port exposed, driver
  has the API) is unaffected.
- **Why upstream hasn't found it**: the official software stack and FPGA deployments
  go through the SimWrapper channel or follow the exclusive-base-address discipline,
  and have never reused kernel addresses in the production form factor. This is a
  case of "contract not hardened into hardware" rather than "logic written wrong".
- **Sibling entries**: I-45 (register-allocation alignment constraints with zero
  hardware checks) is likewise a host-contract type; the internal fix manifest handles both
  uniformly as "No fix (host contract)" — recommending hardware assertions + driver
  contract documentation (the internal fix manifest).

---

## 7. Fix and Fix Verification

**No patch** (the internal fix manifest classification "No fix (host contract)"; disposition is
contract registration + recommendation). Fix suggestions (verbatim from doc/03:762,
expanded):

1. **Expose icache_invalidate at the AXI top level and drive it at kernel
   boundaries**: extend the MMIO register map (AXI4Lite2CTA) with an "ICache flush"
   write register, written once by the host before every kernel launch; or build the
   invalidate generation logic into the kernel-launch sequence (CTA automatically
   emits a one-cycle clear pulse upon receiving a new kernel).
2. **Document the accompanying contract**: state in the driver development
   documentation that "the ICache must be flushed at kernel boundaries, or base
   addresses must be guaranteed non-reused" — whichever hardware option is chosen,
   this contract should be made explicit (it is currently implicit discipline).
3. **Defense in depth**: a simulation-time assertion can be added, "if the first
   fetch hit after a kernel launch is more than one kernel boundary away from the
   last invalidate, raise a warning" (online monitoring of contract violations).

**Fix verification**: this entry currently has no repaired-version modeling (not
covered by VentusF); the verification obligation is bound to the fix option — if
option 1 is adopted, the corresponding wiring contract (the tie-off fact of Top.lean
W11d) must be rewritten into an "MMIO-driven" model with contract tests added.

---

## 8. Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | GPGPU_top.scala:136 (tie-off) → :162/:184 (port + broadcast) → :347/:370 (SM_wrapper→ICache) → ICache.scala:71/:93 (tag valid clear); contrast SimWrapper:83/:111 port exposure, sim-verilator host API | Five source files checked line by line |
| Lean machine-checked proof | `top_icacheInv_never` (rfl level: under the AXI top level, no SM's ICache ever receives invalidate) | Wiring-fact level |
| Simulation | Not executed; doc/13 class C verdict (not reproducible in simulation/FPGA under existing host discipline); verilator channel structurally does not cover it (README.md:184-186) | Ready-to-run (not executed in this environment) (only the SimWrapper channel could demonstrate the contract violation) |
| Fix | No patch; the internal fix manifest "No fix (host contract)", recommending port exposure + contract documentation | Recommendation level |

I-34 is a model example of an "environment-contract" defect: the hardware outsources
the correctness of clearing the ICache at kernel boundaries entirely to implicit
host discipline, and the path is cut only at the production (AXI) top level — the
simulation channel, by contrast, has the capability in full. The mechanism-side
evidence is closed (rfl-level wiring contract); the status rests at 【Pending】
awaiting adjudication of host driver discipline; the minimal object to examine for
that adjudication is the base-address allocation policy on the kernel loading path
in the production deployment driver.
