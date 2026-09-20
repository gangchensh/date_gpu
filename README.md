# Bug-Driven Formal Verification of an Open-Source RISC-V SIMT GPGPU — Artifact

This repository is the **public evidence package** for the paper
*"Bug-Driven Formal Verification of an Open-Source RISC-V SIMT GPGPU"*.

We performed a theorem-proving-level verification and bug-finding study of
**Ventus (乘影, OpenGPGPU)** — the open-source RISC-V Vector SIMT GPGPU from
Tsinghua's THU-DSP-LAB, written in Chisel — using a cycle-level **Lean 4**
model manually translated line-by-line from the RTL. The campaign produced
**52 machine-checked findings** on the original source and its bundled vendor
FPU library, of which **32 are confirmed reachable functional or performance
bugs**, each traced back to the Chisel source and independently validated at
the RTL level.

> **Methodological scope.** The Lean proofs establish properties of the
> *translated model*, not of the Chisel RTL directly; the translation is
> manual and may contain omissions or mistakes. We therefore make **no
> completeness claim** about the RTL bug set. A machine-checked finding is
> reported as a *confirmed RTL defect* only after independent RTL-level
> back-validation (source tracing, ChiselSim/Verilator reproduction, upstream
> corroboration). One finding (I-18) failed this check and was withdrawn —
> the withdrawal record is part of this package.

## Verification target

- Upstream: <https://github.com/THU-DSP-LAB/ventus-gpgpu>
- Snapshot: **`master` commit `6811725` (2025-11-12)**, treated as read-only.
- This package does not include the upstream source tree; fetch the commit
  from the upstream repository. Source locations cited in this package are
  relative to the upstream repository root (`ventus/src/...`).

## Repository layout

| Path | Contents |
|---|---|
| `FINDINGS.md` | **Master table of the 52 findings**: disposition taxonomy (32 confirmed reachable + 1 fix-activated + 10 latent + 4 excluded + 3 dead-code + 2 host-contract), Chisel `file:line`, key Lean evidence theorems, RTL reproduction verdict, fix-plan reference, upstream-fix mapping |
| `doc/03-bug-reports.md` | The complete finding registry (Class I/II/III) with source location, evidence, reproduction method, impact and tolerability analysis |
| `doc/bugs/` | **58 per-finding detail reports (English)**, each with metadata header, mechanism analysis, reachability/harm analysis, formal evidence, reproduction, fix plan, upstream impact; plus `00-comprehensive-defect-report.md` (aggregate statistics, cluster analysis, evidence methodology) and `figures/` (12 diagrams) |
| `lean/` | **Discovery-side Lean 4 development**: the `Ventus/` cycle-level model of the original RTL together with all machine-checked witness proofs (toolchain Lean v4.31.0, pinned in `lean-toolchain`; no mathlib; zero `sorry`). Build with `cd lean && lake build`. Source comments are in Chinese |
| `repro/` | Reproduction package: 11 ChiselSim suites (`*.scala`, 18 cases), the Verilator whole-machine channel (`verilator/`: 10 kernels + execution logs + `run.sh`), and **`RESULTS.md`** — per-case verdicts, the full accounting of the 6 non-reproducing cases, and the patched-RTL regression results |
| `UPSTREAM_CORROBORATION.md` | Mapping between our findings and independent fixes on the upstream `develop` branch (8 findings + 1 family-level commit) |
| `docs-evidence/` | Proof-evidence index for the released Lean development — see below |
| `LICENSE` | Mulan PSL v2 (same as upstream) for `lean/` and `repro/`; documentation under CC-BY-4.0 |

## Proof evidence (`docs-evidence/`)

The complete discovery-side Lean 4 development ships with this package under
`lean/`. The `docs-evidence/` directory provides the navigation and audit
layer on top of it:

| File | Contents |
|---|---|
| `docs-evidence/THEOREMS.md` | **Theorem index**: complete statements (verbatim, with file:line) of all 3,662 theorems in the development |
| `docs-evidence/THEOREM_TO_BUG.md` | Theorem-to-bug mapping: for every finding, the original-side evidence theorem(s) and the fixed-side efficacy/regression theorems |
| `docs-evidence/excerpts/` | **Proof excerpts (verbatim)** for the three flagship findings: I-12 (`cuWmask_deadlock`, `ocI12_deadlock_system`), I-21 (`smI21_alias`, `smI21_dead_rows`, `smI21_witness`), I-25 (T7 witness, `c2w7_tag_safe_next_cycle`) |
| `docs-evidence/STATISTICS.md` | Proof-scale statistics (files / lines / theorems per module; decision-procedure check counts), with measurement dates and a drift note |
| `docs-evidence/AXIOM_AUDIT.md` + `AXIOM_AUDIT_OUTPUT.txt` | Complete `#print axioms` audit: index of all 1,077 audit commands and the full archived output — **zero `sorryAx`, zero errors**; only Lean's standard axioms plus the `bv_decide` (LRAT) and `native_decide` trust families |
| `docs-evidence/LEAN_TREE_MD5.txt` | MD5 integrity manifest of the **released** discovery-side tree (`lean/Ventus/` + `Ventus.lean` + build files), pinning the snapshot this package ships |

Headline numbers (paper snapshot, 2026-09-10): **80 files / 60,337 lines /
2,493 theorems** for the original-side model (`Ventus/`, released here; the
counted tree has since gained one file, `Ventus/Base/BvInduction.lean`), plus
**26 files / 28,347 lines / 1,169 theorems** of fixed-variant models and the
refinement chain (`VentusF/`, **not** part of this release — see below);
**1,909 decision-procedure regression checks**; zero `sorry`; toolchain **Lean
v4.31.0**, no mathlib. The contract registry has 41 entries (25 discharged, 15
axiomatized, 1 refuted, 0 pending).

## Evidence navigation (three flagship cases)

**I-12 — all masked vector instructions deadlock** (cross-module maintenance
drift: decode table, arbiters, crossbar and collector are each locally
consistent):

- Report: `doc/bugs/I-12-masked-vector-deadlock.md`
- Theorems: `cuWmask_deadlock` (CU level), `ocI12_deadlock_system` (system
  closure) — excerpt: `docs-evidence/excerpts/I-12-masked-vector-deadlock.lean.txt`
- Reproduction: `repro/OperandCollectorBugRepro.scala` (ChiselSim),
  `repro/verilator/kernels/i12_vmerge_deadlock.asm` +
  `repro/verilator/logs/i12_vmerge_deadlock.log`
- Fix plan: see the per-finding report

**I-21 — upper 96 KB of shared memory aliases the lower 32 KB byte-for-byte**
(8-bit `setIdx` zero-extended at the SRAM interface; 96 KB of dead silicon):

- Report: `doc/bugs/I-21-sharemem-address-aliasing.md`
- Theorems: `smI21_alias`, `smI21_dead_rows`, `smI21_witness` — excerpt:
  `docs-evidence/excerpts/I-21-sharemem-aliasing.lean.txt`
- Reproduction: `repro/ShareMemAddrAliasRepro.scala`,
  `repro/verilator/kernels/i21_lds_alias.asm` +
  `repro/verilator/logs/i21_lds_alias.log`; bit-exact with the Lean witness
- Fix plan: see the per-finding report; upstream: `05503f8b`

**I-25 — completion-response tag read one transaction late** (a recycled warp
ID misattributes a workgroup's completion; cross-module lifecycle race with no
CPU analogue):

- Report: `doc/bugs/I-25-cta2warp-tag-late-read.md`
- Theorems: T7 witness + `c2w7_tag_safe_next_cycle` — excerpt:
  `docs-evidence/excerpts/I-25-cta2warp-tag-late-read.lean.txt`
- Reproduction: `repro/CTA2warpTagBugRepro.scala` (RTL tag `0x11` vs expected
  `0x08`, bit-exact with the Lean witness)
- Fix plan: see the per-finding report

## Scope of this package

This package is organized around **bug discovery and RTL back-validation**:

- **Included**: the discovery-side Lean 4 development (`lean/Ventus/` — models
  of the original RTL plus all machine-checked witness proofs), the finding
  reports, the reproduction suites and logs, and the upstream-corroboration
  mapping.
- **Not included**: repair patches and the corrected-model Lean development
  (`lean/VentusF/`, fixed-variant models and the refinement chain). Repair is
  outside the bug-discovery scope of the paper; each finding's fix plan is
  documented in its per-finding report under `doc/bugs/`.
- Also not included: internal process documents (work logs, planning
  documents, module reports) and the paper's full LaTeX sources.

Every claim in the paper is tied to a named theorem (in the released tree), a
Chisel `file:line`, and the integrity manifest in
`docs-evidence/LEAN_TREE_MD5.txt`.
