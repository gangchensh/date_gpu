# Engineering Statistics (auto-computed, 2026-09-10; after the I-18 correction, residual discharge (R1-R3), R4 contract tail, and R5 FloatSpec)

> **2026-09-20 note.** The released tree (`lean/` in this package) is the
> discovery-side `Ventus/` development in full, together with `Ventus.lean`,
> `lakefile.toml`, `lake-manifest.json`, and the pinned toolchain file. The
> repair-side `VentusF/` tree is outside the scope of this release. The
> figures below describe the **complete** engineering tree (both sides);
> `LEAN_TREE_MD5.txt` now pins the released discovery-side tree.
>
> **2026-09-14 update.** Two figures below are updated to the final values the
> paper cites: the decision-procedure regression checks (**1,909**; the 09-10
> measurement read 1,837, before later test growth) and the
> reproduction/patch status (28 cases, 22 confirming; merged 38-patch tree,
> 9/11 suites green — see `repro/RESULTS.md`). The proof tree continues to
> evolve; `LEAN_TREE_MD5.txt` pins the snapshot described here.

> Measured on the verification engineering tree with
> `find lean/ -name "*.lean"`, `wc -l`, and
> `grep -cE '^(private )?theorem '`. Toolchain: `leanprover/lean4:v4.31.0`,
> no mathlib, `bv_decide` enabled. Full build constraint: zero `sorry`.

## Totals

| Metric | Ventus/ | VentusF/ | Total |
|---|---|---|---|
| Lean files | 80 | 26 | **106** |
| Lines | 60,337 | 28,347 | **88,684** |
| Theorems (`theorem` signature lines) | 2,493 | 1,169 | **3,662** |

Additional usage counts (occurrences, whole tree):

| Tactic / command | Occurrences |
|---|---|
| `native_decide` | 1,122 |
| `bv_decide` | 555 |
| `#print axioms` audit commands | 1,077 |

Decision-procedure regression checks (theorems/examples whose proof is a single
`decide` or `native_decide` call, counted by `grep -E ':=\s*by\s+(native_)?decide'`
on the Ventus/ tree): **1,909** (1,477 `decide` + 432 `native_decide`, measured
2026-09-14). This is the metric the paper cites as "decision-procedure regression
checks".

RTL reproduction status (final campaign, doc/22): 28 reproduction cases executed
(11 ChiselSim suites with 18 cases + 10 Verilator kernels); 22 confirm the
predicted behavior on the actual RTL; I-18 withdrawn (Class II, model corrected);
the merged 38-patch series applies cleanly, compiles, and turns 9/11 suites green
on the patched RTL. Per-case verdicts and logs: `repro/RESULTS.md`.

## Per-module breakdown

| Tree | Files | Lines | Theorems |
|---|---|---|---|
| Ventus/Arith (ALU, multiplier, divider, CSR, decode, regfile) | 14 | 12,031 | 641 |
| Ventus/Base (handshake, queue model, memory laws) | 6 | 2,841 | 145 |
| Ventus/CTA (CTA scheduler, allocator, CTA2warp, rtcache consistency) | 7 | 6,839 | 309 |
| Ventus/L2 (L2 cache: directory, MSHR, scheduler, SourceD) | 6 | 4,778 | 172 |
| Ventus/Mem (L1 DCache/ICache, LSU, MSHR, ShareMem, SRAM) | 10 | 9,081 | 376 |
| Ventus/Schedule (warp scheduler, operand collector, scoreboard) | 9 | 7,616 | 316 |
| Ventus/SIMT (SIMT stack / branch join) | 5 | 2,160 | 132 |
| Ventus/Spec (contracts, black-box specs, IEEE 754 spec) | 7 | 4,232 | 217 |
| Ventus top level (SM / MultiSM integration, pipeline) | 16 | 10,759 | 185 |
| VentusF (fixed-variant models + refinement/capstone chain + liveness/fairness/fix verification) | 26 | 28,347 | 1,169 |

Note: line counts include model definitions, proofs, comments (comments in the
engineering tree are in Chinese), and per-file `#print axioms` audit blocks.
