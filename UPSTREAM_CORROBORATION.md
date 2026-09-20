# Upstream Corroboration

Independently of our work, the upstream `develop` branch of
[THU-DSP-LAB/ventus-gpgpu](https://github.com/THU-DSP-LAB/ventus-gpgpu) —
178 commits ahead of the verified `master` snapshot `6811725` — contains fixes
that correspond to our findings (checked via the GitHub API on 2026-08-31;
newest develop commit dated 2026-08-18). All upstream fixes are dated earlier
than or parallel to our disclosures; we had reported nothing upstream at that
point, so these constitute independent confirmations that the findings are
real defects.

## Commit mapping (8 findings)

| Upstream `develop` commit | Upstream change | Our finding |
|---|---|---|
| `05503f8b` | LSU shared-memory request width fix | **I-21** (8-bit setIdx aliases upper 96 KB of LDS) |
| `ef2fb0c9` | DCache dirty-mask identity across stalls | **I-28** (dirtyMask lane overwrite loses bytes) |
| `7864f4c8` | Wait for maintenance writes before completion | **I-47** (WG reported done before DCache flush completes) |
| `0cefc242` | Drain warp LSU before barrier | **I-46** (endprg does not wait for in-flight memory ops) |
| `2e1ae642` | Reserve MSHR for pending primary miss | **I-44** (ListBuffer pool exhaustion, duplicate refill) |
| `d0c8ba1a` | Bound L2 directory flush indices | **I-35** (flushCount stuck at 1024) |
| `ed6fb9d1` | Align I-cache response metadata with valid | **I-30** (flush/invalidate response metadata disorder) |
| 2026-08-18, `fix(l2) order dirty victim writeback before refill` | Dirty-victim writeback ordering | **I-43** (drb-full drops dirty victim writeback) |

In addition, commit `862db08d` ("gate L2 bypass reads on victim capacity")
relates to the **LFSR bypass family** (I-23 / I-29 / I-40); we count it as
family-level corroboration, not as an additional finding-level fix.

## Implications

1. The findings are real: eight were important enough for the upstream authors
   to fix independently on their development branch.
2. The findings remain the status quo on the `master`/release line that we
   verified (snapshot `6811725`).
3. The upstream fixes address the defects at their own design level; our
   fixes (not part of this release — repair is outside the paper's
   bug-discovery scope) are validated differently — machine-checked
   efficacy and regression-safety proofs on the fixed model, plus patched-RTL
   regression (`repro/RESULTS.md`).

## Caveat

The entry-by-entry reconciliation between our finding registry and the full
develop-branch change list is an open task; the mapping above covers the
clear correspondences only. Commit subjects above are paraphrased from the
upstream log; see the per-finding reports (`doc/bugs/I-*.md`, §6 "upstream
impact") for the detailed comparisons.
