> English translation of the Chinese master `doc/bugs/III-2-DecodeUnit简报事实错误.md`. Translated 2026-09-13.

# III-2 Lessons Record: Two factual errors in the DecodeUnit task briefing (corrected by agent-9)

| Item | Content |
|---|---|
| ID | III-2 (Class III: specification/proof-side error — specifically, factual errors in the **task briefing the main session gave to a subagent**) |
| Location | The DecodeUnit wave task briefing; concerns the BitPat decode tables of `ventus/src/pipeline/DecodeUnit.scala` and the semantics of chisel `ListLookup` |
| When found | DecodeUnit wave (corrected by agent-9) |
| Status | Corrected; agent-9's zero-shadowing result is accepted per the corrected conclusions |

---

## Background

One of the DecodeUnit wave's tasks was a **shadowing/dead-row audit** of the four BitPat decode tables (IMF/V/VL/VC): a BitPat is a pattern with wildcard bits (value + mask; bits with mask=1 are constraint bits), and when two rows "intersect" (there exists an input matching both rows), shadowing may occur (the earlier row blocks the later one, making the later a dead row). In the task briefing, the main session stated "factual" assertions about the intersection criterion formula and chisel's table-lookup semantics; both were wrong, and both were verified and corrected by agent-9.

## The problems

**Error 1: the BitPat intersection criterion formula was written wrong.** The briefing gave the criterion as:

```
(mA &&& mB &&& ~~~(vA ^^^ vB)) = 0     -- wrong
```

This formula tests "the two rows have no common constraint bits" (`~~~(vA^^^vB)` picks the bits where the values are **identical**) — the semantics are exactly inverted. The **correct criterion** is:

```
(mA &&& mB &&& (vA ^^^ vB)) = 0        -- correct: no conflict in value on commonly constrained bits
```

That is: for each bit, if both rows constrain it (mA&mB=1) and the values differ (vA^vB=1), then no input matches both rows and the two rows are mutually exclusive at least at this bit; only when no bit has a conflict do the rows intersect. Using the wrong formula would misjudge almost all row pairs as intersecting — the conclusions of the entire shadowing audit would be wholesale inverted.

**Error 2: the tooling assumption "espresso minimization; intersection means non-deterministic decode" does not hold.** The briefing assumed chisel's `ListLookup` goes through espresso minimization, so intersecting BitPats would cause non-deterministic decode (hence "disjointness" is a necessary condition for correctness). In fact [tooling verification]:

- chisel's (6.4.0 and 7.x) `ListLookup` is an **element-wise MuxCase with first-match priority** — a deterministic shadowing semantics; decode determinism **does not depend** on disjointness;
- espresso has been removed since chisel 3.5; the "minimization" premise itself no longer exists;
- therefore the real value of a disjointness audit is "**no shadowing / no dead rows**" (every row is reachable, no row is blocked by an earlier row), not "guaranteeing determinism".

## Evidence

- [Direct source reading] The repository's pinned chisel version: `build.sc:32` (`"6.4.0" -> ivy"org.chipsalliance::chisel:6.4.0"`). agent-9's bytecode verification was based on 7.0.0-RC1 in the local coursier cache; the conclusion holds equally for 6.4.0 (espresso has been removed since chisel 3.5, consistent across versions).
- [Lean machine-checked proof] Per the corrected semantics, agent-9's zero-shadowing result is accepted: the four tables' BitPats are pairwise disjoint — `dec_overlap_imf` / `dec_overlap_v` / `dec_overlap_vl` / `dec_overlap_vc` (`lean/Ventus/Arith/DecodeUnit.lean:486-489`, all `by native_decide`). Four tables pairwise disjoint ⇒ match order irrelevant ⇒ the model's first-match semantics is equivalent to the hardware (first-match semantics loses nothing in equivalence).
- Related output: see the "incidental conclusions" of doc/03's I-16 entry (no shadowing, no dead rows; illegal instructions landing on the default row is intentional; the FN≥32 low-5-bit truncation collisions were discharged one by one as harmless).

## Lessons

1. **A briefing is not a proof-free zone.** "Factual" content given to subagents (bit-manipulation formulas, upstream tool semantics) can also be wrong; subagents should **verify before using** factual assertions in briefings, and refutation feedback is a necessary line of defense — had the two errors in this case been taken at face value, the DecodeUnit full-table audit's conclusions would have been wholesale wrong (intersection/disjointness inverted + the determinism conclusion losing its basis).
2. **When writing briefings, mark a confidence level or attach a verification path for facts that "seem obviously true".** Error 1's formula was a bit manipulation written from memory, missing one layer of negation-semantics checking; Error 2's espresso assumption came from an outdated impression of older chisel.
3. **Tool-semantics conclusions must be anchored to the repository's pinned version** (this repo's build.sc:32 = chisel 6.4.0). Other versions in the local cache can only corroborate "the conclusion holds across versions"; they cannot replace verification against the target version — this case happened to be consistent across versions, which must not be taken as the norm.
4. The wording of audit conclusions must align with the semantic evidence: the correct corollary of zero shadowing is "no dead rows + match order irrelevant", not "decode is deterministic" (determinism is unconditionally provided by the MuxCase first-match semantics).

## Conclusion

| Evidence layer | Content | Strength |
|---|---|---|
| Direct source reading | build.sc:32 pins chisel 6.4.0 | Verified verbatim |
| Tooling verification | ListLookup = MuxCase first-match priority (agent-9, based on 7.0.0-RC1 bytecode; the conclusion holds equally for 6.4.0: espresso removed since chisel 3.5) | Consistent across versions |
| Lean machine-checked proof | dec_overlap_imf/v/vl/vc (DecodeUnit.lean:486-489, native_decide) — zero shadowing in all four tables | Full-table enumeration level |

III-2 is a corrective case for the "briefing trust base": factual assertions the main session gives to subagents can also be wrong, and the subagent's verify-before-use plus refutation feedback intercepted two errors that would have inverted the full-table audit's conclusions. The lesson has been merged into the subagent delegation discipline (briefing facts carry confidence levels / verification paths).
