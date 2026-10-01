# 2355 - Same-owner consumer integration audit after the rewrite repair

日期：2026-10-01。

## Result

HEAD `f9809767` contains the intended repair for the two rewrite failures
reported by record 2354:

* the `Finset.sum_sdiff` identity is rewritten in the reverse direction;
* `spectralWeilValue` is unfolded before the source-shell split rewrite.

The repair is directionally correct, but this record does **not** claim that
the full consumer builds. A WSL replay found Lean/Lake, then stopped before
the theorem check because the existing Mathlib checkout has local changes.
No project source was changed by the replay.

Observed blocker:

```text
mathlib: repository
/mnt/c/Projects/Connes-Weil-RH-Proof/.lake/packages/mathlib has local changes
```

The direct Lean fallback also cannot establish the result because the cached
project dependency `C1HealthyYoshidaClosedPrefix.olean` is absent. Therefore
the correct status remains `CONSUMER-INTEGRATION-UNVERIFIED`, not PASS and not
a new mathematical failure.

## Scope boundary

This audit does not alter the same-owner tail supplier, the scalar acceptance
lanes, the selected detector, the signed physical-kernel gate, or map 103.
It does not remove or overwrite the Mathlib working-tree changes.

## Required next replay

Run the full consumer build in a clean, project-compatible Lean environment
with the existing Mathlib changes preserved or separately isolated. The
authoritative pass condition is the original consumer file completing at the
two repaired sites, followed by the permitted-axiom audit. Until then,
2354's scalar-only and consumer-open status remains binding.
