# 1444 — R3 scalar endpoint lower bound

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 alternating-power endpoint.

## Result

For every carrier vector `v` and stage `n`, the intersection projection is
fixed by the alternating power and the projection is contractive. Therefore

```text
||r_b v|| <= ||T_b^n v||.
```

Taking the infimum over the natural-number stages gives the exact lower half
of the scalar endpoint comparison:

```text
||r_b v|| <= ciInf_n ||T_b^n v||.
```

Combined with record 1443, the unresolved no-gap statement is now only the
reverse scalar inequality `ciInf_n ||T_b^n v|| <= ||r_b v||`. Equivalently,
the remaining task is to prove exhaustion of the scalar norm drop, or zero
Fejer distance to the intersection projection; no vector-limit ambiguity is
left.

## Formal declarations

The paired audited leaf adds:

* `doubledShiftAlternatingProduct_pow_norm_projection_le`;
* `doubledShiftAlternatingProduct_pow_norm_projection_le_ciInf`.

## Acceptance

The focused audit build log
[`024_projection_lower_bound_try3.log`](/home/peter/rh/build-logs/024_projection_lower_bound_try3.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and forty standard `Quot.sound` entries.
