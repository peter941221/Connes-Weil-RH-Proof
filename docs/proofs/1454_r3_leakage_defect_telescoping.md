# 1454 — R3 leakage defect telescoping

**Date:** 2026-09-14.

**Classification:** FORMAL structural bridge; no sign, trace, or RH claim.

## Consumer and scope

This brick serves the healthy-`CompactLog`, B5-shaped same-owner consumer
`0 <= C1SameOwnerWeil.qw g`.  It consumes the exact doubled-shift defect from
1452 and the positive-contraction facts from 1453.  It does not alter the
route choice or promote the R3 trace witness.

## Machine result

On the finite-S carrier, with `p_b` the doubled-shift radial projection and
`T_b = p_b * q_1 * p_b`, Lean verifies:

```text
p_b * T_b^(n+1) = T_b^(n+1)
T_b^(n+1) * p_b = T_b^(n+1)

(p_b - T_b) * T_b^(n+1) = T_b^(n+1) - T_b^(n+2)
T_b^(n+1) * (p_b - T_b) = T_b^(n+1) - T_b^(n+2).
```

The applied-vector form of the left identity is also present.  The proof is
only associativity, projection absorption, and the two orientations of the
power-successor identity; no analytic estimate is hidden in it.

## Evidence

Focused build:

```text
/home/peter/rh/build-logs/1454_leakage_defect_telescoping_try3.log
Build completed successfully (3283 jobs).
error: 0
sorryAx: 0
Quot.sound] audit terminators: 5
```

The unified 16-target R3 batch also passed:

```text
/home/peter/rh/build-logs/1454_r1_unified_batch.log
Build completed successfully (3291 jobs).
error: 0
sorryAx: 0
Quot.sound] audit terminators: 98
```

The remaining obligation is concrete: estimate the selected root applied to
the step differences, with the source translation conjugation retained.  A
bounded telescoping identity alone is not an HS or trace-class theorem.
