# 1434 — Strong endpoint convergence transfers through an HS detector root

**Date:** 2026-09-14
**Evidence class:** FORMAL LOWER-DATA ANALYTIC BRICK.
**Consumer:** the healthy-`CompactLog`, B5-shaped detector-specific statement
`0 <= C1SameOwnerWeil.qw g`.

## Result

For a Hilbert--Schmidt detector root `C`, operators `A_a`, and a candidate
endpoint `A`, the new theorem proves:

```text
 A_a(C e_i) -> A(C e_i) for every basis column i
 sup_a ||A_a|| <= 1, ||A|| <= 1
 sum_i ||C e_i||^2 < infinity
 ------------------------------------------------
 sum_i ||(A_a - A)(C e_i)||^2 -> 0.
```

The proof is a dominated-convergence argument for the basis series.  The
majorant is `4 * ||C e_i||^2`; it comes only from the two contraction bounds.

## R3 meaning

This is the first formal theorem that turns the proposed detector smoothing
into an endpoint convergence mechanism without assuming an operator-norm
gap.  It reduces one part of R3 to the strong endpoint theorem for the
doubled-shift two-projection product:

```text
 (p_b q p_b)^n  ->  r_b strongly.
```

That strong convergence is not proved here.  Nor is the final signed trace
identity or G8 readback.  Therefore R3 and RH remain open.

## Formal evidence

Owning module: `ConnesWeilRH/Dev/C1G8R3WeightedStrongToHS.lean`.
Paired audit: `C1G8R3WeightedStrongToHSAudit.lean`.
Grouped acceptance:

```text
build-logs/1434_strong_to_hs_try6.log
Build completed successfully (3179 jobs).
^error: count = 0
sorryAx count = 0
1 audited declaration, [propext, Classical.choice, Quot.sound]
```
