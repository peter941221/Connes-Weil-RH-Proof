# 1433 — R3 endpoint fixed vectors and finite-stage bound

**Date:** 2026-09-14
**Evidence class:** FORMAL LOWER-DATA BRICK.
**Consumer:** the healthy-`CompactLog`, B5-shaped detector-specific statement
`0 <= C1SameOwnerWeil.qw g`.

This brick advances the weighted two-projection route without asserting a
spectral gap, a trace limit, detector positivity for `qw`, or RH.

## 1. Fixed-point geometry

For the doubled-shift radial projection `p_b` and the unit-scale Fourier
projection `q`, the endpoint operator is `T_b = p_b q p_b`.  The formal
intersection is the infimum of the two closed subspaces.  Directly from the
star-projection fixed-point characterization:

```text
v in Ran(p_b) intersect Ran(q)  ->  T_b v = v
                           ->  T_b^n v = v for every n.
```

The Lean declarations are
`doubledShiftAlternatingProduct_fixed_of_mem_intersection` and
`doubledShiftAlternatingProduct_pow_apply_of_mem_intersection`.
This is an exact identification of the endpoint eigenspace, not an
approximate-eigenvector or numerical claim.

## 2. Contraction-stage bound

The same module proves, for every bounded operator `T` with `||T|| <= 1`,

```text
||T^n|| <= 1
||weightedCommutatorStage T D n|| <= n * ||[T,D]||.
```

The proof is a norm induction using the exact recurrence already proved in
1432.  No spectral theorem, angle gap, trace-class shortcut, sign assumption,
`SourceRH`, or external dictionary is used.

## 3. Honest R3 judgment

This closes a finite-stage endpoint obligation, not the endpoint limit.  The
linear estimate is deliberately recorded as insufficient: passing from
`T_b^n` to the intersection projection still requires a detector-weighted
trace-ideal estimate with summable decay.  Any future R3 completion must add
that decay as a proved source estimate; it may not relabel the present linear
bound as convergence.

## 4. Formal evidence

The owning module is
`ConnesWeilRH/Dev/C1G8R3WeightedFiniteStage.lean`, with paired audit
`C1G8R3WeightedFiniteStageAudit.lean`.  The batch build and its axiom
readback are:

```text
build-logs/1433_endpoint_fixed_stage_try4.log
Build completed successfully (3177 jobs).
^error: count = 0
sorryAx count = 0
15 audited declarations, all [propext, Classical.choice, Quot.sound]
```
