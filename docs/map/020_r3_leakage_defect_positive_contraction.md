# 020 — R3 leakage defect positive contraction

**Date:** 2026-09-14.

**Status:** formal structural/order brick; supporting route record, not an RH
claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Exact result

Write `b = log lambda`, `p_b` for the doubled-shift radial projection, and
`T_b = p_b * q_1 * p_b` for the unit-scale alternating product.  The new
audited leaf
`ConnesWeilRH/Dev/C1G8R3LeakageDefectOrder.lean` proves, on the actual
finite-S carrier, the exact identities

```text
D_b := p_b - T_b
    = p_b * (1 - q_1) * p_b
    = ((1 - q_1) * p_b)† * ((1 - q_1) * p_b).
```

Consequently the defect is positive and is ordered by

```text
0 <= D_b <= p_b <= I.
```

The leaf also proves `||D_b|| <= 1` and the exact quadratic-form identity

```text
re <v, D_b v> = ||(1 - q_1) p_b v||^2.
```

Thus the open leakage input is now a genuine complementary-Fourier energy,
not only a difference of two moving operators.

## 2. Energy consumer and boundary

Because `D_b` is a contraction, postcomposition by it cannot increase a
Hilbert--Schmidt column square-sum.  The same leaf instantiates this for the
already-controlled unit-scale `sourceRootCompletedRangeLeftLeg`.  This is a
real detector-weighted energy bound on the named carrier and basis.

It does not prove that the original leakage leg `C_g D_b` is Hilbert--Schmidt:
boundedness of `D_b` is not Hilbert--Schmidt smoothing, and the selected root
`C_g` remains a whole-line Fourier multiplier.  The same-basis signed trace
witness and the common-right finite-Euler leg remain open.  The next analytic
step must either supply a kernel/commutator estimate for `C_g D_b` or produce
a typed no-go showing that the bulk part of `D_b` prevents such an estimate.

## 3. Acceptance

Focused acceptance is `build-logs/1453_leakage_defect_order_try5.log`:
`Build completed successfully (3282 jobs)`, zero `error:` lines, zero
`sorryAx`, and nine audited declarations with only
`[propext, Classical.choice, Quot.sound]`.  The 14-target unified batch
`build-logs/1453_r1_unified_batch.log` also passed:
`Build completed successfully (3289 jobs)`, zero `error:` lines, zero
`sorryAx`, and 93 `Quot.sound]` audit terminators.
