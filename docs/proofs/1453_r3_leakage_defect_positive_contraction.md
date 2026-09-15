# 1453 — R3 leakage defect positive contraction

**Date:** 2026-09-14

**Consumer:** healthy-`CompactLog`, B5-shaped same-owner detector positivity
`0 <= C1SameOwnerWeil.qw g`.

## Result

For the doubled-shift radial projection `p_b` and the unit-scale Fourier
support projection `q_1`, define `T_b = p_b * q_1 * p_b` and `D_b = p_b - T_b`.
The new Lean leaf
`ConnesWeilRH/Dev/C1G8R3LeakageDefectOrder.lean` proves

```text
D_b = p_b * (1 - q_1) * p_b
    = ((1 - q_1) * p_b)† * ((1 - q_1) * p_b).
```

It follows formally that `D_b` is positive and

```text
0 <= D_b <= p_b <= I,
||D_b|| <= 1.
```

For every carrier vector `v`, its quadratic form is exactly

```text
re <v, D_b v> = ||(1 - q_1) p_b v||^2.
```

The leaf also proves that postcomposition by `D_b` cannot increase the basis
Hilbert--Schmidt square-sum of any square-summable factor, and instantiates
that statement for the formal unit-scale `sourceRootCompletedRangeLeftLeg`.

## Interpretation

This is a genuine lower-data improvement: the leakage defect is now an
ordered complementary-Fourier energy and can be consumed by positive-trace
arguments without treating it as an arbitrary signed difference.

It is not the missing trace theorem.  In particular, `||D_b|| <= 1` does not
make `C_g D_b` Hilbert--Schmidt, because the selected root `C_g` is still a
whole-line Fourier multiplier.  The common-right finite-Euler leg and the
same-basis signed G8 readback remain open.  The next attack must prove a
genuine smoothing/commutator estimate for `C_g D_b`, or establish a typed
non-HS obstruction and revise the carrier/leg before claiming progress toward
R3.

## Lean acceptance

Focused log:
`build-logs/1453_leakage_defect_order_try5.log`

```text
Build completed successfully (3282 jobs)
error lines: 0
sorryAx lines: 0
Quot.sound] audit terminators: 9
```

The paired audit prints only `[propext, Classical.choice, Quot.sound]`.

The 14-target unified R3 batch
`build-logs/1453_r1_unified_batch.log` also passed with
`Build completed successfully (3289 jobs)`, zero `error:` lines, zero
`sorryAx`, and 93 `Quot.sound]` audit terminators.
