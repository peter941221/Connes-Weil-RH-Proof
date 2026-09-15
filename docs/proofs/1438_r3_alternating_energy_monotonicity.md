# 1438 — R3 alternating energy monotonicity

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint trace bridge.

## Result

The power-bridge leaf now proves for the actual operator `T_b = p_b q p_b`
on `finiteSCarrier`:

```text
||T_b v|| <= ||v||,
||T_b^n v|| <= ||v||,
n |-> ||T_b^n v|| is antitone,
||T_b^n v|| -> inf_n ||T_b^n v||.
```

The final convergence is the order-theoretic monotone-convergence theorem
for real scalar energies. No spectral gap, operator-norm convergence,
trace-class input, detector sign, `SourceRH`, or external trace formula is
used.

For vectors in the radial subspace the same leaf proves the exact identity

```text
||v||^2 - ||T_b v||^2
  = ||(Ran(p_b))^perp projection of q v||^2
    + ||(Ran(q))^perp projection of v||^2.
```

This is obtained by applying Mathlib's Pythagorean projection identity first
to `q` and then to `p` on `q v`; it is an equality, not a norm estimate.

## Why this matters

Together with [1437](1437_r3_actual_fixed_space_identification.md), the
endpoint problem is sharpened: the fixed vectors are already known exactly,
and the scalar orbit energy cannot oscillate or grow. The remaining
angle-free theorem must show that the limiting vector defect is zero and that
the resulting vector endpoint is `r_b v`; scalar monotonicity alone does not
provide that identification.

## Acceptance

The paired audit build log
[`017_energy_defect_try4.log`](/home/peter/rh/build-logs/017_energy_defect_try4.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and seventeen standard `Quot.sound` entries.
