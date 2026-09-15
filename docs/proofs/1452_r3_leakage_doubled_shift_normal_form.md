# 1452 — R3 leakage doubled-shift normal form

**Date:** 2026-09-14

**Consumer:** healthy-`CompactLog`, B5-shaped same-owner positivity
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

## Result

The R3 source leakage leg now has an exact operator normal form on the actual
`finiteSCarrier`.  For `b = log lambda`, write `U_b` for global-log
translation, `C_g` for the selected root convolution, `p_b` for the doubled-
shift radial projection, and `T_b = p_b * q_1 * p_b` for the alternating
product.  The landed theorem is

```text
sourceRootCompletedRightCommutatorLeftLeg owner lambda
  = U_b * C_g * (p_b - T_b) * U_(-b).
```

The source theorem first gives the left side as

```text
C_g * E_lambda * (1 - Q_lambda) * E_lambda.
```

The proof then uses the exact identities

```text
E_lambda = U_(-b) * P_0 * U_b
Q_lambda = U_b * Q_1 * U_(-b)
p_b      = U_(-2*b) * P_0 * U_(2*b)
```

and the translation covariance

```text
C_g * U_a = U_a * C_g.
```

The remaining calculation is composition algebra: translation parameters add,
`P_0` is idempotent, and the two `U_b` factors turn the middle term into
`T_b`.  Lean checks each cancellation and the subtraction expansion on the
operator algebra; no numerical premise is used.

## Boundary

This is a structural identity only.  It does not say that `C_g` is
Hilbert--Schmidt, does not estimate `p_b - T_b`, and does not provide a
same-basis signed trace witness.  The common-right finite-Euler leg and the
reconnection to `G8SameOwnerReadbackData` remain open.  Consequently R3 sign,
`SourceRH`, and RH are not claimed.

The raw convolution root remains deliberately outside the HS-factor claim:
the source module treats it as a whole-line Fourier multiplier.  The legal
unit-scale prolate-range factor is the separate object closed in record 1451.
## Lean audit

Implementation and paired audit:

- `ConnesWeilRH/Dev/C1G8R3LeakageDoubledShift.lean`
- `ConnesWeilRH/Dev/C1G8R3LeakageDoubledShiftAudit.lean`

Focused acceptance:

```text
build-logs/1452_leakage_doubled_shift_try9.log
Build completed successfully (3281 jobs)
error: 0
sorryAx: 0
Quot.sound] terminators: 3
```

The audit output for all four declarations contains only
`[propext, Classical.choice, Quot.sound]`.
