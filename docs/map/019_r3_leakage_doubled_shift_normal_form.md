# 019 — R3 leakage doubled-shift normal form

**Date:** 2026-09-14.

**Status:** formal structural brick; supporting route record, not an RH
claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Exact result

The independent source leakage leg is now rewritten on the same finite-S
carrier as a conjugated doubled-shift projection defect.  The audited
declaration is
`sourceRootCompletedRightCommutatorLeftLeg_eq_translated_doubledShift_defect`
in `ConnesWeilRH/Dev/C1G8R3LeakageDoubledShift.lean`.

With `b = log lambda`, `U_b` the global-log translation, `C_g` the selected
root convolution, `p_b` the doubled-shift radial projection, and `T_b` the
alternating product, its content is the exact operator identity

```text
sourceRootCompletedRightCommutatorLeftLeg owner lambda
  = U_b * C_g * (p_b - T_b) * U_(-b).
```

Here the displayed `*` is composition of continuous linear endomorphisms.
The proof uses only:

- the source root leakage factorization `C_g * E_lambda * (1-Q_lambda) * E_lambda`;
- exact radial and Fourier-support scale conjugations;
- the zero Hardy-translation defects already proved in the R3 branch;
- translation covariance of the selected root; and
- the unit-scale identity `T_b = p_b * Q_1 * p_b` after the doubled shift.

The proof is therefore an algebraic normal form, not a positivity estimate,
Hilbert--Schmidt assertion, or trace-class conclusion.

## 2. What this changes

The leakage is no longer an unnamed moving-cutoff expression.  A future
estimate can target the concrete defect `p_b - T_b` and use the already formal
no-gap power limit for `T_b` from [017](017_r3_no_gap_alternating_power_limit.md).
The root remains a whole-line Fourier multiplier and is not declared
Hilbert--Schmidt.  The unit-scale prolate-range leg from [018](018_r3_unit_detector_root_square_sum.md)
is still a separate factor; the common-right finite-Euler leg and the
same-basis signed trace witness remain open.

The structural identity does not provide the missing detector-selected
semi-local sign.  Its next order-theoretic consumer is now formal in
[020](020_r3_leakage_defect_positive_contraction.md): the defect is a positive
contraction with an exact complementary-leakage quadratic form.  That result
still does not reconnect the route to
`G8SameOwnerReadbackData` and does not imply `SourceRH`.

## 3. Acceptance

Focused acceptance is
`build-logs/1452_leakage_doubled_shift_try9.log`:
`Build completed successfully (3281 jobs)`, zero `error:` lines, zero
`sorryAx`, and three standard-axiom audit terminators for the four audited
declarations.
