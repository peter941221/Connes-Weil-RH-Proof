# 1808 — C3' even/odd opposite-sign branch

Date: 2026-09-22.

Status: FORMAL route brick complete. The detector-specific C3' sign and RH
remain open.

## Result

For an even test `f` and an odd test `g`, the complete cross gate is zero.
If the even square has positive gate and the odd square has negative gate,
then the two-span determinant is strictly negative. The generic finite-span
quadratic consumer consequently supplies a real coefficient `lam` for which
the two-span gate quadratic form is nonpositive.

The Lean declarations are:

```text
twoSpan_discriminant_neg_of_even_odd_opposite_sign
exists_twoSpan_gate_qform_nonpos_of_even_odd_opposite_sign
```

The first theorem uses the formal cross cancellation and strict sign
arithmetic. The second transports the strict determinant inequality through
the existing symmetric discriminant consumer.

## Route meaning

This closes the opposite-sign algebraic branch of the parity decomposition.
It does not assert that the orbit-selected detector has opposite diagonal
signs, and it does not show that the quadratic-form witness still vanishes at
the three prescribed nodes or detects the hypothetical zero. Those are the
remaining detector-specific obligations. The prior positive-positive branch
is formally hostile because its determinant is strictly positive.

## Verification

Focused build log:
`/home/peter/rh/build-logs/1808_even_odd_opposite_sign_pass.log`

The build completed successfully with 3807 jobs, zero `error:` lines, zero
`sorryAx`, and audit declarations using only
`[propext, Classical.choice, Quot.sound]`.
