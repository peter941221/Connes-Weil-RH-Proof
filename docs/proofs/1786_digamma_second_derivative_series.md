# 1786 — Second derivative of the quarter-line digamma series

Date: 2026-09-21

## Result

The declaration `hasDerivAt_digamma_deriv_of_re_ge_quarter` proves, on the
strict quarter half-plane, that the derivative of `deriv Complex.digamma` is
the explicitly convergent series

`sum_n (-2) * (z + n)^(-3)`.

The proof differentiates the reciprocal-square series term by term. A cubic
quarter-plane majorant is obtained from the existing square majorant, and the
real-frequency-independent summability condition is discharged before the
series derivative theorem is applied.

## Verification and scope

The focused build completed successfully in 3539 jobs. The paired Audit
reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`.

This is formal interface evidence for the second-order scattering-factor
assembly. It does not prove the W2,1 product estimate, the S3
kernel-diagonal majorant, semi-local positivity, or RH. It is a project
derivation based on the existing digamma series; no priority claim is made.
