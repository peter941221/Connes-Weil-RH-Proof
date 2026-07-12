# 031 Xi Rational-Pole Cancellation

Date: 2026-07-12

Status: direct absolute-prime-control version rejected (proof 106). Retain only
as a component if a lower structured prime cancellation theorem is found.

## Objective

Use entire Paley--Wiener approximants to cancel the rational quotient on the
critical line while Xi divisibility preserves every zeta-zero value exactly.

## Execution order

1. Prove exponential Fourier decay for the centered rational function
   `S/P_rho` from the off-line distance `delta`.
2. Construct compactly supported inverse-Fourier truncations `A_T` and weighted
   Sobolev convergence of `A_T` to `-S/P_rho`.
3. Multiply by the centered Xi kernel and route polynomial; prove the resulting
   physical tails and form-domain bounds.
4. Add finite M4 bad-space orthogonality constraints without losing weighted
   convergence.
5. Prove full QW continuity, including prime/pole terms, in the selected
   topology.
6. Only after all five gates pass, consider a Lean route owner.

## Cheap death gate

If the full Weil/prime functional is not continuous in any topology produced by
the rational Paley--Wiener approximation and Xi-kernel tails, reject the plan.

The first tail gate passes by explicit partial fractions: inverse Fourier terms
are one-sided polynomial-exponentials with rate at least `delta`. See proof 105.

The full-prime gate fails under absolute estimates: squared approximation error
decays as `exp(-2 delta T)` while visible Weil prime weight grows as
`exp(T/2)`. No decay is obtained for `delta <= 1/4`. See proof 106.
