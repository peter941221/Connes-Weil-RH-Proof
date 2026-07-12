# 030 Xi-Nullspace Prime-Moment Deformation

Date: 2026-07-12

Status: exact compact-source version rejected by proof 110; noncompact
deformation retained only as analysis input.

## Objective

Preserve the canonical detector's complete zeta-zero value pattern and three
route vanishings while deforming prime-log autocorrelations through directions
divisible by `Xi(s)*s*(s-1/2)*(s-1)`.

## Execution order

1. Write the Fréchet derivative of finitely many autocorrelation moments at the
   quotient detector.
2. Test linear independence of those derivative rows on a finite translated
   family of Xi-kernel corrections.
3. Reject if one nontrivial linear dependence is forced by Xi symmetry.
4. If finite surjectivity survives, solve the nonlinear finite moment system.
5. Only then study uniform tail constants as the cutoff and visible-prime set
   grow.

The abstract derivative-row independence gate passes by the exponential-
polynomial identity argument. See proof 103. The active gate is nonlinear
reachability with controlled physical tails.

New death gate: a nonzero compactly supported log test has a finite-exponential
type Laplace transform and therefore only `O(T)` zeros in radius `T`, whereas a
function divisible by completed Xi has `Theta(T log T)` nontrivial zeta zeros.
Thus exact `Xi*R*A` null directions cannot themselves be compact source tests.
Proof 110 rejects the exact compact version. Any noncompact deformation followed
by cutoff loses exact zero preservation and must pay a new quantitative
prime/tail error; do not treat the derivative-row result as a route owner.

## Forbidden shortcut

Do not assume an arbitrary entire interpolation function `A` with controlled
exponential type. Its type and physical tail are the main analytic content.
