# 025 Canonical Xi-Quotient Detector Plan

Date: 2026-07-12

Status: research candidate with current-owner death gate (2026-07-12). The
finite-codimension rescue is mathematically plausible, but the repository's
`SourceTestAlgebra` has no linear-combination owner and its only concrete
carrier uses Mellin-invalid additive convolution. See proofs 083-085.

## 1. Target

Replace the rejected fixed-window Yoshida radius/count assembly by one
canonical noncompact detector whose transform already vanishes at every
non-target zero, then approximate that detector by compact tests with one
summable error estimate.

```text
route obligation:
  construct a genuine same-test CC20 detector below the RH exit

old weak path:
  interpolate zeros in a radius R, obtain a later tail threshold T_R, and
  require the unproduced fixed point R >= (n_R+1)T_R

new mathematical owner:
  completedRiemannXi divided by the full symmetry orbit polynomial of one
  hypothetical off-line zero, followed by finite orbit interpolation

consumer to rewire:
  none until the compact cutoff, zero-sum sign, and source-domain gates pass

forbidden circular inputs:
  SourceRH, RiemannHypothesis, Weil positivity, detector coverage, all zeros
  real, an assumed compact approximation theorem, or stored zero-sum sign

smallest verification target:
  an analytic quotient-and-tail theorem outside the route API

focused axiom audit:
  only after the mathematical gates close
```

## 2. Candidate

Assume a source nontrivial zero `rho` with `rho.re != 1/2`. Let `O(rho)` be
its finite orbit under

```text
s -> 1-s,
s -> conjugate(s).
```

Let `m_z` be the analytic order of `completedRiemannXi` at `z` and define

```text
P_rho(s) = product_(z in O(rho)) (s-z)^(m_z),
H_rho(s) = completedRiemannXi(s) / P_rho(s).
```

The intended theorem is that `H_rho` extends to an entire function, is nonzero
on the removed orbit, and still vanishes at every source zero outside that
orbit. A finite polynomial `R_rho` then assigns the orbit values required by
the negative finite Weil direction. Multiplication by the route polynomial
adds the three required vanishings without changing the zero set outside the
orbit.

The inverse centered Mellin/Fourier transform is the canonical noncompact
half-density. Its compact cutoff, not finite zero interpolation, is the final
test.

## 3. Why This May Remove The Old Cycle

The old construction learned about other zeros only through an expanding
finite interpolation set. The new numerator is Xi itself:

```text
source zero z outside O(rho)
  -> completedRiemannXi(z)=0
  -> H_rho(z)=0 exactly.
```

After cutting the physical-space half-density at radius `A`, every zero error
comes from the same physical tail. Derivative integration by parts should give

```text
|error_A(sigma+it)| <= C_(A,N) / (1+|t|)^N,
sup_(sigma in [0,1]) C_(A,N) -> 0.
```

The existing source-zero counting/summability theorems can consume this bound.
There is no separately chosen nearby radius and no later threshold that must
fit back inside it.

## 4. Rejection-First Gates

### Gate X1. Entire orbit quotient

Prove the finite orbit, multiplicity transport under both symmetries, exact
divisibility, and nonzero quotient values on the removed orbit.

Reject if the project Xi normalization lacks the required conjugation or
functional-equation symmetry on the same object.

Convention update (2026-07-12): in the centered coordinate `u=s-1/2`, the
additive involution `u -> -conjugate(u)` is exactly the source symmetry
`s -> 1-conjugate(s)`. The symmetry gate survives, but the current raw
`logPullbackRaw` omits the half-density factor and cannot own this quotient.
See proof record 076.

### Gate X2. Inverse-transform tail

Construct the inverse centered transform of `R_rho H_rho`. Prove uniform
two-sided decay, including derivatives, strong enough for prime translations
and the source zero sum.

The key mechanism to test is division by one zero factor. If `Phi` is the Xi
kernel and its transform vanishes at `z`, the ODE solution for division by
`s-z` should use the vanishing moment to cancel the homogeneous exponential
tail. Iterate only after the one-factor estimate is proved.

Reject if division leaves an exponential tail outside the common Weil/QW form
domain or makes the finite-prime series diverge.

Initial reduction (2026-07-12): after setting
`psi(x)=exp(x/2)*completedRiemannXiKernel(exp(2x))`, the theta functional
equation makes `psi` even. Its first derivative has jump `-1` at zero, so the
distributional second derivative contributes `-delta_0`; the `+1` in the
project Xi normalization contributes `+delta_0` and cancels it. The centered
Xi inverse is therefore the ordinary function `psi''-psi/4`. Division by one
zero factor has a two-sided tail formula whose two branches agree by the zero
moment. See proof record 075. Named derivative bounds and orbit iteration
remain open.

Tail update (2026-07-12): the centered theta series gives every derivative of
the Xi inverse the bound
`poly(exp(2*|x|))*exp(-c*exp(2*|x|))`. The one-factor division ODE and the two
zero-moment tail formulas preserve this class; finite orbit multiplicity
iteration is therefore finite and uniform for each hypothetical `rho`. See
proof record 081. The remaining work is termwise derivative justification and
packaging the weighted transform bound.

### Gate X3. Compact cutoff with summable zero error

For a smooth cutoff `chi_A`, prove that the cutoff transform converges at all
source zeros with one summable majorant. The required conclusion is a strict
negative zero sum for one sufficiently large finite `A`, not merely pointwise
or compact-open convergence.

Reject if the cutoff constants cannot be made small uniformly in the closed
critical strip or if the zero sum cannot interchange with the cutoff limit.

Reduction update (2026-07-12): repeated integration by parts turns weighted
physical derivative tails into `C_(A,N)*(1+|t|)^(-N)` uniformly across the
closed centered strip. Since the exact quotient vanishes at every non-target
zero, the square contribution is quadratic in this error and is consumed by
the existing zero-count summability layer. Apply the route polynomial as a
constant-coefficient differential operator after cutoff to retain exact triple
vanishing. See proof record 078. The required weighted derivative bounds are
still to be proved from the theta kernel.

### Gate X4. Square, triple vanishing, and support owner

Choose the finite orbit values so the convolution square has the negative
off-line finite Weil direction. Add the route polynomial/Q-root without
mixing different witnesses. Prove compact support after cutoff and preserve
the strict sign margin.

Reject if Hermitian symmetry forces a nonnegative orbit contribution or if
the triple-vanishing operator kills the target orbit value.

Finite algebra update (2026-07-12): the centered four-point orbit has an
explicit negative square-value pattern, and multiplication by
`u*(u^2-1/4)` adds the three route zeros without vanishing at a nontrivial
off-line orbit. See proof record 077. The analytic quotient and cutoff sign
limit remain open.

### Gate X5. Lower consumer (rescued, new finite-codimension gate)

Audit the exact source consumer before any route API. Either:

```text
the canonical detector lies in a source-backed sign domain strictly below RH,
```

or the candidate is only another proof of the converse Weil criterion and
does not lower an active root.

Reject route execution if the only available sign premise is full Weil
positivity, SourceRH, or the rejected M5B detector contract itself.

Joint-separation update (2026-07-12): translation of the quotient inverse gives
orbit rows `H(u_i) exp(c*u_i)`, while compact bad-space rows decay in the
translation parameter. Analytic continuation and two-sided translation tails
therefore prove algebraic independence before cutoff. The remaining X5 gate is
quantitative stability after cutoff when the M4 space itself depends on the
cutoff interval; see proof record 080. The new consumer is not standalone Weil
positivity: for one fixed interval, impose the finite `B_I` orthogonality rows
on the same quotient cutoff and apply the `-2 Id + K_I` sign. The exact
same-square source bridge remains open. See proof record 083.

The smallest current subgate is finite joint functional separation on one
fixed interval: three Mellin rows, four orbit rows, and a basis of `B_I` must be
independent on the same smooth compact source algebra. The abstract linear-dual
argument and the repository's finite-window interpolation pattern pass, while
same-owner closure remains open. See proof record 084.

Current owner verdict: rejected until a genuine multiplicative, linearly closed
source test carrier is supplied. Do not treat the existing additive concrete
carrier as a placeholder; `not_normalizedCC20MellinConvolutionLaw` is an exact
countertheorem. See proof record 085.

### Gate X6. Lean owner

Only after X1--X5 pass, add the smallest data-bearing owner and an
import-facing `#check/#print/#print axioms` audit. No conclusion may be stored
as a field.

## 5. Existing Infrastructure

The repository already contains:

```text
completedRiemannXi and differentiability
completedRiemannXi_one_sub
finite analytic order and divisor support
completedRiemannXiKernel with explicit two-sided exponential bounds
source zero counting and summability consumers
compact log convolution and finite Mellin interpolation
```

The missing bottoms are quotient divisibility with symmetry multiplicities,
the inverse-transform division estimate, and the same-test compact cutoff
zero-sum limit.

## 6. Sources

```text
Burnol, The Explicit Formula in Simple Terms, arXiv:math/9810169,
  pp. 4-5: Weil's converse first builds a bad direction in a larger test
  class and then obtains compactly supported tests.

Suzuki, Weil's quadratic form via the screw function, arXiv:2606.09096,
  Theorems 1.1-1.5 are unconditional; Corollary 1.6 remains a conjectural
  compact-open limit and is not used as a producer.

Freedman, Finite-core Volterra reductions for a Weyl-positive Riemann phase
  kernel, arXiv:2606.29555: normalized quotient certificate only; external
  Weyl lift, uniform parameter coverage, and de Branges/RH bridge remain.
```

## 7. Decision Rule

```text
X1 or X2 fails:
  reject the canonical quotient before implementation.

X3 fails:
  classify whether the failure is another radius/count cycle.

X1-X4 pass but X5 fails:
  retain a new detector theorem, but do not call it an RH route.

X1-X5 pass:
  begin the minimal Lean producer and re-audit the route dependency graph.
```
