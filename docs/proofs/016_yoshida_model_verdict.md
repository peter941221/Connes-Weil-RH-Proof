# 016 Yoshida Model Verdict

Date: 2026-07-10

Result: rejected candidate producer. RH remains conditional.

The normalized CC20 test space cannot supply the Yoshida detector required by
the source Proposition C.1 route. Its local Weil sum is a negative pole
pairing, not a sum over nontrivial zeta zeros, and its convolution operation is
pointwise addition.

```text
route obligation:
  derive a strict source zero-sum sign from an off-line zero

old weak path:
  finite Mellin interpolation -> normalizedCC20TestSpace detector
  -> -polePairing local sum

new mathematical owner:
  a compact smooth multiplicative convolution algebra with the source zero sum

consumer to rewire:
  the M5B detector input to the final CC20 criterion

forbidden circular inputs:
  SourceRH, detector coverage, a stored strict local-sum sign,
  or a pole-pairing proxy for the zero sum

smallest verification target:
  ConnesWeilRH.Source.CC20YoshidaConstruction

focused axiom audit:
  not_normalizedCC20MellinConvolutionLaw
```

## Lean Evidence

`CC20ConcreteTestSpace.lean` defines the normalized operations as:

```lean
starConvolution := normalizedCC20ConcreteTestAlgebra.convolutionSquare
weilLocalSum := fun g => -normalizedCC20ConcreteEvaluationData.polePairing g
```

The underlying concrete algebra defines:

```lean
convolutionStar := fun f g => f + g
convolutionSquare := fun g => g + g
```

The declarations `NormalizedCC20MellinConvolutionLaw` and
`not_normalizedCC20MellinConvolutionLaw` formalize the mismatch. The latter
uses fixed-window interpolation to choose a test with Mellin value `1`.
The concrete operation gives the value `2` after its alleged convolution
square, while a convolution Mellin law gives `1`.

## Source Evidence

CC20 Appendix C states the actual Yoshida requirement. Its proof of the
reverse implication constructs a compact smooth `g_0` with finite vanishing,
`g_tilde(rho_0) = 1`, and

```text
|g_tilde(rho)| <= epsilon / |rho-rho_0|^2
for each other nontrivial zero rho.
```

Source: Connes and Consani, "Weil positivity and Trace formula the
archimedean place", arXiv:2006.13771,
https://arxiv.org/abs/2006.13771, `weil-compo.tex:2075-2085`.

Finite interpolation at the six repository nodes does not control this tail.
The source strict sign therefore remains unproved after M5A.

## Uniform Tail Layer

`CC20YoshidaTail.lean` now proves:

```text
exists_uniform_mellin_vertical_quadratic_decay
```

For a fixed compact-window test, this theorem gives one constant `C >= 0` for
all `sigma in [0,1]` and all vertical coordinates `t`. The proof writes the
Mellin transform as a Fourier transform, treats the log-slice as a joint
function of `(sigma,u)`, and bounds the first three vertical derivative
integrals on their common compact support.

This result supplies the far-zero decay layer.

`CC20YoshidaNearZeros.lean` proves that source nontrivial zeros in a closed ball
form a finite set. It also proves exact fixed-window Mellin interpolation on
any finite set of complex nodes. The nearby zeros and the route nodes can now
share one interpolation problem.

Appendix C still requires a normalized test family with a tail coefficient
below the requested `epsilon`. The current interpolation theorem sets finitely
many values but does not shrink the uniform far-tail constant. That coefficient
and the strict source zero-sum sign remain in M5B.

Yoshida's original Lemma 1 gives the coefficient-shrinking mechanism. It
convolves one base test `N` times and multiplies by finitely many correction
factors. Mellin transformation turns the convolution into
`Phi_0(s)^N * product_i Phi_i(s)`; the correction factors kill nearby zeros and
the power controls the remaining zeros. Source: Hiroyuki Yoshida, "On
Hermitian Forms attached to Zeta Functions," 1992, pp. 285-286,
https://projecteuclid.org/ebooks/advanced-studies-in-pure-mathematics/Zeta-Functions-in-Geometry/chapter/On-Hermitian-Forms-attached-to-Zeta-Functions/10.2969/aspm/02110281.pdf.

`CC20YoshidaConvolution.lean` now proves this transform product law and its
finite convolution-power form for the genuine compact log convolution. It also
defines the normalized compression `r^-1 f(x/r)`, proves its transform law
`Phi(s) -> Phi(r s)`, and proves that choosing `r=1/(N+1)` keeps the support of
`N+1` convolution copies inside the original base window. A second theorem
adds the finite correction factor and checks its residual support against a
prescribed outer window. The correction producer now realizes arbitrary finite
Laplace-node values in any residual window around zero and retains a uniform
quadratic strip-decay constant for the same correction. The remaining
construction must turn these ingredients into a same-index bound over every
far source zero and then prove the spectral explicit formula and strict sign.

The strip part of that same-index bound is now proved. After normalized
rescaling, the base contraction contributes `(1/2)^(N+1)` and the same finite
correction contributes its quadratic-decay constant. A closed-strip geometry
lemma gives the distance-weighted estimate around the selected zero, and an
epsilon theorem chooses enough convolution copies to make it arbitrarily
small. `sourceNontrivialZero_zero_lt_re` and
`sourceNontrivialZero_re_lt_one` now prove that every source spectral index is
inside the open critical strip; the apparent negative-integer branch is empty.
The strip zero-counting theorem, spectral explicit formula, and strict source
sign remain open.

The counting interface now matches the primary source. Hasanalizade--Shen--Wong
(arXiv:2107.06506, p. 3) defines the symmetric count `N-bar(T)` using
`0 < Re rho < 1` and `|Im rho| <= T`. Lean proves that every arbitrary-center
dyadic shell lies in the corresponding symmetric height window with threshold
`|Im rho| + 2^(n+1)`, and the spectral summability consumer accepts a dyadic
bound for this count directly. The Riemann--von Mangoldt estimate remains an
unformalized sufficient route, not a necessary premise; no counting theorem is
stored as a field or axiom.

The consumer still accepts the standard global shape
`N-bar(T) <= A*T*log(T) + C*T`, but that is no longer treated as necessary.
The sharp axiom-clean consumer accepts any shell bound `K*q^n` with
`0 <= q < 4`: quadratic pointwise decay makes the shell totals geometric with
ratio `q/4`. The Jensen layer constructs the entire xi, proves every source
nontrivial zero contributes to its finite-order divisor, and bounds the
distinct-zero cardinality by Mathlib's Jensen divisor sum.

The symmetric source height window is now proved to lie in the radius `T+2`
closed ball centered at `2`, and its cardinality is connected directly to the
Jensen sphere-bound theorem. The remaining growth proof can therefore be
stated entirely in terms of `completedRiemannXi`.

Choosing the outer radius `2*(T+2)` fixes the Jensen denominator at `log 2`.
The compiled consumer now carries a geometric sequence of such circle bounds
directly through Jensen to spectral summability. Xi's functional equation also
folds the estimate to `Re z >= 1/2`, with an additive radius cost of at most
one. The remaining count problem is one explicit subquadratic xi log-growth
estimate; a full Riemann--von Mangoldt asymptotic is sufficient but unnecessary.

The final compiled interface requires this majorant only on right-half-plane
balls. At level `n` the domain is `Re w >= 1/2` and
`norm(w) <= 2*(|Im rho| + 2^(n+1) + 2) + 3`. The functional equation and the
triangle inequality transport every Jensen-circle point into this ball, so no
separate left-half-plane or circle-parametrization estimate remains.

The xi producer is now connected to Mathlib's modified theta kernel. The
pole-removed completed zeta is exactly half the Mellin transform of
`(hurwitzEvenFEPair 0).f_modif`, and its norm is bounded by the corresponding
real Mellin moment at `Re s`. The kernel functional equation sends the small
interval to the same exponentially decaying theta tail above one. The only
remaining counting analysis is a quantitative growth bound for that real
moment; no complex Gamma/Stirling API is assumed.

The theta tail is now quantitative rather than asymptotic. For
`C_theta = 2/(1-exp(-pi))`, the kernel is bounded by
`C_theta*exp(-pi*t)` above one and by
`t^(-1/2)*C_theta*exp(-pi/t)` below one. These are direct consequences of
Mathlib's Jacobi-theta series estimate and the kernel functional equation.

The large-branch integral is now quantitative as well. For every natural
`n`, Lean proves

```text
integral_0_infinity t^n exp(-pi*t) dt
  = pi^(-(n+1)) * n!
  <= n^n.
```

The equality is Mathlib's real Gamma integral specialized at `n+1`; the
inequality uses `pi >= 2` and `n! <= n^n`. This supplies the required
`n*log n` logarithmic scale. What remains is the measure-theoretic split of the
kernel moment at one, the `t -> 1/t` transport for the small branch, and the
rounding of a general real Mellin parameter to an integer before connecting
the estimate to the compiled dyadic `q < 4` consumer.

## Final Route Verdict

The fixed-window 016 route is rejected as an executable proof route.

The current assembly has two independent producer failures.

First, interpolation belongs to the correction factor, not to the assembled
test. The compiled product law is

```text
Phi_assembled(rho)
  = Phi_base(rho/(n+1))^(n+1) * Phi_correction(rho).
```

Even when `Phi_correction(rho)=1`, the assembled value is zero whenever the
rescaled base value is zero. The axiom-clean rejection guard
`laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_zero_of_base`
formalizes this failure. No current theorem proves the required base factor is
nonzero or normalizes the full product to one at `rho`.

Second, the nearby/far split has an unclosed quantifier cycle:

```text
choose nearby radius R
  -> build a correction and obtain its decay constant C
  -> choose convolution count n from C
  -> far-tail estimate starts only above (n+1)*T.
```

Covering all zeros requires the original nearby radius to dominate the later
threshold, but no theorem proves `R >= (n+1)*T`, no uniform bound controls how
the correction constants grow with `R`, and no fixed-point argument supplies a
single successful choice. Consequently the existing near interpolation and far
estimate do not combine into the Appendix C test.

The narrow-support `qeasy` subroute does not repair these failures. Support can
be made arbitrarily narrow, but Corollary 3.8 only supplies a local remainder
sign after a valid positive-definite test exists. It does not construct the
missing global detector or close the radius/count cycle. Asking for the final
strict detector sign without these producers reaches the existing RH-level
criterion guards rather than a lower theorem.

This verdict rejects the current construction, not every conceivable
Connes--Weil strategy. Reopening requires a genuinely new theorem constructing
one compact test with full-product normalization at `rho` and a simultaneous
global all-other-zero bound, without consuming SourceRH, detector coverage, or
an equivalent no-off-line-zero premise.

## Route Consequence

M5A remains useful for its narrow-window finite-node interpolation and
finite-prime vanishing. It no longer qualifies as a detector producer.

M5B is rejected in its current assembled form. M5C, M6, route rewiring, and root
retirement are inactive because they have no valid detector input.

## Verification

The Windows snapshot passed these WSL ext4 targets:

```text
ConnesWeilRH.Source.CC20ConcreteTestSpace
ConnesWeilRH.Source.CC20YoshidaConstruction
ConnesWeilRH.Source.CC20YoshidaTail
ConnesWeilRH.Source.CC20YoshidaNearZeros
ConnesWeilRH.Source.CC20YoshidaConvolution
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaModelAudit
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaTailAudit
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaNearZerosAudit
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaConvolutionAudit
ConnesWeilRH.Dev.UnconditionalSkeleton
ConnesWeilRH.Dev.UnifiedRemainingGapsRouteAudit
```

The focused guard and uniform-tail audits report only `propext`,
`Classical.choice`, and `Quot.sound`. The route audit reports the same six
project roots as before and the instance premise
`NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider`. No audited
declaration uses `sorryAx`.
