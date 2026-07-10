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
proves that support endpoints add under convolution. The final construction
must shrink the factor windows as `N` grows; otherwise the convolution power
leaves the M5A support window and restores finite-prime terms.

## Route Consequence

M5A remains useful for its narrow-window finite-node interpolation and
finite-prime vanishing. It no longer qualifies as a detector producer.

M5B now requires a genuine multiplicative convolution, a source zero-sum
functional, and the Appendix C all-other-zero estimate. M5C adds the finite
bad-space conditions after M3A constructs the archimedean operator owner.

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
