# 023 Qeasy Full-Product Detector Feasibility Plan

Date: 2026-07-11

Status: closed. The finite positive-definite construction is retained as a
component, but P2--P3 is rejected as an RH-level detector route. This plan does
not reactivate Plan 016 or claim an RH route.

## 1. Route Obligation

```text
route obligation:
  construct one genuine compact test whose full Yoshida convolution product
  detects an off-line zero, has the CC20 local remainder sign, and controls all
  other source zeros without SourceRH-level input.

old weak path:
  interpolate the correction factor to one at rho and infer that the assembled
  product detects rho.

new mathematical owner:
  CompactLogTest base factor, convolution count, finite node set, residual
  correction, and full-product Laplace values in one assembly.

consumer to rewire:
  none before the full detector and same-owner CC20 remainder theorem exist.

forbidden circular inputs:
  SourceRH, no-off-line-source-zero, detector coverage, a bare assertion that
  the base factor is nonzero, or an unresolved nearby/far fixed point.

smallest verification target:
  ConnesWeilRH.Source.CC20YoshidaFullProduct
  ConnesWeilRH.Dev.CC20YoshidaFullProductAudit

focused axiom audit:
  #print axioms
  exists_residualWindow_correction_full_product_interpolation
```

## 2. Fixed Evidence

The old assembly has the exact product law:

```text
Phi_assembled(s)
  = Phi_base(s / (n + 1))^(n + 1) * Phi_correction(s).
```

Thus `Phi_correction(rho) = 1` does not imply detection. The compiled guard
`laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_zero_of_base`
proves that a zero base factor forces the complete product to vanish.

The new theorem
`exists_residualWindow_correction_full_product_interpolation` uses the actual
product value as the interpolation target. Given nonvanishing of the rescaled
base factor at each finite node, it constructs one residual-window correction
such that the complete product has any requested finite set of Laplace values.

Code evidence:

```text
ConnesWeilRH/Source/CC20YoshidaFullProduct.lean
ConnesWeilRH/Dev/CC20YoshidaFullProductAudit.lean
ConnesWeilRH/Source/CC20YoshidaConvolution.lean
```

Source evidence:

```text
Connes--Consani, Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771

Corollary qeasy, weil-compo.tex:831-842:
  D o Q <= 0 for positive-definite tests in the stated narrow support window.

Appendix C, weil-compo.tex:2075-2085:
  one detector must control the full spectral side, not merely a finite set of
  Mellin nodes.
```

## 3. Scope And Non-Goals

Scope:

```text
full-product finite interpolation
finite-node base nonvanishing
same-owner narrow-window qeasy transfer
one simultaneous nearby/far quantifier construction
```

Non-goals:

```text
no reuse of normalizedCC20TestSpace as a source detector
no Cdef endpoint-exhaustion repair
no detector coverage input
no route consumer rewiring or root retirement
no assertion that finite interpolation controls all other zeros
```

## 4. Gates

```text
P0 full-product finite interpolation
  status: proved and axiom-clean

P1 positive-definite finite detector factorization
  status: finite source-zero specialization proved and axiom-clean.
  `exists_convolutionSquare_base_fullProduct_indicator` constructs
  `f = h* * h` with value one at a marked node and zero at every other finite
  node whose rescaled value does not collide with the marked node's Hermitian
  companion. It retains a symmetric narrow support window and a decay constant
  for the same factor `h`.

  The theorem `exists_sourceZero_nearby_convolutionSquare_indicator` now
  specializes the finite node set to

  ```text
  sourceNontrivialZerosInClosedBallFinset rho R union routeNodes.
  ```

  It needs only `rho` to be a source nontrivial zero, `R >= 0`, and every
  route node to have nonnegative real part. The source open-strip theorem
  supplies the strict positivity for every source zero, which excludes the
  Hermitian-reflection collision. The result is one compact `h` whose square
  has value one at `rho`, value zero at every other nearby source or route
  node, narrow symmetric support, and a retained decay constant for `h`.

  remaining: instantiate `routeNodes` with the actual CC20 nodes, then prove
  that the support-preserving convolution power remains a convolution square.
  An arbitrary residual correction remains forbidden because it destroys the
  positive-definiteness required by `qeasy`.

P2 simultaneous radius/count selection
  status: rejected as a lower RH producer. Yoshida Lemma 1 (1992, pp. 285-286) lets support grow
  with its finite correction factors and repeated base. The `qeasy` subroute
  instead fixes a narrow support window, so normalized rescaling moves the
  far-tail threshold to `(n+1) * T`.

  required new theorem:
    construct R, one positive-definite test, T, and n simultaneously with
      R >= (n+1) * T,
    finite detection/vanishing below R,
    and the all-other-zero tail bound above `(n+1) * T`.

  The current order `R -> finite interpolation -> C,T -> n` cannot imply this:
  there is no uniform control of the interpolation constant or tail threshold
  as R grows.

  More decisively, a completed P2 plus the planned `qeasy` transfer is not
  lower than the RH exit. It supplies the concrete detector-existence input
  consumed by `cc20_proposition_c1_from_yoshida_detector` in
  `ConnesWeilRH/Source/CC20YoshidaCriterion.lean:219-243`, whose conclusion is
  `RHDefinitionBridge.standard.SourceRH`. Thus this is an RH-level detector
  theorem in a new parametrization. Do not enter P3 under Plan 023.

  This is a route rejection, not a proof that the standalone quantitative
  fixed-point assertion is false.

  rejected escape:
    do not replace the finite nearby set by zeros at every other source zero.
    A nonzero fixed-support Mellin transform has finite exponential type and
    O(R) disk-zero count, whereas distinct zeta zeros are not O(R). This would
    force the detector to vanish at its marked node as well.

P3 same-owner qeasy transfer
  status: inactive. Completing this transfer would only finish the RH-level
  detector implication identified at P2.

P4 spectral-side detector theorem
  status: inactive. This is part of the rejected P2--P3 global contradiction.
```

## 5. Decision Rules

```text
success:
  P1-P4 are proved from lower analytic data and one selected test reaches the
  CC20 exit without an RH-level premise.

partial:
  a gate is lowered by a theorem but no route consumer changes.

blocked:
  a necessary source statement is unavailable but no contradiction is known.

rejected:
  positive-definiteness cannot be retained by the finite detector assembly,
  the simultaneous quantifiers cannot be closed, or the same-owner transfer
  imports an RH-level statement.
```

## 6. Preserved Components

Plan 023 is closed as an RH route. Preserve only the lower algebraic results:

```text
laplaceAt_involution
fullProductBaseFactor_convolutionSquare
exists_convolutionSquare_base_fullProduct_normalized
exists_convolutionSquare_base_fullProduct_indicator
exists_sourceZero_nearby_convolutionSquare_indicator
laplaceAt_convolutionSquare_convolutionIterate_rescale_inv_natCast
```

They may be used by a future owner whose consumer is strictly weaker than
`SourceRH`. They must not be used to reconstruct `CC20YoshidaDetectorExists`,
detector coverage, or the P2--P3 global contradiction.
