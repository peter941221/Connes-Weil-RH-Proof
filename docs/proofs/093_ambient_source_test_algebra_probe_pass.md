# 093 Ambient Source Test Algebra Probe Pass

Date: 2026-07-12

## Lean evidence

The WSL-verified probe now instantiates the existing
`AnalyticCore.SourceTestAlgebra` without changing its type:

```text
Test              := TestFunction
legacy            := identity equivalence
convolutionStar   := ambient Schwartz convolution
involution        := reflection/conjugation
convolutionSquare := ambient convolution self
```

The structure compiles together with the Fourier product theorem and the
pointwise transport

```text
ambientConvolution f.test g.test = (f.convolution g).test.
```

## Consequence

The earlier API mismatch is fully removed at the type level. No route type
rewrite and no compact-subtype equivalence are required. A genuine source
package can use the existing `SourceTestAlgebra` interface with the ambient
Schwartz carrier and carry compactness through ordinary predicates/witnesses.

## Remaining mathematical owner

The unresolved task is no longer carrier construction. It is to rebuild the
source data on this operation and prove, for the same `convolutionSquare`,

```text
sourceNoDefectTrace
CC20 support-square / positive trace
CCM25 psi, pole, and finite-prime read-offs
```

The invalid additive model cannot be reused for these fields. Until the new
source package is proved, this remains a research owner rather than an RH route
theorem.

