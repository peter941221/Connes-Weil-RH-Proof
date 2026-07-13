# Proof 201: Whole-line crossing nuclear compactness

Status: accepted operator-ideal milestone. The finite-S single-crossing main
operator is now genuinely compact and self-adjoint, with an operator-norm
absolutely convergent rank-one expansion behind each crossing product. RH
remains unproved.

## Route obligation

```text
route obligation:
  prove a genuine operator-ideal property for the named finite-S main operator

old weak path:
  IsTraceClassAlong, meaning only absolute diagonal summability in one basis

new mathematical owner:
  globalConvolutionCrossingPairData and its nuclear rank-one expansion

consumer to rewire:
  the common-domain finite-S post-Q remainder construction

forbidden circular inputs:
  SourceRH, Weil positivity, stored compactness, or a stored remainder sign

smallest verification targets:
  ConnesWeilRH.Source.CC20Concrete.PositiveTrace
  ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

focused axiom audits:
  ConnesWeilRH.Dev.GlobalLogCrossingTraceClassAudit
  ConnesWeilRH.Dev.SelectedCrossingMultiPrimeAudit
  ConnesWeilRH.Dev.SelectedCrossingOperatorBridgeAudit
```

## Nuclear expansion

For Hilbert--Schmidt pair data `A,B : H -> G` and a target Hilbert basis
`(e_j)`, the new theorem proves the operator identity

```text
A^dagger B
  = sum_j rankOne(A^dagger e_j, B^dagger e_j).
```

The operator norms are absolutely summable:

```text
sum_j ||rankOne(A^dagger e_j, B^dagger e_j)||
  = sum_j ||A^dagger e_j|| ||B^dagger e_j||
  < infinity.
```

The proof uses the existing basis-independent adjoint Hilbert--Schmidt
summability and

```text
2xy <= x^2+y^2.
```

Each rank-one term factors through `C`, hence is a Mathlib compact operator.
Finite sums are compact, the sums converge in continuous-linear-map norm, and
the set of compact operators is closed. Therefore both `A^dagger B` and its
adjoint are `IsCompactOperator`.

Named declarations:

```text
traceProductNuclearTerm
summable_norm_traceProductNuclearTerm
traceProduct_eq_tsum_nuclearTerm
traceProduct_isCompactOperator
traceProduct_adjoint_isCompactOperator
```

## Whole-line and finite-S result

`globalConvolutionCrossingPairData` packages the reflected finite-interval
Hilbert--Schmidt factors whose trace product is the actual whole-line crossing.
The equality is proved by
`globalConvolutionCrossingPairData_traceProduct_eq`; compactness is transported
through this operator equality, not stored in the owner.

Consequently the forward crossing and its adjoint are compact. Scalar
multiplication, addition, and finite-sum closure give

```text
K_S = sum_((p,m) in terms)
        1/(m sqrt(p^m)) * (T_(p,m)+T_(p,m)^dagger)

K_S is compact,
K_S is self-adjoint,
K_S is diagonal-trace legal along the named whole-line basis,
Tr(K_S) = sum_((p,m) in terms) finitePrimeTerm(p^m).
```

The positive-interval compactness specialization discharges the common support
premise from the canonical Yoshida source.

```text
finite interval HS pair
          |
          v
operator-norm nuclear expansion
          |
          v
whole-line T_(p,m), T_(p,m)^dagger compact
          |
          v
finite sum K_S compact + self-adjoint
```

## Source screen

A targeted current-paper search found no theorem supplying the missing
semilocal positive owner:

```text
Connes, The Riemann Hypothesis: Past, Present and a Letter Through Time
https://arxiv.org/abs/2602.04022

Groskin, High-Precision Approximation of Riemann Zeros via the Truncated Weil Form
https://arxiv.org/abs/2605.20224

Suzuki, On the Hilbert space derived from the Weil distribution
https://arxiv.org/abs/2301.00421
```

The first describes finite-to-infinite Euler-product convergence as a
potential strategy. The second states that convergence to Riemann zeros is
open and makes no proof claim. The third constructs its Hilbert space under
RH. None proves finite-S semilocal positivity or a same-domain post-Q remainder
identity.

## Boundary of the result

Compactness does not solve the common-domain problem. The whole-line `K_S`
still has to be identified as the single-crossing component of a genuine
finite-S positive owner acting on the same test-root Hilbert space as the CC20
post-Q remainder. No theorem here transports the CC20 compact kernel to that
whole-line space or proves the remainder sign.

## Verification

The generic nuclear layer builds `2356/2356`; the whole-line source builds
`2979/2979`; the three import-facing audits build `2983/2983`. All new nuclear,
compactness, same-object, and finite-S declarations report only:

```text
propext
Classical.choice
Quot.sound
```
