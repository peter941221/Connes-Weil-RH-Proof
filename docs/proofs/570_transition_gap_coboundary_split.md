# Proof 570: Transition-Gap Coboundary Split

## Result

The raw Schur row uses the reverse transition orientation. For the actual
Schur step, write

```text
T = actualSchurTransition
G = EulerTransition - actualSchurTransition†
A = T - T†.
```

Proof 567 gives the row as the boundary-moment telescope with
`EulerTransition† - actualSchurTransition†`. Proof 568 identifies the exact
operator decomposition

```text
EulerTransition† - actualSchurTransition†
  = G† + A.
```

Therefore the named raw row is exactly

```text
raw row
  = transport-adjoint-gap coboundary
    + transition-skew coboundary,
```

where, with `M_S` the named Schur boundary moment,

```text
transport-adjoint-gap coboundary
  = M_S G† - G† M_(p::S),

transition-skew coboundary
  = M_S A - A M_(p::S).
```

The Lean theorem
`suffixActualBandNamedSchurTransitionGapRow_eq_transportAdjointGapRow_add_transitionSkewRow`
proves this equality by first rewriting the operator orientation identity and
only then applying map extensionality. It does not identify `A` with zero or
with the physical transport gap.

## Mathematical Boundary

The skew term is a genuine non-self-adjoint transition residual. A norm bound
for `G` does not bound the full row unless the skew coboundary is controlled in
the same signed object. Likewise, the right Julia co-defect from Proof 569
controls `I - T†T`, but does not control `T - T†`: a contraction can have a
large skew part while its defect is small, and the two are different operator
slots.

If both products are legally trace class, the only general cyclic reduction is

```text
Tr(M_S A - A M_(p::S))
  = Tr(A (M_S - M_(p::S))).
```

This is not zero without an additional equality, support cancellation, or
source-specific trace identity. The raw moment is already an adjoint of the
complete raw response, so deleting the skew term would change the route
operator rather than simplify it.

CCM24 Theorem 4.6 supplies a bounded invertible (`hilbertian`) transport of
Sonin spaces, not the missing signed transition identity or semilocal
positivity producer. Primary source: [Connes--Consani--Moscovici,
arXiv:2310.18423v2](https://arxiv.org/abs/2310.18423), Theorem 4.6.

## What Remains Open

The next real producer must either:

1. factor the complete skew coboundary through the same physical boundary
   column while preserving its sign;
2. prove a trace identity that cancels it against the transport-adjoint-gap
   coboundary on the same carrier; or
3. replace the Schur decomposition by a source construction whose transition
   is self-adjoint for a proved reason.

Independent absolute-value estimates of the two coboundaries are not a Gate
3U proof. Gate 3U, the finite-S sign, negative-owner integration, Burnol's
identity, and RH remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurTransitionOrientation.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurTransitionOrientationAudit.lean
```
