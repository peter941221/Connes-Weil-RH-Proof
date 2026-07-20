# Proof 443: Completed actual-band numerator

Date: 2026-07-20

## Result

The correctly oriented first jet and the ordered nonlinear Gram numerator now
form one relative numerator.  The common inverse Gram covariance stays on the
right until the exact cancellation is proved.

```text
completedNumerator
  = firstJet * Gram + orderedNumerator

completedNumerator * Gram^(-1)
  = quadraticCycle
```

The source file is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualBandCompletedNumerator.lean
```

The focused declaration audit is:

```text
ConnesWeilRH/Dev/CCM24FiniteSActualBandCompletedNumeratorAudit.lean
```

## Algebra

The module defines:

```lean
actualBandCompletedRelativeNumerator
actualBandCompletedRelativeResponse
```

It proves

```lean
actualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma
actualBandCompletedRelativeNumerator_comp_gammaInv_eq_quadraticCycle
sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse
```

The first equality uses the exact source identity
`sourceBandGramResponse_comp_gamma_eq_neg_numerator`.  The second uses the
two-sided inverse identities for the ordered Gram covariance.  The third
consumes Proof 441 on the same source carrier.

The module also verifies paired scalar-gauge invariance.  Rescaling the frame
and the inverse covariance changes both numerator terms by `star c * c`; the
completed response remains the same for `c != 0`.

## Three-branch readback

The numerator expands to the correctly oriented first jet plus the existing
three-branch physical numerator:

```text
firstJet * Gram
  + (outer + second-support + prolate) numerator
```

The expansion is an identity, not an estimate.  It preserves the order needed
for a later Burnol trace argument.

## Boundary

No positivity or trace bound is stored.  In particular, the diagonal Euler
energy from Proof 442 cannot be substituted for the completed relative trace.
The missing theorem is a same-object, family-independent energy-to-boundary
estimate for this numerator after the canonical inverse Gram leg is applied.
