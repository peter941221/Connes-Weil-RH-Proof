# Proof 521: physical inverse versus source-forward Schur transport

## Result

The normalized physical Euler inverse and the source-forward actual Schur
ambient product now live in one exact operator identity.  For every finite
visible-prime list, Lean defines an operator-valued residual by the same
chronological recursion:

```text
physicalResidual([]) = 0

physicalResidual(p::S)
  = physicalResidual(S) * inverse_p
    + forwardAmbient(S) * (inverse_p - SchurTransport_(p,S)).
```

The central theorem is the variation-of-constants identity:

```text
normalizedFiniteEulerInverseList(S) - forwardAmbient(S)
  = physicalResidual(S).
```

No absolute value, norm estimate, sign claim, or residual-zero premise is
introduced.  Keeping the subtraction whole is essential because the active
Gate 3U route depends on cancellation between the physical inverse and the
post-Q Schur channel.

## Physical coframe readback

After precomposition by the actual source inclusion and postcomposition by the
source band projection, the same residual gives:

```text
sourceActualBandForwardCoframe
  = sourceActualBandForwardSchurCoframe +
    sourceActualBandForwardTransportResidual.
```

Adding the existing metric coframe yields the corresponding endpoint split.
This is a direct source-carrier identity, not an identification of the
source-forward Schur endpoint with the physical endpoint.  The remaining
residual is explicit and is the object that a family-uniform Gate 3U producer
must control.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurForwardPhysicalDifference.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurForwardPhysicalDifferenceAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The source and audit contain no `sorry`, `admit`, or user axiom declaration.
The audited theorems are expected to use only
`[propext, Classical.choice, Quot.sound]`.

This proof closes transport/coframe alignment only.  It does not bound the
residual uniformly in the visible-prime family, prove Gate 3U, prove the
finite-S sign, supply Burnol's identity, or prove `_root_.RiemannHypothesis`.
