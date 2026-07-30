# Proof 596: literal coframe survivor residual

## Result

The adjacent metric coframe difference is now kept as one exact residual:

```text
M_(p::S) - M_S * transition(p,S)^dagger
  = AmbientProduct(S)^dagger
      * (SurvivorResidual(p,S) + BoundaryResidual(p,S)).
```

The two channels are defined by

```text
SurvivorResidual
  = upperFactor(p::S) * newFrame(S) * transition^dagger
      * GramInvSqrt(p::S)
    - upperFactor(S) * newFrame(S) * GramInvSqrt(S)
      * transition^dagger

BoundaryResidual
  = upperFactor(p::S) * boundaryDagger(p,S)
      * GramInvSqrt(p::S).
```

Thus the scalar upper-factor mismatch and the two endpoint Gram square roots
remain explicit.  They are not set equal, and the boundary term is not
identified with the survivor term.

```text
                  adjacent metric difference
                             |
              +--------------+--------------+
              |                             |
              v                             v
       survivor mismatch              boundary dagger
       upper + Gram endpoints         Schur range leakage
              |                             |
              +--------------+--------------+
                             v
                  one ambient-adjoint readout
```

The same module records the forward coframe recurrence separately.  No Lean
identity currently cancels that forward recurrence against either residual;
doing so would require a new source theorem with the correct carrier and
orientation.

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidualAudit.lean
```

The focused source proof is axiom-clean with the standard set
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This is an exact algebraic expansion only.  It does not construct bounded
`ambientRow` or `boundaryRow`, prove their uniform bounds, close Gate 3U,
prove the finite-S sign, prove Burnol's identity, or prove RH.
