# Proof 526: full graph physical cascade residual

## Result

Proof 525 gives the one-step identity

    fullGraphPhysicalStep(p,S)
      = actualSchurStep(p,S) + physicalSupportResidual(p,S).

Proof 526 lifts that identity to the same chronological finite-S product.
It defines

    G([]) = I
    G(p::S) = G(S) * fullGraphPhysicalStep(p,S)

    D([]) = 0
    D(p::S) = D(S) * actualSchurStep(p,S)
           + G(S) * physicalSupportResidual(p,S).

Lean proves the exact Duhamel identity

    G(S) - actualSchurForwardAmbientProduct(S) = D(S),

and its additive form

    G(S) = actualSchurForwardAmbientProduct(S) + D(S).

The residual stays whole.  No termwise norm estimate, residual-vanishing
claim, post-Q identification, Gate 3U sign, finite-S positivity, Burnol
identity, or RH conclusion is asserted.

## Lean owners

    ConnesWeilRH/Source/CCM25Concrete/
      CCM24FiniteSActualSchurGraphPhysicalCascadeResidual.lean
    ConnesWeilRH/Dev/
      CCM24FiniteSActualSchurGraphPhysicalCascadeResidualAudit.lean

## Verification

The focused aggregate audit reports only the repository baseline
[propext, Classical.choice, Quot.sound].  The source and audit contain no
sorry, admit, or user axiom.  The aggregate and full repository builds are
run from an Ubuntu 24.04 WSL2 ext4 mirror of the Windows source of truth.
