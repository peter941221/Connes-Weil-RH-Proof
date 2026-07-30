# Proof 608: old-carrier coframe antiresonant reduction

## Result

The result is useful but conditional.  It identifies the exact Bone 1
denominator on the new-frame range; it does not construct the missing bounded
factor.

```text
response factor K_(p,S)
        |
        v
oldFrame * rawIntertwining
  = oldCarrierAnalysis^dagger * K_(p,S)
        |
        | restrict to newFrame
        v
reducedRow * newFrame
  = antiresonantReadout * ambientLoss^dagger * newFrame
```

The source is
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction.lean`.

## What was proved

The nonzero Schur--Markov scalar is cancelled from the response-facing
contract, giving

```text
oldFrame * rawIntertwining
  = oldCarrierAnalysis^dagger * factor.
```

On the actual new suffix frame, both packed physical coordinates come from
one ambient-loss column:

```text
oldCarrierAnalysis * newFrame
  = newRangeAmbientLossLift * ambientLoss^dagger * newFrame,

||newRangeAmbientLossLift|| <= 2.
```

Consequently every supplied Bone 1 response factor produces a readout of
`ambientLoss^dagger * newFrame` with norm at most twice the supplied bound.

## Why it matters

The previous spectral-gap route tried to bound the whole old-carrier analysis
from below.  Proof 590 rules that out.  Proof 608 instead exposes the correct
relative quotient: the numerator must vanish at least as fast as the
antiresonant denominator.  This retains the signed raw row and does not invert
the packed analysis.

## Boundary

No response factor or family-uniform bound is constructed.  The theorem is a
necessary consequence and coordinate reduction, not Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, or RH.

## Verification

```text
focused source build: 3371 jobs, PASS
import-facing audit:  PASS
audited declarations: 8
axioms: [propext, Classical.choice, Quot.sound]
```
