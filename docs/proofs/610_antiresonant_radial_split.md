# Proof 610: antiresonant radial split

## Result

The ambient-loss denominator is now split by the genuine CCM24 radial support
projection.  The split is exact and orthogonal:

```text
full antiresonant column
        |
        +---- radial interior
        |
        +---- radial boundary

||full x||^2 = ||interior x||^2 + ||boundary x||^2.
```

The source is
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit.lean`.

## Boundary channel

The identity part of `I + U_(log p)` is radial and disappears after applying
the radial complement.  Hence the exterior piece is exactly

```text
boundary
  = primeEulerAmbientLossScale(p) * boundaryCrossing,

||boundaryCrossing|| <= 1.
```

Its pointwise `L2` representative is

```text
1_[log(lambda)-log(p), log(lambda))(t)
  * newFrame(x)(t + log(p)).
```

This is a completed half-line crossing on one literal finite window.  Compact
root support may therefore be applied to this channel without moving through
the forward coframe.

## Interior channel

The radial interior retains the hard `I + U_(log p)` antiresonance.  The
Pythagorean identity does not give it a lower bound, and the boundary estimate
does not control vectors with a long alternating tail.

## Boundary of the result

Proof 610 does not factor the signed reduced row through either channel.  It
does not close the uniform quotient, Bone 1, Gate 3U, the finite-S sign,
Burnol's identity, or RH.

## Verification

```text
focused source build: 3375 jobs, PASS
import-facing audit:  PASS
audited declarations: 9
axioms: [propext, Classical.choice, Quot.sound]
```
