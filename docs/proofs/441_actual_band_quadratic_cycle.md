# Proof 441: Actual-band quadratic cycle

Date: 2026-07-20

## Result

The source Sonin remainder and the root-sandwiched ambient ledger now share an
exact trace-compatible owner.  The owner is a four-leg quadratic cycle on the
source Sonin carrier.

```text
sourceActualBandFiniteEulerRemainderResponse
  = actualBandQuadraticCycledResponse
```

The cycle keeps the four terms in their original order:

```text
base^dagger * jet
  + jet^dagger * base
  - base^dagger * base
  + frame^dagger * dual
```

The source file is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualBandQuadraticCycle.lean
```

The focused declaration audit is:

```text
ConnesWeilRH/Dev/CCM24FiniteSActualBandQuadraticCycleAudit.lean
```

## Carrier construction

The ambient root response acts on `finiteSCarrier`.  Its legal readback uses
the rectangular source inclusion and its adjoint.  The module defines four
source-to-ambient root legs:

```text
actualBandBaseRootLeg
actualBandJetRootLeg
actualBandTargetFrameRootLeg
actualBandTargetDualRootLeg
```

The code never assumes that an individual root leg is Hilbert--Schmidt.  It
forms the complete `A^dagger B` pair first, then uses the existing positive
trace owner.

## Exact identities

The module proves the following operator equalities before taking an ordinary
trace:

```text
actualBandFirstJetRootResponse
  = jet * base^dagger + base * jet^dagger

rootSandwichedBandResponse
  = base * base^dagger - dual * frame^dagger

actualBandQuadraticRootResponse
  = actualBandFirstJetRootResponse
      - rootSandwichedBandResponse
```

The source pullback is then identified with the existing source remainder
owner.  The final theorem is

```lean
sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle
```

No finite-dimensional trace cyclicity, ambient trace premise, or new axiom is
used.

## Boundary

This proof closes ownership and carrier alignment.  It does not estimate the
cycle.  A branchwise norm estimate would destroy the cancellation carried by
the displayed four-term sum.  Gate 3U, the finite-`S` sign, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.
