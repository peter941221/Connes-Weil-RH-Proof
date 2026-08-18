# 1035 - Conditional reduction to real Lane R owners

Date: 2026-08-19.

Owner: `Dev/C1XiCenterTwoGammaComplexSplitReduction.lean`.

Probe: `Dev/C1XiCenterTwoGammaComplexSplitReductionProbe.lean`.

## Verdict

The fixed `N = 21` Gamma_R prefix sign for a complex test reduces to the
corresponding sign statement for its real and imaginary component tests,
provided both component squares satisfy the prime-free support condition.

The owner defines:

```text
realValuedTest(g) := forall x, Im(g.test x) = 0

componentPrimeFreeSquare(g) :=
  laneRPrimeFreeSquare(realPartTest(g))
  and laneRPrimeFreeSquare(imagPartTest(g)).
```

It proves that both component constructors are real-valued and that a
real-valued sign producer implies

```text
P_21(g) <= 0
```

from:

```text
laneRTripleVanishing(g)
componentPrimeFreeSquare(g).
```

The proof uses the exact previously established identity

```text
P_21(g) = P_21(realPartTest(g)) + P_21(imagPartTest(g))
```

and adds the two component inequalities.

## Why the support premise remains explicit

The reduction does not claim

```text
laneRPrimeFreeSquare(g)
  -> componentPrimeFreeSquare(g).
```

That implication is not valid from the current data: cross-convolution terms
can cancel in the complex square.  Thus this module narrows the analytic sign
problem to real-valued owners only on the component-supported subfamily; it
does not close the component support gap, the real-valued sign producer, the
universal Lane R target, or RH.

## Lean interface

The main declarations are:

```text
realValuedTest
realPartTest_realValued
imagPartTest_realValued
componentPrimeFreeSquare
realValuedLaneRPrefixSignTarget
laneRFinitePrefixQuadraticValue_nonpos_of_realValued_target
```

## Verification

WSL2 owner/probe builds completed at jobs `3631`/`3632`.  The audited
declarations use only:

```text
[propext, Classical.choice, Quot.sound]
```

No numerical eigenvalue or unproved sign inequality is imported into Lean.

## Reproduction

```text
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplitReduction
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplitReductionProbe
```
