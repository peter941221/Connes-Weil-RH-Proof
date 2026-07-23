# Proof 515: Empty-family physical readout

Proof 515 closes the base case for the completed physical history.  It is a
source-specific result for the genuinely empty visible-prime list; it is not a
producer for a nonempty finite-S family and it does not prove Gate 3U.

## Exact identities

For a family whose visible-prime list is empty, Lean proves

```text
normalizedFiniteEulerInverse = I
sourceActualBandForwardCoframe = 0
finiteEulerMetricCoframe = sourceInclusion
sourceActualBandForwardEndpointCoframe = sourceInclusion
```

The first-jet term therefore vanishes at the empty endpoint, while the metric
coframe retains the source inclusion.  This is the base coordinate that a
defect-only history would lose.

## Terminal readout

`fixedSourceRightReadout` is the right Douglas factor supplied by
`SourceGramInputFactorData.ofPairData` for the fixed two-branch physical pair.
It satisfies

```text
||fixedSourceRightReadout|| <= 1
fixedSourceRightReadout * fixedPhysicalSourceInput = fixedPair.right
```

Combining that factorization with the completed survivor-plus-boundary history
and a zero boundary readout gives

```text
sourceThreeBranchPairData.right * sourceActualBandForwardEndpointCoframe
  = readout * completedRectangularBoundaryColumn
      * fixedPhysicalSourceInput
```

for the empty family, with `||readout|| <= 1`.  The proof uses the actual
`WithLp 2` carrier and the exact component bridge from Proof 514.

## Verification

Focused source and audit checks use Ubuntu 24.04 WSL2.  The audit file prints
the axioms of every new principal declaration; the expected set is

```text
[propext, Classical.choice, Quot.sound]
```

The nonempty physical readout identity, Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
