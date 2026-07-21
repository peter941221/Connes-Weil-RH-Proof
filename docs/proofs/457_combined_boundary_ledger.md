# Proof 457: Combined finite-prefix boundary ledger

## Result

Proof 457 joins the two boundary mechanisms that were previously exposed by
Proofs 455 and 456.  For arbitrary target and source prefix sizes it defines
one signed scalar

```text
L_N = Tr(firstJet_N)
      - Tr(sourceQuadratic_N)
      - rectangularBoundary_N.
```

Lean proves the exact identity

```text
L_N
  = 2 * integral_0^1 weightedBoundaryTrace_N(alpha) d alpha.
```

The right side still contains both the detector core and the antisymmetric
root-cycle defect from Proof 455.  The left side still contains the source
quadratic response and all four rectangular carrier defects from Proof 456.
No term is estimated or split in this module.

## Consumer

The canonical ordinary-trace consumer now accepts a bound directly on `L_N`,
with an independently chosen source-prefix schedule `sourceCutoff N`.  The
consumer derives the weighted-boundary hypothesis by dividing the exact
identity by two, so a future analytic producer can target the complete
source-plus-carrier-plus-root object in one estimate.

## Boundary

This is an exact recombination, not Gate 3U.  The required uniform bound for
`L_N`, the finite-S sign, negative-owner integration, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.  In particular, the source response,
rectangular defect, detector core, and root-cycle defect must not be bounded
separately unless a later theorem proves that their cancellation is preserved.
