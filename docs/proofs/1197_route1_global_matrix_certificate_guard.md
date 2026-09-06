# 1197 - Route 1 global negative-matrix certificate guard

Date: 2026-09-06.

Status: formal guard.  RH is not claimed.

Consumer: the healthy `CompactLog` B5 aggregate owner
`P2BilateralProfileRangeWitness`, through the canonical scalar
`p2AggregateValue`.

## Formal result

The aggregate scalar is formally represented on every finite real span by the
existing gate matrix:

```lean
p2AggregateValue (spanObj w y) =
  y ⬝ᵥ (gateMatrix w *ᵥ y)
```

The standard matrix consumer proves:

```lean
(-gateMatrix w).PosSemidef →
  p2AggregateValue (spanObj w y) ≤ 0
```

The paired exit guard
`not_negGateMatrix_posSemidef_of_healthyDetector_span` then proves that this
certificate is incompatible with `HealthyYoshidaDetectorData rho g` whenever
`g = spanObj w y`.  The reason is formal: the detector package gives
`qw g < 0`, hence the canonical identity
`p2AggregateValue g = -qw g` gives `0 < p2AggregateValue g`.

## Route consequence

This does not kill the aggregate route.  It kills only the universal shape
that seeks one negative-semidefinite matrix certificate on a span containing
the pinned detector.  Any surviving route-1 producer must be one of:

1. a detector-specific signed/defect certificate not equivalent to a global
   negative matrix on a span containing `g`; or
2. a genuinely windowed/renormalized positive trace construction, which is
   the route-2 interface.

The theorem is interface-level formal evidence, not a numerical observation
and not a new RH conclusion.

Evidence: `C1P2BilateralProfile.lean`,
`C1P2BilateralProfileExit.lean`, and their paired audit modules.  Focused
build `p2-global-matrix-nogo-2.log` completed successfully with standard
axioms only and zero `sorryAx`.
