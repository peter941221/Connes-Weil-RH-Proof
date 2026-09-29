# 001 — Formal actual-owner cardinality bridge

Status: **FORMAL SUPPORT / NOT A ROUTE GO**.

This subroute closes the exact owner-cardinality interface needed before any
weighted-zero-measure or full-owner C3′ estimate can be priced. It is support
only; it is not a claim that the selector, signed margin, or RH route is
closed.

## Consumer and owner

The consumer remains the same selected healthy `CompactLog` detector and its
same-owner `qw(g) >= 0` obligation. The owner is the exact source-zero set in
the selected closed ball, not a compact numerical prefix.

## Closed theorem

The Lean theorem

```text
sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth
```

proves the chain

```text
closed-ball source zeros
  -> symmetric-height bound
  -> doubled Jensen circle
  -> dyadic xi-growth estimate
  -> explicit finite cardinality upper bound.
```

The paired audit uses only `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`, according to the recorded 2119 build and audit evidence.

## Evidence

- `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerCardinalityProbe.lean`
- [proof record 2119](../../../../docs/proofs/2119_routea_formal_owner_cardinality_bound.md)
- [artifact 2119](../../../../results/2119_routea_formal_owner_cardinality_bound.json)

At the recorded stress point the formal translation gives an upper bound of
about `3002.56` owner nodes. This is a certified upper bound, not a measured
zero count. It is too loose for the previous 30–62-node compact selector;
that quantitative gap belongs to a sibling subroute and does not invalidate
this formal bridge.

## Boundary

This GO closes only the owner-cardinality premise. It does not prove a
sublinear weighted certificate, the finite-window signed C3′ margin, or RH.
