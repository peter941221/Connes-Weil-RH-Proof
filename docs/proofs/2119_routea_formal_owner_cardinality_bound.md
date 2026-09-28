# 2119 - Formal actual-owner cardinality bridge and quantitative gap

Date: 2026-09-28.

Status: `FORMAL-COUNT-BRIDGE-LANDED`; the compact selector is not yet a Go.

The new Dev module proves the following chain for the exact owner used by
Route A.005:

```text
sourceNontrivialZerosInClosedBall rho R
    -> symmetric height R + dist(2, rho)
    -> doubled Jensen circle
    -> unconditional dyadic xi-growth bound
    -> explicit source-owner cardinality upper bound
```

Formal evidence:

- `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean`
- theorem `sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth`
- paired audit `ConnesWeilRH/Dev/C1RouteAOwnerCardinalityProbe.lean`
- WSL Lake build log: `build-logs/routea_owner_cardinality_lakebuild_20260928.log`
- paired audit log: `build-logs/routea_owner_cardinality_audit_20260928_v3.log`

Both owning-module build and paired axiom audit completed with exit code 0.
The audit reports only the permitted standard axioms:
`[propext, Classical.choice, Quot.sound]`.

At the current stress point
`rho = 0.945 + 39.25244858548658 i`, `N = 0`, the numerical translation
of the formal bound is:

```text
closed-ball radius                 43.2666238039
required dyadic rung                 n = 4
xi growth exponent                2080.5658126196
source-owner ncard upper bound    3002.5554464806
largest screened compact family      62 nodes
bound / 62                         48.43x
```

The `xi(2) = pi/6` value in this table is a numerical translation of the
normalization, not a Lean numeral certificate. The formal theorem retains the
exact expression involving `‖completedRiemannXi 2‖`.

Decision: the existing unconditional Jensen/growth interface is too loose to
justify a 30--62 node compact ladder for the actual abstract owner. This is a
quantitative gap, not a global Route A no-go. A successful Go now requires one
of:

1. a substantially sharper explicit zero-count bound on this owner window;
2. an owner-local construction whose cost scales sublinearly in the count; or
3. a different signed mechanism that does not interpolate every source zero in
   the closed-ball owner.

Do not treat `3002` as the measured number of zeros; it is only the current
formal upper bound.

Artifact: `results/2119_routea_formal_owner_cardinality_bound.json`.
Script: `scripts/routea_formal_owner_cardinality_bound_2119.py`.
