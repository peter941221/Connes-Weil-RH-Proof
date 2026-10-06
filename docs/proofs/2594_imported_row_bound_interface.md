# Record 2594: imported row-bound owner interface

Date: 2026-10-05

Status: LEAN-IMPORTED-ROW-BOUND-OWNER-INTERFACE-PASS.

The 30 exact rational row bounds from the independent 2351 Fraction check are
now imported into Lean as `NNReal` values. Lean proves every imported bound is
strictly below one. The owner theorem then requires only two remaining facts:

1. the actual complex defect matrix has each row's NNReal norm sum bounded by
   the corresponding imported row bound;
2. that defect matrix is the operator
   `I - X.comp ownerMomentOperator2588`.

Once those two facts are proved, the theorem establishes all 30 captured
interpolation targets through the existing 2589 chain.

## Evidence

- `scripts/generate_row_bounds_2593.py`
- `ConnesWeilRH/Dev/C1RouteACorrectionRowBounds2593.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionRowBoundOwner2594.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionRowBoundOwner2594Audit.lean`
- `results/2594_imported_row_bound_validation.json`

The clean Linux-side build and audit pass with only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

The row bounds are imported data, not yet a proof about Lean's analytic
integrals. The actual matrix-entry enclosure, defect construction, and
row-bound containment remain open. Membership, owner transfer, producer GO,
and RH remain open.

The next move is to formalize the actual matrix/defect enclosure, not to add
more local second-chord cells.