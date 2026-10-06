# Record 2591: row-sum defect certificate interface

Date: 2026-10-05

Status: LEAN-ROW-SUM-TO-CAPTURED-OWNER-PASS.

This record closes the abstract norm-conversion step. For a complex 30 by 30
defect matrix, if every row satisfies

    sum_j ||D[i,j]|| < 1,

a Mathlib matrix norm theorem proves that the associated operator on
`Fin 30 -> Complex` has operator norm less than 1. If that operator is the
actual defect

    I - X.comp ownerMomentOperator2588,

the theorem immediately proves that the captured owner realizes every one of
its 30 interpolation targets.

The row sum is the maximum possible amplification of a vector in the sup norm:
each output coordinate is bounded by one row's weighted absolute sum. This is
why the numerical 2338 row certificate is the correct object to import here.

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionOperatorNorm2590.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionDefectRows2591.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionDefectRows2591Audit.lean`
- `results/2591_defect_rows_validation.json`

The clean Linux-side build and axiom audit pass. All audited declarations use
only `[propext, Classical.choice, Quot.sound]`.

## Boundary

The 2338 row values are still external. We have not yet proved in Lean that
the exported 900 analytic matrix rectangles enclose the actual integral matrix,
that the candidate inverse produces the stated defect matrix, or that all row
sums are below one. Therefore exact membership, owner transfer, producer GO,
and RH remain open.

The next target is a generated rational matrix-defect payload together with a
Lean containment/equality interface for the actual analytic operator.