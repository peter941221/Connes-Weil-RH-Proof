# Record 2588: analytic moment operator and determinant interface

Date: 2026-10-05

Status: LEAN-ANALYTIC-MOMENT-OPERATOR-INTERFACE-PASS.

This record turns the existing analytic matrix definition
`ownerMomentMatrix2351` into a continuous linear operator on the coefficient
space `(Fin 30 -> Complex)`. Its application theorem identifies the operator
with the matrix `mulVec` action, and a generic injectivity hypothesis on that
operator proves that the matrix determinant is nonzero.

The dependency chain is now explicit:

```text
2338 numeric defect bound
        -> operator injectivity (2587)
        -> owner matrix determinant nonzero (2588)
        -> hdet for the exact analytic owner
        -> exact owner realization and membership
```

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionMomentOperator2588.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionMomentOperator2588Audit.lean`
- `results/2588_moment_operator_validation.json`

The clean Linux-side build succeeds. The axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

2588 does not claim that the 2338 defect bound is already a Lean theorem. The
900 analytic matrix-entry intervals, their relation to the actual integrals,
and the strict operator-norm defect remain external. Therefore `hdet`, owner
transfer, producer GO, and RH remain open.

The next target is a certified entrywise-to-operator defect lemma specialized
to the `Fin 30` matrix, followed by importing the 2338 rational interval data.