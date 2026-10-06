# Record 2589: captured-owner defect interface

Date: 2026-10-05

Status: LEAN-CAPTURED-OWNER-DEFECT-INTERFACE-PASS.

This record connects the previous algebraic layers to the actual captured
owner. Given a continuous linear preconditioner `X` satisfying

    ||I - X.comp ownerMomentOperator2588|| < 1,

the Lean theorem proves that `ownerMomentMatrix2351` has nonzero determinant,
then reuses the existing exact owner realization theorem to prove all 30
captured Laplace interpolation equations.

The dependency chain is now:

```text
2338 analytic matrix certificate
        |
        v
operator defect < 1
        |
        v
2587 operator injectivity
        |
        v
2588 determinant nonzero
        |
        v
2589 captured owner realizes targets
        |
        v
2586 interval membership interface
```

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionDefectOwner2589.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionDefectOwner2589Audit.lean`
- `results/2589_captured_owner_defect_validation.json`

The clean Linux-side build succeeds. The axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

The strict defect premise is still not a Lean theorem. The 2338 Arb matrix
intervals, the candidate inverse, and the row defect bound remain external
artifacts. Consequently exact interval membership, producer GO, and RH remain
open.

The next target is not another local cell. It is a finite `Fin 30` certificate
that converts the exported entrywise interval data into the operator defect
premise used here.