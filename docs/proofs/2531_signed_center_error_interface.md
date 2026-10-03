# Record 2531 — signed center-plus-error Lean interface

Date: 2026-10-03.

Record 2531 adds the first Lean support layer for the active 2528/2530
representation. It proves two generic inequalities:

```text
‖value - center‖ <= error
    -> ‖value‖ <= ‖center‖ + error

for every i in a finite family,
‖value i - center i‖ <= error i
    -> ‖sum value i‖ <= ‖sum center i‖ + sum error i
```

The second theorem keeps the complex center sum intact until the final norm.
This is the algebraic rule needed by the 2530 payload and explicitly avoids the
2529 implementation shape that summed wide complex rectangles and suffered
interval-dependency inflation.

Formal artifacts:

- `ConnesWeilRH/Dev/C1RouteASignedCenterError2531.lean`
- `ConnesWeilRH/Dev/C1RouteASignedCenterError2531Audit.lean`

Validation:

```text
lake build ConnesWeilRH.Dev.C1RouteASignedCenterError2531    PASS
axiom audit                                                     PASS
  [propext, Classical.choice, Quot.sound]
```

This record does not import the 2530 node payload, does not prove bump/phase
transcendental enclosures, does not prove whole-cell curvature bounds, and does
not close the selected-owner signed margin. Producer GO, SourceRH, and RH remain
open.
