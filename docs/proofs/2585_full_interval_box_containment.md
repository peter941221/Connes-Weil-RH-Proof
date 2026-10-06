# Record 2585: full 2338 interval containment in 2570 boxes

Date: 2026-10-05

Status: FULL-INTERVAL-BOX-CONTAINMENT-PASS.

The validator parses the rational literals in the generated Lean
`correctionCoefficientBox2570` source and compares them with the complete
record-2338 Arb solution intervals for the correction channel. All 30 complex
rows and all 60 real/imaginary coordinates are contained in their matching
boxes.

The minimum outward margin is zero. Some interval endpoint therefore touches
its box boundary; the result is containment, not a positive numerical safety
margin. The check remains external because it does not prove that the Arb
intervals enclose the exact analytic solution inside the Lean kernel.

## Boundary

The remaining formal gap is certificate soundness: a Lean-consumable proof
must establish that these exact analytic solution intervals enclose the
solution of the fixed `capturedActualCorrectionOwner2584` moment system. Until
that is imported or independently formalized, Lean membership, producer GO,
and RH remain open.

## Evidence

- `scripts/validate_full_interval_box_containment_2585.py`
- `results/2585_full_interval_box_containment.json`
- `results/2338_exact_interpolation_repair.json`
- `ConnesWeilRH/Dev/C1RouteACorrectionCoefficientBoxes2570.lean`
