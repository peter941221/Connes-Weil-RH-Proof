# Record 2584: captured owner parameter instance

Date: 2026-10-05

Status: CAPTURE-PARAMETERS-FORMALIZED.

The 2338 capture now has an exact rational Lean lift for all 30 family widths,
modulations, nodes, and target values. The width theorem proves that the
captured widths are exactly the existing `storedWidth` entries; both the
external repair and Lean use the squared width as the analytic radius.

`capturedActualCorrectionOwner2584` instantiates the existing analytic moment
solution and is connected to the 2583 membership bridge. Its node realization
and box-membership implication compile with only the standard axiom trio.

## Boundary

The imported values are exact lifts of captured binary64 operands. This record
is a parameter identity, not an interval proof. The remaining premise is the
2338 directed componentwise residual for this exact fixed instance, together
with the determinant/invertibility certificate required by the realization
statement. Exact membership, producer GO, and RH remain open.

## Evidence

- `scripts/generate_capture_parameters_2584.py`
- `scripts/validate_owner_parameter_alignment_2584.py`
- `ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionCaptureOwner2584.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionCaptureOwner2584Audit.lean`
- `results/2584_owner_parameter_alignment.json`
