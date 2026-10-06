# Record 2586: exact interval to correction-box Lean interface

Date: 2026-10-05

Status: LEAN-EXACT-INTERVAL-BOX-INTERFACE-PASS.

The generated module imports the 30 by 4 rational endpoints from the repaired
record-2338 correction intervals. Lean proves every endpoint is contained in
the corresponding record-2570 correction box. It also proves the reusable
interface theorem:

    h_exact_interval : forall i,
      exactCorrectionInterval2586 i contains actual i
    -> forall i, correctionCoefficientBox2570 i contains actual i

The theorem is intentionally conditional. The premise is the missing analytic
soundness fact: the external Arb interval must be proved to enclose the exact
solution of the fixed captured owner. Importing interval endpoints and proving
box containment does not establish that premise.

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionExactIntervals2586.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionExactIntervals2586Audit.lean`
- `scripts/generate_exact_correction_intervals_2586.py`
- `results/2586_exact_interval_interface_validation.json`

The clean Linux-side build succeeds. The axiom audit reports only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or new axiom is used.

## Boundary

The selected-owner consumer remains open. Do not claim producer GO or RH until
the `h_exact_interval` premise is itself proved in Lean, or replaced by an
independently formalized exact analytic interval solver certificate.