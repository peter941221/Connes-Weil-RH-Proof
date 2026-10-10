Record 2658: 190 exact phase-rotation pins
Date: 2026-10-10

Result

Positive for the rotation-pin layer.  `scripts/generate_phase_pins_2658.py`
emits one Lean module for each panel of entry (0, 3).  Each module replays
the exact rational phase `psi * center` through the existing record-2646
complex exponential engine and proves both cosine and sine coordinate
errors using the same certified radius.

The generator computes each rational state with the same 320-bit directed
rounding and 400-bit upward radius rules as the Lean engine, then checks
both coordinate errors against 200-digit mpmath values before emission.
That high-precision calculation is a generation guard; Lean's kernel replay
and record-2646 error theorems establish the certificate.

Validation

- P095 pilot: direct Lean elaboration succeeded in 64.15 seconds.
- P000 and P189 edge pilots: built successfully, including phases near the
  extremes of the full interval.
- Full umbrella: 3917/3917 jobs built successfully in 80.72 seconds,
  with no errors or `sorryAx`.
- The generated audit prints 570 theorems; every dependency list is exactly
  `[propext, Classical.choice, Quot.sound]`.
- Every generated chain uses `decide +kernel`; the coordinate pins use
  `phaseExp_cos_error2646` and `phaseExp_sin_error2646`.

Artifacts

- `ConnesWeilRH/Dev/C1RouteAPhasePin2658P{TAG}.lean` for tags P000-P189.
- `ConnesWeilRH/Dev/C1RouteAPhasePins2658.lean` imports all 190 modules.
- `ConnesWeilRH/Dev/C1RouteAPhasePinAudit2658.lean` audits the axiom lists.
- `results/2658_phase_pins.json` records phase inputs, centers, radii, and
  generator hash.

Scope

Only the per-panel real and imaginary coordinates of the rotation are
certified.  The rotation has not yet been multiplied into the complex panel
integrals, summed across panels, or compared with the 2597 rectangle.  This
record does not establish Producer GO, SourceRH, or RH.
