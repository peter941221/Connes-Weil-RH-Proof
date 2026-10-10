Record 2657: certified real-exponential pins for all entry (0, 3) panels
Date: 2026-10-10

Result

Positive for the pin layer.  `scripts/generate_amp_pins_2657.py` emits one
module for each of the 190 record-2624 panels, including panel 109.  The
separate analytic-integral pilot at panel 109 does not supply this amplitude
pin, so omitting its pin would leave the partition assembly incomplete.
Each module replays the existing `compactExp_real_error2620` ball for the
exact rational exponent

    amp_k = exp(beta * center_k - 30 / (1 - center_k^2)).

The 46 panels whose variation certificate is vacuous also carry the
normalized-phase supremum pin needed by their monotone-integral channel.
Four amplitude chains underflow their stored center to zero (panels 0, 1,
188, and 189); their exact positive radius still certifies the exponential.
The generator checks every emitted exp enclosure against 200-digit mpmath
evaluation before writing the Lean literals.  This check catches generation
mistakes; the Lean replay and existing analytic theorem provide the proof.

Proof and build evidence

- Replay tactic: `decide +kernel` on the concrete record-2620 rational chain.
- Full umbrella: `ConnesWeilRH.Dev.C1RouteAAmpPins2657`, 3916/3916 jobs,
  build completed successfully in 79.13 seconds, 0 error and 0 `sorryAx`.
- A 472-theorem audit covers every amplitude chain/pin and every
  supRe chain/pin.  All 472 depend on exactly
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears.
- The initial cold P095 pilot built in 44 seconds; after dependencies were
  warm, the batch modules built in roughly 2-3 seconds each.
- `native_decide` is not used: its audit adds an auxiliary
  `native_decide.ax_1_1`, which violates the project's allowed axiom list.
  A one-step `norm_num` replay does not close the `Rat.floor` obligations;
  direct `decide +kernel` was both simpler and auditable.

Artifacts

- `ConnesWeilRH/Dev/C1RouteAAmpPin2657P{TAG}.lean` for tags P000-P189.
- `ConnesWeilRH/Dev/C1RouteAAmpPins2657.lean` imports the full panel batch.
- `ConnesWeilRH/Dev/C1RouteAAmpPinAudit2657.lean` prints all 472 axiom
  dependency lists.
- `results/2657_amp_pins.json` records exact arguments, centers, radii,
  underflow flags, panel counts, and the generator hash.

Scope

This closes only the real-exponential amplitude and normalized-phase
supremum pins.  It does not prove the panel partition sum, the complex
rotation assembly, containment in `analyticMomentInterval2597_row_03`,
Producer GO, SourceRH, or RH.  The next step is to combine these pins with
the 2646 phase engine and 2655-2656 panel certificates, then prove the
190-panel assembly and its containment in the committed rectangle.
