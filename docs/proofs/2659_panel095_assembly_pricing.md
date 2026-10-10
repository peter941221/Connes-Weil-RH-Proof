Record 2659: P095 panel assembly pricing audit
Date: 2026-10-10

Result

The P095 input data are internally consistent for the next Lean assembly
lemma.  The exact center contribution is formed from

    amplitude_center * rotation_center * polynomial_integral.

The proposed first enclosure uses the L1 complex norm (the sum of absolute
real and imaginary coordinates) and the product inequality
`|ab|_1 <= |a|_1 * |b|_1`.  It charges the amplitude and rotation radii
separately while keeping the polynomial integral exact.

This is a pricing audit, not a proof of entry containment.  It identifies
the exact rational constants and the conservative error term that the Lean
assembly theorem must reproduce.  The analytic residual certificate from
2656 remains a separate addend and is not silently folded into this product
charge.

Evidence: `results/2659_panel095_assembly_pricing.json` and
`scripts/price_panel_assembly_2659.py`.

Lean interface

`ConnesWeilRH/Dev/C1RouteAPanelAssembly2659P095.lean` now replays the
center product and proves strict positivity and nonnegativity of the exact
L1 product charge.  Its three declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`.  The file intentionally stops
before replacing centers by their error balls and before claiming the
analytic panel containment; those are the next assembly obligations.

Erratum (record 2660)

The original charge carried one phase radius in each of its two phase
slots.  The record-2658 phase radius is a PER-COORDINATE radius, so the L1
rotation error is at most `2 * phaseRadius2658P095` and BOTH phase slots
must carry the factor 2.  `panelAssemblyCharge2659P095` and the pricing
script were corrected in place; the corrected float charge is
3.0108388912202296e-87 (was 1.7925e-87).  Soundness fix, not a
tightening; the consumer theorem is record 2660.
