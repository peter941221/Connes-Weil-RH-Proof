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
