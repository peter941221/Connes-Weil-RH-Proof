006: whole-cell base enclosure and local bump proof

Status: EXTERNAL BASE ENCLOSURE PASSES; WEIGHTED-FAMILY WHOLE-CELL BOUND FORMAL.

The 2338 base coefficient boxes, signed modulation, squared-width family
radii and selected-detector target remain unchanged. The 10240-cell external
totals are 2.688398948825133 / 2.676690127388878 for sigma = -1/2 / +1/2.
The gate is 2.7790943782. Record 2535 charges an analytic fourth-derivative
envelope to cover the whole cell; no sampled maximum enters the total.

Record 2536 proves the local order-0..4 derivative bound for the existing
widthBump function, including its flat support boundary. Records 2537-2538
compose it with the weighted complex exponential and prove the explicit
whole-cell third-derivative bound, with no assumed derivative magnitude.

Next steps

1. Assemble the signed aggregate's midpoint-second bound from the proved
   familywise third bounds. Keep the midpoint complex sum before the norm
   and add coefficient uncertainty separately. Completion requires the
   same center-plus-error inequality used by the 2535 evaluator.

2. Certify node and midpoint values and import exact rational cell sums in segments.
   Completion requires both Lean endpoint inequalities without numeric premises.

3. Connect the midpoint-plus-error representation to the exact interpolation
   owner and propagate the proved bounds into the selected-owner signed budget.
   Completion requires the matching owner and a complete signed margin;
   passing the base endpoint pin alone is insufficient.

Evidence:
docs/proofs/2535_whole_cell_fourth_enclosure.md
docs/proofs/2536_coupled_bump_envelope.md
results/2535_whole_cell_enclosure.json
results/2535_whole_cell_validation.json
results/2536_coupled_bump_validation.json
docs/proofs/2537_weighted_family_derivatives.md
docs/proofs/2538_weighted_family_whole_cell.md
results/2538_weighted_cell_validation.json
