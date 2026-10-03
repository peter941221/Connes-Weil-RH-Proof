006: whole-cell base enclosure and local bump proof

Status: EXTERNAL BASE ENCLOSURE PASSES; LOCAL BUMP BOUND FORMAL.

The 2338 base coefficient boxes, signed modulation, squared-width family
radii and selected-detector target remain unchanged. The 10240-cell external
totals are 2.688398948825133 / 2.676690127388878 for sigma = -1/2 / +1/2.
The gate is 2.7790943782. Record 2535 charges an analytic fourth-derivative
envelope to cover the whole cell; no sampled maximum enters the total.

Record 2536 proves the local order-0..4 derivative bound for the existing
widthBump function, including its flat support boundary. The proof does not
yet compose that bound with the weighted complex exponential.

Next steps

1. Prove the weighted external-family derivative formula and compose its
   fourth-derivative magnitude with localCoupledBumpUpper2536. This supplies
   the actual function behind the external evaluator's familywise bound.
   Completion requires a theorem on the existing weighted owner definition.

2. Apply the fourth bound to the third derivative on each cell, then certify
   node and midpoint values and import exact rational cell sums in segments.
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
