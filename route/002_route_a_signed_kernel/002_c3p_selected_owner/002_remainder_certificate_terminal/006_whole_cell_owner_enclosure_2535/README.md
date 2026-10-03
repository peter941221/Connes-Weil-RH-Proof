006: whole-cell base enclosure and local bump proof

Status: EXTERNAL BASE ENCLOSURE PASSES; ANALYTIC BOUND AND ADAPTIVE NODE PILOTS FORMAL.

The 2338 base coefficient boxes, signed modulation, squared-width family
radii and selected-detector target remain unchanged. The 10240-cell external
totals are 2.688398948825133 / 2.676690127388878 for sigma = -1/2 / +1/2.
The gate is 2.7790943782. Record 2535 charges an analytic fourth-derivative
envelope to cover the whole cell; no sampled maximum enters the total.

Record 2536 proves the local order-0..4 derivative bound for the existing
widthBump function, including its flat support boundary. Records 2537-2538
compose it with the weighted complex exponential and prove the explicit
whole-cell third-derivative bound, with no assumed derivative magnitude.
Record 2539 assembles the signed midpoint-second bound and cell chord
integrals into a full-strip inequality on the 10240-cell grid. It retains
coefficient membership as a premise; full-grid numerical bounds remain open.
Record 2540 certifies the center node x=0 (grid index 5120): the signed
midpoint-plus-error expression is at most 69/5. It imports the exact 2338
base rectangles and proves their inclusion in radius-10^-30 balls. Membership
of the intended interpolation coefficients in those rectangles remains open.
Record 2541 certifies the first positive nonzero node, index 5121/10240 at
sigma=1/2, with upper 13.7900014901. It retains signed modulation in all 30
complex exponentials and includes the proved evaluation and coefficient errors.
Record 2542 replays that node through a compact proved rational evaluator and
certifies indices 5440 and 10239 at sigma=-1/2 and +1/2. The support-edge
cases use 17 squarings for the one active family; exterior families are
proved zero from their definitions. The complete grid remains open.
Record 2543 certifies the actual midpoint of cell 5440 at sigma=+1/2:
the signed order-two midpoint-plus-error expression is at most 2494.6018425.
All 30 exact complex derivative factors retain their signs, and rounded
derivative centers carry a proved evaluation/rounding charge. Third-order
endpoint numerics and the fourth-order envelope still need certification
before the midpoint result yields a whole-cell integral bound.

Next steps

1. Certify third-order endpoint values and the fourth-order cell envelope,
   then extend the midpoint certificate to the remaining production cells.
   Completion requires
   concrete numerical inequalities with the scaled-argument and error gates
   checked for each case. Price witness size before full-grid expansion.

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
docs/proofs/2539_signed_aggregate_cell.md
results/2539_signed_aggregate_validation.json
docs/proofs/2540_center_node_certificate.md
results/2540_center_node_validation.json
docs/proofs/2541_nonzero_node_certificate.md
results/2541_nonzero_node_validation.json

Records 2544-2546 certify both third endpoints, the fourth envelopes and
the first complete numerical integral upper for cell5440 at sigma=+1/2:
0.000758415674, conditional on coefficient-ball membership. This does not
complete the other cells/signs or exact-owner transfer. Current evidence:
docs/proofs/2546_first_cell_integral.md and results/2546_cell_readback.json.
