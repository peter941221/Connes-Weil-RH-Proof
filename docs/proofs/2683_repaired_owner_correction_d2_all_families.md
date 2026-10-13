# Record 2683: repaired-owner correction-D2 family bridges

Status: Lean bridge GREEN for all 30 repaired correction-owner families in
cell 4096 and the correction-D2 cell consumer. This is not an RH proof.

The generator `scripts/generate_routea_repaired_owner_correction_d2_2683.py`
reuses the record-2682 second-factor rectangles and the record-2676 staged
rounding contract. Each family bridge composes the existing whole-cell
phi/trigonometric enclosure, the repaired correction coefficient from record
2680, and the outward-rounded D2 factor rectangle into the corresponding
`record2676CorrectionD2FamilyRects` rectangle. The proof keeps the negative,
positive, and zero modulation sign branches explicit.

The generated modules are
`C1RouteARepairedOwnerCorrectionD22683Family0.lean` through
`Family29.lean`, with one audit module per family. The consumer
`C1RouteARepairedOwnerCorrectionD22683Consumer.lean` applies
`correction_D2CellSumContained` to all 30 family bridges and proves
`record2683RepairedOwnerCorrectionD2CellContained`.

Evidence:

- `results/2676_cell4096_containment_screen.json` remains
  `CELL4096_CONTAINMENT_SCREEN_PASS`; the correction-D2 aggregate is inside
  its exported rectangle.
- Linux-native Lean 4.30 compiled all 30 family modules and the consumer.
- All 31 audits exit 0. Every audited declaration reports exactly
  `[propext, Classical.choice, Quot.sound]` after whitespace normalization;
  no `sorryAx` appears.

Scope remains local. This closes correction-D2 familywise containment for cell
4096. The other 8191 cells, global finite-sum owner transfer, `chargeRest`,
the signed infinite-xi tail, Producer GO, `SourceRH`, and RH remain open.
