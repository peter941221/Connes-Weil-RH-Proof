# Record 2679: repaired-owner cell/base-M0 Lean bridge

Status: Lean bridge GREEN for cell 4096 and the base-M0 channel; this is not an
RH proof.

The repaired binary64 owner is decoded from the stored bit patterns in
`record2678BaseCoefficient`.  For each of the 30 families, the source module
proves that the corresponding whole-cell value belongs to its outward-rounded
dyadic rectangle.  It then proves the finite rectangle sum equals the exported
aggregate rectangle and that this aggregate is contained in the record-2675
base-M0 outer rectangle.  The exported consumer theorem is
`record2678BaseM0CellContained`.

The numerical source of the dyadic endpoints is
`results/2678_repaired_owner_point_screen.json`; rerunning
`python3 scripts/routea_repaired_owner_point_screen_2678.py` reproduced the
same JSON (MD5 `322b977edd5e1826cbfea49f403ca3ff`) and reports
`aggregate_inside_exported: true` with `family_count: 30`.

Validation used Linux-native Lean/Mathlib v4.30.  The target module compiled
with an explicit `.olean` output, and the audit module reported exactly
`[propext, Classical.choice, Quot.sound]` for
`record2678BaseM0AggregateFamilySumEq`, `record2678BaseM0AggregateSubset`, and
`record2678BaseM0CellContained`; no `sorryAx` was present.

This closes only the named cell/base-M0 bridge.  It does not prove the other
three channels, the remaining 8191 cells, `chargeRest`, the signed xi tail,
Producer GO, `SourceRH`, or RH.  The next producer-relevant step is to repeat
the same actual-owner enclosure for the remaining channel/cell obligations,
while preserving the explicit owner and provenance checks.
