# Record 2687 - exact 2048-cell repaired-owner price sum

Status: EXACT FINITE-SUM THEOREM AND AXIOM AUDIT GREEN; CELL CONTAINMENT
REMAINS OPEN.

The record-2687 screen contains 2048 repaired-owner cells and four channel
prices per cell. Its stored binary64 charges sum to
`0.37817841912789424` of `knownError2109`. The JSON artifact preserves the
input bit patterns and source hashes for the grid screen, continuous-price
probe, cell exporter, interval evaluator, and strip owner.

`scripts/generate_routea_partition_sum_2687.py` decodes the cell totals as
exact rationals and renders 64 Lean chunks of 32 cells each. The generated
module proves each chunk sum, the 2048-cell count, the exact composed sum, and
that the exact sum is below `knownError2109`. The Linux-native Lean 4.30 build
and audit pass. Both audited theorems depend only on
`[propext, Classical.choice, Quot.sound]`; neither uses `sorryAx`.

The artifact field `total_upper_sum` is the nearest binary64 rounding of the
aggregate, despite its name. For this artifact, that rounded value is below the
exact rational sum by approximately `5.59e-11`. The generator checks that the
field is the nearest-rounded aggregate, but the Lean budget theorem uses the
exact cell sum directly and makes no upper-bound claim about the rounded
field.

This is exact arithmetic over sampled cell prices, not a continuum enclosure.
No theorem yet proves that the four actual channel functions lie in the
recorded rectangles across these 2048 intervals, or that these prices bound
their continuum integrals. The next step is to parameterize the cell
rectangle-containment proof and instantiate
`weightedFourNormIntegral_le_of_partitionRectangles2686` with the resulting
family. The evaluator-continuum link, `chargeRest`, signed infinite-xi tail,
Producer GO, `SourceRH`, and RH remain open.

Evidence: `results/2687_repaired_owner_2048_grid_screen.json`,
`scripts/generate_routea_partition_sum_2687.py`,
`ConnesWeilRH/Dev/C1RouteAWeightedPartitionSum2687.lean`, and its audit module.
