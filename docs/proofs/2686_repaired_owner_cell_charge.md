# Record 2686 - repaired-owner cell-4096 integral charge

Status: LEAN PARAMETERIZED FOUR-CHANNEL CELL AND PARTITION CONSUMERS GREEN;
cell 4096 instance and axiom audit pass.

The theorem `weightedFourNormIntegral_le_of_cellRectangles2686` accepts any
interval, exponential weight `exp(sigma * x)`, four complex rectangle
enclosures, norm and weight bounds, four cell-price bounds, and a total-price
bound. It proves that the sum of the four weighted norm integrals is below the
total price. Continuity of each channel supplies interval integrability
internally, so callers do not need to assume it separately.

The concrete theorem `record2686RepairedOwnerCellCharge` instantiates this
interface with the four repaired-owner rectangle bridges from records 2679,
2680, 2682, and 2683. It proves that the four weighted norm integrals on cell
4096 are bounded by the recorded binary64 cell charge.

The theorem `weightedFourNormIntegral_le_of_partitionRectangles2686` composes
the same interface over an arbitrary finite partition. It accepts separate
rectangle, norm, and price functions for each channel and each cell, plus a
per-cell total-price bound. It sums each channel's local integrals and bounds
their total by the sum of the per-cell total prices.

Linux-native Lean 4.30 compilation and audit pass. The generic cell theorem,
the finite-partition theorem, and the cell-4096 instance use exactly
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The interface is reusable, but only cell 4096 currently has these four live
rectangle bridges connected to it. The other 8191 cells, the 8192-cell
continuum enclosure, the `chargeRest` transfer, the signed infinite-xi tail,
Producer GO, `SourceRH`, and RH remain open.
