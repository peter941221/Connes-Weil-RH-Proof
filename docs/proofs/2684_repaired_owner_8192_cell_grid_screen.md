# Record 2684 - repaired-owner 8192-cell grid screen

Status: NUMERICAL GRID SCREEN PASS. This record closes the numerical
screening question for the complete 8192-cell partition, but it is not a Lean
continuum enclosure and it is not a Producer GO or RH result.

The driver `scripts/routea_repaired_owner_grid_screen_2684.py` initializes the
repaired binary64 owner once per Linux worker and evaluates all four channels
with the record-2242 natural interval evaluator. Every cell uses the same
directed binary64 price chain as record 2675: cell width, monotone exponential
weight, complex rectangle corner norm, products, and upward accumulation.
The evaluator's binary64 geometry cache is disabled so cell 4096 can be
compared bit-for-bit with record 2675. The compact JSON stores each binary64
as its 64-bit pattern, from which its exact rational value can be reconstructed.
Before writing, the driver checks all indices, adjacent endpoint continuity,
and the complete cell-4096 replay against record 2675.

Evidence from `results/2684_repaired_owner_8192_cell_grid_screen.json`:

```text
cells                         8192
cell adjacency                8191/8191 bitwise continuous
cell 4096 replay              endpoints, four rectangles, charge: PASS
rounded total upper (binary64) 7200470187264645 / 1073741824
exact sum of cell bit patterns proved in record 2685
rounded upper decimal        6705960.433245306
knownError2109 ratio          0.08989038704792249
worst cell                    4033, 11492.407134352972
below knownError2109          true
```

The independent readback checked the index permutation, adjacent endpoint
bit patterns, and cell-4096 equality against the 2675 JSON artifact. The
`total_upper_sum.exact` field is the exact rational decoding of the final
binary64 rendering, not the exact rational sum of the 8192 cell totals. Record
2685 recomputes that sum from every stored cell-total bit pattern in Lean and
proves the displayed binary64 value is above it. The screen therefore finds
no failed cell and keeps the numerical price below the committed budget by
about 11.1x.

The artifact still has these explicit false fields: `continuum_enclosure_proved`,
`lean_numeric_imported`, `actual_owner_identity_proved`,
`infinite_xi_tail_closed`, `producer_go`, and `rh_claim`. The next proof task
is to feed each cell's containment obligations into the parameterized Lean
partition consumer in
`ConnesWeilRH/Dev/C1RouteAWeightedCellPartition2684.lean`, followed by the
live-owner `chargeRest` identity and the signed infinite-xi tail.
