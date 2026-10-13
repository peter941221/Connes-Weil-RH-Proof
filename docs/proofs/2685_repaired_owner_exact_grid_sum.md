# Record 2685 - repaired-owner exact 8192-cell price sum

Status: LEAN EXACT-SUM AND BUDGET ARITHMETIC PASS. This closes the import and
finite-sum arithmetic for record 2684's cell-total bit patterns. It does not
prove that those rectangles contain the continuous actual-owner channels.

The generator `scripts/generate_routea_partition_sum_2685.py` first checks the
record-2684 source hashes, ordered cell indices, 8192-cell count, and the
stored rounded-total readback. It decodes each `cells_data[*][6]` binary64 bit
pattern as its exact rational value and checks that the exact rational sum
rounds to the artifact's stored total. The generated Lean module uses the
existing `binary64Value2674` decoder, proves 256 exact chunk sums of 32 cells,
proves the composed ledger has length 8192, then combines the chunk
equalities into the full exact sum.

The exact rational cell-total sum is the fraction in
`record2684GridChargeExact2685`. Its decimal rendering is approximately
`6705960.433245306`. The JSON's `total_upper_sum.exact` is
`7200470187264645/1073741824`, the exact rational value of the rounded
binary64 total `0x415994ca1bba4a85`; it is not the exact sum of the cell
fractions. Lean separately proves that this rounded value is an upper bound
for the exact sum and that the exact sum is below `knownError2109`.

The certificate is generated from every cell total rather than from the
rounded aggregate. This distinction matters because converting an exact
fraction sum to binary64 can move it either way; the direction must be
checked, even where the displayed value happens to round upward.

Verification: Linux Mathlib v4.30 compilation passes for the generated module
and companion audit. The exact-sum, rounded-upper, and budget declarations
audit to `[propext, Classical.choice, Quot.sound]` with no `sorryAx`; the
ledger-length declaration needs only `propext`.

The remaining route obligations are the continuum containment of every cell
rectangle for the actual repaired-owner channels, the actual-owner identity,
the `chargeRest` transfer, and the signed infinite-xi tail. Producer GO,
`SourceRH`, and RH remain open.
