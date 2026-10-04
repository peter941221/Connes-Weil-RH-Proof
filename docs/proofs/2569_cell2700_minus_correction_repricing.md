# Record 2569 — Cell2700-minus repriced at the correction pair

Verdict: REPRICE-VALIDATED. The 2565 three-piece certificate structure closes
at the record-2338 `ideal_correction_coefficient` pair (correction midpoints,
1e-28 per-family charge) in exact external arithmetic. The recomputation
pipeline reproduces the committed base-pair aggregates bitwise where their
rounding forms coincide and within their quantization quanta elsewhere, and
the repriced cell bound 3.32e-2 is cross-checked against an independent
2561-method enclosure of the same integral at the same cell at ratio 1.054.
No rounding-grade deepening is needed at the correction coefficient scale:
the rationalization charges stay at 1e-13 against values up to 24.5.

## What was computed

`scripts/price_cell2700_minus_correction_2569.py` rebuilds the 2565 pricing
from the committed deterministic helpers (multiplier 2543,
precision_evaluate 2547, the 2558 per-family third envelopes) with only two
things swapped: the coefficient centers (base -> correction rows) and the
per-family ball charge (1e-30 -> 1e-28). Per family it evaluates the order-0
exp values at the cell2700 edges, the order-1 and order-2 jets at the
cell2700 midpoint (x = -R + 5401/2·STEP, R = 65536001/10^7), and closes the
2562/2565 three-piece summand

    S = step·C + 2|σ|·step·(J1 + C·half) + σ²·(half·(N0l + N0r) + C·step³/12)

with C = |Σ c_i·u2_i(mid)| + third_agg·half and third_agg =
Σ (|c_i|_L1 + charge)·t_i over the committed 2558 envelopes.

## Base self-check (pipeline validation at the committed pair)

+--------------------------+-------------------------------+
| check                    | delta vs committed            |
+--------------------------+-------------------------------+
| third_agg vs 2565 L1     | 0.0 (bitwise, exact rational) |
| literal                  |                               |
| n0l / n0r uppers         | +1.38e-16 (bitwise form)      |
| mid / j1 uppers          | -9e-8 (quantum: mine +1/10^8, |
|                          | committed +1/10^7)            |
| exact cell sum           | -2.30e-10 (mine tighter;      |
|                          | committed bound still covers) |
+--------------------------+-------------------------------+

The exact base sum recomputes to 5.0717541e-6 inside the committed bound
5071985/10^12, with the same piece profile (curvature piece 4.986e-6, about
98 percent).

## Correction repricing (sigma = -1/2, cell 2700)

+---------------------------+---------------------------+
| quantity                  | value                     |
+---------------------------+---------------------------+
| curvature upper C         | 25.282987207              |
| first-jet upper J1        | 0.612763250               |
| endpoint uppers N0l/N0r   | 0.0153245019/0.0154559338 |
| third L1 aggregate        | 1270.6477579              |
| piece 1 (step·C)          | 3.236222e-2               |
| piece 2 (jet)             | 8.050488e-4               |
| piece 3 (endpoint)        | 4.925974e-6               |
| exact sum                 | 3.3172198889e-2           |
| cell bound                | 3317219889/10^11          |
+---------------------------+---------------------------+

Cross-check: the 2561 trapezoid enclosure of exp(σx)f″ over the same cell
prices node 3.14570905e-2 + remainder 7.0986723e-6 = 3.14641891e-2; the
three-piece bound is 1.0543x it, as expected for a triangle-inequality
decomposition of the same integral.

Charges at the correction scale: j1 1.26e-13, mid 2.40e-13,
n0l/n0r 1.23e-13 - eleven orders below the values they travel with. The
committed 160-bit rationalization grade survives the 5.5e17 correction
coefficients untouched.

## Findings

1. The 2568 guess "about 12 per cell" describes the 2561 grid average, not
   cell2700: the repriced cell2700 bound is 3.32e-2, a factor 6546 above the
   base-pair bound, because the correction coefficients are huge on the
   narrow families concentrated near the origin while cell2700 sits at
   |x| about 3.1.
2. At this far-out cell the correction summand stays curvature-dominated
   (piece 1 is 97.6 percent); the 2561 node-dominance of the grid total is a
   near-origin phenomenon.
3. The 2568 step-3 regeneration is a parameter swap: same generator chain,
   same position-keyed tables (exp inputs, factors, centers, third
   envelopes, 90 leaves), only the coefficient-row key and the 1e-28 charge
   change. No rounding-grade deepening, no structural change to the 2566
   lanes.

## Explicitly not claimed

No Lean module has been regenerated at the correction pair yet; 2563/2565
stand as committed base-pair artifacts. Membership is unchanged (the 2564
probe numbers stand: correction needs the 1e-28 pair, 1.56x slack). The
single-cell result does not price the grid: the near-origin cells dominate
the 2561 total and must be priced by the regenerated full-grid chain. No RH
claim; the two-channel product theorem keeps both endpoint inputs as
hypotheses.

Evidence: scripts/price_cell2700_minus_correction_2569.py,
results/2569_cell2700_minus_correction_repricing.json,
scripts/price_cell2700_minus_2565.py,
scripts/price_correction_second_2561.py,
results/2561_correction_second_10240.json,
results/2338_exact_interpolation_repair.json,
docs/proofs/2568_row_scope_correction.md,
docs/proofs/2565_correction_second_cell2700_minus.md.
