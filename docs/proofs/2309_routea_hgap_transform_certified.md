# 2309 — TRANSFORM-SIDE-CERTIFIED: the hgap finite-window transform majorant is machine-enclosed; window + 2307 tail closes hgap at 477248.99 / 1e7 (20.95x margin)

Record 2308 certified the finite-window weight factor but inherited the
transform-side perturbation majorant `T_cell` from the 2298/2302 chain at
its declared rounding model (complex128 BLAS gemm leg, model-grade
execution bounds, float64 cell assembly).  This record discharges the
transform side on the same dyadic cells, so that the window half of the
2275/2286/2304 split

    hgap <= window charge + tail charge

is certified end to end on the numeric side, and joined with the 2307
tail closes hgap:

    window + tail <= 477248.99 + 1.96e-27 < 1e7   (margin 20.95x).

Verdict: **TRANSFORM-SIDE-CERTIFIED** at numeric grade — the per-cell
enclosure of `sup_cell |T_ch|` carries mechanically counted float64
execution budgets on the exclusive-extended path (`mpmath.iv` cell
assembly, iv `error_terms`), the certified weight side is the 2308
certificate on the same cells, and the object difference radii are the
2299/2301 iv ledger.  `hgap_closed` is TRUE at numeric grade: the whole
chain 2275 split / 2308 weight / 2309 transform / 2307 tail is now
interval-certified on the numeric side.  No Lean discharge, no producer
GO, no RH claim.

+-------+-------+---------------------------+-----------+----------------+---------+--------+
| denom | cells | certified charge upper    | x budget  | x 2308 charge  | t_sum   | s      |
+-------+-------+---------------------------+-----------+----------------+---------+--------+
|  64   |  5120 | 8.638192915438176e+05     | 0.086382  | 0.999999997379 | 8.951e-9| 191.4  |
| 128   | 10240 | 5.718159145338645e+05     | 0.057182  | 0.999999998569 | 8.895e-9| 405.8  |
| 256   | 20480 | 4.772489858117574e+05     | 0.047725  | 0.999999999137 | 8.867e-9| 877.8  |
+-------+-------+---------------------------+-----------+----------------+---------+--------+

The last column ("x 2308 charge") is the decisive cross-record reading:
replacing the model-grade `T_cell` by its certified enclosure moves the
charge by only -2.62e-9 / -1.43e-9 / -8.63e-10 relative -- the certified
majorant is a hair TIGHTER than the inherited model-grade one (budgets
sit pointwise below the model errors on all 14 channel/order slots), and
the 2302/2308 charge predictions are confirmed to 9 decimal places.

The certified charge intervals (36+ digit renderings of 266-bit
endpoints) are cohesive to < 1e-38 relative:

+-------+------------------------------------------------------------+
| denom | charge interval (lower endpoint rendering)                 |
+-------+------------------------------------------------------------+
|  64   | 863819.291543817596583565825334104280136223031             |
| 128   | 571815.914533864540335078018146575987167652553             |
| 256   | 477248.985811757424832064525248710763476013974             |
+-------+------------------------------------------------------------+

## What was certified, and how

The quantity is the 2298/2302 transform-side cell majorant

    T_cell = error_terms(sup_b, sup_c; r_b, r_c)
           = sb^2 (2 sc rc + rc^2) + sc^2 (2 sb rb + rb^2)
             + (2 sb rb + rb^2)(2 sc rc + rc^2),

with `sup_ch` the per-cell supremum of the generalized-series derivative
sum over the Taylor degree 6, `r_b / r_c` the object difference radii
(3.60197836093736384022473499768301276290e-14 and
6.49325319027400810934590685351926100249e-11, iv ledger 2299/2301), and
the charge accumulated over the same dyadic cells as 2308:

    charge <= sum_cells h * K_sup * A_sup * T_cell.

**Exclusive-extended evaluator.**  `evaluate_jets_extended` keeps the
order-0 leg bitwise identical to the stored evaluator (same operations,
same order, same final complex128 cast -- enforced by the
`np.array_equal(jets[0][sub], stored)` control on every rung), and
replaces the complex128 BLAS gemm for orders >= 1 by explicitly counted
clongdouble elementwise contractions
`inner_k += polynomial[:, degree, :][:, None, :] * moments[:, degree][None, :, None]`
over the 768 panels.  The cross-path control against the 2302
`evaluate_derivatives` gemm leg measures max |difference| / (budget +
model error) <= 2.12e-4 on every rung.

**Mechanical budgets.**  Each stored float64 complex jet becomes an
interval through the exact rational cast (`float.as_integer_ratio`) plus
a counted budget `budget_ch,k = M_ch,k R_k`:

+-------+--------+---------------+--------------------+--------------------+
| order | counts | R upper       | base budget        | corr budget        |
+-------+--------+---------------+--------------------+--------------------+
|   0   |   546  | 1.1321e-15    | 6.13041774679e-14  | 9.95627332455e-11  |
|   1   |   609  | 1.1355e-15    | 2.53200255383e-12  | 4.11216829352e-09  |
|   2   |   673  | 1.1390e-15    | 1.04581511356e-10  | 1.69848476036e-07  |
|   3   |   736  | 1.1425e-15    | 4.31937603681e-09  | 7.01500129196e-06  |
|   4   |   800  | 1.1459e-15    | 1.78403653195e-07  | 2.89741353146e-04  |
|   5   |   863  | 1.1494e-15    | 7.36820959669e-06  | 1.19665431765e-02  |
|   6   |   927  | 1.1529e-15    | 3.04324383595e-04  | 4.94246373991e-01  |
+-------+--------+---------------+--------------------+--------------------+

`M_ch,k = 2 r (2 pi support)^k L1COEF_ch` with `L1COEF` the iv sum of
exact-ratio |coefficients| over all 30 families x 768 panels, grouped
before any triangle bound (the 2291/2308 ladder law one level deeper);
`R_k = C_k u_ext (1 + 2 u_ext) + ((1 + pi_gap)^k - 1) + E_moment +
E_phase + 2 u2/(1 - u2) + 1e-40` with `u_ext = 2^-64` (iv unit,
`mpmath.iv` object), `pi_gap = 1.5968198827228853e-20`, `E_moment =
7.138601127853249e-17`, `E_phase = 8.090813274909634e-16`, and `C_k` the
documented compiled-operation count (546, 609, 673, 736, 800, 863, 927).

**Budget validity and tightness.**  All 14 (channel, order) budgets are
pointwise below the 2302 model execution bounds (ratios 0.5989 at order 0
decaying to 0.0458 at order 6), so the certified cell majorant is the
strictly tighter one; the dps-100 reference control
(`MODE=reference`, 24 samples, orders 0/1/3/6) measures the actual
execution residuals against the budgets: worst allowance ratio
9.617e-4 (base, order 0, xi = -3.605: residual 5.896e-17 vs budget
6.130e-14), i.e. the budgets dominate the true error by >= 1000x at
every sampled point.

**Subsample sandwich.**  On 65 cell centres per rung, the certified T
interval must sit above the stored-jet witness (the same Taylor assembly
with ZERO error padding -- the nonzero budgets and interval rounding can
only widen it: min margin observed 1 + 3e-12) and below the model-grade
T (max margin 1 - 6e-12, as budgets are tighter).  A certificate that
crosses either wall on the subsample fails the run -- the earlier
direction-inverted wall caught a real control-design error, see lessons.

**Weight side and closure.**  The weight factor `K_sup A_sup` on the
same cells is the certified 2308 interval ladder; the directed product
sum is accumulated in `mpmath.iv` at dps 80 with cell intervals cohesive
to < 1e-38.  Closure against the 2307 tail certificate:

+--------------------------------------------------+---------------------+
| window charge upper (best rung 256)              | 477248.9858117574   |
| 2307 tail best upper (order 36)                  | 1.9586382184619955e-27 |
| sum                                              | 477248.9858117574   |
| budget                                           | 1e7                 |
| margin                                           | 20.953423259749634  |
+--------------------------------------------------+---------------------+

Even the cheapest 2307 tail rung (order 16, 6918.973606907222) closes:
sum 484167.9594186646, margin 20.66x.

## Controls (all rungs)

+---------------------------+---------------------+--------------------------+
| control                   | 64 / 128 / 256      | meaning                  |
+---------------------------+---------------------+--------------------------+
| order_zero_bitwise        | true / true / true  | order-0 leg verbatim     |
| cross_path_max_ratio      | 1.71e-4 / 6.81e-5 / 2.12e-4 | ext vs 2302 gemm  |
| pure_witness_min_margin   | 1+4.1e-12 / 1+3.5e-12 / 1+3.2e-12 | above witness |
| model_grade_max_margin    | 1-1.8e-11 / 1-1.0e-11 / 1-5.5e-12 | below model  |
+---------------------------+---------------------+--------------------------+

Plus: module selftest 5/5 PASS (26.5 s; includes the strict order-0
verbatim control against the stored evaluator and the
budgets-below-model-errors check), artifact selftest 17/17 OK.

## Lessons locked

- `ivmpf.a` and `.b` are degenerate INTERVALS; their sum can widen
  (`a + b` need not be representable), so `float((a + b) / 2)` raises on
  non-zero width.  Use `.mid` (mpi_mid at ctx.prec, degenerate by
  construction) for float readouts of interval endpoints.
- The soundness direction of a TIGHTENED majorant is measured against
  the zero-padding stored-jet witness, not against the model-grade T:
  budgets below model errors put the certified T strictly BELOW the
  model T, so "certified >= model" is the wrong sign to assert.
- A plain `mp.mpf` unit mixed into iv arithmetic raises "can only create
  mpf from zero-width interval"; `mp.iv.prec`-scale units must be built
  as `mp.iv.mpf(2) ** -k` (here 2^-64 extended, 2^-53 stored cast).
- `mp.iv.mpf([lo, hi])` list form is the house constructor for
  re-wrapping an existing interval; the two-argument form does not exist.
- The extended-jets polynomial tensor is (chunk, length, 2): index
  `polynomial[:, degree, :]` before broadcasting, not `[degree]`.

## Nonclaims

- The exclusive-extended path keeps the platform contract
  (round-to-nearest, 64-bit significand, smoke checked, not a formal
  machine proof); operation counts assume one rounding per compiled
  operation and no reordering beyond the counted structure (FMA only
  shrinks errors).
- Structural lemmas are inherited: the 768:6 panel interpolation and
  envelope model (2296/2297), carrierwise grouping (2297), the
  mass-based sup-derivative and Lagrange ladders (2293/2302), the
  `error_terms` propagation (2298), the 2298-2302 integrand
  identification, and the 2275/2286/2304 split.
- The object difference radii inherit the 2299/2301 interval prices
  (interpolation-model structural assumptions retained).
- The weight factor and its substrate trusts (libm cos/sin, numpy
  pairwise summation, 2280 convention) are the 2308 certificate, cited
  not re-derived.
- Numeric grade only: no Lean hgap discharge, no producer GO, no RH
  claim.

## Provenance

- script: `scripts/routea_hgap_transform_cert_2309.py`
- artifacts: `results/2309_hgap_transform_certified.json`,
  `results/2309_transform_step_den{64,128,256}.json`,
  `results/2309_reference_controls.json`
- selftests: `MODE=selftest` (module, 5 tests),
  `scripts/routea_hgap_transform_cert_selftest_2309.py` (artifact, 17 tests)
- upstream: `results/2308_window_weight_certified.json` (weight side),
  `results/2307_hgap_tail_certified.json` (tail),
  `results/2301_regenerated_carrier_evaluator.json` +
  `results/2299_carrier_refined_remainder_screen.json` (radii ledger),
  `results/2275_gap_owner_audit.json` (owner capture)

Next registered obligation: the localized [-2, 2] instrument (window
successor) at interval grade, and the Lean absorption of the residual
hypotheses with `hgap` now closed at numeric grade end to end.