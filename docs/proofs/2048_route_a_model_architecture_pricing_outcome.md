# 2048 — Route A link L2, third architecture: panel-local model priced VIABLE

Verdict: **MODEL-L2-VIABLE** at the registered owner (one-copy G8-H), with
the L3 enclosure outstanding.  Probe: `scripts/routea_interval_kernel_model_2048.py`,
artifact `results/2048_interval_kernel_model.json`.  The direct architecture
died at h = 0.05 (record 2043) and the IBP architecture died at h <= 0.01
(record 2046); this record prices the third and last registered L2
architecture (panel-local model, registered unpriced in record 2046
section 4) and finds it under budget by 7.8x at h = 0.001.

## 1. Readings

Ladder (owner one-copy G8-H, `rho = 0.6 + 40.9187190121475i`, scale 0.88,
support 9.504, book 1647 prime powers, window [-40, 40], fine grid
`dxi = 0.00025`, 320001 points, `int_g = 2.7090445469307654e+19`,
`gmax = 3.790609580492212e+19`, budget `1e19`, hard bar `1.11e20`):

```
+--------+---------+----------------+----------------+----------+
| h      | panels  | TV_sup2        | charge         | x budget |
+--------+---------+----------------+----------------+----------+
| 0.05   |   1600  | 3.542334e+22   | 5.070492e+21   | 507.05   |
| 0.02   |   4000  | 2.912943e+22   | 6.671333e+20   |  66.71   |
| 0.01   |   8000  | 2.578520e+22   | 1.476356e+20   |  14.76   |
| 0.005  |  16000  | 2.365777e+22   | 3.386370e+19   |   3.386  |
| 0.002  |  40000  | 2.226225e+22   | 5.098585e+18   |   0.510  |
| 0.001  |  80000  | 2.177824e+22   | 1.246934e+18   |   0.125  |
+--------+---------+----------------+----------------+----------+
```

Every row satisfies the charge law of section 2 exactly
(`factorization_rel <= 2.0e-16` between the two assembly orders).  The
crossing sits at

```
h* = sqrt(8 * budget / (C_book * TV_sup2)) ~ 2.8e-3   (~28k panels).
```

Nodal-enclosure coefficient and headroom
(`Coef1(h) = sum_k c_k sum_i |W_i(k)|`, `dg* = (budget - charge)/Coef1`):

```
+--------+-------------+-----------------+
| h      | Coef1       | dg*             |
+--------+-------------+-----------------+
| 0.01   |  22864.209  | -6.0197e+15     |
| 0.005  |  23211.184  | -1.0281e+15     |
| 0.002  |  23309.192  | +2.1028e+14     |
+--------+-------------+-----------------+
```

Verdict line: best row h = 0.001, charge `1.246934e+18` + model float
slack `5.536e+10` + archimedean charge `3.917065e+16` = **`1.286104e+18`
= 0.129 x budget** (< budget -> VIABLE; the hard bar is 86x above the
total, so the verdict is not close to gray).

Anchors (all pass):

```
+----+--------------------------------------+--------------------------------+
| id | what                                 | reading                        |
+----+--------------------------------------+--------------------------------+
| A1 | direct-architecture 0.05 row         | width_mean 569.0868 vs 569.087  |
| A2 | interval sigma containment           | 4/4 (u = 0, 2pi, 20pi, 80pi)   |
| A3 | closed-form blocks                   | mp rel 2.42e-27, ind 1.18e-27, |
|    |                                      | float64 abs 4.21e-15 < 1e-13   |
| A4 | tent partition of unity              | worst rel 2.70e-14             |
| A5 | remainder-bound validity on real g   | 0 violations, worst 0.6552,    |
|    |                                      | agg loss median 57.47x         |
| A6 | grid stability at the two finest     | rel 1.02e-6 / 5.19e-7,         |
|    |                                      | TV_sup2 monotone in h          |
| A7 | cross-read vs record 2046 stencil    | rel 0.0206                     |
+----+--------------------------------------+--------------------------------+
```

## 2. The architecture and the charge law

On each panel `[x_i, x_i + h]` write `g = l_i + r_i` with `l_i` the chord.
The model part is closed form: with `BC = int cos`, `BL = int (t-a) cos`
(both evaluated by the small-angle-stable I1/I2 form, verified against
mpmath quadrature at 2.4e-27), the panel integral is

```
I_i = g(x_i) * BC(om) + (Delta g_i / h) * BL(om).
```

The remainder is charged by the crude L1 bound: linear-interpolation error
gives `|r_i| <= (h^2/8) sup_panel |g''|`, and one panel contributes at most
`(h^3/8) sup |g''|` per book term.  Summing the book (`c_k = 2 Lambda(k)/sqrt k`,
`C_book = sum c_k = 458.0476`) and the panels:

```
charge(h) = (h^3/8) * C_book * sum_panels sup|g''|
          = (h^2/8) * C_book * TV_sup2(h),
TV_sup2(h) = sum_panels h * sup_panel |g''|   (non-decreasing in h).
```

Two facts make this architecture work where direct and IBP did not:

1. the model part has no cancellation structure to lose -- every panel
   integral is a closed form in (BC, BL) whose float64 echo sits at the
   absolute floor of O(1) trig evaluations (A3);
2. the charge is second order in h, and the ladder confirms the law
   exactly at every rung, so the threshold is a real number, not a trend.

Correction of the record-2046 section 4 registration: the charge form
registered there as `(h^2/4) * C_book * TV2` is 2x conservative; the
panel-local model charges `(h^2/8) * C_book * TV_sup2`.  The registered
viability estimate `~h = 0.001` survives the correction (it improves).

## 3. What it moves

- **L1 (nodal enclosures) is no longer free**: `dg*` turns positive only
  at h = 0.002 (+2.10e14) and is negative at 0.005 and 0.01.  The L1
  requirement is now a stated budget: enclosures `sum_i |Delta g_i|` must
  sit below `dg*(h)`.
- **L3 (enclosed sup |g''|) is the binding external input.**  The whole
  charge rides on `sup_panel |g''|`, and this record reads floats from the
  committed 2037 pipeline (stencil estimate, no enclosure).  The L3
  charge must be shown of the same order as the remainder term; this is
  registered, not priced.
- The model part's own float64 execution is 9 orders below the remainder
  charge (`dg_reference`: at 1e-15 relative error the charge is
  8.836e+08; the assembled-and-measured slack is 5.536e+10), so no
  enclosure of the model part is needed.
- The crude bound is nearly sharp per (panel, k) at 0.655 (A5), so the
  refinement headroom is the aggregate booking loss (57.47x median),
  registered, not priced.

## 4. Instrument notes

1. **Gate failures are adjudicated against structural bounds, never by
   loosening the gate.**  The first version of the independent
   product-rule check omitted the `/om` on `h sin(om b)`, so the check
   read rel_ind up to 47.6 and forced ANCHOR-FAIL while the checked closed
   form agreed with mpmath quadrature at 2.42e-27.  The adjudication: the
   term's analytic ceiling is `|h sin(om b)/om| <= h/om`, and the coded
   term was `1.97e-3 > 4.59e-4` -- a structural violation, so the CHECKER
   was wrong, not the checked.  The fixed rig now carries that ceiling as
   an explicit assertion (`t1_ceiling` in A3 rows).  This is the fourth
   instance of the batch's gate-at-the-design's-floor theme, with the
   twist that the failure was in the instrument.
2. **A relative-only gate would have blamed the wrong object.**  The
   float64 echo's relative measure reads 3.92e-12 only because a block
   passes through a zero; its absolute value is 4.21e-15, at the floor of
   O(1) trig evaluations.  The gate is on the absolute value with the
   scaling table in the run log.
3. **Cheap diagnostic paths must replicate the full path's call order.**
   `--a3only` reproduces A3 in 0.3 s (vs 285 s full) and found the
   transcription bug only because it kept the quad-before-product-form
   order of the real run.
4. Monotonicity anchors are written in the ladder's actual direction:
   `TV_sup2` is non-decreasing in h and the ladder runs decreasing, so
   the anchor reads `rows[i].TV >= rows[i+1].TV`.

## 5. Scope and non-claims

- float `g`, `g'` from the committed 2037 pipeline; `sup|g''|` is a float
  stencil estimate -- L3 (enclosed sup) NOT implemented;
- nodal enclosures (L1) charged as zero; `Coef1` and `dg*` are reported
  instead;
- the archimedean term uses the committed direct interval method at
  `dxi = 0.05` only (smooth; small);
- no full-line tail (L4 separate); no coefficient enclosure;

- not a producer theorem; not RH.  This record prices one architecture
  under one owner; it does not construct the L2 link.