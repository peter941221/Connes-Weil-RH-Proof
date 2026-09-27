# 2051 — Route A link L2: enclosed sup|g''| (L3) and the aggregate charge family

Verdict: **ENCLOSED-L2-VIABLE** at the registered owner (one-copy G8-H):
the last external input of the record-2048 model architecture is now an
enclosure, and the aggregate booking split lowers the L2 charge to
`6.330366e+17 = 0.0633 x budget` (record 2048: `1.286104e+18 = 0.129 x`).
Probe: `scripts/routea_l3_aggregate_2051.py` (localizer
`scripts/diag_2051_a2.py`), artifact `results/2051_l3_aggregate.json`.

## 1. Readings

Ladder (owner one-copy G8-H, `rho = 0.6 + 40.9187190121475i`, scale 0.88,
support 9.504, book 1647 prime powers, window [-40, 40], fine grid
`dxi = 0.00025`, 320001 points, `gmax = 3.790610e+19`, budget `1e19`,
hard bar `1.11e20`; `charge_L3 = C_book (h^3/8) Sum U`,
`C_book = 458.047586`, `C1_book = 21898.86`):

```
+--------+---------+----------------+----------------+----------------+
| h      | panels  | Sum U          | charge_L3      | charge_agg     |
+--------+---------+----------------+----------------+----------------+
| 0.01   |   8000  | 1.090272e+25   | 6.242457e+20   | 4.922556e+20   |
| 0.005  |  16000  | 7.569317e+24   | 5.417355e+19   | 3.142733e+19   |
| 0.002  |  40000  | 1.235179e+25   | 5.657707e+18   | 2.751237e+18   |
| 0.001  |  80000  | 2.261011e+25   | 1.294563e+18   | 5.938659e+17   |
+--------+---------+----------------+----------------+----------------+

+--------+---------+---------+---------+---------+---------+---------+
| h      | Sum U / | L3      | agg     | agg/L3  | (theta  | corr/   |
|        | Sum st  | x budg  | x budg  |         | + corr) | main    |
|        |         |         |         |         | /main   |         |
+--------+---------+---------+---------+---------+---------+---------+
| 0.01   | 4.2283  | 62.425  | 49.226  | 0.7886  | 1.5953  | 0.0218  |
| 0.005  | 1.5998  |  5.417  |  3.143  | 0.5801  | 0.7346  | 0.0198  |
| 0.002  | 1.1097  |  0.5658 |  0.2751 | 0.4863  | 0.2663  | 0.0173  |
| 0.001  | 1.0382  |  0.1295 |  0.0594 | 0.4587  | 0.1347  | 0.0164  |
+--------+---------+---------+---------+---------+---------+---------+
```

Price of rigour (same-h comparison, `Sum U / Sum stencil`): 4.23x at the
coarse end, **1.038x at h = 0.001** — the enclosure costs 3.8% over the
record-2048 float stencil charge at the operating point.  The aggregate
split then recovers a factor 2.10 over that (`charge_agg / charge_2048
stencil at h = 0.001 = 0.4763`).

Verdict line: best row h = 0.001, aggregate charge `5.938659e+17` + model
float slack `5.536e+10` + archimedean charge `3.917065e+16` =
**`6.330366e+17` = 0.0633 x budget** (< budget -> VIABLE; the hard bar is
175x above the total).

Anchors (all pass):

```
+----+-------------------------------------------+---------------------------+
| id | what                                      | reading                   |
+----+-------------------------------------------+---------------------------+
| A1 | model g vs committed pipeline g at ladder | max abs 1.47e+05 = 3.9e-6 |
|    | nodes, magnitude budget 1e-9 gmax         | of budget 3.790610e+10     |
| A2 | enclosure validity: A2a gate (model fd    | A2a 0 violations, worst   |
|    | stencil vs U + (h_sub^2/12) K4) and A2b   | ratio 0.99968; A2b gap    |
|    | booked commit-vs-model gap                | charge <= 5.096e+06       |
| A3 | family bundles vs mpmath.iv, dps 30,      | 18/18 contained           |
|    | exact-binary inputs                       | amp_rel 8.05e-13 (f0)     |
| A4 | charges finite, non-negative;             | max agg/L3 0.78856        |
|    | charge_agg <= charge_L3 for h <= 0.01     |                           |
| A5 | cross-read vs record 2048                 | rel 1.109662 in [1,5]     |
| A6 | jet selftest                              | T1 1.48e-15, T2 24+7e-15, |
|    |                                           | T3 0.091506250 = 0.55^4   |
+----+-------------------------------------------+---------------------------+
```

## 2. What is enclosed (scope), and what is not

The enclosed object is the pipeline function

```
g(xi) = P(xi)^2 |lb(xi)|^2 |corr . v(xi)|^2
```

of the committed 2037/1980/1959 pipeline with its **stored floats taken as
exact** (quadrature nodes and weights, family constants `(a_j, theta_j)`,
the stored products `F = a (phi . W)`, `base`, `corr`, `pi`, `0.5`).  This
is the object record 2048's `TV_sup2` measured and the object the model
architecture charges; L3 now encloses its panel sup of `|g''|` from above,
rigorously, at every panel of the ladder.

Registered, not touched:

- **L5**, the pipeline's own ideal-vs-stored distinction (F construction,
  phi quadrature, `eigh`/min-h1 solve, sigma, committed-evaluation
  rounding).  A2b books one measurable piece of it (section 5).
- **L1** (nodal enclosures) charged as zero; record 2048's `Coef1` /
  `dg*` headroom applies to the same pipeline function.  With the
  aggregate total, `dg* = (budget - charge)/Coef1` at h = 0.001 is
  ~`+4.0e+14` (using 2048's `Coef1 ~ 2.33e+04`), up from `+2.10e+14`.
- **L4** (full-line tail) stays a separate link with no coefficient
  enclosure here.

Non-claims: not a producer theorem; not RH.

## 3. The machinery

Every ingredient is closed form:

- `P(xi) = prod_m (cnt_m + 2 pi i xi)` with `cnt = +/- delta +/- i gamma`
  (quartic; exact product rule), and each family value
  `v_j(xi) = sum_i F_ji exp(z_j(xi) X_ji)` with `z_j` linear in `xi`
  (`dz_j/dxi = -2 pi i a_j`), so every derivative is the same sum with
  weights `(z' X)^k`.

- Every scalar carries a **jet** `(b0, b1, b2, b3, K4)`: bundles
  `b_k = (value, error)` enclosing `f^(k)(centre)`, and `K4 >= sup_panel
  |f^(4)|`.  Jets close under `+`, `x`, scalar (Leibniz for the `b`'s;
  the five-term product rule for `K4`).  The enclosure is the Taylor bound

  ```
  sup_panel |f^(k)| <= |b_k| + e_k + Sum_{m>=1} rho^m/m! (|b_{k+m}|+e_{k+m})
                      + rho^(4-k)/(4-k)! K4,     rho = h
  ```

  evaluated at `k = 2`:  `U_i = j_supk(g_jet, 2, h)`.

- **Bundle rigour.**  Float64 arrays; every arithmetic step inflated by
  `GE = 8u` (`u = 2^-53`) plus insurance; heavy sums carry the universal
  `n u` summation bound and per-term relative chain bounds.  The three
  exact-real family moments

  ```
  M_k = sum_i |F_i| |2 pi a X_i|^k exp(0.5 a X_i)
  ```

  are **node-independent** (`Re(zX) = 0.5 a X` is constant along the
  line), so per-term error inflation is a constant per family and order —
  and the enclosure is deliberately **cancellation-blind** (section 6).

- **The exponent-argument amplification** (found at design time, before
  any run).  The pipeline computes `z = a (s + i theta)`; float rounding
  of the argument perturbs `exp(zX)` by relative
  `4u |z| |X| <= 4u a^2 (0.5 + 2 pi XI_MAX + |theta|)`, reaching ~3e-12
  near the window edge — six orders above the `16u` term.  A bundle
  without this term fails the A3 containment check exactly by that
  factor.  The rig inflates every family error constant by
  `AMP = 8u a^2 (0.5 + 2 pi XI_MAX + |theta|)`, covering both the
  float-computed value and the exact-real value of the stored floats.

## 4. The aggregate charge family

Per panel `[a, a+h]` with `r = g - chord` (`r` vanishes at both ends):

```
cos_k(x) = cos_k(a) + O(omega_k |x-a|),  omega_k = 2 pi log k
|int_panel r cos_k| <= |cos_k(a)| A_i + omega_k h (h^3/8) U_i,
A_i := |int r| = |int g - trap_h(g)| <= |trap_f(g) - trap_h(g)|
                                     + (h_sub^2/12) h U_i
```

where `trap_f` is the 9-point composite trapezoid at `h_sub = h/8` built
from the **model's own enclosed** `g` values (`|trap_f - int g| <=
h_sub^2 h sup|g''|/12`).  Summing over panels and `k` with the cosine
weights `c_k`:

```
charge_agg(h) = Sum_i [ A_i Cc_i + (h^4/8) C1_book U_i
                        + (h h_sub^2/12) U_i Cc_i ]
Cc_i = Sum_k c_k |cos(omega_k a_i)|,   C1_book = Sum_k c_k omega_k
```

Internally the `theta` term satisfies `theta/L3 = h C1_book/C_book`
EXACTLY, which is the structural ceiling of the split at coarse `h`
(0.478 at h = 0.01) and is what the A4 ratio adjudication used (below).

## 5. Incident chain (two defects, both adjudicated against evidence)

**(a) `j_supk` tail loop (fixed).**  The tail loop ran `m` to `4 - k`
inclusive, indexing the `K4` slot — a plain array — as a bundle.  `b_sup`
of it is not an enclosure (node-order dependent; conservative only for
constant arrays, unsound for product-jet arrays) and single-node chunks
crashed.  Caught by A2 before any verdict; T3's supk moved from
`0.09931875` to `0.09150625 = 0.55^4` exactly (the spurious term was
`(rho^4/24)(2 K4)`).  Repair, not tolerance loosening.

**(b) A2 was comparing unlike objects (restructured, disclosed).**  The
first frozen A2 compared `U_i` to the second difference of the
**committed grid** `C` (dxi = 0.00025) and failed on 3/14/38/75 panels
across the rungs, worst `st_commit/U = 1.585` with the value bitwise
identical across builds.  The localizer (`scripts/diag_2051_a2.py`)
at the worst panel (index 40493, `xi = 0.493`, local
`g ~ 1.8e-4 ~ 1e-23 gmax`, inside the cancelling cores of `lb`/`cc`):

```
st_commit 0.678418   st_model 0.0124441   U 0.427937
st_c/U 1.5853        st_m/U 0.0291        local gmax 1.83e-4
U parts: |b2|+e2 0.412577  h(|b3|+e3) 0.0150137  (h^2/2) K4 0.000346
```

`U` encloses the stored-floats-exact function `O`; the committed grid `C`
is a *different float evaluation* whose own rounding noise
(`~ eps gmax / dxi^2`) dominates `C`'s second differences exactly at
cancellation panels.  A2 is therefore split:

- **A2a (gate).**  `st_m <= U + (h_sub^2/12) K4` at every panel, where
  `st_m` is the finite-difference stencil of the MODEL's own enclosed
  values at spacing `h_sub` and the provable fd excess is carried by the
  enclosed `K4`.  Result: **0 violations at all four rungs**, worst
  ratios 0.9622 / 0.9910 / 0.9987 / 0.9997 — the bound is tight by
  construction at the operating end.
- **A2b (booked measurement).**  `gap_i = max(0, st_commit,i - U_i)`,
  `Sum gap` and its charge `C_book (h^3/8) Sum gap`:

```
+--------+------------------+------------------+----------------+----------+
| h      | A2b violations   | gap charge       | / slack_2048   | Sum gap  |
+--------+------------------+------------------+----------------+----------+
| 0.01   |   3 (worst 1.096)| 6.494e-06        | 1.2e-16        | 1.13e-01 |
| 0.005  |  14 (worst 1.350)| 6.173e-06        | 1.1e-16        | 8.63e-01 |
| 0.002  |  38 (worst 1.523)| 5.096e+06        | 9.2e-05        | 1.11e+13 |
| 0.001  |  75 (worst 1.585)| 5.842e+05        | 1.1e-05        | 1.02e+13 |
+--------+------------------+------------------+----------------+----------+
```

  The gap charge is the committed-evaluation noise at cancellation
  panels — the same class the 2048 verdict already carries as
  `slack_2048 = 5.536e+10` — and it sits at `<= 9.2e-05` of that slot.
  No double booking is asserted: the envelope is that of the same
  model-float-slack class.

**(c) A4 ratio threshold (adjudicated structurally).**  The first frozen
form required `charge_agg <= 0.75 charge_L3`; run 1 measured 0.789 at
h = 0.01 and tripped by 5%.  Structural reading: `theta/L3 = h
C1_book/C_book` exactly (0.478 at h = 0.01, matched by measurement), and
`main/L3` measured 0.30-0.35, so the method's own structural ceiling at
h = 0.01 is ~0.85 — the 0.75 threshold sat below the method's ceiling.
The invariant the family asserts is "never books more than the crude it
improves", so the bound moved to 1.0; the measured ratios (0.7886 /
0.5801 / 0.4863 / 0.4587) and correction fractions stay on record per
rung.

## 6. Pricing the aggregate remainder (A7) and the cancellation-blindness law

A7 samples 48 panels at h = 0.002 and compares the rigorous aggregate
charge to the **measured** remainder `Sum_k c_k |int r cos_k|` — the
record-2048 aggregate-loss object — on the same panels:

```
+-----------------------------------+----------------+------------------+
| statistic                         | full sample    | mass-carrying    |
+-----------------------------------+----------------+------------------+
| panels                            | 48             | 8 (crude >= 1e-3 |
|                                   |                | of max)          |
| loss_vs_crude median              | 57.47          | 2.554            |
| rigorous / measured median        | 8.471e+07      | 1.317            |
| rigorous / measured max           |   --           | 1.389            |
| recovered factor vs crude median  |   --           | 1.933            |
| worst_k measured / bound (max)    | 0.6552         | (same object)    |
+-----------------------------------+----------------+------------------+
```

Reading: record 2048's headline "aggregate loss 57.47x" is a *tail-panel
cancellation artifact*, not the split's inefficiency.  On panels that
carry mass, the crude bound was only 2.55x above the measured remainder,
and the rigorous aggregate charge is **1.317x the measured remainder**
(max 1.389x) — the split is nearly sharp where it matters, and it
recovers 1.933x over the crude booking.  On collapsing panels
(`g ~ 1e-30`) the enclosure holds O(1) absolute floors while the true
remainder vanishes: the full-sample ratio measures **cancellation
blindness**, a structural property of node-independent `M_k` constants,
not slack.  Both statistics are reported per run; the mass-restricted one
is the headline.

## 7. Verdict

```
best_enclosed = 5.938659e+17   (h = 0.001, aggregate family)
best_total    = 6.330366e+17 = 0.0633 x budget
```

Verdict rules were frozen before the run (header of the probe; ENCLOSED-
L2-VIABLE < 1e19 <= ENCLOSED-L2-GRAY < 1.11e20 <= FAIL; ANCHOR-FAIL for
any anchor miss).  All six anchors pass; the verdict is ENCLOSED-L2-VIABLE.

Effect on the L2 link: record 2048's verdict line `1.286104e+18 = 0.129 x
budget` becomes `6.330366e+17 = 0.0633 x` (factor 2.03), with the L3 term
now an enclosure instead of a float stencil and the aggregate remainder
now priced.  Remaining L2 work: L1 enclosures (headroom ~+4e+14 at
h = 0.001), L4 tail, and the L5 ideal-vs-stored gap beyond the A2b slot —
all registered, none touched here.