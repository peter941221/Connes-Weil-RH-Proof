# 2262 — Ball-ization of the 2258 cancellation-split quantities (directed MPFR enclosures)

Date: 2026-09-30

Consumer: the float64 reconstruction of 2258. This record replaces every
2258 reading by a certified enclosure of the same quantity, computed at
256-bit MPFR along the 2234 path with one-sided guards, so the
cancellation factors and pro-rata ratios carry interval certificates
instead of float64 readings.

Verdict: **all four cancellation factors are certified, tightly bracketing
the 2258 readings — `base_M0 [19.25392469924447, 19.25392469936748]`
(reading `19.253924699305877`), `corr_M0 [64.55476819263616,
64.55476819302037]`, `base_D2 [10.296262425921586, 10.296262425988186]`,
`corr_D2 [61.12031609013271, 61.120316090533244]` — and every failure
count is reproduced exactly: rows `10 / 4 / 11 / 4` nodes over the uniform
budget at the certified LOWER ratios, channels `a` and `b` both `3/30`.
Max float64-reading residual `0` ulp over norms/triangles/shares/family
masses (all four anchors `>=` the certified lower norms). Mask decisions
certified (min `|q - 0.04| = 1.819057697104165e-06`, 0 disagreements, 0
undecided). The certified floor-ratio upper bounds are all `<= 0.00288` of
the budget (the float64 floor readings are cancellation noise at the
`S ~ 1e19` scale and are kept for audit only). The 2258 conclusions
survive interval certification.**

## Method

Per grid node `x` (committed 2197 grid, `NX = 240001`), each family is
evaluated at 256-bit MPFR with the 2234 operation order; the signed sums
`G_r` accumulate in MPFR RNDN (double precision object slots). Certified
magnitudes use the analytic forms `|g_M0| = |c| phi` and
`|g_D2| = |c| phi hypot(g, h)` (`|e^{i theta x}| = 1` exactly). Every
upper accumulation (`up_sum / up_prod / up_div`) is guarded by one
`nextafter` toward `+inf`, every lower bound by one toward `-inf`; by
induction over nonnegative partial sums each accumulator is a rigorous
one-sided bound (guards are per-operation, so no accumulated-drift
correction is needed; they show up as interval width ~`n · 2^-53`, e.g.
`6e-12` relative on `base_M0`).

Two directed-extraction laws discovered while building this (both fixed
and now canonical):

1. **underflow law**: `phi = e^{-K/q}` underflows float64 to `0.0` near
   the mask edge (`K/q ~ 745`, `phi ~ 1e-326`). A plain relative+absolute
   pad on such an extraction creates `~2^-52 |c| hypot(g,h) ~ 1e6`-scale
   garbage that the `hypot(g,h)` factor amplifies into the D2 magnitudes
   (the 2242 denormal-artifact zone, here at `q ~ 0.04`). Fix: strictly
   positive magnitudes (`phi`, the core modulus) use directed
   `mpfr_get_d(RNDU/RNDD)` conversions with **relative-only** pads.
2. **hypot box law**: `|core| = hypot(g, h)` lower bounds must be
   computed as `hypot(boxmin|g|, boxmin|h|)` (box min-abs, `0` when the
   box straddles), and uppers as `hypot(boxmax|g|, boxmax|h|)`. Using
   `hypot(max(0, g_l), max(0, h_l))` collapses the dominant D2 zone
   (`h ~ 0`, `g < 0` near `x = 0`) to `~0` and loses an order of
   magnitude of the triangle lower bound (`tri_l` landed at `1.05x`
   instead of `10.3x`).

## Results

```text
row       cancellation certified          reading (2258)     fails  pass
base_M0   [19.25392469924447, ...67348]   19.253924699305877 10/30  20/30
corr_M0   [64.55476819263616, ...02037]   64.55476819282815   4/30  26/30
base_D2   [10.296262425921586, ...88186]  10.296262425954872 11/30  19/30
corr_D2   [61.12031609013271, ...33244]   61.12031609033278   4/30  26/30
```

Row norms (certified) vs 2234 anchors: `[2.0033357887425325,
2.0033357887486734]`, `[913.4469710789731, 913.4469710817222]`,
`[6688.576604749533, 6688.576604770359]`, `[1526140.6871854812,
1526140.6871905248]`; every anchor `>=` the certified lower bound
(consistency of two independent upper-bound pipelines). Channels
`a = base_D2 x corr_M0` and `b = corr_D2 x base_M0` both fail at `3/30`
nodes at the certified lower diagonal ratios. Certified max single-node
ratios (lower) `21.806 / 25.331 / 19.866 / 25.850` vs the 2258 readings
`21.806 / 25.331 / 19.866 / 25.850` (agreement to 10 significant digits).

Deep-`phi` note: in the band `q` within a few percent of the mask edge the
float64 readings themselves carry a relative error up to `(K/q) · 2^-53 ~
1e-12` from the float64 rounding of the exponent feed; the certified
enclosures bound the true values there, and the aggregate comparison is
unaffected (0 ulp residuals).

## Nonclaims

- the certified objects are the true mathematical quantities with the
  committed 2258 mask semantics; the float64 readings carry their own
  ~1e-15 (aggregate) / ~1e-12 (deep-phi) rounding, reported as ulp
  residuals;
- the float64 floor readings are cancellation noise (`ag - (S - AG)` at
  the `1e19` scale); the certified floor enclosures are the meaningful
  objects;
- the signed pieces and the Hall top-3 datum of 2258 are not part of this
  certification (informational there);
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_cancellation_split_ball_2262.py`
  (12-worker chunked, MPFR 256-bit, SLACK-pad `2^-52`, one-nextafter
  guards);
- artifact: `results/2262_cancellation_split_directed.json`
  (md5 `1277bfe4f9850174174f654d5520295f`);
- machinery: `scripts/routea_weighted_zero_direct_product_outward_2234.py`
  (MPFR path), `scripts/routea_weighted_zero_cancellation_split_2258.py`
  (semantics, mask);
- predecessor: `docs/proofs/2258_routea_weighted_zero_cancellation_split.md`.