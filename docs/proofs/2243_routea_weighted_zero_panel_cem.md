# 2243 — Composite-EM panel landing on the certified zero count

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **viable**. With `Z = 0` certified (2242), the panel allowance
drops to `panel_cem = (dx^2/12)(2 a_max) M_k(sigma)` with the risk term
`N_risk = 0`, and the 2238 envelope reprices by `5.187365461729664x`:

```text
                       2234                2237 (panel 2234)   2238                2243
C_upper                2.4866178385966296e9 2727859.2133313827  1249100.8031538636  240796.76135588222
tail upper / margin    70.74142972939994   0.07760447056089889 0.03553548732728288 0.006850392090059914
inflation over 2197    32108.532816055962   35.22356982617925   16.12905429459266   3.109295925568858
headroom vs margin     --                   --                  28.14x              146.0x
```

The 2119 coarse transfer product closes with it: `48.428313652912905 x
0.006850392090059914 = 0.3317529367828551` (`3.01x` slack inside the
margin; was `1.721x` over at the 2238 standing).

## The panels and the binding row

`panel_cem` at `sigma = 1` (the row that binds after the recomputation),
against the 2238 measured-cell panels:

```text
            2234              2238               panel_cem (2243)     gain vs 2238
base_M0     1.8076571806532764 0.9194450801774107 0.001034980056666458  888.370x
base_D2     11693.314770969451 6422.964947252888  7.229989871395511     888.378x
corr_M0     2862.4920101295183 1510.5771804832668 1.5948664429589159    947.150x
corr_D2     17018191.948288612 9716500.106800418  9721.552345634816     999.480x
```

Binding row (`sigma = 1.0`, channel a): inflated sums
`base_M0 2.0566210054949954`, `base_D2 7945.304436068302`,
`corr_M0 1196.4645507389077`, `corr_D2 506449430.219294`; coefficient
inflations `1.3417597941262356e-04 / 0.15661735075389552 /
0.2745032452784508 / 320.41481073633196`; then
`C_channel_a = db * mc / (2 pi)^2 = 240796.76135588222` (binds),
`C_channel_b = dc * mb / (2 pi)^2 = 26383391.220194407`. Screen:
`B_upper = 9506275.102584327`, `spectralMultiplicityConstant =
301.83032993648527`, high-shell budget upper `11477128602.720102 =
0.006850392090059914` of the signed-margin anchor `1675397327895.099`
(`1.675397327895099e12`; `146.0x` headroom).

Controls: radii are the 2237 certified values (`1005486.289224448` /
`2057069012.526474`); the chunk-trapezoid sums drift from the committed
2197 values only at binary64 last-ulp level (`2.2e-16 / 5.4e-16 / -1.0e-15
/ -4.6e-16` relative), and the reduction is the 2238 loop bitwise with
only `panel_new -> panel_cem` substituted (same ladders m0..m4, same
coefficient inflation, same `exp(a_max * 0.01)` cover, same
min-of-two-channels composition).

Projection vs landing: the 2238-doc projection (`C_upper
384556.5741856599`, `tail/margin 0.010940194125321153`) applied a
panel-only scalar gain `3.248x` to the 2238 row; the full recomputation
inside the coefficient-inflated sums and the min-of-two-channels
composition gives the gain `5.187365461729664x`, so the landing is
`1.597x` below the registered projection. The four `sigma = 1`
`panel_cem` values themselves reproduce the projection table bitwise
(relative `0.0`), so the difference is entirely the gain composition. The
landing is the number of record; the projection was conservative.

## Gates and arithmetic

The script refuses to run unless `results/2242_zero_count_certificate.json`
reads `ZERO-COUNT-CERTIFIED`; the certificate fields (`min_floor` per
channel, `edge_B2_re_lower_bound = 435200.11369115417`) are copied into the
artifact. The identity behind the substitution is the 2238
composite-trapezoid form: with `Z = 0` the telescoped `Delta` sum is
`g'(x_N) - g'(x_0) = 0` and every surviving term is `dx^2`-rate, so the
risk-cell count drops by certificate, not by measurement.

## What this closes and what it does not

Closed: the 2238 registered composite-EM lever, end to end — certified
zero count (2242) plus the repriced envelope (this record). The 2119 count
refinement lever (needs `>= 1.721x` on its own) is moot at the coarse
product reading, which now sits at `0.3317529367828551`.

Not closed / nonclaims:

- the coarse product reading is a reading, not a proof of the
  complete-owner transfer; the formal transfer item remains open (2157
  unchanged; 2134 bypassed);
- the reduction inherits the 2238 machinery (ladder majorants, coefficient
  inflation) unchanged; only the panel charge moved;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_panel_cem_2243.py`;
- gate: `results/2242_zero_count_certificate.json`;
- inputs: `results/2234_sigma_*.json` (sigma rows),
  `results/2237_generation_certificate.json` (radii),
  `results/2238_panel_dx2_reprice.json` (prior envelope);
- artifact: `results/2243_panel_cem_reprice.json`.