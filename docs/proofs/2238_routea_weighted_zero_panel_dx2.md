# 2238 — Panel allowance: dx^2-law with measured zero-free cells

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **viable**. Replacing the 2234 O(dx) panel by the dx^2
composite-trapezoid law on measured zero-free cells, stacked on the 2237
certified generation radii, reprices the envelope by `2.184x` over 2237
and `1990.73x` over 2234:

```text
                          2234               2237 (panel 2234)   2238
C_upper                   2.4866178385966296e9 2727859.2133313827 1249100.8031538636
tail upper / margin       70.74142972939994    0.07760447056089889 0.03553548732728288
inflation over 2197       32108.532816055962   35.22356982617925 16.12905429459266
headroom vs margin        --                   --                28.14x
```

The record also isolates the structural obstruction that caps this law
(~1.8x here): the risk-cell corner mass still uses global `phi^(k)`
majorants. A composite-Euler-Maclaurin reading with a certified real-zero
count removes the risk cells entirely (registered; projected `tail/margin
~0.0109`).

## The identity

On the committed uniform grid (240001 nodes, step `dx =
2.1333333333333338e-05` over `[-a_max, a_max]`) two integrations by parts
give the composite-trapezoid identity (Stieltjes form, valid for
`g = |h_k| e^{sigma x}` with `h_k` entire):

```text
T - I = (dx^2/12) sum_p Delta_p - (dx^2/2) sum_p int_0^1 B_2(t) dg'
```

with `Delta_p` the one-sided increment of `g'` across cell `p`. The
`Delta` sum telescopes:

```text
sum_p Delta_p = g'(x_N) - g'(x_0) + sum_{node kinks} J,
```

and `g'(+-a_max) = 0` **exactly**: the phi support `exp(-K/(1-u^2))` on
`|u| < 1`, extended by zero, has all derivatives zero at `|u| = 1`. Every
surviving kink rate is `dx^2`:

```text
|T - I| <= (dx^2/12) (sum_{node kinks} J + TV(g')),
TV(g')  <= int |g''| + sum_{all kinks} J,
J       <= 2 e^{sigma a} m_{k+1}   (global slope majorant).
```

Numerical verification of the identity and of the bounds (local recon,
non-artifact): smooth `e^x sin 3x` identity residual `-2.204e-07` on
`T - I = -3.563313835098e-04`; kink test `|sin 3x|` on `[0, 2pi]`,
`|T - I| = 1.316033765231e-03 <= 2.171312968240e-02`; kink-at-node
variant (5 node kinks, `n = 96`), `|T - I| = 1.285931237307e-02 <=
2.356025356163e-02`.

## The shipped charge

A cell is certified zero-free by the node test `|h_k(x_p)| > dx m_{k+1}`
(both endpoints; a zero in the cell forces the endpoint value below
`dx sup|h_k'|`). On the committed 2234 chunk arrays (lower bound
`U - 2 slack ~= U`, the slack being `~1e-60` relative):

```text
                       base_M0       base_D2       corr_M0       corr_D2
cells                  240000        240000        240000        240000
N_risk                 182747        199759        189618        207826
threshold dx m_{k+1}   0.1091722416  697.6396781   172.8782829   1014605.2179
median |h_k|           1.534e-06     4.734e-03     8.276e-04     1.652
panel 2234             1.8076571807  11693.314771  2862.4920101  17018191.9483
panel 2238             0.9194450802  6422.9649473  1510.5771805  9716500.1068
gain                   1.9660306196  1.8205478104  1.8949657436  1.7514734484
```

The gap between the threshold and the medians is the classification wall:
76-87% of cells are risk cells because the corner mass is bounded by the
global `m_{k+1}`, which is `1e3..1e6x` above the local slope scale. Both
rates of the charge are `dx^2`:

```text
panel = (dx^2/12) [ (2 a_max) M_k(sigma)
                    + N_risk (dx M_k(sigma) + 2 e^{sigma a} m_{k+1}) ],
M_k(sigma) = e^{sigma a} (m_{k+2} + 2 sigma m_{k+1} + sigma^2 m_k)
```

with the `phi^(k)` majorant ladder (same rule as 2234; order-4 from the
Bell expansion of `phi^(4)`, every `u^{2j} q^{-m} e^{-K/q}`, `m <= 8`,
bounded by `e^{-K}`):

```text
        m0           m1             m2             m3              m4
base    69.1932841   5117.4488218   401728.86527   32701859.8783   2812505182.41
corr    108311.6626  8103669.5019   618612076.69   47559619541.1   3774481604789.3
```

## Binding row (sigma = 1.0)

```text
base_M0                 2.998972357333835
base_D2                 15558.273343860988
corr_M0                 3169.537007543597
corr_D2                 3707252433.007615     (non-binding channel b)
C_upper                 1249100.8031538636    channel a = base_D2 x corr_M0/(2 pi)^2
C_channel_b             281620901.822096
B_upper                 49312523.13684655
high-shell budget       59536060513.57989
coeff_infl (2237 radii) unchanged carrier: 1.342e-04 / 0.15662 / 0.27450 / 320.41
```

Controls: radius = 2237 certified values `1005486.289224448` /
`2057069012.526474` (`radius_source` recorded); chunk-vs-committed-2197
trapezoid drift at `sigma = 1`: `2.2e-16 / 5.4e-16 / -1.0e-15 / -4.6e-16`.

## Registered lever: composite-EM panel with certified zero count

The telescoped identity shows the risk cells are unnecessary: the exact
composite bound with `Z` = number of real zeros of `h_k` on the interval is

```text
panel_cem = (dx^2/12) [ (2 a_max) M_k(sigma) + 2 Z e^{sigma a} m_{k+1} ]
```

and a numpy scan of the four channels on the same uniform grid finds
`Z = 0`: no interior zero candidates; deepest interior dips `2.487e-12`
(`base_M0`, at `x = -1.5621`, zoom-refined) and `4.920e-09` (`base_D2`,
at `x = -1.5960`); the `|h| ~ 5e-314` candidates at `x = +-2.5079` are the
phi-decay tail at the support edge, not zeros. Certified projections
(same arithmetic as the pipeline, ladders and `sigma = 1`):

```text
              panel_cem        gain vs 2234   projected C_upper   projected tail/margin
base_M0       0.0010349801     1746.56x
base_D2       7.2299898714     1617.33x       384556.5741856599  0.010940194125321153
corr_M0       1.5948664430     1794.82x       (channel a binds)   (3.248x below 2238)
corr_D2       9721.5523456     1750.56x
```

The certification path: (i) validate the two dips per base channel by
interval arithmetic (a lower bound `|h_k| > 0` on the dip neighborhoods —
the empirical dips sit `2.5e-12`/`4.9e-9` above the float noise floor);
(ii) certify the outer region by per-node local slope probes (the global
`m_{k+1}` is only needed where the node test fails, and there the local
`|h_k'|` replaces it). Not claimed here: any of this without the probes —
the projections are estimates at the stated conventions.

## What this closes and what it does not

Closed: the panel term at both charges (dx^2 measure form and the
zero-free node test) with the risk-cell count measured from the committed
chunks; stacked on 2237 the envelope reads `0.0355` of the signed margin.

Not closed:

- the risk cells still carry the global `m_{k+1}` (the wall); the
  composite-EM lever above is the registered removal, with `Z = 0`
  empirical but not yet certified;
- the real-zero count `Z = 0` claim is numerical (float eval on the
  uniform grid), not a certificate;
- complete-owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_panel_dx2_2238.py` (recon +
  reprice; reuses 2234 construction and 2237/2236 radii)
- inputs: `results/2234_sigma_*.json`, `results/2234_chunk_*.npz`
  (local-only), `results/2237_generation_certificate.json`,
  `results/2238_panel_recon.json`
- outputs: `results/2238_panel_recon.json`,
  `results/2238_panel_dx2_reprice.json`