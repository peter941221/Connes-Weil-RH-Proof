# 2234 — Direct-product outward envelope: first brick, measured too loose

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: the enclosure is *outward and correct*, but the envelope is
`32108x` the committed 2197 screen and `70.74x` the signed margin. The
direct-product certificate does not survive at this price. Two crude
allowances are identified and attributed (2235, 2236): the coefficient
radius and the panel majorant.

## Construction

The record-2197 screen is re-evaluated with 256-bit MPFR RNDN plus an
explicit forward-error slack, on the committed grids (240001 x-nodes,
101 sigma-nodes, x in `[-2.5600000000000005, 2.5600000000000005]`):

```text
per x node, per family:
  q      = 1 - (x/a)^2, skip q <= 0
  phi    = exp(-K/q)
  e1     = -2K(x/a)/(a q^2)
  e2     = -(2K/a^2)(q^-2 + 4(x/a)^2 q^-3)
  G      = e2 + e1^2 - theta^2,  H = 2 theta e1
  sums   += c phi e^{i theta x},   c phi (G + iH) e^{i theta x},  c in {base, corr}
slack     = 2^-200 x (sum of term magnitudes), per node per norm
sigma     = weighted trapezoid over the 101 grid points, w = exp(sigma x),
            MPFR exp per node, endpoints half-weight
```

Allowances, all outward:

```text
slack     2^-200 x magnitude sum; the exp-chain condition amplification is
          bounded by sup_q (K/q) e^{-K/q} = 30 e^-30 = 2.8e-12, so at
          256 bits the margin over the naive gamma_n accounting exceeds 2^100
panel     L x (2 a_max) x dx / 4 with global phi^(k) majorants
          |phi^(k)| <= e^-K poly_k(K, 1/a), k <= 3
          (master bound sup_{q in (0,1]} q^-m e^{-K/q} = e^-K, m <= 29)
sigma     one factor exp(a_max d_sigma) per norm between grid points
coeff     per-family absolute mass bounds 2a e^{sigma a} |phi^(k)|_majorant
          times the record-2201 provisional radius
```

The sigma=1 sums reproduce the committed 2197 values to the binary64
rounding level (`2.2e-16`, `5.4e-16`, `-1.0e-15`, `-4.6e-16` relative on
`base_M0`, `base_D2`, `corr_M0`, `corr_D2`), and the three-node smoke
control matches an independent numpy evaluation of the same formula
(`1e-16` to `1e-12` relative, the numpy binary64 drift; the endpoints
`x = +-a_max` are exactly zero by the support mask).

## Measured envelope

```text
binding row (sigma = 1.0)              2234 outward      2197 committed
base_M0                                3.999861398432025  2.0033357887456087
base_D2                                525836.1735144356  6688.576604759935
corr_M0                                186688.8251495832  913.4469710803505
corr_D2                                1048023425365.1514 1526140.687188009
C_upper                                2.4866178385966296e9 (2197: 7.7444e4)
B_upper                                98167737454.56252
high-shell budget upper                118520002340115.58
tail upper / signed margin             70.74142972939994
inflation over the 2197 screen         32108.532816055962
```

Attribution at the binding row (the four sigma=1 sums are already correct;
every factor here is an allowance):

```text
panel_base        1.8076571806532764     (vs base_M0 2.0033)
panel_base_D2     11693.314770969451     (11.5x the base_D2 norm scale)
panel_corr        2862.4920101295183
panel_corr_D2     17018191.948288612     (11.2x the corr_D2 norm)
coeff_infl_base   0.02303114682009543    relative
coeff_infl_corr   47.19205173325543      relative
coeff_infl_base_D2 26.883181442594267    relative
coeff_infl_corr_D2 55085.076713871786    relative  <- dominant
```

## What this closes and what it does not

Closed: an *outward* enclosure of the 2197 direct-product quantities at
256-bit MPFR with explicit, documented allowances; the sums themselves are
correct to the committed values.

Not closed: the envelope is not viable. The dominant defect is the
coefficient allowance (`5.5e4` relative on the corr_D2 channel): the
record-2201 radius belongs to a solve whose coefficients reach `5.69e17`
while the quantity's per-unit-coefficient mass sensitivity is `1/6.4e6`
(2235). The panel allowance is the second defect (`~11x` on the D2
channels).

Follow-ups: 2235 reprices the coefficient channel from the 2197 system's
own scales and measures that the 2201 radius prices that same channel, not
a different system; 2236 charges the solve floor
`Ainv (resid + gamma_30 A c)` and reaches viability.

## Provenance

- script: `scripts/routea_weighted_zero_direct_product_outward_2234.py`
- modes: `MODE=build` (construction cache), `MODE=smoke` (drift control),
  `MODE=chunk CHUNK=k` (12 x-chunks -> `results/2234_chunk_k.npz`,
  local-only), `MODE=sigma SIGMA_INDEX=j` (101 sigma artifacts),
  `MODE=reduce`
- outputs: `results/2234_direct_product_outward.json`,
  `results/2234_sigma_*.json` (101)
- base screen: `scripts/routea_weighted_zero_direct_product_mass_screen_2197.py`
- no producer or RH claim