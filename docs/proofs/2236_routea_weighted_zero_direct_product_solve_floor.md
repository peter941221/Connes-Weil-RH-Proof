# 2236 — Direct-product outward envelope: viable at the solve floor

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **viable**. Charging the coefficient channel at the computed
binary64 solve floor instead of the record-2201 combined radius reprices
the 2234 envelope by `913.57x`:

```text
                         2234                 2236
C_upper                  2.4866178385966296e9 2721865.34164875
tail upper / margin      70.74142972939994    0.07743395177596035
inflation over 2197      32108.532816055962   35.14617376530097
```

This opens the first gap of ladder item 4 (low-shell / `B_zm` side): the
direct-product outward certificate now sits `12.9x` below the signed-margin
anchor `1.675397327895099e12`, with the `2197` screen's own multiplicity
proxy and no coefficient-radius overcharge.

## The two readings of the coefficient channel

Under the discrete-defined operand convention (2230) the coefficient
vector is solved *from stored operands*, and the channels separate:

```text
solve      the binary64 LU chain's forward error; standard backward-error
           charge with gamma_30 = 30 u / (1 - 30 u) = 6.661338147750985e-15:
               r_c = Ainv_inf (||resid||_inf + gamma_30 A_inf c_inf)
           r_base = 998596.0653225501
           r_corr = 2044934208.0214145
generation stored matrix entries vs their embedded-float ideal; screened at
           eta = 1e-12 (2233 w-channel 9.16e-14 x 10), registered but not
           absorbed here
```

The record-2201 radius overcharged the solve channel by `172.94x`
(`charge_2201_over_floor_corr`); that factor is the whole 2234 defect.

The envelope is read under both readings:

```text
solve-floor charged    C_upper 2721865.34164875    tail/margin 0.07743395177596035
stored-exact (r = 0)   C_upper 1850509.4347934648  tail/margin 0.05264487413912939
binding row            sigma = 1.0 in both (binding_row_invariant)
```

The verdict does not depend on the reading: the binding row is channel a
(`base_D2 x corr_M0 / (2 pi)^2`) and both coefficient charges enter it only
through the moderate inflations below.

## Binding row (sigma = 1.0)

```text
base_M0                 3.9103349086507246
base_D2                 21791.878179718606
corr_M0                 4930.962615257418
corr_D2                 6079019388.2506695
panel_base_D2           11693.314770969451     (unchanged from 2234)
coeff_infl_base         0.0001332565212854297
coeff_infl_base_D2      0.15554411024810127
coeff_infl_corr         0.27288393003079797
coeff_infl_corr_D2      318.52465971799757     (non-binding channel b)
C_upper                 2721865.34164875
B_upper                 107454936.62043647
high-shell budget       129732635893.80194
```

Channel b (`corr_D2 x base_M0`, `6.021265077660421e8`) remains the loose
one: its `corr_D2` inflation is `318.5` relative, driven by the same
solve-floor radius against the D2 mass bounds. It is not binding.

## What this closes and what it does not

Closed: a viable outward price of the 2197 direct-product quantities at
`0.0774` of the signed margin under a stated convention, with every
allowance documented (slack, panel, sigma-cover, solve floor) and both
coefficient readings reported.

Not closed:

- the generation channel (stored matrix vs embedded-float ideal) is
  screened at `1e-12`, not certified — the registered lever; a certified
  enclosure (MPFR-defined matrix and solve) would retire it;
- the panel allowance (global `phi^(k)` majorants) still costs `~11x` on
  the D2 channels and is the second registered lever;
- the multiplicity constant is still the 2197 diagnostic proxy;
- complete-owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_direct_product_solve_floor_2236.py`
  (reuses `run_reduce` of the 2235 script)
- inputs: `results/2235_direct_product_reprice.json` (system scales),
  `results/2234_sigma_*.json` (sigma sums)
- outputs: `results/2236_direct_product_solve_floor.json`,
  `results/2236_robustness_zero_coeff.json`