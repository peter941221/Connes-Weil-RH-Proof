# 2235 — Coefficient-channel reprice from the 2197 system's own scales

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: the repricing moves the 2234 envelope by only `1.325x`
(`2.4866e9 -> 1.8762e9`, `70.74x -> 53.38x` the signed margin). The
diagnosis that motivated it — that 2234 imported a radius from a different
system — is *falsified* by the measurement: the record-2201 preflight had
already priced this system. What this record establishes instead is the
attribution: one radius was charging two channels (generation and solve),
which 2236 then separates.

## Measurement

The committed 2197 construction is rebuilt (same calls, same floats) and
its scale data measured:

```text
A_inf (inf-norm of a_mat)              7.94200337904096e-13
Ainv_inf (inf-norm of inverse)         6.77049894501907e+17
cond_inf = A_inf Ainv_inf              537713.2549913471
base coefficient inf-norm              277567753448698.28
corr coefficient inf-norm              5.6875117346762605e+17
residual inf-norm, base solve          6.4676997486962715e-15
residual inf-norm, corr solve          1.1417431493021041e-11
```

Repriced radii with the generation screen `eta = 1e-12` (ten times the 2233
w-channel moment gap `9.16e-14`):

```text
r_base = Ainv_inf (eta A_inf c_inf + resid)   149256239.14296788
r_corr = Ainv_inf (eta A_inf c_inf + resid)   305832774936.21344
record-2201, base-labeled                     172590522.1940381
record-2201, correction-labeled               353647211564.1207
```

The two radii land within `13%` of the 2201 values, and
`corr_c_inf = 5.6875117346762605e+17` is bitwise the `|coeff|_max` of the
2233 c-channel ledger: the 2201 preflight and the 2197 screen solve the
same 30x30 system. The 2234 envelope was therefore not repairable by
radius rescaling.

## Binding row after the reprice (sigma = 1.0)

```text
coeff_infl_base         0.01991732983838039
coeff_infl_base_D2      23.248568387831508
coeff_infl_corr         40.81150837491613
coeff_infl_corr_D2      47637.36661309164     <- still dominant
panel_base_D2           11693.314770969451    (unchanged)
panel_corr_D2           17018191.948288612    (unchanged)
C_upper                 1.876174557677763e9
tail upper / margin     53.3750174924163
```

## What this closes and what it does not

Closed: the scales and residuals of the 2197 system, and the falsification
of the "wrong system" reading. The number `rho := sum_f mass_f / norm` — the
objective-relative sensitivity of the screen to a uniform coefficient
error — is measurable and small: `1/6.4e6`, which is why a radius of
`3e11` must overcharge by five orders.

Not closed: viability. The next step (2236) charges only the solve channel
at its computed floor `Ainv (resid + gamma_30 A c)` and leaves the
generation channel to the ledger; the panel channel remains the second
registered lever.

## Provenance

- script: `scripts/routea_weighted_zero_direct_product_reprice_2235.py`
  (`run_reduce` shared with 2236)
- inputs: `results/2234_sigma_*.json`, `results/2234_direct_product_outward.json`,
  the 2197 construction rebuilt in-process
- output: `results/2235_direct_product_reprice.json`
- no producer or RH claim