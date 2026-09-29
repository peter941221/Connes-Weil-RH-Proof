# 2237 — Direct-product outward envelope: certified generation channel

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **viable**. The generation channel — the gap between the stored
binary64 30x30 matrix and its embedded-float ideal, screened at
`eta = 1e-12` since 2233 and registered as the largest 2236 lever — is
replaced by a measured 256-bit MPFR enclosure of all 900 entries. The
certified charge is `2.2e4..2.5e4x` below the screen, so the envelope
moves by only `+0.22%`:

```text
                          2236 (screen)         2237 (certified)
C_upper                   2721865.34164875      2727859.2133313827
tail upper / margin       0.07743395177596035   0.07760447056089889
repricing vs 2234         913.57x               911.56x
```

The registered generation lever is retired; the residual coefficient
charge is now the 2237 solve floor plus a certified `0.59%` generation
increment on `r_corr` and `0.69%` on `r_base`.

## What is certified

Per entry `(i, j)`: `A*_ij = a_j sum_p phi(X_p / a_j) W_p
exp(a_j (node_i + i theta_j) X_p)` in 256-bit MPFR — `exp`, `sin`, `cos`
and every term product at `RNDN`, the four directed accumulators at
`RNDD (lo) / RNDU (up)`, then left-scaled by `a_j` with the same directed
rounding, and each entry carries a `2^-200` magnitude-sum slack:

```text
delta_ij = max(|A_bin64_ij - (lo - slack)|, |(up + slack) - A_bin64_ij|)
```

measured as an MPFR difference (no binary64 cancellation), one family
(30 entries) per job, 30 jobs over the committed operand dump
`results/2237_operand_dump.npz`
(md5 `599e1714c9beb092b6704bcde3670caf`; nodes, values, fam_a, fam_theta,
X, W — the same operands the 2197 system is built from).

```text
delta_max                    9.490758943075902e-29   at entry [7, 7]
delta_max / A_inf            1.1950081723865955e-16  (~0.54 ulp of A_inf)
interval halfwidth max       8.361167990095088e-86
bitwise columns verified     30 / 30  (rebuilt a_mat, entry for entry)
```

The `delta/A_inf` scale says the deviation is exactly the binary64
rounding of the stored formula against its exact real evaluation — the
enclosure measures rounding, it does not discover structure.

## The charge

The per-entry deviations enter the coefficient radius through the same
slot the `1e-12` screen used: `v = max_i sum_j |Delta A_ij| |c_j|`, with
the cancellation guard `1 + 10 cond_inf (delta_max/A_inf + gamma_30) =
1.0000000364614705`:

```text
                       base                  corr
v (certified)          1.0176832913826672e-14 1.7923057312538845e-11
v (screen eta=1e-12)   2.20444403580237e-10   4.5170237415133973e-07
cert / screen          4.616507721922061e-05  3.967890880851082e-05
gen radius increment   6890.223901897575      12134804.505058868
floor (2236)           998596.0653225501      2044934208.0214145
r (certified)          1005486.289224448      2057069012.526474
```

`v_corr` is `3.97e-05` of the screen (`2.52e4x` tighter); the certified
increment is `0.59%` of the corr floor. `v_base` binds at node 4,
`v_corr` at node 15.

## Binding row (sigma = 1.0)

```text
base_M0                 3.9103385035608915
base_D2                 21812.117931842637
corr_M0                 4937.235601159832
corr_D2                 6114979882.496457
panel_base_D2           11693.314770969451    (still the 2234 panel)
coeff_infl_base         0.00013417597941262356
coeff_infl_base_D2      0.15661735075389552
coeff_infl_corr         0.2745032452784508
coeff_infl_corr_D2      320.41481073633196    (non-binding channel b)
C_upper                 2727859.2133313827
B_upper                 107691565.18979038
high-shell budget       130018322610.4439
```

Same binding row and same channel structure as 2236; only the four
`coeff_infl` entries move (all by `<= 0.85%`), so the `+0.22%` envelope
delta is exactly the certified generation charge.

## What this closes and what it does not

Closed: the generation channel is a measured interval enclosure with the
30/30 bitwise column gate, the dump md5 pin, and the `2.52e4x` screen
separation; the largest registered 2236 lever is retired.

Not closed:

- the panel allowance (global `phi^(k)` majorants) is still the 2234
  panel here — priced in 2238;
- the multiplicity constant is still the 2197 diagnostic proxy — the
  2240 audit shows it is the formal Lean constant bitwise;
- complete-owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_matrix_enclosure_2237.py`
  (dump / family / reduce; reuses `run_reduce` of the 2235 script)
- inputs: `results/2237_operand_dump.npz` (md5
  `599e1714c9beb092b6704bcde3670caf`), `results/2237_fam_*.json` (30),
  `results/2235_direct_product_reprice.json` (system scales),
  `results/2234_sigma_*.json` (sigma sums)
- outputs: `results/2237_generation_certificate.json`