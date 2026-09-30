# 2306 — TAIL-SHARP-COVERED: the grouped flat-edge tail clears the 1e7 hgap budget by 4.66e38 at N = 36

Record 2306 rebuilds the 2304 flat-edge integration-by-parts tail with a
direct, grouped, directed evaluation of the exact derivative, and prices it
against the `1e7` hgap budget:

    Tail = int_{|xi| > 40} kernel(xi) |ann(xi)|^2 |B(xi)|^2 |C(xi)|^2 dxi
        <= 2 A1^2 (V_N^b V_N^c)^2 / (2 pi)^{4N}
           * int_40^inf (log xi + C_W) xi^{8-4N} dxi,
    V_N^ch = 2 Rmax * sup_y |h_ch^{(N)}(y)|.

Verdict: **TAIL-SHARP-COVERED** at artifact grade — every order `N >= 16`
clears the budget; the best bound is `2.145448788e-32` at `N = 36`
(margin `4.661029457099352e38`). Orders 8 and 12 are the only dead ones.
The tail half of hgap is now numerically free: the live constraint on the
budget is the finite-window half, untouched here.

+--------------------------------------------------------------------------------+
|  order N |  tail bound     |  margin (1e7 / tail) |  binding channel          |
+----------+-----------------+----------------------+---------------------------+
|   8      | 1.795497633e+22 | 5.57e-16             | dead                      |
|  12      | 2.605891575e+12 | 3.84e-06             | dead                      |
|  16      | 553.7599646     | 1.81e+04             | base                      |
|  20      | 2.620431005e-06 | 3.82e+12             | base                      |
|  24      | 4.702185332e-14 | 2.13e+20             | base                      |
|  28      | 1.496353188e-21 | 6.68e+27             | base                      |
|  32      | 8.037361636e-29 | 1.24e+35             | base                      |
|  36      | 2.145448788e-32 | 4.66e+38             | corr  (best)              |
|  40      | 3.743581634e-30 | 2.67e+36             | corr                      |
|  44      | 1.542224733e-22 | 6.48e+28             | corr                      |
+--------------------------------------------------------------------------------+

The bound turns over past `N = 36` because the u-space magnitude ratio of
the surplus terms grows with N faster than `(2 pi)^{-4N}` decays. The
turnover is instrumentation cost, not mathematics.

## Why 2304 failed, restated as a measurement

2304 charged `V_N` through three stacked losses: a decoupled partition
majorant of the psi derivatives (~1e17x loose at order 20), a familywise
triangle over the 30 families, and dropped carrier phases. 2306 replaces
all three with one grouped object: the exact N-th derivative of the full
complex family sum, enclosed on rational cells with the carrier phases
kept exactly (grouping-before-modulus, the 2291 law).

The derivative is evaluated in the (u, s) variables of the psi-compression,

    h_f^{(N)}(y) = e^{lambda_f y} e^{-K/s_f} Q_f(y),
    u = y/R_f,  s_f = 1-u^2,
    Q_f(y) = sum_{j=0}^N C(N,j) lambda_f^{N-j} R_f^{-j} A_j(u) s_f^{-2j},
    psi^{(j)}(u) = psi(u) A_j(u) s^{-2j},
    A_0 = 1,  A_{j+1} = s^2 A_j' + 2u (2j s - K) A_j.

An expanded y-polynomial form (P_f as a single complex polynomial in y)
was implemented first and rejected by measurement. The binomial expansion
of `s^{2(N-j)}` cancels catastrophically near `|y/R| ~ 0.5`: the
coefficient-magnitude sums run up to ~1e16x the polynomial value, which
poisons every slack term of the enclosure. Measured magnitude-to-value
ratios at `y = 1.7588`, `N = 20`, per family:

+----------------------------+-------------------+---------------+-------------+
|  family                    | expanded poly     | u-space j-sum | Bell ladder |
+----------------------------+-------------------+---------------+-------------+
|  R = 1.76, theta ~ -39..-15| 1e7 .. 1e15       | 12.0          | 1.035       |
|  R = 1.84, theta = -39.25  | 2.29e15           | 26.5          | 9.5         |
|  R = 2.08, theta = 39.25   | 2.96e16           | 1228          | 5.5e3       |
|  R = 2.32, theta = 39.25   | 1.37e16           | 1981          | 7.8e6       |
|  R = 2.32, theta = 0       | 2.06e2            | 8.3e4         | 7.8e6       |
|  R = 2.00, theta = 0       | 2.06e2            | 136           | 627         |
+----------------------------+-------------------+---------------+-------------+

The u-space j-sum keeps every factor as a positive power of `s` or a power
of the complex constant `lambda`, so the magnitude chain tracks the
computation instead of the polynomial's coefficients. With the declared
kappa = 2^-30 the residual slack is below 1e-4 of the value at every
family; the Bell ladder (an mpmath control path, not a production path)
is 1.035x accurate only near the singular families where the weight is
already zero, and 7.8e6x elsewhere.

The first order-20 run of this instrument, before the u-space rewrite,
produced `tail_bound = 5.083377274e+31` with `inflation_base = 1.21e9`;
the same order now reads `tail_bound = 2.620431005e-06` with
`inflation_base = 1.008`.

## The enclosure

Each family is bounded on rational cells (the master grid is pre-split at
`+-R_f` for all 30 families, then the top-512 cells by upper bound are
bisected six times, 11277 cells at every covered order):

    ub(cell) = |sum_f c_f t_f(m)| + kappa * magchain
               + (Delta/2) sum_f |c_f| sup_cell |t_f'|,

with midpoint `m`, width `Delta`, and honest triangle bounds

    |A_j(u)| <= magA_j(u_max)               (coefficient triangle),
    sup_{s in [s_lo, s_hi]} e^{-K/s} s^{-m}
        = e^{-K/s*} s*^{-m},  s* = clip(K/m, s_lo, s_hi)   (m >= 1),
    |A_j'| s^{-2j} <= (magA_{j+1} + 2 u_max (2j s_hi + K) magA_j) S(2j+2),

the last from the exact ODE identity `A_j' = (A_{j+1} - 2u(2j s - K) A_j)/s^2`
(A generated to order N+1; the `s^-2` soaks into the S-function clip, so no
raw `1/s_lo^2` ever appears). The S-function is validated against brute
force grids in the selftest, and the ODE identity against central
differences (`4.8e-11` worst relative).

Declared slack model: every computed binary64 quantity q with tracked
running magnitude `M_q` satisfies `|q - q_true| <= kappa M_q`,
`kappa = 2^-30`, which carries ~7 decades of headroom over `2^-53` and
covers evaluation chains of up to ~1e6 rounding steps.

## Controls

Kappa variation (relative movement of the upper bound between
`kappa = 2^-24` and `kappa = 2^-36`, orders 20/24/28):

+-------+---------------------+---------------------+----------------+
|   N   | ub_base (k=24)      | ub_base (k=36)      | rel. movement  |
+-------+---------------------+---------------------+----------------+
|  20   | 2.1973691948e+38    | 2.1973689346e+38    | 1.18e-08       |
|  24   | 1.0407323862e+46    | 1.0407322706e+46    | 1.11e-07       |
|  28   | 5.2043801504e+53    | 5.2043795758e+53    | 1.10e-07       |
+-------+---------------------+---------------------+----------------+

The slack term is nowhere near binding; the enclosure is set by the
deterministic triangle bounds, not by the declared rounding model.

Independent mpmath Bell-path recomputation at the recorded best-order
argmaxes (closed-form log-derivative ladder
`L_m = -(K m!/2)[(1-u)^{-(m+1)} -/+ (1+u)^{-(m+1)}]`, complete Bell
recursion `psi^{(j)} = psi Y_j`, no shared code with the A_j recursion):

+---------+-------------+-------------------+-----------------+-------------+
| channel | y           | mpmath |T|        | recorded ub     | ub / true   |
+---------+-------------+-------------------+-----------------+-------------+
| base    | 0.4440      | 4.03132259688e+68 | 1.9499989993e+69| 4.84        |
| corr    | 1.2127      | 4.33787681699e+63 | 1.0994159308e+71| 2.53e+07    |
+---------+-------------+-------------------+-----------------+-------------+

The base enclosure is within 4.84x of the true sup at its argmax. The
corr enclosure is 2.5e7x loose locally at its argmax cell; the corr
channel is the binding one only at `N >= 36`, where the budget margin is
astronomical anyway.

2304 cross-check: feeding 2304's own recorded rigorous `V` values through
the 2306 tail formula reproduces 2304's recorded bounds to the stored
8-digit precision (ratios 1.0000001 / 1.0 / 1.0 / 0.99999999 at orders
16/20/24/28). The tail formula has not drifted.

## Errata carried from 2304

1. 2304's `v_ladder` omits the integration-length factor `2 R_f` per
   family. 2306 carries a single `2 Rmax` factor on the grouped sup
   (allowed because the grouping replaces the familywise triangle).
2. 2304's price arithmetic: `(2.9973776e17 / 1e7)^{1/4} = 416.1`, not 74;
   with the restored `(2 Rmax)^4 = 2.95e4` length factor the price is
   5450x per channel. 2306 makes the question moot by clearing the budget
   outright.

## Pitfalls found and fixed while building this instrument

- The A_j recursion `A_{j+1} = s^2 A_j' + 2u(2j s - K) A_j` was written
  first without the `2u s` leg (`2u(2j - K)`); the Bell closed form caught
  it at 12.7 relative error. The Bell control is kept in both selftests.
- The cell value carried the cell-sup factor `e^{y_hi/2}` instead of the
  midpoint factor `e^{m/2}`; the mpmath value control showed an exactly
  uniform `5.000e-07 = e^{Delta/2} - 1` bias, which is how it was found.
- A raw `1/s_lo^2` in the derivative bound produced `inf` at cells touching
  `+-R` and `inf * 0 = nan` in the zeroed tails; folding into `S(2j+2)`
  removed the division entirely.

## Nonclaims

- Artifact grade: the binary64 evaluation carries the declared
  running-magnitude slack model (kappa = 2^-30), not a machine-verified
  interval certificate. The uniform 1.008x base inflation at the crossing
  order means a certificate at N = 20 is a factor ~1.01 away from what the
  instrument already reads; certifying it means intervalizing the same
  expressions, not re-pricing the mechanism.
- The kernel triangle bound, the prime-power sum and the annihilator l1
  norm are 2304's constants, unchanged and not re-certified here.
- This record covers the tail half of hgap only. The finite-window half
  (records 2295-2302, sampled-grade proxies 0.0405x - 0.0494x of budget)
  needs its own certified enclosure before any hgap certificate.
- The tail bound is an absolute-value bound; it does not supply the signed
  finite-window functional, the selected-owner readback or the producer
  margin. No hgap certificate, no producer GO, no RH claim.

## Reproduction

    MODE=selftest python3 scripts/routea_hgap_tail_sharp_2306.py
    MODE=order ORDER=20 python3 scripts/routea_hgap_tail_sharp_2306.py
    for N in 8 12 16 20 24 28 32 36 40 44; do
        MODE=order ORDER=$N python3 scripts/routea_hgap_tail_sharp_2306.py; done
    MODE=kcontrol ORDER=20 KAPPA_LOG2=24 python3 scripts/routea_hgap_tail_sharp_2306.py
    MODE=reduce python3 scripts/routea_hgap_tail_sharp_2306.py
    MODE=control python3 scripts/routea_hgap_tail_sharp_2306.py
    python3 scripts/routea_hgap_tail_sharp_selftest_2306.py

Each order costs ~6 s at N = 20 on the WSL2 side; the full ladder is
minutes. Module selftest: PASS (A_j vs Bell 7.66e-39, u-sum vs mpmath
Leibniz 1.11e-14, ODE identity 4.8e-11, 2304 formula ratio
1.000000027443027). Artifact selftest: 13 tests, PASS.

Artifacts: `results/2306_hgap_tail_sharp.json` (reduce),
`results/2306_order_{8..44}.json`, `results/2306_kc_{N}_k{k}.json`,
`results/2306_mp_control.json`. Owner capture:
`results/2275_gap_owner_audit.json`. Predecessor:
`results/2304_hgap_tail_moment_probe.json`.