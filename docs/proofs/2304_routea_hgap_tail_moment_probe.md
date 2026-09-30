# 2304 — TAIL-MOMENT-DEAD at the partition ladder; certification price 74x

Record 2304 prices the infinite-xi tail

    Tail = int_{|xi| > 40} kernel(xi) |ann(xi)|^2 |B(xi)|^2 |C(xi)|^2 dxi

by a mechanism disjoint from the frozen quadrature instruments (2286-2294):
**flat-edge integration by parts**. It is a probe, not a certificate.

Verdict: **TAIL-MOMENT-DEAD** at probe grade — the best bound over the
tested orders is `2.9973776e17` at `N = 28`, above the `1e7` hgap budget.
The same table also shows that the measured ladder clears the budget by
thirteen orders at `N = 20`, so the failure is entirely the quality of the
closed-form sup-ladder. The quantified certification price is a ladder
within `74x` of the partition majorant at `N = 28`.

## Why the mechanism is structurally right

`phi_R(y) = exp(-30/(1-(y/R)^2))` is C-infinity and flat at `y = +-R`.
The tested function `h = phi E` with `E(y) = e^{(1/2 + i theta) y}` is then
also flat there (Leibniz makes every boundary term `h^(j)(+-R)` vanish), so
N-fold integration by parts on `B(xi) = int_{-R}^{R} h(y) e^{-2 pi i xi y} dy`
has **no boundary terms** and is a pure remainder:

    |B(xi)| <= V_N / (2 pi xi)^N,   V_N = ||h^(N)||_inf.

Four transforms give `xi^{-4N}`, which beats the `xi^4` annihilator growth
and the `log xi` archimedean growth for every `N >= 2`:

    Tail <= 2 A1^2 (V_N^b V_N^c)^2 / (2 pi)^{4N}
            * int_40^inf (log xi + C_W) xi^{8-4N} dxi,

with `A1 = 2497731.388738144` the annihilator coefficient l1 norm
(`ann` coefficients `2.374535e6, -1.901e-11, -1.216375e5, 1.819e-12,
1.558545e3`) and `C_W = 2810.1333609392077` the kernel triangle bound
(`c_sigma = 8.631252422799024` from the shifted digamma representation plus
`2 sum_p log(p) p^{-1/2} = 2801.5021085164085` over the 41136 prime powers).
The closed-form integral is finite for `N >= 3`; `N = 2` diverges.

## The two ladders

`psi(u) = exp(-30/(1-u^2))`, `L_m = d^m/du^m log psi`, and
`psi^(j) = psi * Y_j(L_1..L_j)` with the complete Bell polynomial.

| j  | measured sup | rigorous partition sup | ratio   |
|----|--------------|------------------------|---------|
| 0  | 9.3576e-14   | 9.3576e-14             | 1.0     |
| 1  | 4.5095e-13   | 1.1229e-11             | 24.9    |
| 2  | 5.6146e-12   | 1.3924e-09             | 248     |
| 3  | 5.9769e-11   | 1.7814e-07             | 2980    |
| 4  | 9.4325e-10   | 2.3481e-05             | 24894   |
| 8  | 8.1383e-05   | 9.3314e+03             | 1.15e8  |
| 12 | 1.3373e+01   | 5.4991e+12             | 4.11e11 |
| 16 | 9.3794e+06   | 4.6037e+21             | 4.91e14 |
| 20 | 4.2650e+13   | 9.8537e+30             | 2.31e17 |

The measured ladder is a grid maximum (4.4M points, float64; overflow past
`j = 20`); the rigorous ladder is a closed-form partition majorant,
`|L_m| <= K m! 2^{m+1} s^-(m+1)` with `s = 1-u^2` and
`sup_{s<=1} e^{-K/s} s^{-p} = e^{-K}` for `p <= K`, `e^{-p}(p/K)^p`
otherwise, evaluated in 60-digit arithmetic. The partition ladder is
`25x` loose at `j = 1` and `2.3e17x` loose at `j = 20`, growing about
`6.3x` per order.

## Tail table

| N  | rigorous bound | measured-ladder bound |
|----|----------------|------------------------|
| 3  | 3.280886e+41   | 4.9792417e+36          |
| 4  | 6.6882508e+39  | 3.1506766e+33          |
| 6  | 9.020919e+36   | 5.6804487e+27          |
| 8  | 2.3232374e+34  | 2.5645446e+22          |
| 10 | 9.157217e+31   | 1.8887054e+17          |
| 12 | 5.1105747e+29  | 1.9694053e+12          |
| 14 | 3.8572001e+27  | 3.0005029e+07          |
| 16 | 3.8062805e+25  | 752.93551              |
| 20 | 7.8838255e+21  | 2.3017598e-06          |
| 24 | 8.2953498e+18  | -                      |
| 28 | **2.9973776e+17** | -                   |
| 32 | 2.2798313e+18  | -                      |
| 36 | 4.8407403e+21  | -                      |
| 40 | 8.8101592e+26  | -                      |
| 44 | 6.1242436e+33  | -                      |

The rigorous bound has a minimum at `N = 28` and rises afterwards; the
per-order gain `(2 pi)^{-4}` is eventually beaten by the ladder growth.

## Calibration at small xi

The 30-family transform at `xi = 40` cannot be measured: the term scale is
about `1e12` while the flat-transform decay is of order
`exp(-2 sqrt(30 pi xi)) = exp(-173.6) ~ 1e-75`, so any finite-precision
quadrature returns cancellation noise. The mechanism is controlled instead
on a single family (`R = 6.5536`, `c = 1`, `theta = 0`) where the transform
is resolvable in 60-digit arithmetic:

| xi | measured abs B | best ratio (bound/measured) at N = 20 |
|----|----------------|----------------------------------------|
| 1  | 5.535498051e-19 | 36.55                                 |
| 2  | 3.807191324e-25 | 50.69                                 |
| 4  | 4.879635685e-34 | 3.77e+04                              |

All ratios are `>= 1`, so the IBP bound holds; it is tight at small `xi`
and power-law-loose where the true decay is faster than any power.

## Erratum caught during the probe

The first run of the partition majorant used the *inverted* branch of
`sup_{s<=1} e^{-K/s} s^{-p}` (it took `e^{-p}(p/K)^p` where the critical
point `s* = K/p` lies outside the domain). The corrected branch shrinks
the `j = 1` majorant from `7.2e-2` to `1.1229e-11`, a factor `6.4e9`, and
moves the tail minimum from `N = 24`/`8.3e18` to `N = 28`/`3.0e17`. The
table above is the corrected run.

## Certification price

+ required ladder improvement at `N = 28`: `(2.997e17 / 1e7)^{1/4} = 74x`
  per channel; equivalently, both `V_N` must be within `74x` of the truth.
+ the measured ladder already clears the budget by `4.3e12x` at `N = 20`,
  so no structural obstruction is left: the missing ingredient is a
  **rigorous but tight** sup-ladder.
+ named suppliers, in order of expected sharpness: (a) a 1-D directed-MPFR
  interval Bell evaluation of the **grouped complex** `h^(N)` (the 2291
  law: grouped/familywise is `4.07x` base and `3572.9x` corr, so grouping
  alone pays part of the 74x), and (b) sharpening the partition algebra
  (simultaneous optimization of `psi` and the Bell factors instead of
  independent `sup` bounds).

## Non-claims

+ probe grade: the measured ladder is a grid maximum, not an interval
  enclosure; the rigorous ladder is a valid majorant, not a tight one;
+ the tail bound is an absolute-value bound: it does not supply the signed
  finite-window functional, the selected-owner readback or the producer
  margin;
+ the kernel triangle bound, the prime-power sum and the annihilator l1
  norm are not yet arithmetic-certified;
+ no hgap certificate, no producer GO, no RH claim.

## Reproduction

    MODE=selftest python3 scripts/routea_hgap_tail_moment_probe_2304.py
    MODE=probe    python3 scripts/routea_hgap_tail_moment_probe_2304.py

Artifact: `results/2304_hgap_tail_moment_probe.json`.