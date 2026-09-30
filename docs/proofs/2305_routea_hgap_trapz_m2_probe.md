# 2305 — M2 route and per-cell intervalization both priced out; the float64 owner transform is blind past |x| ~ 1

Record 2305 prices the two remaining instruments of the window lane on the
ideal smooth integrand

    Gi(x) = kernel(x)^2 |ann(x)|^2 |B(x)|^2 |C(x)|^2,

the 2275 trapezoid cap `|int_cell Gd - T_cell| <= M2 h^3/12` with the
window total `M2/375` at 4000 cells of `h = 1/50`, and the 2302 per-cell
screen's missing ingredient (directed enclosures of the kernel and the
annihilator weights). It is a probe, not a certificate.

Verdicts:

+ **M2-CAP-FAILED** — the global route needs `M2 <= 3.75e9`; on the
  precision-validated zone `|x| <= 1` alone the measured `|Gi''|` reaches
  `1.610654527471709e15`, so the route is over budget by `>= 4.30e5x`.
+ **PANEL-LOCAL-FAILED** — the panel-local sum `sum_cells sup|Gi''| h^3/12`
  at the design `h = 1/50` is `>= 398x` over budget from the validated zone
  alone; the route needs `h <= 1.0e-3` (>= 8e3 cells on `[-1, 1]`, 8e4 on
  `[-4, 4]`, 8e5 over `[-40, 40]`).
+ **KERNEL-INTERVAL-FAILED-NEEDS-GROUPING** — exact per-cell intervalization
  of the prime-power cosine sum (arc rule), the quartic annihilator and the
  archimedean sigma term charges `>= 1.08e4x` the budget from `|x| <= 1`
  alone (`8.86e12x` over the full sampled window).
+ **Precision finding** — the owner transform is not resolvable in float64
  past `|x| ~ 1`: the corr coefficient scale is `5.69e17` and the family-sum
  cancellation floor is `~3e-11`, so the float64 `|C(4)|` misses the true
  value by `3.7e3x`. High-precision control values (mpmath `quadgl`,
  phase-aware panels, dps 50–60, bitwise stable across all four settings)
  are the true decay.

## The precision finding (the structural result)

| x | abs B float64 (40x16 / 80x16 / 40x32)   | abs B mpmath        | abs C float64 (same three)                        | abs C mpmath        |
|---|------------------------------------------|---------------------|---------------------------------------------------|---------------------|
| 1 | 0.196355697948276 / 374 / 286            | 0.19635569794827712 | 3.0362939e-06 / 3.0363009e-06 / 3.0363036e-06     | 3.0363003090952906e-06 |
| 2 | 2.690462421189e-05 / 475e-05 / 413e-05   | 2.6904624215247886e-05 | 4.3840e-10 / 4.2596e-10 / 4.0622e-10          | 4.2780015472502136e-10 |
| 4 | 2.499441829e-09 / 2.499441542e-09 / 2.499441181e-09 | 2.499440681570086e-09 | 3.5116e-12 / 1.1865e-11 / 3.5570e-12 | 9.440112224881565e-16 |

Reading:

+ `|B|` is float64-resolvable everywhere tested (agreement `4.6e-7`
  relative at `x = 4`), because its cancellation floor is `~2e-14`
  (`noise_floor_base = 206.9`).
+ `|C|` is resolved at `x = 1` (`2.1e-6` relative, and the three float64
  settings agree to `2e-6`), marginal at `x = 2` (the settings spread over
  `8%` and the best value is `2.5%` off), and **lost** at `x = 4`: the true
  `|C(4)| = 9.44e-16` sits `3.7e3x` below the float64 reading. The corr
  cancellation floor is `noise_floor_corr = 3.086636908941589e5`.
+ the mpmath control is itself converged: `dps` 50/60 crossed with 16/24/32
  nodes per panel returns **bitwise identical** values at `x = 2` and
  `x = 4`.
+ the true decay `0.196, 2.69e-05, 2.50e-09` (base) and
  `3.04e-06, 4.28e-10, 9.44e-16` (corr) is super-exponential in `x`, as the
  2304 flat-edge mechanism predicts, and it is *faster* than the
  `(2 pi x)^4` annihilator growth — the weight lives at small `|x|`.

Consequence for the pricing below: the trusted zone is `|x| <= 1`; every
headline number is quoted as a **lower bound** from that zone, so the
verdicts do not depend on the unresolvable band. The two float64 rows
(`h = 0.02` vs `h = 0.005`) confirm the `h^2` mass law: the trusted-zone
masses are in ratio `15.59` against `16`, and the full sampled-window
masses `17.80` against `16` (`h_squared_trend_ratio = 4.2196` against the
expected 4).

## P4 — the M2 route

Sampled `sup |Gi''|` by region (cells of the dense window `[-4, 4]`):

| region      | h = 0.02        | h = 0.005       |
|-------------|-----------------|-----------------|
| abs x <= 0.5 | 6.201067194097186e12 | 6.472043495690401e12 |
| abs x <= 1.0 | 9.28419958426094e14  | **1.610654527471709e15** |
| abs x <= 1.5 | 5.276840206615754e17 | 6.832270221115519e17 |
| abs x <= 4.0 | 3.996405448204249e22 | 4.035286586833944e22 |
| argmax       | -3.65 (unresolved)   | -3.6675 (unresolved) |

The full-window rows are float64 noise (the same mechanism as the
calibration table above); the trustworthy lower bound is the `|x| <= 1`
row, and the untrusted rows do not affect any verdict:

    global route (2275):  M2 * 80 * h^2 / 12  <= 1e7  <=>  M2 <= 3.75e9
    measured lower bound: M2 >= 1.610654527471709e15
    failure factor:       4.295078739924558e5

Panel-local route (`mass(h) = sum_cells sup|Gi''| h^3/12`, `~ h^2`):

| quantity (h = 0.005)          | value                  |
|-------------------------------|------------------------|
| mass, abs x <= 0.5            | 748304.6897587209      |
| mass, abs x <= 1.0 (trusted)  | 2.487254233683885e8    |
| mass, abs x <= 1.5            | 8.003046823002486e10   |
| mass, abs x <= 4.0 (noise)    | 5.2491159499288424e16  |

    at the design h = 1/50 the trusted zone alone gives >= 398x over budget
    route needs h <= 1.0e-3 (from the trusted-zone quadratic coefficient
    9.94901693473554e12)

## P3 — per-cell intervalization of the kernel and annihilator

Exact ingredients on the 400 cells of `[-4, 4]` at `h = 0.02`:

| ingredient                          | value                  |
|-------------------------------------|------------------------|
| prime-power cos-arc width, max      | 2848.7562906663193     |
| prime-power cos-arc width, mean     | 2389.6687626920107     |
| prime-power triangle width (2 sum)  | 5603.004217032817      |
| annihilator quartic width, max      | 11698.555732552893     |
| sigma slope cap (pi psi'(1/4))      | 54.02700293316511      |
| kernel width, max                   | 2849.8368307249825     |

The arc rule is exact (per-prime, from the critical points inside the cell
arc) and buys only `2x` against the triangle bound: the 41136 prime powers
retain almost no cancellation when intervalized one at a time. Charging
`width(kernel^2) <= 2 |kernel| width(kernel)` against the weight
`|ann|^2 |B|^2 |C|^2`:

    abs x <= 1 only (trusted weight):      1.0846201262976184e11  (1.08e4x budget)
    abs x <= 4 (weight partly noise):      8.861925680429115e19  (8.86e12x budget)

Both fail. The remedy is the 2291 law applied one level deeper: group the
complex owner sum (and the prime-power sum) before taking the modulus,
rather than intervalizing each prime independently.

## What this does and does not change

+ It prices out the two remaining instruments of the window lane as
  *standalone* devices: the 2275 M2 cap needs a mesh four orders finer
  than the design, and the 2302 cell screen needs grouping before its
  kernel weights can be intervalized.
+ It does not touch the frozen constants, `bUpper2243`, the 2303
  corrected-strip envelope or the Lean chain; `hgap` remains open.
+ It fixes the precision budget for any successor instrument: the owner
  corr transform must be evaluated in directed arithmetic at dps >= 50
  with a phase-aware panel rule (the float64 pipeline loses it at `|x| ~ 2`,
  and the *derivatives* lose it earlier), or replaced by analytic bounds.
+ The localization it measures is usable constructively: the weight lives at
  `|x| <= 2`, so a localized instrument on `[-2, 2]` (the regime exploited
  by the 2280 phase-centered Filon screen) is the natural successor to the
  global `[-40, 40]` mesh.

## Non-claims

+ probe grade: sampled sup values are grid maxima, not interval
  enclosures; `Gi` is the ideal smooth integrand, not the finite-rule `Gd`
  of 2275; the kernel's prime-power sum is evaluated in float64 (its own
  cancellation is mild, term scale `5603/2` against `|kernel| ~ 10-100`,
  but it is not directed);
+ the untrusted-band rows are retained in the artifact only as evidence of
  the noise mechanism; no verdict uses them;
+ the annihilator, the sigma cap and the arc rule are exact arithmetic, but
  the weight profile they are charged against is float64-sampled;
+ no hgap certificate, no producer GO, no RH claim.

## Reproduction

    MODE=selftest python3 scripts/routea_hgap_trapz_m2_probe_2305.py
    MODE=probe    python3 scripts/routea_hgap_trapz_m2_probe_2305.py

Artifact: `results/2305_hgap_trapz_m2_probe.json`.