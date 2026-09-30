# 2308 — WINDOW-WEIGHT-CERTIFIED: the finite-window hgap weight factor is machine-enclosed at 477248.99 (0.0477x budget, 1.179x the 2302 sampled proxy)

Records 2295-2302 measured the finite-window half of hgap with *sampled*
float64 weights at cell centres (proxies 0.0405x - 0.0494x of the 1e7
budget, screen grade).  Record 2302 registered the next obligation: a
continuous kernel/annihilator weight bound on the same cells, retaining all
41136 prime powers and signed cancellations before bounding variation,
followed by a directed summation.  This record discharges the weight side
of that obligation:

    charge = int_{|xi| <= 40} |kernel(xi)| |ann(xi)|^2 T(xi) dxi
           <= sum_cells h * sup_cell(|kernel| |ann|^2) * T_cell,

with sup_cell W enclosed by a centre Taylor polynomial (degree 4) of the
frozen 2280 kernel convention carrying certified float64 execution budgets
and a certified Lagrange remainder (the S-moment ladder: all 41136 signed
terms grouped BEFORE the triangle bound), and the cell sum accumulated in
`mpmath.iv` arithmetic.

Verdict: **WINDOW-WEIGHT-CERTIFIED** at mixed grade — the weight factor is
interval-certified; the transform-side perturbation majorant `T` and the
object difference radii are inherited from the 2297/2301/2302 chain at its
declared standard-arithmetic/BLAS rounding model.  The certified charge is
`477248.986223656685616186624442024032126507423...` at step 1/256
(0.0477x budget), 1.179x the finest 2302 sampled proxy.  No hgap
certificate, no producer GO, no RH claim.

+-------+-------+---------------------------+-----------+---------+--------+---------+
| denom | cells | certified charge upper    | x budget  | x proxy | rem    | time s  |
+-------+-------+---------------------------+-----------+---------+--------+---------+
|  64   |  5120 | 8.638192938082192e+05     | 0.086382  | 2.00260 | 1.4047 |  45.3   |
| 128   | 10240 | 5.718159153523268e+05     | 0.057182  | 1.39932 | 0.04390| 102.9   |
| 256   | 20480 | 4.772489862236567e+05     | 0.047725  | 1.18282 | 0.00137| 253.0   |
+-------+-------+---------------------------+-----------+---------+--------+---------+

("x proxy" is against the *same-grid* sampled-weight proxy with the
inherited `T_cell`: 431349.618 / 408638.012 / 403484.835; the cross-record
reading against the 2302 finest proxy 404928.783977559 is 1.17860.)

The certified charge intervals (36+ digit renderings of 266-bit endpoints)
are cohesive to < 1e-38 relative:

+-------+------------------------------------------------------------+
| denom | charge interval (lower endpoint rendering)                 |
+-------+------------------------------------------------------------+
|  64   | 863819.293808219213961629722483863203730616929             |
| 128   | 571815.915352326916788558557530673141709342775             |
| 256   | 477248.986223656685616186624442024032126507423             |
+-------+------------------------------------------------------------+

## What was certified, and how

The kernel convention is the 2280 frozen float64 parameterization

    kernel(xi) = sigma(2 pi xi) + 2 sum_n w_n cos(2 pi log(n) xi),
    n over the 41136 prime powers <= 492475,  w_n = log(p)/sqrt(n),
    logn = math.log(n),  theta = ((2.0*pi)*logn)*xi   (left-associated),

with `sigma(u) = log pi - Re psi(1/4 - i u/2)`.  Per dyadic cell
`[c-d, c+d]` (d = h/2, exact rational midpoint gap ZERO — a strict
improvement over the 2302 decimal grids, whose midpoint gap was 2.5e-11):

- **Taylor coefficients.**  `f^(j)(c) = sum_n 2 w phi^j [cos,-sin,-cos,sin]
  (theta + j pi/2)` is evaluated in numpy float64 over all 41136 terms
  (grouped before any norm), with a certified execution budget
  `u[(6j+40) A_j + 40 |c| B_j + 2]` where `A_j = sum 2 w phi^j` and
  `B_j = sum 2 w phi^j log n` are certified S-moment ladders in iv
  (every factor an exact-real product of float64 values in 266-bit iv;
  the true-parameter cast conversion rides in the budget constants).
  `j = 0` carries the interval sigma evaluated at the cast-widened true
  argument; `j >= 1` carries the symmetric arch slack
  `|sigma^(j)| <= 2^-j j! 4^(j+1) (1 + 2*4^-(j+1))` (Stirling recurrence).
- **Remainder.**  Lagrange tail `(d^5/5!) (A_5 (1+54u) + (2 pi)^5
  |sigma^(5)|-bound)`; the measured remainder obeys the exact d^5 law:
  1.4047 -> 0.04390 -> 0.00137, a factor 32.000 per halving on both rungs.
- **Annihilator.**  Interval product form of the four frozen nodes
  (+-0.445 +- 39.25244858548658 i) over the cell, node and argument casts
  covered by a 4u relative widening; `sup |ann|^2` is the rectangle-sup.
- **Directed summation.**  `sum_cells h * supW_cell * T_cell` accumulated in
  `mpmath.iv` at dps 80 (266 bits); `T_cell` is the 2298/2302 perturbation
  majorant `sum(error_terms(sup_b, sup_c, r_b, r_c))` on the same cells.

Measured certified constants (frozen at every rung):

+---------------------+-------------------------------------------+
| S-moment A_0        | 2801.5021085164085   (= 2 S1, 2 x 1400.751)|
| S-moment A_5        | 5791701927943.102                          |
| S-moment B_4        | 921777990747.0049                          |
| err_j @ c=40, j=0..4| 5.55e-09, 4.00e-07, 2.94e-05, 2.18e-03, 0.164|
| arch bounds j=0..4  | 6, 56.55, 1302.8, 47998, 2.399e6           |
+---------------------+-------------------------------------------+

The budget at j = 4 (0.164 at |c| = 40) is 12 orders below the coefficient
scale 7.70e10 and enters the cell sup only through `d^4/24 ~ 2.3e-10`;
`err_0 ~ 5.6e-9` is invisible against the sigma width ~1.2e-14.  The sigma
engine is the 2043 `sigma_arch_iv` routine (Stirling shift 8, six Bernoulli
terms, analytic remainder (1/12) 8.25^-14 <= 3.97e-15) with the Bernoulli
coefficients rebuilt inside the interval context from exact integer ratios;
anchors against the float64 1741 engine: u = 0 (5.372183419225642...), and
u = +-125.66370614359172 (-2.995729634952...) all contained.

## Refinement laws and controls

The charge falls 1.511x then 1.198x per halving toward the sampled proxy
(proxy ratio 2.00x -> 1.40x -> 1.18x), driven by the d^5 remainder
collapse (1.4047 -> 0.00137, exactly 32.000x per halving).  Two measured
subtleties:

1. The **mean of per-cell sup/center ratios is NOT the charge ratio**: the
   kernel-mean ratio *rises* between denom 128 and 256 (2.73 -> 3.88) while
   the charge ratio falls, because finer grids land more centres near
   kernel zeros (per-cell max 674 -> 15211) in cells whose T-weight is
   small.  The T-weighted charge ratio is the convergence measure.
2. The annihilator ratio is essentially flat (sup/center mean
   1.0103 -> 1.0051 -> 1.0025, max 1.2684 -> 1.0589): the degree-8
   annihilator varies little across these cells; the weight-side work is
   all in the oscillatory kernel.

Inherited T-side readings are stable across the three grids
(`t_sum_max` 8.95/8.89/8.87e-9; `max_cell_sup_base` 1.06809 -> 1.06783;
`max_cell_sup_corr` 65.74 -> 65.16), so the charge decay is weight-side,
as designed.

## Certification lessons (found while building this instrument)

1. The **true-parameter control reference must multiply by
   `phi^j = (2 pi log n)^j`**, not `log(n)^j`: an early dps-100 reference
   dropped the (2 pi)^2 factor at j = 2 and produced a phantom 9.6e4 gap
   (2 x |sum 2 w phi^2 cos|) that looked like a 3e9 x budget violation.
   The decisive control was `est - ref_conv = 5.6e-9` on the *same*
   float64 parameters: the float path was faithful, the reference was not.
2. The derivative trig pattern must be `(cos, -sin, -cos, sin)` with the
   sin/cos selector `(1, 0, 1, 0)`, not `(0, 1, 0, 1)`; an inverted
   selector silently replaces the j = 2 coefficient by a sine sum.
3. Float interval endpoints need one outward `nextafter` per side when
   built from `center +- radius` in float64: the endpoint rounding and the
   certified-radius truncation can each shrink an endpoint by half an ulp.
4. `492475` is the (sieve) prime-power *limit*, not a book element: the
   largest book entry is the prime 492467 (492475 = 5^2 * 19699 is not a
   prime power).  Book checks must compare against `floor(e^support)`, not
   the last element.
5. Coarse grids fail loudly and correctly: at d = 0.0625 (denom 8) the
   Taylor degree-4 sup exceeds the centre weight by ~6.5e3x because the
   kernel wavelength (~0.0765 at the top prime) is comparable to the cell;
   the end-to-end selftest control runs at denom 32 (measured 6.0x,
   asserted < 12x) where the chain is meaningful.

## Nonclaims

- The transform-side perturbation majorant `T_cell` (cell transform
  suprema, derivative execution bounds, object difference radii from the
  2301/2297 artifacts) is inherited at its declared rounding-model grade;
  only the weight factor is interval-certified here.
- The certified kernel bounds the true Weil kernel through the frozen 2280
  float64 parameterization with certified cast budgets; libm cos/sin and
  numpy pairwise summation enter inside those budgets as declared
  substrate trust (same class as the mpmath.iv substrate trust of 2307).
- `sigma_arch_iv` is a verified-copy of the 2043 routine with iv-rebuilt
  coefficients; its analytic remainder is a bound, not a proof of the
  Stirling expansion.
- Finite window |xi| <= 40 only; the infinite tail is 2307 and is not
  re-touched.  The structural identification of the window integrand
  (kernel |ann|^2 T) is inherited from 2298-2302 and is not re-derived.
- The stored charge endpoints are 36+ digit renderings of 266-bit
  intervals (renderings cohesive to < 1e-38 relative, width far below the
  verdict margins); the rendering cannot flip a budget comparison.
- No hgap certificate, no producer GO, no RH claim.

## Reproduction

    STEP_DENOM=64  python3 scripts/routea_hgap_window_cert_2308.py
    STEP_DENOM=128 python3 scripts/routea_hgap_window_cert_2308.py
    STEP_DENOM=256 python3 scripts/routea_hgap_window_cert_2308.py
    MODE=constants python3 scripts/routea_hgap_window_cert_2308.py
    MODE=reduce python3 scripts/routea_hgap_window_cert_2308.py
    MODE=selftest python3 scripts/routea_hgap_window_cert_2308.py   # 9/9 PASS
    python3 scripts/routea_hgap_window_cert_selftest_2308.py        # 13 tests OK

Environment: WSL2 side, Python 3.12.3, mpmath 1.4.1 (`iv.dps = 80`, 266
bits), numpy 2.5.3.  Each rung costs 45/103/253 s (transform-dominated);
the full ladder ~7 minutes.

Module selftest landmarks: prime book pinned (41136, limit 492475); moment
ladder encloses the float64 sums; budget dominance against a dps-100
true-parameter reference at two real cells (j = 2, 4); polynomial sup
dominates a dense grid on three cells; annihilator sup dominates; the
numpy path replicates `SOURCE.prime_kernel` to <= 1e-11; sigma anchors;
arch bounds vs finite differences; end-to-end at denom 32 with
cert >= proxy (band [0.999, 12)).

Artifact selftest landmarks: verdict/scope flags; monotone ladder shape;
budget clearance (< 0.1x every rung, < 0.05x best); soundness direction
cert >= same-grid proxy on every rung with tightness < 3x; the exact
factor-32 d^5 remainder signature on both rungs; cross-record 1.17860x the
2302 finest proxy; dyadic cell geometry (radius exactly 1/(2 denom), zero
midpoint gap); charge-interval cohesion; pinned S-moment constants;
inherited T-side readings; provenance; step-vs-artifact consistency.

Artifacts: `results/2308_window_weight_certified.json` (reduce),
`results/2308_window_weight_step_den{64,128,256}.json`.  Predecessor:
`results/2302_local_frequency_taylor_screen.json`.  Owner capture:
`results/2275_gap_owner_audit.json`.

Next: the transform side at interval grade (the last non-model factor of
the window half), then the localized [-2, 2] instrument as the window
successor; with 2307, a certified tail rung plus this certified weight
factor is one transform-majorant away from a full hgap certificate at
numeric grade.