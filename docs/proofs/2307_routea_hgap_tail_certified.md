# 2307 — TAIL-CERTIFIED: the grouped flat-edge hgap tail is machine-enclosed at 1.9586382184619955e-27 (margin 5.11e33) at N = 36

Record 2306 priced the tail half of hgap at artifact grade with a declared
running-magnitude slack model (`|q - q_true| <= kappa M_q`, `kappa = 2^-30`).
Record 2307 removes the slack model entirely and re-encloses the same
grouped scheme in interval arithmetic: every endpoint is an outward-rounded
`mpmath.iv` bound at `dps = 40` (136 bits), the `A_j` ladder is exact
arbitrary-precision integer arithmetic, and the annihilator l1 norm and the
kernel constant `C_W` are certified in-script (own sieve for the prime-power
sum).

    Tail = int_{|xi| > 40} kernel(xi) |ann(xi)|^2 |B(xi)|^2 |C(xi)|^2 dxi
        <= 2 A1^2 (V_N^b V_N^c)^2 / (2 pi)^{4N}
           * int_40^inf (log xi + C_W) xi^{8-4N} dxi,
    V_N^ch = 2 Rmax * sup_y |h_ch^{(N)}(y)|   (certified cell enclosure).

Verdict: **TAIL-CERTIFIED** — the certified tail is
`1.9586382184619955e-27` at order 36 (margin `5.1055881100147315e+33`).
Every certified rung clears the `1e7` hgap budget; the tightest certified
rung (N = 16, the crossing order) still clears by a factor 1445. Any single
certified rung discharges `tail <= 1e7`; the ladder is redundancy.

+-----+------+-------+---------------------------+----------------+---------+
|  N  |  n0  | cells | certified tail upper      | margin         | time s  |
+-----+------+-------+---------------------------+----------------+---------+
|  16 | 4096 |  4109 | 6.918973606907223e+03     | 1.445301e+03   |  338.8  |
|  20 | 4096 |  4109 | 2.452555829669849e-05     | 4.077379e+11   |  466.2  |
|  24 | 2048 |  2061 | 3.362393870024703e-12     | 2.974072e+18   |  305.6  |
|  36 | 2048 |  2061 | 1.958638218461996e-27     | 5.105588e+33   |  570.1  |
+-----+------+-------+---------------------------+----------------+---------+

The certified enclosure per rung (certified `V` intervals, cell argmaxes):

+-----+---------------------------+---------------------------+--------------+
|  N  | V_base (upper)            | V_corr (upper)            | argmax y     |
+-----+---------------------------+---------------------------+--------------+
|  16 | 8.306422352561896e+31     | 1.572111191894244e+32     | 0.0464/0.3632|
|  20 | 3.762127771277007e+39     | 3.737828451708567e+39     | 0.0752/0.3600|
|  24 | 2.754293751373607e+47     | 3.331248421577158e+47     | 0.2848/0.4000|
|  36 | 9.382582452430505e+70     | 1.186074348079619e+74     | 0.5280/1.2704|
+-----+---------------------------+---------------------------+--------------+

## What was certified, and how

The 2306 cell scheme was re-implemented in interval arithmetic without
changing its mathematics:

- `A_j` coefficients are exact Python ints (the 2306 float64 recursion loses
  exactness past `2^53`); coefficient triangles are taken on `|A_j|`
  intervals.
- The cell sup of the S-function is the monotone clip image
  `sup_{s in [s_lo,s_hi]} e^{-K/s} s^{-m} = e^{-K/s*} s*^{-m}` with
  `s* = clip(K/m, s_lo, s_hi)` evaluated in iv; the ODE identity
  `A_j' = (A_{j+1} - 2u(2j s - K) A_j)/s^2` is folded into `S(2j+2)`.
- The family sum runs over complex intervals with carrier phases kept
  exactly (grouping-before-modulus, the 2291 law); cell value interval plus
  the `(Delta/2) sum |c_f| sup |t_f'|` mid-value correction.
- `a1` (annihilator l1 norm) and `c_w` are certified closed forms; the
  prime-power tail of `C_W` is summed over an own exact sieve up to
  `floor(upper(e^{2 S}))` (S = 6.553600000000003), 41136 prime powers up to
  492475.
- The tail integral is the closed form
  `40^{1-p}/(p-1) (log 40 + 1/(p-1)) + C_W 40^{1-p}/(p-1)`, `p = 4N - 8`,
  verified against normalized high-precision quadrature in the selftest
  (rel 1.32e-20).

No kappa model, no sampled maximum, no float64 on the certificate path.
The float64 instrument of 2306 runs alongside on the *same lattice* as a
crosscheck; the two bounds agree to (2-8)e-9 relative:

+-----+---------------------+---------------------+-----------+-------------+
|  N  | cert/float ub base  | cert/float ub corr  | cert/lb b | cert/lb c   |
+-----+---------------------+---------------------+-----------+-------------+
|  16 | 0.9999999979        | 0.9999999916        | 1.3089    | 2.1405e+01  |
|  20 | 0.9999999976        | 0.9999999924        | 1.3799    | 2.2082e+01  |
|  24 | 0.9999999964        | 0.9999999956        | 4.3126    | 4.9440e+01  |
|  36 | 0.9999999961        | 0.9999999979        | 31.0910   | 1.2016e+10  |
+-----+---------------------+---------------------+-----------+-------------+

The certified bound sits *below* the float bound by ~1e-8 relative: the
float carries the `kappa * magchain` term (`kappa = 9.3e-10` times a chain
factor of a few), the certificate carries only interval inflation
(1e-29..1e-40 relative). That direction is the kappa signature: it is the
evidence that the certified path has no slack term of its own. `cert/lb >= 1`
for every rung is the opposite (soundness) direction against the sampled
lower bound.

## Certified constants vs the 2306 float64 conventions

+--------+------------------------------------+-----------------------+---------+----------+
| const  | certified upper (136-bit)          | 2306 float64          | ulp gap | width/val|
+--------+------------------------------------+-----------------------+---------+----------+
| a1     | 2497731.3887381445419385430953961  | 2497731.388738144     | +0.76   | 2.3e-40  |
| c_w    | 2810.1333609392076324898619004401  | 2810.1333609392077    | -0.16   | 4.6e-37  |
+--------+------------------------------------+-----------------------+---------+----------+

The certified interval width is ~25 orders below one float64 ulp: the
certificate resolves both closed forms far beyond double precision. The
float64 constants are rounded renderings that sit within one ulp (the
certified upper is +0.76 ulp above the a1 float64, i.e. 2306's float64 a1
underestimated by 1.4e-16 relative, and -0.16 ulp below the c_w float64);
their effect on the 2306 tail numbers is <= 3e-16 relative, invisible.
The a1 comparison must rebuild any high-precision reference from the *same*
float64 terms: an exact-rational `1/12` differs from its float64 by ~1.7e-17
relative, and the six Bernoulli terms sum to a phantom `7.2e-20` gap that
looks like a certificate error (the selftest does this correctly: b-ref rel
`2.288e-37`).

## Comparison with the 2306 artifact-grade ladder

2306's `run_order` refines the top-512 cells by six bisections (11277 cells
at every covered order). The certified instrument deliberately evaluates
the master lattice only -- a pure function of `n0` and the family cuts, with
no data-dependent cell selection that would itself need certification:

+-----+---------------------------+---------------------------+-------------+
|  N  | certified (master lattice)| 2306 float (refined)      | ratio       |
+-----+---------------------------+---------------------------+-------------+
|  16 | 6.918973606907223e+03     | 553.7599646               | 1.2495e+01  |
|  20 | 2.452555829669849e-05     | 2.620431005e-06           | 9.3594e+00  |
|  24 | 3.362393870024703e-12     | 4.702185332e-14           | 7.1507e+01  |
|  36 | 1.958638218461996e-27     | 2.145448788e-32           | 9.1293e+04  |
+-----+---------------------------+---------------------------+-------------+

The gap between the columns is the refinement gain (9x at N = 20 to 9.1e4 x
at N = 36, where the high-order sup is exquisitely cell-sensitive).
Refinement is a cost optimization, not a requirement: even the coarse-lattice
certificate clears the budget by 33 orders at its best rung and 1445x at its
tightest. The 2306 refined-lattice numbers remain artifact grade; the 2307
certified numbers are the master-lattice ones above.

## Certification lessons (found while building this instrument)

1. `mpmath.iv` constructors and arithmetic round endpoints **outward**
   (spot-verified: a 266-bit integer lands in an outward 136-bit interval
   with relative width ~1e-41; float64 inputs are exact points). Comparing
   endpoints with `mp.mpf(endpoint)` **outside** a `workdps` context silently
   re-rounds at the default `mp.dps = 15` and produces phantom divergences;
   every in-script comparison runs inside `mp.workdps(120)`.
2. The cell sup needs `s_lo = min` of the two endpoint lowers -- an early
   `max` made the evaluation range too narrow and read `3.6e34` where the
   float instrument read `9e-134` (cell-level diagnostic at N = 8, n0 = 96,
   y ~ 2.5088, R = 2.56).
3. The S-function clip must be the monotone *image* `[clip(lower q),
   clip(upper q)]`; an early empty-intersection "swap" fallback extended the
   evaluation to `K/m` and inflated the sup by ~158 orders.
4. The 2306 `c_sigma` convention `0.5/8.0` must be carried as written; a
   mistyped `0.125` moves `c_w` by 1/16 relative.
5. `CUTOFF_MARGIN = 0` is already sound for the prime cutoff: `floor` of the
   outward upper of `e^{2S}` contains every `n <= e^{2S}`; an added
   "+64 primes" margin inflated `c_w` by 7.5e-5 relative (this was the
   1.0000754 ratio first blamed on the cutoff itself).
6. The frozen instrument constants are float64 by convention (2306); the
   certified closed forms differ from them at the ulp level, and reference
   comparisons must rebuild from the same float64 terms (see above).

## Nonclaims

- Structural identification of the tail integrand (grouped exact derivative
  `h^{(N)}`, annihilator split, kernel bound) is inherited from 2304/2305
  and is not re-derived here; 2307 certifies the numeric enclosure of the
  2306 scheme, not its analytic provenance.
- This closes the **tail half** of hgap only. The finite-window half
  (records 2295-2302, sampled-grade proxies 0.0405x - 0.0494x of budget)
  still needs its own certified enclosure before any hgap certificate.
- Master-lattice certification only: no adaptive refinement is certified,
  and the 2306 refined-lattice numbers are not certified.
- Substrate trust: `mpmath.iv` outward rounding is assumed and spot-verified
  at this grade, not formally proved; the certificate is exactly as strong
  as the interval substrate.
- Stored endpoints are 30+ digit renderings of 136-bit intervals; the
  measured renderings are cohesive to <= 1e-29 relative and every verdict
  margin carries >= 3 orders of headroom, so the rendering cannot flip a
  budget comparison.
- Orders 8 and 12 are not certified: 2306 measured them 15+ orders above
  budget (dead), and a certificate there is pointless.
- No hgap certificate, no producer GO, no RH claim.

## Reproduction

    MODE=order ORDER=16 N0=4096 python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=order ORDER=20 N0=4096 python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=order ORDER=24 N0=2048 python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=order ORDER=36 N0=2048 python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=constants python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=reduce python3 scripts/routea_hgap_tail_cert_2307.py
    MODE=selftest python3 scripts/routea_hgap_tail_cert_2307.py     # 14/14 PASS
    python3 scripts/routea_hgap_tail_cert_selftest_2307.py          # 12 tests, OK

Environment: WSL2 side, Python 3.12.3, mpmath 1.4.1 (`iv.dps = 40`,
136 bits), numpy 2.5.3. Each rung costs 306-570 s; the full ladder is
~28 minutes.

Module selftest landmarks: exact `A_j` vs 2306 float worst rel `0.00e+00`;
S-function vs brute-force grid sup worst deficit `0.00e+00`; value
enclosure contains the dps60 evaluation; `a1`/`c_w` within 1e-12 of the
2306 floats (ratio `1.000000000000000`); `c_w` certified encloses the dps120
reference of the frozen constants (b-ref rel `2.288e-37`); tail closed form
vs quadrature rel `1.32e-20`; end-to-end N = 8, n0 = 96: certified ub >=
float lb, certified/float ub ratio `1.000000` (both argmax and max).

Artifact selftest landmarks: verdict and scope; ladder shape and margins;
per-order endpoint admissibility (ordered, cohesive, `V = 2 Rmax ub`
recomputed); the no-kappa crosscheck signature in both channels; constants
within 2 float64 ulps and certified width < 1e-30 relative; iv construction
outwardness; exact big-int `A_j`; S-function sup; tail quadrature; the
end-to-end certified-vs-float cell bound; provenance.

Artifacts: `results/2307_hgap_tail_certified.json` (reduce),
`results/2307_cert_order_{16,20,24,36}_n*.json`. Predecessor:
`results/2306_hgap_tail_sharp.json`. Owner capture:
`results/2275_gap_owner_audit.json`.

Next: certified enclosure of the finite-window half of hgap (grouped
analytic weights, the 2291 law one level deeper), then the localized
[-2, 2] instrument as the window successor; carrier: a single certified
tail rung plus a certified window bound is a full hgap certificate at
numeric grade.