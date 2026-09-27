# 2055 — Route A link L2: the sigma-channel Taylor model and the second ladder extension at m = 1600

Verdict: **REDUCED-L2-VIABLE** at the registered owner (one-copy G8-H,
ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support 9.504).  Both
levers that record 2054 registered are moved with methods, and the window
node of the L2 architecture on the m = 1600 object now lands at

```
total = 4.339137e+10 (aggregate remainder, h = 0.00025)
      + 1.308048e+07 (L1 nodal input at the same rung)
      + 6.072137e+08 (sigma-channel third-order Taylor enclosure)
      = 4.401166e+10  =  0.0129 x the re-based ideal budget (3.406050e+12)
                      =  0.1292 x the 10% bar          (3.406050e+11)
```

so the window node IS priced under the 10% bar, by a factor 7.74.  The
two movements and their sizes:

```
addend           2054 reading     2055 reading     factor
----------------+----------------+----------------+--------
aggregate       | 7.564715e+11   | 4.339137e+10   | 17.43x
sigma channel   | 9.287269e+11   | 6.072137e+08   | 1529.5x
L1 nodal        | 1.307804e+07   | 1.308048e+07   | 1.0002x
----------------+----------------+----------------+--------
total           | 1.685212e+12   | 4.401166e+10   | 38.29x
```

The decomposition also shows the addend ORDER is now stable in the other
direction: the aggregate remainder is 98.6% of the total (0.1274x bar10 by
itself, 7.85x under), the sigma enclosure 1.4%, the nodal input 0.03%.
The old-convention total (the 2048 A1 archimedean projection kept in place
of the Taylor model) would read 9.721314e+11 = 2.854x bar10: the sigma
method change is decisive on its own and the ladder extension is decisive
on its own -- each lever alone leaves the total above the bar (the 2054
record's reading), and only the pair crosses it.

Probe: `scripts/routea_reduced_second_2055.py` (md5
`091b8dc45517c96c70c615743a33a486`, WSL ext4 mirror run, 1226.0 s),
artifact `results/2055_reduced_second.json` (md5
`b5c1a9c914d7499e1a06780b4797eeed`).  L4 (record 2053) is NOT re-run and
is NOT affected (evaluator-independent).  L5 is not touched.  This record
prices the window node only.

## 1. Frozen rules, controls, and anchors

Object and scope as 2054: the committed 2037-class float pipeline with the
phi-quadrature rule at m = 1600 (`xw1600 = phi_weights(a, panels = 6,
m = 1600)`, 9600 nodes/fam), committed base/corr and kernel, window
[-40, 40], stored floats exact; budget = |Q_1600| =
3.4060498718812666e+12 (the 2053 frozen value), bar = 10% of it.

The two method changes, frozen in the probe header (script lines 8-115):

  (A) **The sigma channel, third-order Taylor model.**  2048 A1 (kept by
      2054) priced `int sigma*g` by the direct interval method on 0.05
      panels at zeroth order: `arch_proj = sum_i w_sigma(panel_i) *
      g_mid_i * 0.05`, with `w_sigma` the ordinary interval width of
      `r43.sigma_arch_iv` over the panel (`~ |sigma'| dxi`, so
      refinement-proof).  The 2055 enclosure replaces it per panel by
      `int_panel sigma*g = sigma(m) G0 + sigma'(m) G1 + (1/2) sigma''(m)
      G2 + R3` with `|R3| <= (1/6) sup_panel|sigma'''| r^3 int_panel |g|`,
      `r = dxi/2`: the moments `G_k = int (x-m)^k g` are trapezoids of the
      committed fine-grid samples with `(dxi^2/12) int |g^(j)|` error
      charges bounded by the model's own sup enclosures on the 0.001
      grid, and `sigma^(k)(m)`, `sup_panel|sigma'''|` come from the
      termwise-differentiated Bernoulli ladder + elementary tail charges
      (section 4).  The reported quantity is the one-sided deviation
      bound `arch3 = sum_i W_i`, matching the A1 convention it replaces.

  (B) **The aggregate ladder, extended to h = 0.0005 and 0.00025** (six
      rungs: 0.01, 0.005, 0.002, 0.001, 0.0005, 0.00025).  The 2054
      endpoint step ratio 4.06 sits on the h^2 law of the hump panels'
      trap-difference charge; the rung machinery (`r51.run_rung`,
      re-used verbatim) is h-parametric and the ladder nodes land on the
      fine grid (h/dxi = 2 and 1).  Machinery note: `run_rung`'s stencil
      slices read `gpp` up to index `2 n_pan + 1`, one past the fine-grid
      stencil's single trailing edge copy at the new rungs, so the probe
      passes `gpp` with two additional trailing copies (the same edge
      convention `fine_grid` itself uses).  For h >= 0.001 the slices
      never reach the pad, so 2054-identity is untouched -- gated
      bitwise by P2.

Frozen verdict rule: `total = min over the six rungs of min(charge_L3,
charge_agg) + charge_L1 at the best rung + arch3`; VIABLE if all gates
pass and total < bar10, GRAY if < budget3, FAIL otherwise, ANCHOR-FAIL on
any gate miss.

Gates: P1/P2/P3 (arch-old, rung h = 0.001 fields, L1 at h = 0.001 all
reproduce the 2054 artifact, rel <= 1e-9); C1/C2 (Q400/Q1600 vs 2053,
rel <= 1e-6, sign < 0); C3 (setup constants incl. C_book/C1_book);
C4 (span equivalence 0); C5 (m = 400 vs the 2051 artifact, rel <= 1e-9);
C6 (arch width_mean vs 569.087, 2%); A1 (a1_abs_max <= 1e-9 gmax at all
six rungs); A2a (0 violations at all six rungs); A2b (booked gap charge
<= 1e9 at all six rungs); A3 (r51 iv containment); A6/B5 (r51/r52
selftests); A7 (sigma-derivative containment vs mpmath polygamma at dps
45, 17 u-points x 4 orders, worst ratio < 1); A8 (committed
`r43.sigma_arch_iv` contains the same mp digamma references); A9
(charge_L3 and charge_agg strictly decreasing over the six rungs);
A10 (Taylor-3 mp references -- mp sigma derivatives at dps 45 times the
same float moments -- inside the panel enclosure at 9 sampled panels and
inside `[C +/- arch3]` for the whole window); B1 (containment 7/7);
B3 (ladder-vs-fine bitwise 0.0 at both new rungs); B4 (charges finite,
non-negative).  All 21 pass.

## 2. Controls read

  +---------------------------------------------------------------------+
  | control                          | reading                           |
  +----------------------------------+-----------------------------------+
  | P1 arch-old vs 9.287269e+11      | rel 0.000e+00 (bitwise)           |
  | P2 rung h=0.001, five fields     | rel 0.000e+00 all (bitwise)       |
  | P3 L1 at h=0.001 vs 1.3078036e+07| rel 0.000e+00 (bitwise)           |
  | C1 Q_400 vs 2053 (-1.1112e+20)   | rel 6.661e-16, sign_ok            |
  | C2 Q_1600 vs 2053 (-3.4060e+12)  | rel 2.442e-15, sign_ok            |
  | C3 C_book / C1_book              | rel 0.000e+00 both (bitwise)      |
  | C4 worker/parent, ParModel/base  | 0.0 / 0.0                         |
  | C5 m=400 L3 and agg vs 2051      | rel 0.000e+00 both (bitwise)      |
  | C6 width_mean vs 569.087 (2043)  | 569.0867771360982, rel 3.92e-07   |
  |    width_mean vs 2054            | rel 0.000e+00 (bitwise)           |
  | A3 / A6 / B5                     | pass / pass / pass                |
  | A7 sigma-deriv worst ratios      | sig 0.1042, s1 6.773e-05,         |
  |                                  | s2 2.996e-04, s3 1.184e-04        |
  | A8 committed sigma_iv vs mp      | worst dev/span 0.9375 (< 1)       |
  | B3 new rungs (0.0005 / 0.00025)  | 0.0 / 0.0 (bitwise)               |
  | B1 containment                   | 7/7, worst ratio 2.274e-05 at    |
  |                                  | xi = -6.68; diff 0.0 at xi=-7.03 |
  +----------------------------------+-----------------------------------+

Reading: every reproduction gate is BITWISE, not tolerance-level.  The
rung rows at h = 0.01 / 0.005 / 0.002 / 0.001 match the 2054 artifact on
all five frozen fields to rel 0.0; the m = 400 control row matches the
2051 artifact on both charges to rel 0.0 (sum_U 1.235178868676494e+25,
tight median 12874481.7590); the arch projection matches 2054 to the last
float (928726947225.5668, rel 0.0).  The tier-B diagnostic is unchanged
from 2054 (d_base 2.151e-09, d_corr 2.481e-09, Q shift 1.017e-08 rel).

A7's reading is the batch's instrument element: the four sigma
derivative channels are contained by their interval enclosures with worst
validation ratios 0.104 (sigma itself, dominated by the committed
routine's own truncation near u = 0), 6.8e-05, 3.0e-04, 1.2e-04 -- five
orders of margin on the odd channels and an order on sigma.  A8 is thin
but exact in the right direction: the committed `r43.sigma_arch_iv`
enclosure has worst dev/span 0.9375 at u = 0 (its REM constant
(1/12)/8.25^14 = 1.23e-14 is exactly the u = 0 tail bound, and the true
truncation there is 1.14e-14 -- the committed comment's "3.97e-15" is a
stale constant, the code is sound) -- this is the one margin inside the
run that is under 2x, and it is the committed routine's, not the new
machinery's.

## 3. The window price at m = 1600

Rungs (all six; `r51.run_rung` verbatim, fine grid 320001 pts, gmax
2.556148e+14, U grid 80001 pts at 0.001):

```
h        charge_L3      charge_agg     agg_main       agg_theta      sum_U
---------+--------------+--------------+--------------+--------------+-----------
0.01     | 4.835546e+14 | 3.837446e+14 | 1.493574e+14 | 2.311832e+14 | 8.4455e+18
0.005    | 5.570126e+13 | 3.318516e+13 | 1.950061e+13 | 1.331514e+13 | 7.7828e+18
0.002    | 6.904699e+12 | 3.418537e+12 | 2.712511e+12 | 6.602153e+11 | 1.5074e+19
0.001    | 1.633533e+12 | 7.564715e+11 | 6.675343e+11 | 7.809778e+10 | 2.8530e+19
0.0005   | 3.990430e+11 | 1.784765e+11 | 1.662895e+11 | 9.538949e+09 | 5.5756e+19
0.00025  | 9.871025e+10 | 4.339137e+10 | 4.155651e+10 | 1.179813e+09 | 1.1034e+20
```

The first four rows ARE the 2054 rows (P2 bitwise).  The step ratios of
`charge_agg` over the six rungs read 11.564 / 9.707 / 4.519 / 4.238 /
4.113: the sequence walks onto the h^2 law (ratio 4) as h falls -- the
hump panels' trap-difference charge, `(h^3/12)|g''|` per panel times
`3/h` panels `= h^2 |g''|/4` -- and the last two rows confirm the
extrapolation from the 2054 endpoint within 1% (predicted 1.8e+11 /
4.3e+10, measured 1.784765e+11 / 4.339137e+10).  Best rung h = 0.00025,
`min = 4.339137e+10` (agg < L3 at every rung; the ratio agg/L3 falls
0.794 -> 0.596 -> 0.495 -> 0.463 -> 0.447 -> 0.440 along the ladder).  A1 residual <= 4.062 (bound 1e-9
gmax = 2.556e+05), A2a 0 violations at every rung (worst fraction 1.000
at the three finest -- the bound sits at its own ceiling), A2b booked
gaps 0 / 0 / 5.096e+06 / 5.842e+05 / 5.038e+04 / 6.241e+03 with
violation counts 0 / 0 / 4 / 10 / 231 / 1107 (the fd-excess panel count
grows as h falls while the booked charge falls -- booking only, never
charged).

L1 nodal at h* = 0.00025 (the 2052 calculus at m = 1600, 320001 nodes):
Coef1 23327.599223, e_g max 71791.89 / median 3.937e-19, charge
1.308048e+07 (nodal 1.307422e+07 + echo 6.261e+03).  The P3 control at
h = 0.001 reads 1.3078036402e+07 rel 0.0 against 2054 -- the nodal
charge grows 0.019% from h = 0.001 to h* (Coef1 23323.213 -> 23327.599);
rigor on this addend is free at the reduced evaluator either way.

Sigma channel at m = 1600 (1600 panels of 0.05, r = 0.025):
`arch3 = 6.072137e+08` (one-sided), centre `C = -2.347126e+14`: the
Taylor model certifies the window's `int sigma*g` -- which itself is
large and cancellation-prone, `-2.35e+14` -- to an absolute 6.07e+08,
relative 2.6e-06.  The mp reference (mpmath digamma/polygamma at dps 45
against the same float moments) lands at `dev = 2.348e-02` from C, i.e.
3.87e-11 of W, and the per-panel reference deviations are <= 8.1e-12 of
their W_i.

Assembly:

```
best_min (agg at h = 0.00025)   4.339137e+10
charge_L1 (at the same rung)    1.308048e+07
arch3 (Taylor-3 enclosure)      6.072137e+08
--------------------------------------------
total                           4.401166e+10
  = 0.0129 x budget3  =  0.1292 x bar10    ->  REDUCED-L2-VIABLE
old convention (arch_old)       9.721314e+11  =  2.854 x bar10
```

## 4. The sigma machinery and its price

The element is the interval sigma-derivative chain, validated in-run:

```
sigma(u) = log pi - Re psi(1/4 - i u/2),  w = z + 8,  z = 1/4 - i u/2
psi(z)   = psi(z+8) - sum_{j<8} 1/(z+j)      [exact shift identity]
psi'(w)  = 1/w + 1/(2w^2) + sum_{n<=6} B_2n w^{-2n-1}            + T1
psi''(w) = -1/w^2 - 1/w^3 - sum (2n+1) B_2n w^{-2n-2}            + T2
psi'''(w)= 2/w^3 + 3/w^4 + sum (2n+1)(2n+2) B_2n w^{-2n-3}       + T3
```

with tail charges from the exact Gauss representation
`psi(w) = log w - 1/(2w) - 2 int_0^inf t/((w^2+t^2)(e^{2 pi t}-1)) dt`
expanded to n = 6: `|T0(w)| <= 2 M13/(|w|^12 Dmin(w))` with
`M13 = |B_14|/28 = 1/24` and `Dmin = x^2+y^2 if |y| <= x else 2x|y|`,
`T1..T3` by Cauchy on the disk `|w - w0| = rho = x/2` (Re w >= 4.125 on
it), all times SAFE = 8 (the pointwise validation against mpmath peaked
at diff/charge 0.93 pre-SAFE at u = 0, the least-convergent sample --
the factor is margin, not derivation).  Chain to the xi axis:
`d sigma/du = -(1/2) Im psi'(z)`, `d^2/du^2 = (1/4) Re psi''(z)`,
`d^3/du^3 = (1/8) Im psi'''(z)`, `d^k/dxi^k = (2 pi)^k d^k/du^k`.

The enclosure W = sum W_i decomposes per panel into the sigma value
channel (`w_h(sigma)|T0|`), the slope and curvature channels
(`h1|T1|`, `(1/2)h2|T2|`), the moment-error channels
(`(|sig_c|+w_h)e0`, `(|c1|+h1)e1`, `(1/2)(|c2|+h2)e2`), and the Taylor
remainder `(1/6) S3 r^3 (I + e0)`.  Bin table of W (1600 panels):

```
xi bin     | W                | C                | max S3 over bin
-----------+------------------+------------------+----------------
[-40,-8)   | 1.057630e-02     | -1.326055e+03    | 4.028e-03
[-8,-5)    | 6.072117e+08     | -2.347124e+14    | 1.704e-02
[-5,-1)    | 1.960189e+03     | -2.415998e+08    | 2.795e+00
[-1,1)     | 8.797179e-08     | 8.786138e-05     | 1.197e+05
[1,5)      | 3.240012e-13     | -5.140300e-12    | 2.795e+00
[5,40)     | 1.567641e-12     | -1.814e-13       | 1.704e-02
```

The mass hump [xi in [-8,-5]] carries 99.99966% of W and essentially all
of C.  The third-order remainder is NOT the binding channel: the
sigma'''-large zone sits at xi ~ 0 (max S3 = 1.2e+05 at [-1,1]) where the
object is mass-free (|g| ~ 1e-8..1e-4, bin W = 8.8e-08) -- the
cancellation structure that made the 2053-era Taylor worry moot is
exactly this mass/smoothness anti-correlation.  The worst single panel
is 680 (xi = -5.975), W_i = 5.983e+07, with S3_i = 9.966e-03: the price
inside W is carried by the moment-error and slope channels on the hump
(T0-scale terms), not by R3.  The centerpiece number is the comparison:
9.287269e+11 -> 6.072137e+08 is a 1529.5x reduction in the sigma channel
at unchanged scope, with the enclosure honest at relative 2.6e-06 around
the large cancelling center.

## 5. Consequence and next items

The window node of link L2 is now VIABLE at the 10% bar on the object a
certificate needs, with 7.74x margin (remaining slack 2.966e+11).  What
is binding inside the priced total is now unambiguous: the aggregate
remainder at h = 0.00025 (98.6% of the total; 0.1274x bar10 alone) --
and it is itself on a measured h^2 law (charge_agg ~ 6.94e+17 * h^2 from
the last two rungs; h = 0.000125 would extrapolate to ~1.1e+10 at 2x
nodes).  The sigma channel is second at 1.4%, moment-error-bound at
dxi = 0.00025; the nodal input third at 0.03%.  None of these needs
action for the bar; the levers are registered for the next tightening
round.

Standing boundaries, unchanged by this record: L4 (the full-line tail,
record 2053) is evaluator-independent and was not re-run -- the priced
object here is the WINDOW node only; L5 (F construction, phi quadrature,
eigh/min-h1, sigma) remains registered and untouched (the tier-B
diagnostic continues to price the eigh/min-h1 component at ~3.5e+04
absolute, four orders below the bar); COVER (uniformity over
hypothetical off-line zeros) is open at the program level.

## 6. Incident chain (instrument only; one caught by a gate, one pre-run)

1. **The sigma conjugation incident (caught by A7).**  The first smoke
   run failed A7 on exactly two channels: s1 ratio 2.19e+20 and s3 ratio
   1.21e+20, while sig (0.104) and s2 (3.0e-04) passed.  That parity
   signature IS the diagnosis: s1 = -(1/2)Im psi'(z) and s3 =
   (1/8)Im psi'''(z) are ODD in u, sig and s2 = (1/4)Re psi''(z) are
   EVEN, and conjugation of the ladder's w-powers (`1/w_bar`, `w_bar^2`
   -- two sign slips in the complex-tuple port of the validated mpmath
   prototype) flips exactly the odd channels and is invisible to the
   even ones.  Fix: `t1c = (x/m2, +y/m2)`, `w2i = -2xy` for
   `w = x - i y`.  After the fix the four ratios are 0.104 / 6.8e-05 /
   3.0e-04 / 1.2e-04 and the A10 window deviation collapses 6.7e-09 ->
   2.3e-02-vs-6e+08 (3.9e-11 of W).  Law: an interval implementation of
   an analytic chain must be validated on BOTH parities; a single
   even-channel check is a silent pass for a conjugated ladder.
2. **The gpp trailing-copy adaptation (pre-run, machinery note).**  At
   h = 0.0005 / 0.00025 the stencil slices run one past the fine-grid
   stencil's trailing edge copy; the probe passes `gpp` with two extra
   trailing copies (the `fine_grid` edge convention itself).  Bitwise
   safety for the old rungs is gated by P2 (rel 0.0 across all five
   fields), so the adaptation is measured, not argued.
3. **The smoke/full geometry discipline.**  The smoke run exercises a
   reduced geometry (dxi 0.002, ladder 0.02/0.004, a 41-panel arch
   window) and its "verdict" line is meaningless by construction (the
   arch window is a subset); its role is plumbing and the A7/A8/A10
   gates, which run full in smoke.  Smoke totals are never quoted.

## 7. Scope and nonclaims

- The verdict is a forward error bound on the L2 SIGNED-STRUCTURE float
  pipeline with stored floats as exact: the aggregate/rung charges are
  interval bounds, the L1 nodal charge is the 2052 committed-DAG
  calculus, the sigma channel is the new Taylor-3 enclosure; the same
  scope as records 2048-2054.
- The symplectic/pipeline error constant INS and the AMP amplification
  constants are the 2051/2052 committed ones; not re-derived here.
- The sigma-derivative tails carry SAFE = 8 margin over the elementary
  and Cauchy bounds (validation peak 0.93 pre-SAFE).
- The m = 1600 phi rule's own residual (the 2053 cross-read rel 4.3e-12
  against ideal) is not charged here.
- L4 stands (record 2053); L5 registered, not touched; COVER open;
  not a producer theorem; not RH.

Numbers, per-rung rows, gate booleans, bins, and reference checks are in
`results/2055_reduced_second.json`.