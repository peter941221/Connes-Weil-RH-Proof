# 2046 — Route A interval chain, link L2, second architecture (quadrature by parts): IBP-L2-FAIL, and the model-based architecture registered as the next reopen

Verdict: **IBP-L2-FAIL**.  The quadrature-by-parts architecture for the
record-2041 link L2 dies on the one-copy G8-H owner: the preregistered
width law is CONFIRMED as a law and its input is measured 1826x over
budget.

```
book_width_ibp = 2 * TV2 * B2,  B2 = sum_k 2 Lambda(k)/sqrt(k) / omega_k^2
              = 2 * (2.5264e22) * (0.361486) = 1.8265e22
required TV2: 1e19 / (2 B2) = 1.3832e19   measured TV2 = 2.5264e22
overrun: 1826x budget (1e19);  164x abs(Q);  165x the hard bar 1.11e20.
```

The IBP trade is also strictly DOMINATED on this owner: at the finest
direct grid (dxi = 0.01, record 2043) the direct enclosure total is
3.5062e21, 5.2x TIGHTER than the IBP total, and IBP is dxi-independent
while the direct charge is linear in dxi - IBP only "wins" for grids
coarser than ~0.052, where it still fails by two orders of magnitude.
The one-IBP variant is no better (2 B1 TV1 = 1.4225e22): the
derivative-order trade has SATURATED, the second integration by parts
is 1.28x worse than the first because TV2/TV1 ~ 38 rad/unit cancels
the B1/B2 gain.

The run then produced a second, more useful finding - priced here in
section 4 and REGISTERED as the next reopen: the panel-local
MODEL-based architecture (interpolate g on each panel, integrate the
model against cos in closed form, bound only the remainder) has a
different charge law, (h^2/4) * C_book * TV2 with C_book =
sum_k 2 Lambda(k)/sqrt(k) = 458.05, which is viable at h ~ 0.001
(~80k panels, 0.29x budget) under the crude L1 remainder bound.

Owner and instrument are the committed record-2037 state; verdict
rules were frozen in the rig header before the run (the anchor design
was repaired mid-run - section 5).  Artifact:
`results/2046_interval_kernel_ibp.json`.  Rig:
`scripts/routea_interval_kernel_ibp_2046.py` (WSL ext4 mirror, mpmath
iv dps 20).

## 1. Readings

Direct-architecture ladder (reproduces record 2043 exactly; the A1
anchor):

```
+--------+--------+------------+------------------+-----------------+
|  dxi   | panels | width_mean | proj_total       | proj_arch       |
+--------+--------+------------+------------------+-----------------+
| 0.05   |  1600  |  569.0868  | 1.5411483e22     | 3.91707e16      |
| 0.02   |  4000  |  254.6580  | 6.8983784e21     | 1.56664e16      |
+--------+--------+------------+------------------+-----------------+
```

A1: width_mean(0.05) = 569.0868 vs the committed record-2043 569.087
(relative 4e-7).  A1b: the linear ratio 254.6580/569.0868 = 0.4475 =
0.4 +- 12%.  Sigma containment 4/4 (u = 0, 2 pi, 20 pi, 80 pi).

IBP channel (fine grid dxi = 0.01, 8001 points, int g = 2.7091e19):

```
+--------+---------------+--------------+-------------------+---------+
|  dxi   | TV1           | TV2          | book_width_ibp    | /budget |
+--------+---------------+--------------+-------------------+---------+
| 0.05   | 9.01279e20    | 3.45325e22   | 2.49660e22        |  2497x  |
| 0.02   | 7.38670e20    | 2.84956e22   | 2.06015e22        |  2060x  |
| 0.01   | 6.59258e20    | 2.52637e22   | 1.82650e22        |  1826x  |
+--------+---------------+--------------+-------------------+---------+
```

Constants: S1 = sum_k 2 Lambda(k)/sqrt(k) omega_k = 21898.86
(2043's measured effective slope 12943 is (2/pi) S1 = 13940 up to the
clipping corrections - consistent cross-read); B1 = 10.7883;
B2 = 0.361486.  TV1/g = 24.3 and TV2/g = 932 - with TV2/TV1 ~ 38
rad/unit, the owner's own oscillation scale (not a single k).

## 2. Why it dies

The bound architecture is exact: two integrations by parts telescope
the book's boundary terms to the two line endpoints (pointwise), and
the remainder is charged by the bounded-variation envelope
|int g'' cos| <= int |g''| <= TV2 per term, giving per-term width
2 (1/omega_k^2) TV2.  The charge is dxi-INDEPENDENT (the panel count
decouples from the budget) - that was the point of the architecture -
but the measured input destroys it: g is NOT smooth at the scale the
trade needs.  The trade pays omega_k^{-2} per term to remove the
oscillation, but the derivative charge TV2 = int |g''| carries the same
g-oscillation back at full strength: TV2/g = 932.

Domination, in one line: charge_IBP = 2 B2 TV2 (flat in h) vs
charge_direct = S1_eff h int g (linear in h); crossover
h* = 2 B2 TV2 / (1.2943e4 * int g) = 0.0521.  Below h* - i.e. on
every grid that could matter - the direct architecture is tighter, and
at the finest registered grid it is 5.2x tighter.

## 3. The derivative-order trade saturated

One integration by parts (charge 2 B1 TV1 with B1 = sum c_k/omega_k)
gives 1.4225e22 - BETTER than two integrations by parts (1.8265e22)
by 1.28x.  The gain factor per IBP is (B_{n}/B_{n-1}) * (TV_{n-1}/TV_n)
~ (1/38) * (38) ~ 1: on this owner the oscillation scale makes the
per-term omega^{-1} reduction and the derivative blow-up cancel
exactly at first order, and the second order is already negative.
Any n-IBP architecture is dead here for the same reason.

## 4. Registered next reopen: panel-local model architecture (unpriced)

Replace the IBP remainder by an interpolation remainder.  Per panel of
width h:

```
g = g_lin + r,   g_lin = linear interpolant at the panel endpoints,
                 r(a) = r(b) = 0,  |r| <= (h^2/8) sup_panel |g''|;
int g cos = int g_lin cos  +  int r cos
model part: CLOSED FORM, no oscillation width (pointwise endpoint
            sin/cos and endpoint values of g with ulp-scale enclosures);
remainder:  |int r cos| <= int |r| <= (h^3/8) sup_panel |g''|
            (CRUDE L1 bound: it does NOT use the omega_k oscillation).
Summed over the book:  book_width_model = (h^2/4) C_book TV2,
            C_book = sum_k 2 Lambda(k)/sqrt(k) = 458.05.
```

Measured input TV2 = 2.5264e22 gives the analytic estimate ladder:

```
+--------+------------------+---------+--------------------+
|   h    | book_width_model | /budget | verdict zone       |
+--------+------------------+---------+--------------------+
| 0.01   | 2.893e20         |  28.9x  | FAIL zone          |
| 0.005  | 7.232e19         |   7.2x  | GRAY zone          |
| 0.002  | 1.157e19         |   1.16x | GRAY (marginal)    |
| 0.001  | 2.893e18         |   0.29x | VIABLE by estimate |
| 0.0005 | 7.232e17         |   0.07x | VIABLE by estimate |
+--------+------------------+---------+--------------------+
```

So the model architecture is the FIRST L2 design whose charge lands
below the 1e19 budget: ~80k panels at h = 0.001 with a 3.46x margin
(viable threshold h <= 1.86e-3, ~43k panels at 1.0x).  Why it works:
the model part uses g's smoothness at panel scale instead of fighting
the book oscillation; the crude L1 remainder pays only h^2 with the
large but h-free constant C_book (no omega-weighting at all).

Caveats that make this a REGISTRATION, not a result: (i) the estimate
uses the float-stencil TV2 and the crude L1 bound; a probe must
measure the model path's actual enclosure widths (endpoint enclosures
of g = link L1, enclosed sup|g''| = link L3, the closed-form model
part's own interval widths, and the archimedean part - all small by
estimate but unmeasured); (ii) the crude bound beats IBP over the
whole relevant range (crossover in charge at h* = sqrt(8 B2/C_book) =
0.0795), so any future probe must price the crude form, NOT the IBP
form; (iii) higher-order panels (quadratic models: h^3 * C_book *
TV3-type charges) exist as a ladder but need TV3+ measurements and
are NOT priced here.  None of this touches L1/L3/L4; the L3 coupling
(enclosed sup|g''| at the panel scale) is the shared cost.

## 5. Instrument notes (anchor design repaired mid-run; the verdict quantity was never affected)

The first full run returned ANCHOR-FAIL, and the failure was the
ANCHOR DESIGN, not the rig - three successive iterations, each
diagnosed by a scaling law rather than by loosening:

1. Same-grid float-vs-float book comparison at h = 0.01, gate 1e-6:
   measured 1.148e-4.  Diagnosis: both sides carry the O(h^2) grid
   error (the real-g ladder 1.74e-4 / 4.34e-5 / 1.08e-5 at
   h = 0.01/0.005/0.0025 has ratios 4.003/4.001).  A same-grid
   float comparison cannot anchor a derivative-order trade.
2. Trigonometric surrogate, analytic derivatives, code path at
   h = 1e-5, gate 1e-8: measured 1.059e-7.  Diagnosis: the trapezoid
   floor of the remainder integral, amplified by omega^2/omega^2.
3. Closed-form (no quadrature) identity check, gate 1e-12: measured
   1.511e-12.  Diagnosis: double-precision evaluation floor with mild
   cancellation at |mu - omega| ~ 0.35 (the identically-zero
   difference of terms of magnitude ~4).  Fixed by a per-k float
   budget: |residual| <= 1e-12 * (|b/omega| + |(mu^2/omega^2) I_k| +
   |I_k|) - measured slack 7.55e-13.

Final anchor set (all green in the artifact): A1 (reproduces 2043),
A1b (linearity 0.4475), A2a closed-form (1.511e-12 rel, 7.55e-13
slack), A2a code-path (1.059e-7 at h = 1e-5, gate 1e-6), A2b (h^2
scaling ratios 4.003/4.001, finest 1.08e-5), sigma 4/4.  The identity
itself was also verified by hand in the record-2046 preparation
(product-to-sum both sides); the closed-form check is its float echo.

## 6. Scope and non-claims

- Verdict covers the one-copy G8-H owner, the registered grids, and
  the IBP charge family (bounded-variation remainder).  It does NOT
  declare the L2 family dead: the model-based architecture of section
  4 is registered, estimated viable, and UNPRICED.
- TV1/TV2 come from float stencils of the committed 2037 pipeline:
  width BUDGET pricing only.  Enclosed sup|g''| (L3) and endpoint
  enclosures of g (L1) are not counted anywhere.
- The section-4 ladder is an ANALYTIC estimate from the measured TV2,
  not a probe result.
- No full-line tail (L4), no coefficient enclosure, no Lean.  Not a
  producer theorem.  Not RH.  Route A's binding status is unchanged
  (2038 no-go; link L2 architectures now: direct MEASURED DEAD (2043),
  IBP MEASURED DEAD (this record), model-based REGISTERED UNPRICED).