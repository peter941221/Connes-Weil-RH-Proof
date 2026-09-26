# Record 2020 — COVER currency desk: the scale coordinate as exact prime-index, the comb as a fair sampler

Date: 2026-09-27.

Status: desk record for the direction-C pricing question left open by records
1998 and map 107.  Inputs are three labeled post-hoc diagnostics on
already-committed artifacts (record-1998 section 2 F-c pattern); no new cell
is measured, no gate sign is claimed, nothing is promoted, RH is not claimed.

Verdict in one block:

```text
scale coordinate     np(s) = #{n prime power : n <= exp(2 * s * m_pool)} —
                     an IDENTIFICATION (27/27 committed cells), so the visible
                     prime book is a pure function of (layer, height, scale)
                     and it moves with the height too (m_pool = 3.40 at
                     gamma_1 vs 3.80 at gamma_2..gamma_6, committed layer)
book steps           spacing 2.0e-3 (committed gamma_2-6), 3.4e-3 (gamma_1),
                     1.2e-4 (ext) in scale — 1-2 orders below the 0.01 grid
book step weight     a single crossing moves C by <= 0.574|C| (committed
                     gamma_1@0.88, 4 crossings per 0.01 cell, aggregate
                     <= 1.86|C|) and <= 0.0686|C| (ext gamma_7@0.92, 227
                     crossings per 0.01 cell, aggregate <= 10.6|C|)
flip rate at 0.01    pooled: C 80/171 = 0.468 against an independence
                     reference 2mu(1-mu) = 0.494; healthy 70/171 = 0.409
                     against 0.424; flat in h (0.01..0.04) -> COMB-WHITE
healthy measure      mu = 0.306 pooled over 180 certified cells at delta =
                     0.10 -> H = 1/mu = 3.27, per-height 1.64 .. 21.0
ruling               the 0.01 comb carries no interval currency at delta =
                     0.10 (record 2016's KNOT_COMPLEX is the run structure of
                     a near-white sequence); the measure currency H is
                     measured and, because the grid behaves as a fair
                     sampler, unbiased; direction C's debt is now named and
                     measurable (C1 registered below); nothing is promoted
```

## 1. What this desk is

Records 1998 put five attack directions on one price sheet and left direction
C (family-covering certificate with explicit Diophantine structure) as
`UNCHANGED / research-grade`, naming the obstruction as badly-approximable
gamma for the phase vectors `gamma*log p`.  Record 2016 then measured the
width law and returned `KNOT_COMPLEX`; record 2018 measured the quadrature
ladder and returned `LADDER-CONVERGED / BAND-OUT`; map 107 rules that A and D
are excluded and C is the shape that survives.  What none of these did is
quantify *why* the comb is knotty and *what a certificate would have to
control* on the scale axis.

This desk does that, with three post-hoc diagnostics over committed rows:

```text
results/2020_book_boundary.json      the visible book is an exact function
                                     of the scale (script cover_book_boundary_2020.py)
results/2020_book_step_weight.json   the weight of one book crossing
                                     (script cover_book_step_weight_2020.py)
results/2020_flip_rate.json          sign(C(s)) as a sequence along scale:
                                     flip rate vs distance, and the healthy
                                     measure (script cover_scale_fliprate_2020.py)
```

All three read only `results/2012_cover_scan_rows_width.json` and
`results/2012_cover_scan_rows_floor.json` and re-run the committed rig
machinery for reproducibility checks.  None of them measures a new cell.

## 2. The obligation and the currency question, stated once

In the committed vocabulary (records 1983/1994, map 104): a detector is a
one-parameter family of owner nodes read off at a scale `s`; its gates are
the moments `C`, `D`, `det` of one signed measure; the healthy face is
`C > 0 and D < 0 and det < 0`; the health screen for formal consumption is
`C > 0` (record 1931).  COVER's uniformity clause asks: for every
`delta > 0` and every `gamma`, there is a scale at which a healthy selected
detector exists — as an argument, not as a per-gamma computation.

The currency question is: *what kind of control over the scale coordinate
would such an argument need?*  Three candidate currencies:

```text
window currency    healthy sets contain intervals of width >= w_instr in
                   scale, so an argument may pick a scale and use
                   nearby scales' measured signs
measure currency   healthy sets have positive measure along scale, so an
                   argument may average / count without interval structure
point currency     healthy sets are isolated points ("crystals"), so the
                   argument must certify the sign at exactly its chosen
                   scale and nothing nearby
```

The diagnostics below separate these on the measured data.

## 3. The scale coordinate is an exact prime-index (identification)

The gate anatomy is committed and simple in outline
(`fourpoint_owner_density_1959.py:386-447`): the prime channel of a gate is
the sum over `prime_powers_up_to(exp(support_radius))` of
`2*Lambda(n)/sqrt(n)*cos(2*pi*xi*log n)` against the owner's spectral
weight, and the row builder sets `support_radius = 2 * max_width(family)`
(lines 618/733 with `n = 0`), while every family width is
`scale * pool_entry` (`fourpoint_rh_reach_probe_1983.py:118`).  Hence

```text
np(s) = #{n : n a prime power, n <= exp(2 * s * m_pool)}
        m_pool = max family width at s = 1 (a function of layer and gamma)
```

`cover_book_boundary_2020.py` recomputes this on the committed nodes and
compares with the measured `n_primes` of the committed rows: **27/27 match**
(9 slots x 3 scales), with the three distinct book sizes that occur:

```text
layer      slot(s)              m_pool   exp(2*m_pool)   np(0.80) np(0.90) np(1.00)
committed  gamma_1               3.40       897.85          64       106       178
committed  gamma_2 .. gamma_6    3.80      1998.20         103       182       332
ext        all three slots       5.40     49020.80         788      1985      5121
```

Three consequences, in order of weight:

1. Record 2017 section 3c measured that `n_primes` is a function of
   `(layer, height, scale)` alone, invariant under delta and dxi.  That is
   no longer an empirical invariance to be validated; it is an identity.
   The scale axis *is* the index of the visible prime book.
2. The book moves with the height as well: at the same scale the same layer
   shows 106 primes at `gamma_1` against 182 at `gamma_2` (both committed) —
   `m_pool` differs across heights because the family pool does.  A
   certificate uniform in gamma must control a book that is itself
   gamma-dependent.
3. The book's granularity is far below the measurement grid:

```text
slot group            prime powers per 0.005 scale at the window edge   step spacing
committed gamma_1     10                                                3.4e-3
committed gamma_2-6   19                                                2.0e-3
ext all               460                                               1.2e-4
```

## 4. The weight of one book crossing

When `s` crosses a boundary of the book, exactly one term
`delta_n = 2*Lambda(n)/sqrt(n) * What(log n)` enters (`What` = cosine
transform of the owner's spectral weight).  `cover_book_step_weight_2020.py`
rebuilds the route-B machinery at two committed cells and computes every
per-term weight against `|C|` (route B reproduces the committed-route value
to 1.8e-5 and 5.5e-5 relative, at the route-spread level):

```text
quantity                                committed gamma_1@0.88   ext gamma_7@0.92
|C|                                      6.0908e-01              1.7331e+02
|prime channel| / |C|                    3.9934e+04              1.0239e+02
all-term max / |C|                       3.3216e+04              4.4364e+01
all-term median / |C|                    4.8343e+00              8.8303e-02
crossings inside one 0.01 scale cell     4                       227
single crossing, max / |C|               5.7373e-01              6.8600e-02
crossings sum / |C|                      1.8606e+00              1.0598e+01
```

Reading:

- `C` is a **residual**: the prime channel cancels the archimedean channel
  to 4.5 orders (committed) / 1.6 orders (ext) before `C` is what is left.
  Sign statements about `C` are statements about a near-cancellation.
- The book's largest terms are the **lowest** primes (the largest single
  term, `n = 3`, is 83 per cent of the whole prime channel at the committed
  cell) and they never enter or leave inside the measured window.  The terms that *step*
  during a scale crossing are the **boundary** primes near
  `exp(2*s*m_pool)`, and those are the ones this table scores.
- In the committed layer a **single** crossing can move `C` by up to
  0.574|C|, and the four crossings inside one 0.01 cell can sum to up to
  1.86|C| — enough to traverse the sign of `C` strictly inside a grid cell.
  In the ext layer single crossings are small (0.0686|C|) but there are 227
  of them per cell, aggregating to up to 10.6|C|.
- Therefore: a claim about the sign of `C` **at one scale** is book-exact and
  finite (the book at that scale has exactly `np(s)` terms).  A claim about
  an **interval** of scales must carry the crossing terms, and the measured
  crossing budget says the interval's sign is not inherited from its
  endpoints.

## 5. The comb as a sampler: flip rate and healthy measure

`cover_scale_fliprate_2020.py` treats `sign(C(s))` and the healthy indicator
`C>0 and D<0 and det<0` (face `WIRE1`) as sequences along the committed
`delta = 0.10` grids and counts how often two certified cells at scale
distance `h` disagree.  Certified = face is not `INSTRUMENT`; 180 certified
cells (6 committed slots x 21, 3 ext slots x 18).

```text
h      C-sign flip         healthy flip        (pooled, certified pairs)
0.01   80/171 = 0.468      70/171 = 0.409
0.02   72/162 = 0.444      67/162 = 0.414
0.03   52/153 = 0.340      44/153 = 0.288
0.04   69/144 = 0.479      65/144 = 0.451

independence reference 2*mu*(1-mu):   C 0.494,  healthy 0.424

cross-instrument check (five-point floor grid, h = 0.02, disjoint pairs):
      C 14/32 = 0.438,  healthy 15/32 = 0.469

ratio R(0.02)/R(0.01):   C 0.950,  healthy 1.010   ->  COMB-WHITE
```

A smooth comb with isolated zero crossings has `R(h)` proportional to `h`
for small `h`; a white sequence has `R(h)` flat at `2*mu*(1-mu)`; an
alternation with period near 0.02 has `R(0.02)/R(0.01)` near 0.  The pooled
data is **flat at the independence value**, cross-checked on the independent
floor grid.  So at `delta = 0.10` and the 0.01 grid:

1. The sign sequence carries no dominant interval structure.  Record 2016's
   `KNOT_COMPLEX` is thereby *explained*: the "multiple narrow bands" are
   runs in a near-white sequence, with the fine structure living at the book
   crossing scale (section 3), below the grid.
2. Because the grid behaves like an unbiased sampler, the measured healthy
   fraction is an estimate of the healthy *measure*:

```text
slot                certified cells   healthy (WIRE1)   mu_H     H = 1/mu_H
committed gamma_1        21                 7          0.333       3.00
committed gamma_2        21                 5          0.238       4.20
committed gamma_3        21                 9          0.429       2.33
committed gamma_4        21                10          0.476       2.10
committed gamma_5        21                 4          0.190       5.25
committed gamma_6        21                 1          0.048      21.00
ext gamma_5              18                11          0.611       1.64
ext gamma_7              18                 3          0.167       6.00
ext gamma_8              18                 5          0.278       3.60
pooled                  180                55          0.306       3.27
```

3. Per-slot, the flip classes are heterogeneous, and the sample sizes are
   small (16-19 pairs per stride, so a single-slot ratio carries roughly
   0.2-0.3 of noise): `gamma_1` and `gamma_2` read `COMB-SMOOTH`
   (R(0.02)/R(0.01) of 1.75/1.89 and 1.68/1.05 on the two indicators),
   `gamma_4`, `gamma_5` (both layers) read `COMB-ALTERNATING`
   (ratios 0.53-0.65), the rest read `COMB-WHITE`.  The **pooled** class is
   the ruling; the per-slot classes are a reported spread, not findings.

4. Contrast with the dxi axis (M1 smoke, records 2019): at fixed scale, the
   dxi = 0.002 re-read of the four smoke cells reproduced signs with 0
   flips, `r = 1.2e-06 .. 3.7e-05` of the amplification budget
   (`RP-COMPLETE`).  The sign of `C` is a *scale* fact, not a *quadrature*
   fact; refining dxi cannot substitute for sampling more scales.

## 6. Pricing direction C against these measurements

What a direction-C certificate must produce, in this vocabulary:

```text
given (delta, gamma): exhibit s = s(delta, gamma) and certify
    C(delta, gamma, s) > 0,  D < 0,  det < 0
uniformly in gamma — an argument, not a per-gamma computation.
```

The ingredients it must control, each now measured:

```text
(a) the owner family's motion in (gamma, s): nodes and widths — smooth;
    no continuity in gamma is measured anywhere in this layer's history

(b) the book at the chosen s: EXACT (section 3) — np(s) terms, finite,
    computable; so a pointwise certificate needs no book error term

(c) the residual itself: a cancellation of 4.5 orders (committed) /
    1.6 orders (ext) happens before C is defined, so certifying the sign
    of C at a point is a cancellation-level statement (section 4)

(d) interval claims: dead at the 0.01 grid — the crossing budget (section 4)
    says an interval's sign is not inherited from its endpoints, and the
    flip rate (section 5) says the sign sequence is white at that grid
```

Where the F-d cost lands (record 426's shape): a certificate that freezes a
finite family of rationally independent frequencies and controls a sum over
phases must pay a small-denominator exponent `omega >= n` for `n`
independent frequencies; the committed gate's frequency set at scale `s` has
exactly `np(s)` elements, each the log of a prime power.  So in this
normalization the barrier's `n` equals the book size at the hitting scale
(64..332 committed, 788..5121 ext over the measured window).  The certificate
cannot be a fixed-family small-denominator statement; it must be a statement
about a moving, exactly-known family — smooth motion of the owner spectral
weight and the archimedean channel against a book whose membership is a
step function of `(gamma, s)`.

The currency that remains after the measurements:

```text
window currency    none measured: at delta = 0.10 no interval structure at
                   the 0.01 grid (COMB-WHITE); intervals, if any, are
                   narrower than 0.01 and the crossing budget keeps them
                   plausible below that (C1 tests this directly)

measure currency   measured: mu = 0.306 pooled (H = 3.27), per-height
                   1.64..21.0; the grid's white behavior makes these
                   unbiased estimates at the grid scale

point currency     the operative one: book-exact pointwise certification is
                   finite and exact; the cost is the cancellation level of
                   (c) plus the gamma-uniformity of (a)
```

This does not discharge the F-d cost law — it locates it.  A certificate on
this route pays in (i) cancellation-depth bookkeeping (measured: 4.5 orders),
(ii) the gamma-uniform motion of the family and the book (unmeasured), and
(iii) the ubiquity input that makes it RH-equivalent (unchanged).

## 7. What changes in routing

```text
+---+----------------------+---------------------------------------------+
| A | window-track theorem | stays excluded; the window currency is now  |
|   |                      | measured as absent at the 0.01 grid         |
+---+----------------------+---------------------------------------------+
| C | family-covering      | stays research-grade, but its debt is now   |
|   | certificate          | named, split into measurable pieces, and    |
|   |                      | the scale side is registered as C1 below    |
+---+----------------------+---------------------------------------------+
| E | total positivity     | unchanged (no new evidence)                 |
+---+----------------------+---------------------------------------------+
```

Nothing is promoted.  The producer-side binding obligation (`D < 0` on the
selected healthy owner) is untouched, and the F2 gate of record 1997 stands:
no COVER mechanism may be promoted while the producer's own margin is open.

Consolidation note (so it is not registered twice): the three axes of the
uniformity question now have owners — dxi refinement is M1 (record 2016
section 5, running as record 2019 phase `edges`), the delta density is M2
(record 2017 section 5, running as record 2019 phase `floor2`), and the
scale-side fine structure is C1 below.  No second registration is created
for the delta or dxi sides.

## 8. Registered follow-up C1 (scale ladder)

Registered here, to be pre-registered and run as its own record:

```text
object      the scale-resolution ladder of the healthy set on three slots
            (committed gamma_1, committed gamma_4, ext gamma_5), contiguous
            sub-window scale in [0.86, 0.96], grids step 0.005 (21 cells)
            and step 0.002 (51 cells) per slot; delta = 0.10; dxi = 0.004;
            216 cells total

derived     R(h) for h = 0.002, 0.005, 0.01 (strides) on the two
            indicators; mu_H(h) per grid; the ladder of H(h)

verdicts    SAMPLER-ALL-RESOLUTIONS   R(h) within 3 sigma of 2*mu(1-mu) at
                                      every h, and mu_H(0.002) within 3
                                      sigma of mu_H(0.01)  ->  measure
                                      currency is resolution-independent
            WINDOW-LADDER             R falling like h at the finest h, or
                                      mu_H rising with resolution  ->
                                      windows wider than 0.002 exist
            ALTERNATING-LADDER        R(0.002) above R(0.01)  ->  the
                                      oscillatory slots' period is visible
            INSTRUMENT-FAIL           anchors / A3 / np mismatch as in 2019

cost        the 0.002 cells are the expensive ones: ~90-150 min heavy
```

C1 is the direct test of the fair-sampler reading of section 5 at a
resolution where the committed layer has 1-2 book crossings per cell
(0.002 against a 2.0e-3 step spacing) — i.e. the coarsest ladder on which
the crossing mechanism is individually resolvable.

## 9. Scope and honesty

- Everything here is empirical, about committed artifacts and the committed
  rig; the three diagnostics are labeled post-hoc (record-1998 section 2
  F-c pattern) and are reproducibility checks, not proofs.
- The identification in section 3 is exact *of the committed code path*
  (support radius = 2 * max width, n = 0 in these runs); it is a statement
  about the rig's book, not about the mathematics of the explicit formula.
- No theorem, no Lean brick, no gate sign, no promotion, no RH claim.

See also: 1998 (priced directions), 426 (small-denominator barrier),
2014/2015 (AHD dual outcome; amplification identity), 2016 (width law,
KNOT_COMPLEX), 2017 (delta floor), 2018 (quadrature ladder), 2019
(registered M1/M2), map 107 (COVER measured state), 1931 (health screen).