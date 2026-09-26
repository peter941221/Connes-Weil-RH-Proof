# Record 2018 - certified-evaluation layer: resolution-ladder outcome

Date: 2026-09-27.

Status: outcome of the record-2015 pre-registration.  Third record of the
evaluation-layer track (2013 priced it, 2015 registered the ladder, this is
the run).  No theorem, no Lean brick, no RH claim.

## 1. Verdict

```text
first pass, as run    INSTRUMENT-FAIL / AMP-SLACK / LADDER-BAND-OUT
second pass           LADDER-CONVERGED / AMP-SLACK / LADDER-BAND-OUT
                      (L1, L2 and all 16 row checks pass)

registered clauses     mass   eps strictly decreasing on both steps at 4/4
                              owners, sh <= 0.7 at 4/4 (bar: 3 owners);
                              no owner at sh >= 1, so no aliasing floor
                       amp    12/12 pairs with r <= 0.1 (bar: 10)
                       band   all four owners outside [lo, 100*lo]
```

The first pass failed its gate for an instrument reason that has nothing to do
with the numbers (section 4): the rig's L2 reference table carried
seven-significant-digit values while the registered bar is `1e-9`.  The second
pass, with the references read at full precision from the committed artifact,
reproduces the first pass **bit for bit** - 208 numeric fields over all 16
rows, worst relative difference exactly `0.0` - and passes the gate.  So the
reading below is the ladder's numbers, and the first pass's verdict is the
instrument's history, not a measurement.

## 2. The ladder

```text
owner   eps(0.008,0.004)  eps(0.004,0.002)  eps(0.002,0.001)   sh     order
G5-H    4.857707e-04      2.794747e-04      1.335018e-04      0.478   0.80
G5-W    7.541733e-04      4.429618e-04      7.205532e-05      0.163   0.77
G7-H    2.149266e-03      1.156932e-04      6.413413e-05      0.554   4.22
G8-H    1.868144e-03      3.936062e-04      6.759648e-05      0.172   2.25
```

`sh` is the registered shrinkage factor `eps(0.002,0.001)/eps(0.004,0.002)`;
`order` is the registered fitted order over the coarser pair.  With the finer
pair the fitted orders are `1.07, 2.62, 0.85, 2.54`.  The registered reading is
therefore exact: the offsets shrink on both steps at every owner (per-halving
factors `1.70` to `18.6`), and no owner shows the record-1985 shape
(`sh >= 1`) - the mass functional has **no aliasing floor in this range** at
these four owners, so the finest grid is a usable provisional limit under the
registered clause.

The fitted orders are widely scattered (0.77 to 4.22) and disagree between the
two steps at every owner.  That is the registered caveat doing its job: the
ladder shows convergence, not a power law, and a fitted order is not a bound.

## 3. The well-conditioned coordinates

`S1` registered `D` as the well-conditioned coordinate and the ladder as the
place where its convergence order becomes visible.  It is:

```text
owner   D offset 0.008 -> 0.004 -> 0.002   ratios per halving   order
G5-H    2.2154e-05  5.5879e-06  1.4000e-06   3.97, 3.99         1.99, 2.00
G5-W    4.8609e-06  1.2360e-06  3.1044e-07   3.93, 3.98         1.97, 1.99
G7-H    2.0349e-05  5.7223e-06  1.4698e-06   3.56, 3.89         1.83, 1.96
G8-H    3.2231e-06  7.1375e-07  1.7305e-07   4.52, 4.12         2.17, 2.04
```

`D` converges at order 2 at every owner, on both steps - the cleanest power
law in the whole record, and it is a statement about the coordinate the
binding obligation lives in, not the cancelled one.

Two further convergence signals, neither registered as a verdict but both
sharp:

```text
inter-route spread_C    2.8e-03 -> 1.7e-04 -> 1.1e-05 -> 6.8e-07   (G5-H)
                        2.4e-02 -> 1.5e-03 -> 9.4e-05 -> 5.9e-06   (G5-W)
                        8.9e-04 -> 5.5e-05 -> 3.8e-06 -> 3.2e-07   (G7-H)
                        3.9e-04 -> 2.4e-05 -> 1.5e-06 -> 1.0e-07   (G8-H)

ratios per halving      16.5, 15.5, 16.2 ... i.e. order 4 in dxi, exactly
                        the quadrature order of the committed route pair
                        (record 1959's instrument observation, now seen at
                        four new owners and three new resolutions)

record-1919 identity    3.0e-04 -> 1.5e-04 -> 7.6e-05 -> 3.8e-05  (G5-H)
residual (dev_var)      halving per refinement, order ~1, monotone at 4/4
```

So the three quantities separate cleanly: the *route* discrepancy is a
quadrature artefact (order 4), the *mass* drift is the measure-level quantity
(order 1..2 fitted), and `D` sits at order 2.  A `P1` constant anchored on
route agreement may use `dxi^4`; one anchored on the mass coordinate must use
the measured drift, and neither may be extrapolated as a law.

## 4. Errata and instrument

**(a) The L2 gate failure was a transcription, third occurrence of the class.**
As run, L2 failed at all four owners (`dev_C` 2.90e-07, 4.50e-08, 1.60e-07,
5.68e-08; `dev_D` 1.65e-09, 1.39e-07, 1.85e-07, 3.51e-07) against the
registered `1e-9` bar - and the failing values are exactly the half-ulps of
seven-significant-digit references (`1.494812e+00` cannot represent
`1.4948124334...` to better than `2.9e-07`).  With the four references read at
full precision from `results/2003_route_a_health_selector.json`
(`cases[].rows[0]`, the `sigma = 0` row the registration names), the check
gives `dev_C = dev_D = 0.00e+00` at all four owners **on the first pass's own
rows**, and `L1` (against the record-2011 anchors) already gave `0.0` as run.
The rig's table is corrected; the rule this project keeps re-learning is that
anchor tables are generated from committed artifacts, never typed from prose
or from memory - record 2016's K1 failure was the same defect, fixed in
record 2017, and this is its second recurrence.

**(b) Erratum on record 2014 section 5.**  That section tabulated
`dev_C / |2+f|` as "a lower bound on the mass-level relative offset eps" and
then read the four values (`3.64e-07, 2.60e-07, 6.17e-06, 6.91e-06`) as the
offset itself.  The ladder measures both factors separately and identifies the
table exactly:

```text
C offset  =  r * eps * |2 + f_fine|          (r as the registration defines it)
owner   C offset      r             eps           |2+f_fine|   product
G5-H    2.620687e-03  7.498317e-04  4.857707e-04  7194.8214    2.620687e-03
G5-W    2.242469e-02  3.456483e-04  7.541733e-04  86024.253    2.242469e-02
G7-H    8.310924e-04  2.862567e-03  2.149266e-03  135.0839     8.310924e-04
G8-H    3.678583e-04  3.691453e-03  1.868144e-03  53.3424      3.678583e-04

record 2014's four tabulated values, against the measured eps:
3.64e-07 / 4.86e-04 = 1/1334        (G5-H)
2.60e-07 / 7.54e-04 = 1/2901        (G5-W)
6.17e-06 / 2.15e-03 = 1/348         (G7-H)
6.91e-06 / 1.87e-03 = 1/270         (G8-H)
```

so record 2014's four numbers are `eps * r` - dividing each by the ladder's
`eps` returns the ladder's own `r` to three digits (`7.49e-04, 3.45e-04,
2.87e-03, 3.69e-03`) - and its own bound is `270x .. 2900x` loose: the
measured mass-level offset is `4.86e-04` to `2.15e-03`, and the attainment
factor is `r = 1.06e-05 .. 3.69e-03` (`AMP-SLACK`, all 12 pairs).  Every
inequality in record 2014 section 5 stands - the correction is to the
identification, not to the algebra - and a pointer is added there.  The error
propagated into record 2015's registered band check (`BAND_LO` was built from
those four values), which is why the band reads OUT at all four owners; a
pointer is added to the pre-registration as well, and the clause is left
exactly as registered.

**(c) What AMP-SLACK means.**  The record-2014 identity
`|Delta A| / |A| <= eps * |2+f|` is a valid bound and is nowhere near
attained: the C offset is 3 to 5 orders of magnitude below the worst case at
every one of the 12 pairs.  Consumers of `P1` may use the bound but not as an
equality, and the quantity `P1` must bound is `eps` - now measured, at these
owners - not `eps / |2+f|`.

## 5. What the ladder settles, and what it does not

```text
settles     the mass coordinate converges in dxi over 0.008 -> 0.001 at the
            four owners, at 1.7x to 18.6x per halving, with no aliasing floor
            in range (the record-1985 shape does not appear) - the first of
            the three inputs record 2013's P1 was priced against
settles     the shape of the second input: the amplification bound holds with
            3-5 orders of slack, and the constant P1 needs is eps, measured
does not    prove a bound.  A fitted order is not a truncation estimate at a
            fixed dxi, and the ladder is measured on the owner construction -
            it cannot show that a constant survives it
does not    measure eps or r at the comb's heights.  Record 2016 section 5's
            resolution caveat was priced with the factor 1 (assuming the worst
            case); the ladder shows the attainment is r <= 3.7e-3 here, so the
            caveat must be re-priced with eps and r measured at the committed
            layer's band edges (gamma_1/gamma_2), which is a registered
            follow-up next to the dxi = 0.002 re-read, not a result
```

## 6. Artifacts

```text
results/2015_resolution_ladder.json                     second pass, verdict
results/2015_resolution_ladder_run1_7digit_l2.json      first pass, as run
build-logs/2015_resolution_ladder.log                   first pass
build-logs/2015_resolution_ladder_run2.log              second pass
scripts/resolution_ladder_2015.py                       rig (L2 table
                                                        corrected after run 1)
```

Driver note: the first pass's artifact is kept under its own name because the
second pass overwrites the canonical path, and the two are the determinism
evidence: the second pass reproduces the first on 208 numeric fields (C, D,
det, B01, both spreads, W0, mp, mm, f, var_plus, var_minus, delta_mean) across
all 16 rows with worst relative difference `0.0`, and the derived pair table is
identical.  No cell, threshold or clause was changed between the passes: only
the reference table of L2.

## 7. Scope

Four owners, the cone layer (17-node owners, two-copy family, 34-element
basis), one delta (0.10), the `sigma = 0` row only, four resolutions
(`0.008, 0.004, 0.002, 0.001`), the committed selector.  This is a
measurement of the rig on the committed construction, not a theorem about the
operator.  No gate sign is proved, the binding obligation (`D < 0` on the
selected healthy owner) is untouched, the F2 gate of record 1997 stands, stage
2 of record 2011 is not licensed, and RH is not claimed.

See also: 1985 (the aliasing failure this ladder is built against), 2003/2004
(the L2 anchors), 2006 (the cone layer the machinery is imported from),
2011/2014/2014a (the owners, the two-point offsets, the amplification
identity, and the identification corrected in section 4), 2013 (`P1`), 2015
(the pre-registration), 2016/2017 (the COVER halves whose resolution caveat
section 5 re-prices).