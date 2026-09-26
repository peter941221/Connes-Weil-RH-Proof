# Record 2014 - Route A: A-HD constrained health-maximization outcome

Date: 2026-09-26.

Status: outcome of the record-2011 desk, whose pre-registration was committed
before the run (`docs/proofs/2011_route_a_ahd_dual_desk_preregistration.md`).
One instrument amendment is filed with it, record 2014a. No theorem, no Lean
brick, no RH claim.

## 1. Verdict

```text
registered verdict   INSTRUMENT-FAIL   - carried entirely by the J1 anchor
                                        band on the C coordinate at G5-W
amended verdict      A-HD-MIXED        - after record 2014a, from the same
                                        checkpoint, no new rows
stage 2              NOT licensed      - the registered conditional gate
                                        (A-HD-GAIN) is not met
```

The desk therefore did **not** reach its registered gain bar, and the honest
one-line answer to the record-2004/2010 "Next" question is:

```text
the margin-increasing branch is NOT a law in the ordinate.  It is an
owner-specific phenomenon: at the four registered owners the attained gain
orders exactly as 1 / (2 + f) does, f = mm / A being the committed
cancellation order of record 2010 section 4.  At gamma_8 the branch does not
turn within the registered grid; at gamma_7 it turns immediately; the two
gamma_5 owners have no positive cone at all.
```

## 2. Instrument (record 2014a governs)

```text
owner   anchor dev C    anchor dev D    layer dev C,D   rows   identity   J4
G5-H    2.6206869e-03   2.2154470e-05   0.00e+00        28/28  pass       pass
G5-W    2.2424693e-02   4.8609087e-06   0.00e+00        28/28  pass       pass
G7-H    8.3109237e-04   2.0349000e-05   0.00e+00        28/28  pass       pass
G8-H    3.6785833e-04   3.2231142e-06   0.00e+00        28/28  pass       pass
```

`layer dev` is the deviation of the `sigma = 0` row from the committed
record-2006 cone anchor at the same `dxi = 0.008`: 0.00e+00 on C and on D, all
17 printed digits, at all four owners.  Off the anchors, the 48 grid cells
shared with the committed record-2006 cone artifact reproduce C, B01, D and det
to 0.00e+00 relative, with identical route-robust health verdicts.

```text
rows          112 registered rows (4 owners x (4 ranks x 7 amplitudes)), all
              certified on three routes (Ap and B present, so the spread is a
              two-route spread and not the record-1994 instrument law's
              degenerate floor), all with D < 0 (112/112, D >= 0 count is 0)
              at every owner
identity      record-1919 identity within its band on every row
J4            half-resolution re-read (dxi = 0.004) of each owner's maximiser:
              C sign unchanged and route-robust health verdict unchanged at
              4/4; relative C shifts 5.0e-04 .. 1.1e-03, relative D shifts
              4.8e-06 .. 2.2e-05
conditioning  cond <= 2.5e+04, pin errors <= 1e-6, visible-prime counts
              2393 / 1985 / 2393 / 1647 (unchanged from the committed owners)
```

## 3. The rule and its maximisers

Registered rule: `G(owner) = max C(rank, sigma) / C(0)` over certified rows with
`D < 0`.  Registered readings R1-R4 alongside.

```text
owner   f(0)       C(0)          D(0)            M(rank,sigma)  C(M)         G
G5-H    7.1963e+03  +1.490895e+00 -6.307521e+12  (6, 0.05)      -3.411330e+00  -2.288
G5-W    8.6087e+04  +2.501712e-01 -2.251368e+14  (6, 0.05)      -1.147614e+01  -45.873
G7-H    1.3280e+02  +1.731540e+02 -2.035961e+20  (4, 0.05)      +2.862982e+02  1.653
G8-H    5.1246e+01  +6.641075e+02 -1.111265e+20  (6, 1.60)      +9.361501e+03  14.096

owner   healthy(M)  R1 f(M)/f(0)  R2 |D(M)|/|D(0)|  R2 det(M)     R3
G5-H    false       -0.439         0.972            +2.090e+13    false (all ranks)
G5-W    false       -0.022         0.997            +2.575e+15    false (all ranks)
G7-H    true         0.676         1.605            -1.116e+23    false (all ranks)
G8-H    true         2.479         1.865            -1.953e+24    true at ranks 2, 4, 6
```

Two owners have a healthy maximiser.  At G5-H and G5-W every one of the 28
registered rows is unhealthy: the perturbation does not merely fail to improve
the margin, it destroys it (best available `C` is `-3.41` against a committed
`+1.49`, and `-11.48` against `+0.25`).

## 4. The finding: the gain orders as the conditioning does

```text
owner   f(0)       1/(2+f)     gain G     improving rows (of 28)
G5-W    8.6087e+04  1.1616e-05  -45.873     0
G5-H    7.1963e+03  1.3894e-04   -2.288     0
G7-H    1.3280e+02  7.4185e-03    1.653     2
G8-H    5.1246e+01  1.8781e-02   14.096    19
```

The two orderings agree exactly (four owners, rank correlation 1).  Read as a
reading and not as a law: `n = 4` and the interesting direction of the
hypothesis is untested - the registration chose these four owners because they
were the committed ones, not because they sampled `f`.  What the table does
establish is that the selector freedom is a *relief on the cancellation order*
and not a height effect: the two owners with the same ordinate (gamma_5) sit at
opposite ends of the gain table, and the two owners with different ordinates
(gamma_7, gamma_8) sit adjacent, both positive.

Three further readings on the branch.

```text
(a) no turn at gamma_8.  At G8-H the C ratio is monotone in sigma at ranks 2,
    4 and 6 and has not turned at the largest registered amplitude
    (sigma = 1.60, i.e. 1.6 times the H1 norm of the committed correction):
    5.726 (rank 2), 11.944 (rank 4), 14.096 (rank 6) at sigma = 1.60.  Rank 1
    is the collar and collapses at every amplitude (-132.8 at sigma = 1.60).
    The registered grid bounds the branch; it does not exhaust it.

(b) the obligation margin follows, sub-proportionally.  At the two healthy
    maximisers |D| also grows (1.605 at G7-H, 1.865 at G8-H) and det stays
    negative, so the C-improving branch does not degrade the binding
    obligation - it strengthens it, by less than it strengthens C.  At the
    two unhealthy owners |D| is flat (0.972, 0.997): D is nearly blind to the
    perturbation that kills C, which is the record-2010 conditioning
    asymmetry seen from the other side.

(c) R4, the registered response census.  corr(C response, |D| response) is
    -0.934 (G5-H), -0.774 (G5-W), -0.994 (G7-H), -0.991 (G8-H).  The pooled
    correlation is dominated by the sign structure of the C response (a
    |D| ratio is positive by construction while C ratios change sign), so it
    is reported as registered and (b) carries the reading: within the branch
    that improves C, |D| grows too, and the maximiser is not the row of
    largest |D| growth.
```

## 5. Resolution offsets: the measured constant behind record 2013's P1

The desk measures the same cells at `dxi = 0.008` and, on the maximisers, at
`dxi = 0.004` (J4).  With `A = C` and `f = mm / A` the mass split gives

```text
|Delta A| / |A|  <=  eps * (|mp| + |mm|) / |A|  =  eps * |2 + f|,
```

so the observed relative C offset between the two resolutions inverts to a
lower bound on the mass-level relative offset `eps`:

```text
owner   dev_C(anchor)  / |2+f|    dev_C(J4 max) / |2+f(M)|
G5-H    3.64e-07                  3.48e-07
G5-W    2.60e-07                  2.60e-07
G7-H    6.17e-06                  7.09e-06
G8-H    6.91e-06                  5.81e-06
```

The two columns agree per owner (to 5 percent at G7-H, 16 percent at G8-H):
the mass-level offset at half resolution is an owner property, between
`2.6e-07` and `7.0e-06`, and the C coordinate's exposure is that number times
`|2 + f|`.  This is the first measured value of the quantity record 2013's
`P1` has to bound.  In plain terms: at half resolution the C coordinate is
determined to between `3.7e-04` (G8-H) and `2.24e-02` (G5-W) relative, so the
worst owner sits a factor 45 from the cancellation wall - the point where the
offset reaches 1 and the sign of A is no longer determined - and it is that
owner whose anchor band the registration as written could not meet.  The
measured offsets also say why: `eps` does not degrade across the fibre (the two
columns agree), only `|2 + f|` does.

**Erratum on record 2013 section 2.**  That section writes
`|mp| + |mm| = (1 + f) * |A|` and requires `eps < 1 / (1 + f)`.  With the
committed definition `f = mm / A` and `A = mp - mm` the correct identity is
`|mp| + |mm| = |2 + f| * |A|`, so the requirement is `eps < 1 / |2 + f|`:
`1.3894e-04` (G5-H), `1.1616e-05` (G5-W), `7.4185e-03` (G7-H), `1.8781e-02`
(G8-H), against 2013's `1.3893e-04`, `1.1616e-05`, `7.5264e-03`, `1.9514e-02`.
The slip is a constant `1` inside the amplification factor, so no order, no
height ordering and no conclusion of 2013 changes; the table is corrected here
because record 2013 is a price list and its numbers are quoted.

## 6. What this does not license

```text
stage 2       not run.  The registered conditional gate is A-HD-GAIN; the
              amended verdict is A-HD-MIXED.  The health-window question of
              record 2011 section 5 - is the window a property of the
              committed point or of the owner - is therefore still OPEN, and
              is now the natural next registration (its gate must be set on
              the amended verdict shape before, not after, its run).
definability  record 2011 section 6 stands unchanged.  The maximiser is a grid
              argmax over a finite canonical set; no producer is licensed, and
              nothing here is promoted to a Lean artifact.
obligation    unchanged.  No gate sign is proved; D < 0 remains measured on
              the committed owner class and is not proved for any of them.
COVER         untouched.  This desk says nothing about hypothetical off-line
              zeros; the published record-2012 scans run on the committed
              selector, which this desk confirms is the binding selector at
              gamma_1..gamma_6 (no positive cone there means the selector
              freedom cannot be spent at those heights).
```

## 7. Artifacts

```text
results/2011_route_a_ahd_dual.json              registered verdict, 112 rows
results/2011_route_a_ahd_dual_amended.json      amended verdict, same rows
results/2011_route_a_ahd_dual_partial.json      measurement checkpoint
build-logs/2011_ahd_full.log                    measurement pass
build-logs/2011_ahd_reduce.log                  registered verdict pass
build-logs/2011_ahd_amended.log                 amended verdict pass
scripts/routea_ahd_dual_2011.py                 rig (--reduce, --amended-anchor)
```

Driver note, recorded because the artifacts must say how they were produced:
the measurement pass completed all four cases and checkpointed them, then the
verdict block raised a `TypeError` (a boolean treated as an iterable in the J4
aggregation).  The verdicts above were recomputed from the checkpoint by
`--reduce`; no row was re-measured and no threshold changed.  The checkpoint is
the measurement evidence.

## 8. Scope

Four owners, one `delta`, one family, one resolution for the grid and one
further resolution on four rows; a finite registered amplitude grid that bounds
but does not exhaust the branch.  Nothing here is a theorem.  RH is not
claimed.

See also: 1983 (the committed owner class), 1994/1994b/1996 (the layers),
2003/2004/2006/2010 (the cone layer this desk extends), 2005 (the F52
instrument law the routes here clear), 2011 (registration), 2013 (the price
list, corrected in section 5), 2014a (the anchor-gate amendment).