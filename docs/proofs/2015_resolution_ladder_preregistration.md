# Record 2015 - certified-evaluation layer: the resolution-convergence ladder (pre-registration)

Date: 2026-09-26.

Status: pre-registration. Committed before the run. No theorem, no Lean brick,
and no RH claim.

## 1. Why this ladder

Record 2013 priced the certified-evaluation layer and named its root brick:

```text
P1  an explicit bound on | <g, K W_rig> - <g, K W_true> | for the functionals
    actually used, with the constant carried through the committed owner
    construction.  Its three consumers are the D interval certificate, the F2
    tail measurement and the health-witness certification.
```

Record 1985 is why `P1` exists: `D` was replicated to 12 stable digits while
`cert_ok` stayed FALSE, because the `dxi` ladder could not distinguish a
converged value from the quadrature aliasing floor of `W` (an arithmetic dreg
of `~1e-18` rather than a convergence signal).  A bound is not needed to *see*
that; it is needed to *consume* a number exactly, and the first thing any
bound must be anchored on is the measured behaviour of the rig as `dxi`
decreases.

Record 2014 section 5 measured that behaviour at exactly two resolutions and
found the amplification law that connects the well-conditioned and the
cancelled coordinates:

```text
|Delta A| / |A|  <=  eps * |2 + f|,      A = C,  f = mm / A,
```

with `eps` (the mass-level relative offset at `dxi = 0.008`) at least
`2.60e-07` (G5-W), `3.64e-07` (G5-H), `6.17e-06` (G7-H), `6.91e-06` (G8-H).
Two points cannot separate a power law from a floor, and the identity itself
was tested on four owners at one resolution pair.  This ladder tests both.

## 2. Registered objects

```text
owners        the record-2011 owners, cone layer (17-node EXT owners,
              two-copy 0.75a / 1.0a family), committed selector:
                G5-H  delta 0.10, gamma_5,  sc 0.92
                G5-W  delta 0.10, gamma_5,  sc 0.90
                G7-H  delta 0.10, gamma_7,  sc 0.92
                G8-H  delta 0.10, gamma_8,  sc 0.88
rows          sigma = 0 (rank 0) only, one row per (owner, dxi):
                dxi in {0.008, 0.004, 0.002, 0.001}   ->  4 x 4 = 16 rows
gate settings k = 30, xi_max = 40, n = 0; the owner layer, family, amplitude
              construction and readout are imported from
              `routea_health_cone_2006` (same import discipline as record 2011,
              so no second copy of the machinery can drift)
readout       C, B01, D, det, the three certified-route spreads, route list,
              n_primes, pin errors, cond, W0, tail beyond |xi| > 4, total mass,
              and the record-1919 mass split mp, mm, A, f, xp, xm, var_pm,
              delta_mean with its identity deviations
```

`dxi = 0.001` gives 80001 grid points, i.e. eight times the committed
`0.008` grid; the ladder is priced at about twenty minutes of wall time and is
run in one pass.

## 3. Registered derived quantities

```text
reference        the finest grid (dxi = 0.001) is the PROVISIONAL reference.
                 The ladder does not assume it is converged: section 4 makes
                 its convergence a gated reading.

eps(owner, pair) the mass-level offset between two grids of the same owner,
                 eps = max( |mp_1 - mp_2| / |mp_2| , |mm_1 - mm_2| / |mm_2| ),
                 the second grid being the finer one

C offset         the same definition applied to C, reported alongside

amplification    r(owner, pair) = (C offset) / ( eps * |2 + f_reference| ),
                 the fraction of the record-2014 worst-case amplification
                 |2 + f| that the pair actually attains

order            p(owner) = log( eps(0.008, 0.004) / eps(0.004, 0.002) )
                 / log(2), reported with the same ratio for the finer pair,
                 eps(0.004, 0.002) / eps(0.002, 0.001), as the shrinkage
                 factor sh(owner)
```

## 4. Registered instrument checks

```text
L1  the dxi = 0.008 rows equal the committed record-2011 anchors - which
    record 2014 section 2 established are bit-identical to the committed
    record-2006 cone anchors - to <= 1e-9 relative on C and on D.  Both this
    ladder and record 2011 read the same checkpoint of the same machinery, so
    the registered requirement is equality, not a band.
L2  the dxi = 0.004 rows equal the record-2004 anchors of
    results/2003_route_a_health_selector.json (cases[].rows[0], measured at
    dxi = 0.004 on the same 17-node layer and the same 34-element basis) to
    <= 1e-9 relative on C and on D.  That file's own reference_dev against
    results/1994b_ext_convention_control.json is 0.0 on C and 6.2e-16 on D, so
    the check is against a committed cell two records deep, not against a
    rerun of this ladder.
L3  every row certified on three routes with the two no-interpolation routes
    present (so the spread is not the record-1994 instrument law's degenerate
    single-route floor), pin errors <= 1e-6, cond <= 1e8, density finite,
    and the record-1919 identity within its band.
L4  the record-1919 mass readout is present and finite on all 16 rows; a row
    whose mass split is unavailable is a failed row, not a missing reading.
```

## 5. Registered decision rules

Mass-convergence verdict (gated by L1-L4):

```text
LADDER-CONVERGED   eps(0.008, 0.004) > eps(0.004, 0.002) > eps(0.002, 0.001)
                   and sh(owner) <= 0.7 at three or more owners
                   <=>  the mass coordinate keeps shrinking at least like
                   dxi^0.5 and the finest grid is a usable provisional limit
LADDER-FLOOR       sh(owner) >= 1.0 at two or more owners, i.e. the offset
                   stops shrinking between the two finest grids - the
                   record-1985 aliasing shape, which would mean the rig's mass
                   functional has a floor no refinement in this range removes
LADDER-MIXED       otherwise
```

Amplification verdict (the record-2014 identity, tested on 12 pairs):

```text
AMP-ATTAINED   r >= 0.5 at eight or more of the twelve (owner, pair) pairs:
               the worst-case factor |2 + f| is attained to within a factor
               two, so no consumer of P1 may use a smaller amplification
AMP-SLACK      r <= 0.1 at ten or more of the twelve: the bound is loose by
               more than an order of magnitude and the offsets are
               sign-cancelling rather than aligned
AMP-MIXED      otherwise
```

Band check against record 2014 section 5 (reported, not gating its verdicts):

```text
each owner's eps(0.008, 0.004) must be >= the record-2014 lower bound for that
owner and <= 100 times it; all four within the band is reported as
LADDER-BAND-CONFIRMED, and any owner outside it is reported with its value
```

Correction (record 2018 section 4, added after the run, clause left as
registered): the four `lo` values are `eps * r`, not `eps`.  Record 2014
section 5 tabulated the inverted lower bound `dev_C / |2+f|`, and this ladder
measures the attainment factor separately (`r` in `1e-4 .. 4e-3`, the
registered `AMP-SLACK` clause).  The band therefore reads OUT at all four
owners, and that reading is an instrument fact about the band's construction,
not a measurement of the mass coordinate.

Registered secondary readings:

```text
S1  the C offset and the D offset per pair, next to eps: D is the
    well-conditioned coordinate and the ladder is where its convergence order
    becomes visible
S2  p(owner) and sh(owner): the fitted order, with the caveat that a fitted
    power law is not a bound
S3  n_primes and the route set per row: the grid refinement does not move the
    visible-prime set, so all four rows of an owner must carry the same
    n_primes; a difference is an instrument failure, not a reading
S4  the record-1919 identity deviations per row, which are the only
    independent check that the grid still represents ONE signed measure at the
    finest resolution
```

## 6. What this ladder does and does not settle

It settles, on committed owners and committed machinery, whether the rig's
mass functional converges in `dxi` in the measured range, at what order, and
whether the record-2014 amplification identity holds as a bound and how
tightly.  Those are the three inputs `P1` needs to carry a constant.

It does not prove a bound.  A fitted order is not an estimate of the
truncation error at a fixed `dxi`, and this ladder does not touch the second
half of `P1` - the part where the constant must survive the committed owner
construction (kill pools, widths, pins) rather than being measured on it.

## 7. Scope

Four owners, one `delta`, one family, four resolutions, the `sigma = 0` row
only.  No gate sign is proved, the binding obligation (`D < 0` on the selected
healthy owner) is untouched, the F2 gate of record 1997 stands, stage 2 of
record 2011 is not licensed, and RH is not claimed.

## 8. Artifacts

```text
scripts/resolution_ladder_2015.py
results/2015_resolution_ladder.json
results/2015_resolution_ladder_partial.json
```

See also: 1985 (the aliasing failure this ladder is built against), 1994b (the
committed cell L2 anchors on), 2003/2004 (the anchors), 2006 (the cone layer
the machinery is imported from), 2011/2014/2014a (the owners, the measured
two-point offsets, and the amplification identity), 2013 (`P1`).