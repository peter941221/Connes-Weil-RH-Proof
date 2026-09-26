# Record 2011 - Route A: A-HD constrained health-maximization desk (pre-registration)

Date: 2026-09-26.

Status: pre-registration. Committed before the run. No theorem, no Lean
brick, and no RH claim.

## 1. Why this desk

Records 2003/2004 and 2010 leave two facts standing next to each other.

```text
(1) the committed selector is not health-extremal. Record 2004 found a fibre
    direction at G8-H along which the health margin increases monotonically,
    C = 664.35 -> 2128.7 (factor 3.20) with D < 0 and det < 0 certified at
    every registered amplitude; record 2010 found the same branch at ranks
    2, 4, 6 with factors 3.20 / 4.26 / 4.04 at sigma = 0.80.

(2) the health witness is a cancelled quantity. Record 2010 section 4: the
    committed A is the residual of a cancellation of order f = mm / A, with
    f = 7196 (G5-H), 86087 (G5-W), 133 (G7-H), 51 (G8-H); the obligation
    D < 0 is certified-route stable to <= 6.0e-04 while the witness C > 0
    carries a certified-route spread up to 6.9e-02.
```

Together they say that certifying `C > 0` at an arbitrary committed point needs
a relative accuracy of order `1 / f`, and that the fibre contains points where
that demand is smaller. The honest form of the health question is therefore a
constrained design problem:

```text
maximise C(d) over the feasible fibre, subject to D(d) < 0,
```

not the certification of a point that was chosen without regard to either
quantity.

An unregistered post-hoc read of the committed record-2010 artifact
(`results/2006_route_a_health_cone.json`, 128 rows) supports the design target
and is the motivation for this registration. It is labelled here as what it
is - a diagnostic on committed data, not evidence:

```text
corr( C response, |D| response )             = -0.097   (128 rows)
rows with C(sigma) > C(0)                    = 14
their |D| response range                     = [0.77, 1.60]
D < 0                                        = 128 / 128
```

So the C-improving and the D-degrading directions are not aligned: the
constraint does not fight the objective, and on 12 of those 14 rows the
obligation margin improves as well. Record 2010's section 7 item 3 asked for
exactly this reconciliation; the registered run below re-measures it on a
registered grid rather than relying on this reading.

## 2. Registered objects

```text
owners          G5-H (gamma_5, sc 0.92), G5-W (gamma_5, sc 0.90),
                G7-H (gamma_7, sc 0.92), G8-H (gamma_8, sc 0.88)
delta           0.10 for all four
family          support-preserving two-copy 0.75a / 1.0a (as in 2003/2004/2006)
directions      eigenvectors of the restricted H1 Gram at ranks 1, 2, 4, 6 of
                17, each normalised to unit H1 norm; rank 1 = largest
                restricted eigenvalue. The direction set is the energetic end,
                where records 2004/2010 found the improving branch.
amplitudes      sigma in {0.05, 0.10, 0.20, 0.40, 0.80, 1.20, 1.60} in units
                of E_ref. The grid is extended past 2004/2010's 0.80 so that
                "does the branch keep growing, or has it already turned" is a
                registered reading rather than an extrapolation.
anchor          sigma = 0 (the committed selector)
gate settings   k = 30, n = 0, xi_max = 40, dxi = 0.008
rows            4 owners x (4 ranks x 7 amplitudes + 1 anchor) = 116
stage 2         conditional, see section 5: 5 scales x (4 ranks x 7
                amplitudes + 1 anchor) at the winning owner = 145 rows
```

Per row the probe records the gate entries and their certified-route spreads,
the route list, the prime-power count, pin errors and conditioning, and the
record-1919 signed-mass statistics `mp, mm, f = mm / A, xp, xm, Var_+, Var_-`,
`W(0)`, the tail fraction beyond `|xi| > 4` and the total mass.

## 3. Registered instrument checks

```text
J1  anchor reproduction: the sigma = 0 row reproduces the record-2004 anchor
    of results/2003_route_a_health_selector.json (dxi = 0.004) to <= 5e-3
    relative on C and on D. The band is the registered resolution offset of
    this scan (dxi = 0.008 is half the record-2004 resolution), not a
    tolerance on the physics.
J2  every registered row: three routes, spread_D < 1/3, pin errors <= 1e-6,
    cond <= 1e8, density finite.
J3  record-1919 identity on route B: |det_B - det_var| / max(|det_B|, 1)
    <= 5e-3 and the same for det_moment (the record-2007 calibrated band at
    dxi = 0.008).
J4  resolution stability: on each owner's maximising row, re-read the same
    configuration at dxi = 0.004. The registered requirement is that the sign
    of C and the route-robust health verdict are unchanged; the relative
    shifts of C and D are reported, not bounded. Absolute gate entries carry a
    resolution offset (records 2007/2009), so no design point may rest on a
    reading that flips when the resolution is halved.
```

## 4. Registered decision rules

For each owner let

```text
G(owner) = max over registered (rank, sigma) of  C(rank, sigma) / C(0),
           restricted to rows that are certified with D < 0 at that row.
M(owner) = the registered (rank, sigma) attaining G.
```

```text
A-HD-GAIN     G(owner) >= 2.0 at two or more owners, with M certified and
              D < 0 there
A-HD-NOGAIN   G(owner) < 1.2 at every owner
A-HD-MIXED    otherwise
```

Registered secondary readings, reported and not gating:

```text
R1  the 1/f relief at M: the pair (C ratio, f ratio) at that row
R2  det at M, and the D-margin ratio |D(M)| / |D(0)|
R3  whether C is still increasing over the last two registered amplitudes at M
    (the branch-turned reading)
R4  the D-response census over the whole registered grid: the correlation of
    the C response with the |D| response, so that record 2010 section 7 item 3
    is answered on registered data
```

## 5. Conditional stage 2 (registered now, run only if A-HD-GAIN)

If A-HD-GAIN holds at some owner, apply the same canonical rule at scales
`sc in {0.86, 0.88, 0.90, 0.92, 0.94}` for that owner: at each scale recompute
the restricted-Gram directions and take the rule's maximiser, then record the
C-sign pattern over the scale grid.

```text
A-HD-WINDOW-WIDENS   the healthy scale run at the rule's maximisers is longer
                     than the committed one by >= 2 extra scales
A-HD-WINDOW-SHIFTS   same length, different position
A-HD-WINDOW-NARROWS  otherwise
```

The committed window at the registered heights is `sc = 0.92` (gamma_7) and
`sc = 0.88` (gamma_8), single-scale on the five-point grid (record 1996). Stage
2 measures whether the health window is a property of the committed point or
of the owner, which is the sequencing question for the record-2012 COVER scan.

## 6. Definability clause (stated before any promotion)

The measured maximiser is a grid argmax over a finite canonical set. Promoting
it to a producer requires a canonical rule - existence, uniqueness, and
definability from the owner data - in the spirit of the committed
minimum-norm bricks (records 1927/1929/1930, `exists_min_norm_on_sparse_source_support`).
This desk measures the attainable gain and prices the rule; it does not itself
license a hand-picked owner, and no conditional sign statement is promoted to a
producer theorem here.

## 7. Scope

The desk samples a finite fibre at four registered `(delta, gamma)` points and
at one resolution; stage 2 adds five scales at one owner. It measures; it does
not prove. Nothing here touches the COVER layer, the binding obligation
(`D < 0` on the selected healthy owner), record 1926's selector no-go, the
F2 gate of record 1997, or any Lean artifact. RH is not claimed.

## 8. Artifacts

```text
scripts/routea_ahd_dual_2011.py
results/2011_route_a_ahd_dual.json
results/2011_route_a_ahd_dual_smoke.json
```