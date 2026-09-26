# Record 2006 - Route A health-cone shape scan and signed-measure readout

Date: 2026-09-26.

Status: pre-registration. Committed before the run. No theorem, no Lean
brick, and no RH claim.

## 1. Why this scan

Record 2004 sampled two canonical directions per owner - the two most
energetic eigenvectors of the H1 metric restricted to the feasible fibre -
and returned `A-H-CONE-MIXED`. One of those directions (G8-H, rank 2)
increased the health margin monotonically by a factor `3.20` while keeping
`D < 0` and `det < 0` certified. Two things follow:

1. The registered direction choice is worst-case biased, so the shape of the
   healthy set in the fibre is unknown: it may be a sliver around one
   direction, or a region spread across the spectrum.
2. A direction that improves the margin exists, so "does the fibre hold a
   usable healthy region" is an open, measurable question.

This scan samples the fibre across the whole restricted spectrum, and records
the signed-measure moments of record 1919 on every row so the mechanism of
the improvement can be read from the same data rather than from a second run.

## 2. Registered objects

```text
owners                G5-H (gamma_5, sc 0.92), G5-W (gamma_5, sc 0.90),
                      G7-H (gamma_7, sc 0.92), G8-H (gamma_8, sc 0.88)
delta                 0.10 for all four
family                support-preserving two-copy 0.75a / 1.0a
directions            eigenvectors of G_Z at ranks 1, 2, 4, 6, 9, 12, 14, 17
                      of 17, each normalised to unit H1 norm
                      (rank 1 = largest restricted eigenvalue)
amplitudes            sigma in {0.02, 0.05, 0.20, 0.80} in units of E_ref
anchor                sigma = 0, direction independent (the committed selector)
gate settings         k = 30, n = 0, xi_max = 40, dxi = 0.008
rows                  4 owners x (8 ranks x 4 amplitudes + 1 anchor) = 132
```

The restricted spectra are resolved across the whole range: the relative
eigenvalues of `G_Z` decay from `1.0` to `7.5e-10 .. 1.1e-09` over ranks
1..17 for these four owners, and the smallest consecutive gap (`4.4e-08` to
`7.5e-10`) is still far above the eigenvector noise level, so all 17
directions are numerically meaningful.

Per row the probe records, in addition to the gate entries and their
spreads: pin errors, conditioning, route list, prime-power count; the record
1919 identity (channel-split determinant on route `B` against the two-side
variance form and the quartic moment form of the same signed measure); the
signed-mass statistics `mp, mm, f = mm/A, xp, xm, delta_mean, Var_+, Var_-`;
`W(0)`; the tail fraction beyond `|xi| > 4`; and the total mass.

## 3. Registered instrument checks

```text
I1  anchor certified, and |C(0.008) - C(0.004)| / |C(0.004)| <= 5e-3 on C and
    on D, against the record-2004 anchors in
    results/2003_route_a_health_selector.json (dxi = 0.004). The 5e-3 band is
    the registered resolution offset of this scan, not a tolerance on the
    physics: dxi = 0.008 is half the record-2004 resolution.
I2  every row has three routes, spread_D < 1/3, pin errors <= 1e-6,
    cond <= 1e8.
I3  record-1919 identity on route B:
    |det_B - det_var| / max(|det_B|, 1) <= 1e-6 and the same for det_moment.
```

## 4. Registered decision rules

Cone shape. For each owner and each registered rank, the health radius is the
largest registered amplitude with a certified healthy row (`C > 0`, `D < 0`,
`det < 0`, certified). Let `N` be the number of `(owner, rank)` pairs, out of
`4 x 8 = 32`, whose health radius is at least `0.05`.

```text
H-CONE-FAT          N >= 16
H-CONE-STRATIFIED   2 <= N < 16
H-CONE-THIN         N <= 1
```

Rank dependence of the improvement. For each owner, let `j*` be the rank
maximising the ratio `C(0.80) / C(0)` over the registered ranks where `C(0)`
is the anchor margin.

```text
RANK-ENERGETIC      j* in {1, 2, 4} for at least 3 of 4 owners
RANK-PLACEMENT      j* in {12, 14, 17} for at least 3 of 4 owners
RANK-FLAT           neither
```

Mechanism of the improvement. On the rows where the margin increases with
amplitude, compare the negative-mass fraction `f = mm / A` at the largest
registered amplitude with its anchor value.

```text
MECH-SCALE          max relative change of f over those rows <= 0.20
MECH-MIX            otherwise
```

## 5. Scope

The scan samples a finite fibre at four registered `(delta, gamma)` points and
at one resolution. It measures; it does not prove. `H-CONE-*` describes this
owner class and this family only, `RANK-*` and `MECH-*` are descriptions of
the same finite data, and nothing here touches the COVER layer, the binding
obligation (`D < 0` on the selected healthy owner), or any Lean artifact.

Absolute gate entries carry the registered resolution offset of section 3, so
every shape claim is a within-run ratio at fixed `dxi`.
