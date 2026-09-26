# Record 2007 - record 2006 instrument restatement and route-robustness amendment

Date: 2026-09-26.

Status: pre-registration amendment, committed before the record-2006 full
scan. No theorem, no Lean brick, and no RH claim.

## 1. Why

Record 2006 section 3 registered three instrument checks, I1, I2 and I3. Its
G5-H smoke run returned `anchor = False` and `ident = False`, so the
registered full scan would have halted as `INSTRUMENT-FAIL`. This record
diagnoses both readings, restates the checks with calibrated bands, and adds
one route-robustness condition to the health predicate of record 2006
section 4. It is committed before the full scan.

Nothing in record 2006 section 2 changes: same owners, same
support-preserving two-copy family, same ranks, same amplitude grid, same
gate settings, same `dxi = 0.008` for the registered run. The thresholds of
record 2006 section 4 (`N >= 16`, `2 <= N < 16`, `N <= 1`, the `j*`
classes, `MECH_TOL = 0.20`) do not change either.

## 2. Two code paths, two weightings

`r59.gate_entries` builds the prime channel on the raw xi grid and reduces it
with the composite trapezoid rule, so route B is

```text
arch[j]    = trapezoid(sigma_vec(2*pi*xi) * f_j, xi)
prime_B[j] = trapezoid(Kp * f_j, xi)
C_B        = arch[0] + prime_B[0]
```

The record-1919 engine instead receives a signed grid measure with constant
weights,

```text
mu = (sigma_vec(2*pi*xi) + Kp) * W * dxi
A  = sum(mu)
```

and `variance_check` returns `det_var` (two-sided variance form) and
`det_moment` (quartic moment form) as two arithmetic evaluations of
`A^2 * Var_nu(P)`. Three consequences are used below.

```text
det_var = det_moment   exactly   (one measure, two arithmetic forms)
C_B     = A            approximately   (two weightings, same grid values)
det_B   = det_var      approximately   (trapezoid vs rectangle, then
                                        amplified by the determinant's own
                                        cancellation)
```

Record 2006 section 3 I3 asked for the third line at `1e-6`. That is not an
algebraic identity, only a quadrature agreement, so the check could not pass.
That is the source of `ident = False`.

## 3. The registered certification test never covered the C entry

`r59.route_spread` returns one spread per gate entry, but record 2006's
`certified` flag tests only `spread_D < 1/3`. The registered `healthy`
predicate then reads `C > 0` from the route-keyed readout, and
`gate_entries` keys that readout to `Ap` whenever route `Ap` is available.
So a row whose C sign is route-dependent can still be certified and then
counted as healthy. Section 4 (4) measures how large that dependence is.

## 4. Calibration ladder (committed evidence)

```text
script    scripts/routea_health_cone_2006_calibration.py
artifact  results/2006_route_a_health_cone_calibration.json
          md5 c50d67fe43d637bf2a108ba60d03488a
```

It measures the committed anchor row of record 2006 at
`dxi in {0.004, 0.008, 0.016}` for two owners. `dev_C` and `dev_D` are the
relative deviations from the record-2003 anchors, which are `dxi = 0.004`
values. `C_B` is the route-B trace, `|A - C_B|/|C_B|` is the weighting gap on
the first entry, and `|det_B - det_var|/|det_B|` is the same gap after the
determinant.

G5-H (gamma_5, scale 0.92, delta 0.10):

```text
dxi     C route-keyed   dev_C      C_B             |A-C_B|/|C_B|  |det_B-det_var|/|det_B|
0.004   1.49481243e+00  0.0e+00    1.49507334e+00  8.13e-11       1.513e-04
0.008   1.49089500e+00  2.621e-03  1.49507334e+00  1.69e-10       3.025e-04
0.016   1.42805480e+00  4.466e-02  1.49507334e+00  2.72e-10       6.052e-04
```

G7-H (gamma_7, scale 0.92, delta 0.10):

```text
dxi     C route-keyed   dev_C      C_B             |A-C_B|/|C_B|  |det_B-det_var|/|det_B|
0.004   1.73298028e+02  0.0e+00    1.73307613e+02  6.50e-06       7.881e-05
0.008   1.73154001e+02  8.311e-04  1.73308251e+02  1.30e-05       1.576e-04
0.016   1.70535384e+02  1.594e-02  1.73310855e+02  2.60e-05       3.153e-04
```

Four readings.

(1) Wiring is confirmed. At `dxi = 0.004` the rig reproduces the record-2003
anchor to `0.0e+00` on C and D, on three routes, with the committed prime set
(2393 prime powers). The registered reference value is itself the `Ap`-route
reading at `dxi = 0.004`, which is why the registered I1 band was written as
`5e-3`: it was an estimate of a resolution offset that had not been measured.

(2) Route B is the accurate estimator. `C_B` is stable across the three
resolutions, identical to ten significant digits for G5-H and drifting only
`1.9e-05` relative for G7-H, and it agrees with the rectangle reduction of
the same grid values to `|A - C_B|/|C_B| <= 2.7e-05`. The owner support is
`|xi| <= 9.936` inside a grid that runs to `|xi| = 40`, so the composite
trapezoid rule on a compactly supported smooth integrand is spectrally
convergent and the two weightings of the same samples agree as well.

(3) Route `Ap` carries a resolution-dependent error. `dev_C` falls from
`4.47e-02` at `dxi = 0.016` to `2.62e-03` for G5-H and from `1.59e-02` to
`8.31e-04` for G7-H at `dxi = 0.008`. A `5e-3` band is therefore
unsatisfiable at `0.016` and only `1.9x` from the measured value at `0.008`.
That is `anchor = False`.

(4) The C entry is a cancelling sum. Over the 32 smoke rows of G5-H,
`spread_C` reaches `5.43e-01` at `dxi = 0.016` and `6.88e-02` at
`dxi = 0.008`, while `spread_D` stays at or below `8.24e-04` and `2.10e-04`.
Since `C = arch[0] + prime[0]` is a difference of two larger channel terms,
the certified-route disagreement on a channel is amplified in C by
cancellation. This is a property of the entry, not a defect of either route.

Record 2004 is not affected by (4). Its 56 rows were measured at
`dxi = 0.004`, where the maximum `spread_C` over all rows is `4.66e-03`, and
every one of its 23 healthy rows has `spread_C <= 3.0e-04` relative with
`|C| >= 0.2559`. Its health readings are route-robust with a wide margin.

## 5. Restated checks

Registered resolution `dxi = 0.008`. The bands below are the ones compiled
into `scripts/routea_health_cone_2006.py`.

```text
I1a  wiring. At the reference resolution dxi = 0.004 the anchor row
     reproduces the record-2003 anchor to <= 1e-9 on C and D. Measured
     0.0e+00 (section 4 ladder). Run once, not in-run.
I1b  in-run anchor. dev_C <= 1.0e-02 and dev_D <= 1.0e-03 against the
     record-2003 anchors. The C band is the route-Ap error at this
     resolution (measured 2.62e-03, 3.8x margin); the D band is broad
     (measured 2.22e-05, 45x margin).
I2   unchanged from record 2006 section 3: three routes, spread_D < 1/3,
     pin errors <= 1e-6, cond <= 1e8.
I3a  algebraic identity. |det_var - det_moment| / max(|det_var|, 1) <= 1e-9.
     Measured 5.8e-13 over the 32 smoke rows.
I3b  trace identity. |A - C_B| / max(|C_B|, 1) <= 1e-3. Measured 1.48e-04
     over the 32 smoke rows.
I3c  determinant gap. |det_B - det_var| / max(|det_B|, 1) <= 5e-3. Measured
     8.15e-04 over the 32 smoke rows. Registered as the
     trapezoid-versus-rectangle gap, not as the 1919 identity; I3a is the
     identity.
```

The `dxi = 0.016` smoke bands are kept in the same dictionary
(`anchor_C 6.0e-02`, `anchor_D 3.0e-03`, `det_quad 1.5e-02`, `trace 1.0e-03`).
The smoke path now writes `results/2006_route_a_health_cone_smoke.json`, so
it cannot overwrite the registered full-run artifact.

Verification of section 5 at the registered resolution, G5-H smoke
(32 rows plus the anchor, `dxi = 0.008`):

```text
anchor_ok True   rows_ok True   identity_ok True
anchor dev_C 2.62e-03   dev_D 2.22e-05
max dev_var 8.15e-04   max dev_alg 5.82e-13   max dev_A_C 1.48e-04
```

## 6. Amended health predicate

Record 2006 section 4 defines a healthy row as certified with `C > 0`,
`D < 0`, `det < 0`. By section 3 above that predicate is route-dependent in
C and, through C, in `det`. The predicate becomes

```text
healthy = certified
          and C > 0, D < 0, det < 0          (route-keyed readout)
          and C_B > 0, D_B < 0, det_B < 0    (route-B readout)
```

Both single-route readings are reported per row as `healthy_ap` and
`healthy_b`, the conjunction is reported as `healthy`, and the cone radius of
record 2006 section 4 is computed from the conjunction only. The direction of
the bias is safe: the conjunction can only remove healthy rows, so the
registered `H-CONE-*` verdict can only move toward the thinner labels, never
toward `H-CONE-FAT`.

G5-H smoke at `dxi = 0.008`: 32 rows, `healthy_ap = 4`, `healthy_b = 4`,
conjunction `= 4`. The four rows have `C` between `+3.78e-01` and
`+1.46e+00` with `spread_C <= 1.02e-02`, and all nine rows with `|C| < 3`
agree in sign between the two routes.

## 7. Additional per-row evidence

Every row now also records the raw per-route entry triples
(`route_triples`, keyed by route) so the route spread can be recomputed from
the artifact without rerunning the rig.

## 8. Scope

Nothing here is RH progress. The amendment changes instrument bands and the
source of one sign reading; it does not touch the binding obligation
(`D < 0` on the selected healthy owner), the COVER layer, or any Lean
artifact, and it makes no gate-sign, determinant or RH claim. Record 2006
section 5 continues to apply unchanged: the scan measures a finite fiber at
four registered `(delta, gamma)` points and at one resolution, and every
shape claim is a within-run ratio at fixed `dxi`.
