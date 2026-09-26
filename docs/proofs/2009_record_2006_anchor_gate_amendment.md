# Record 2009 - record 2006 anchor gate restatement (second amendment)

Date: 2026-09-26.

Status: pre-registration amendment. Committed before the registered record-2006
full scan is re-executed. No theorem, no Lean brick, and no RH claim.

## 1. Why

The record-2006 full scan ran at the instrument amended by record 2007. It
completed all 132 rows at `dxi = 0.008` in 2474 s and returned
`INSTRUMENT-FAIL` on one condition only: the G5-W in-run anchor band.

```text
tag    anchor_ok  rows_ok  ident_ok  dev_C(reported)
G5-H   True       True     True      2.62e-03
G5-W   False      True     True      2.24e-02
G7-H   True       True     True      8.31e-04
G8-H   True       True     True      3.68e-04
```

Every row of every owner is certified on three routes; the trace identity and
the algebraic identity hold on all 128 rows of all four owners. This record
shows that the failing condition has no instrument content, replaces it with
the two conditions that do, and re-registers the scan.

## 2. The anchor deviation is a resolution measurement, not a wiring defect

`dev_C` compares the rig's route-keyed readout at the registered resolution
`dxi = 0.008` against the record-2003 anchor, which is the same readout at
`dxi = 0.004`. Record 2007 section 4 established that the route-keyed readout
is the `Ap` route and that `Ap` carries a resolution-dependent error while
route B is spectrally convergent.

The four-owner ladder below (script
`scripts/routea_health_cone_2006_calibration.py`, artifact
`results/2006_route_a_health_cone_calibration.json`) makes the point
quantitatively. `C_Ap` is the route-keyed readout, `C_B` the route-B trace,
and `|A - C_B|/|C_B|` the weighting gap between the route-B entries and the
rectangular grid measure.

```text
tag    dxi     C_Ap            dev_C      C_B             |A-C_B|/|C_B|
G5-H   0.004   1.49481243e+00  0.0e+00    1.49507334e+00  8.13e-11
G5-H   0.008   1.49089500e+00  2.621e-03  1.49507334e+00  1.69e-10
G5-H   0.016   1.42805480e+00  4.466e-02  1.49507334e+00  2.72e-10
G5-W   0.004   2.55909888e-01  0.0e+00    2.56294484e-01  5.86e-11
G5-W   0.008   2.50171188e-01  2.242e-02  2.56294485e-01  5.82e-11
G5-W   0.016   1.60491414e-01  3.729e-01  2.56294490e-01  2.51e-11
G7-H   0.004   1.73298028e+02  0.0e+00    1.73307613e+02  6.50e-06
G7-H   0.008   1.73154001e+02  8.311e-04  1.73308251e+02  1.30e-05
G7-H   0.016   1.70535384e+02  1.594e-02  1.73310855e+02  2.60e-05
G8-H   0.004   6.64351862e+02  0.0e+00    6.64367832e+02  5.82e-07
G8-H   0.008   6.64107475e+02  3.679e-04  6.64368116e+02  1.164e-06
G8-H   0.016   6.59776619e+02  6.887e-03  6.64369272e+02  2.328e-06
```

Three readings.

(1) The route-B trace is resolution-stable for every owner. `C_B` moves by at
most `2.3e-08` relative across the three resolutions (G5-W), and by `1e-10`
for G5-H, while `C_Ap` moves by up to `3.7e-01` relative. Route B is the
accurate estimator, as record 2007 section 4 (2) found.

(2) `dev_C` is not bounded by a single number, because the `Ap` error is
proportional to the channel magnitude while `dev_C` divides by the committed
`|C|`. The absolute offset `dev_C * |C_ref|` is `3.92e-03` for G5-H,
`5.74e-03` for G5-W, `1.44e-01` for G7-H and `2.44e-01` for G8-H; the
relative `dev_C` orders the owners differently (`G5-W` worst, `G8-H` best).
Any single relative band therefore either fails a correctly wired small-`C`
owner or is vacuous for a large-`C` owner.

(3) The committed reference values are themselves `Ap` readings and are
systematically low by the amount in column `C_B - C_Ap(0.004)`: `+2.61e-04`
(G5-H), `+3.85e-04` (G5-W), `+9.59e-03` (G7-H), `+1.60e-02` (G8-H). This is
an accuracy remark on the reference constants, not on any registered
conclusion: every healthy row of record 2004 has `|C| >= 0.2559` against
offsets of order `1e-3` or less on the owners where `|C|` is small.

## 3. Restated instrument

```text
I1a  wiring, gates once. At the reference resolution dxi = 0.004 the anchor
     row reproduces the record-2003 anchor to 0.0e+00 on C and D, for all four
     owners. Evidence: the section 2 ladder. This is the wiring check; it is
     exact, so it cannot be tuned.
I1b  binding entry, gates in-run. dev_D <= 1.0e-03 against the record-2003
     anchors. Measured at the registered resolution: 2.215e-05 (G5-H),
     4.861e-06 (G5-W), 2.035e-05 (G7-H), 3.223e-06 (G8-H), so the band has at
     least a 45x margin. D is the binding obligation of the project, and its
     readout is resolution-stable, so this condition carries content.
I1c  reported, not gated. dev_C per case, recorded as `anchor_dev_C_reported`
     in the checks and as `reference_dev` in the case blocks. Section 2 (2)
     is the registered reason it is not a pass/fail condition.
I1d  one measure, gates in-run (this was record 2007's I3b).
     |A - C_B| / max(|C_B|, 1) <= 3.0e-03. Measured at the registered
     resolution: 1.30e-05 over the ladder, and at most 4.02e-04 over the 128
     rows of the first full run.
I2   unchanged. Three routes, spread_D < 1/3, pin errors <= 1e-6, cond <= 1e8.
I3a  unchanged. |det_var - det_moment| / max(|det_var|, 1) <= 1e-9. Measured
     at most 5.82e-13 over the first full run.
I3c  unchanged. |det_B - det_var| / max(|det_B|, 1) <= 5.0e-3. Measured at
     most 8.71e-04 over the first full run.
```

The verdict gate is therefore `anchor_ok and rows_ok and identity_ok` with
`anchor_ok` reading I1b only. Nothing in record 2006 section 2 (owners,
family, ranks, amplitudes, gate settings, `dxi = 0.008`) and nothing in
record 2006 section 4 (the thresholds and the registered classes) changes.
The route-robust health predicate of record 2007 section 6 also stands
unchanged, and the first full run already used it.

## 4. Why the registered resolution is not changed

The first full run shows that `Ap` is more accurate at `dxi = 0.004`, and a
repeat at `0.004` would also be directly comparable with records 2003 and
2004. That option is rejected here, deliberately. The cone verdict counts
`(owner, rank)` pairs whose health radius reaches `sigma = 0.05`, and the
first run places `N = 14` against the registered `H-CONE-FAT` threshold of
`N >= 16`. Several of those pairs sit exactly at the threshold (radius equal
to `0.05`). Changing the resolution after seeing that count would make the
verdict resolution-tunable, so `dxi = 0.008` is kept as registered.

## 5. Reproducibility expectation for the re-executed scan

The registered scan is re-executed with the amended instrument. The rig is
deterministic, so the re-executed artifact must reproduce the first run's
row-level content. Recorded here before the re-execution, as the registered
expectation:

```text
certified rows          32/32 for each of G5-H, G5-W, G7-H, G8-H
C_B < 0 counts          28/32, 32/32, 16/32, 11/32
det < 0 counts           9/32,  0/32, 17/32, 22/32
healthy rows            4, 0, 16, 21 on both routes and on the conjunction
health radii            G5-H 6:0.02 12:0.02 14:0.02 17:0.02, G5-W none,
                        G7-H 1:0.05 2:0.05 4:0.05 6:0.20 9:0.05 12:0.05
                        14:0.02 17:0.05,
                        G8-H 1:0.05 2:0.80 4:0.80 6:0.80 9:0.05 12:0.05
                        14:0.02 17:0.05
N                       14
rank winners            G5-H 14, G5-W 6, G7-H 6, G8-H 4
```

A deviation would be a reproducibility finding and would be recorded as such
in the outcome record, which is record 2010.

## 6. Scope

Nothing here is RH progress. The amendment restates one instrument gate and
re-executes the registered scan. It does not touch the owner, the family, the
ranks, the amplitudes, the `(delta, gamma)` points, the decision thresholds,
the binding obligation (`D < 0` on the selected healthy owner), the COVER
layer, or any Lean artifact, and it makes no gate-sign, determinant or RH
claim.
