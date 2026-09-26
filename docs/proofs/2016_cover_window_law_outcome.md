# Record 2016 - COVER layer: health-window width-law outcome

Date: 2026-09-27.

Status: outcome of the width-law half of the record-2012 pre-registration,
whose two-stage floor cost structure was committed before this run (record
2012 section 2a). The delta-floor half is still running and will be record
2017. No theorem, no Lean brick, no RH claim.

## 1. Verdict

```text
registered verdict   KNOT_COMPLEX
driver-corrected     KNOT_COMPLEX   (identical: the corrected clause moves no
                                     height across a threshold)
floor scan           not in this record (record 2017)
```

The registered rules, applied verbatim: every one of the eight heights is
multi-band, so `WINDOW_STABLE` fails on its own clause; and `WINDOW_PINCHING`
fails because it needs `width(gamma_1) >= 5` while `width(gamma_1) = 4`.  The
record-1998 parenthetical - "multiple narrow bands, drift" - is what the data
is.

```text
record-1998 routing   WINDOW_STABLE   -> the window-track theorem is desk-able
                                         NOT licensed by this data
                      WINDOW_PINCHING -> directions C or E
                                         NOT triggered (gamma_1 is as narrow
                                         as the high heights)
                      KNOT_COMPLEX    -> what this record reports
```

## 2. The width map (delta = 0.10, 21-point scale grid, dxi = 0.004)

```text
layer      gamma      C>0 bands (sc)                            widths   max
committed  14.1347  [0.80-0.83] [0.88-0.90] [0.95] [0.99-1.00]  4,3,1,2   4
committed  21.0220  [0.80] [0.83-0.84] [0.87-0.90] [0.92-0.93]
                    [0.96-0.97] [1.00]                          1,2,4,2,2,1  4
committed  25.0109  [0.80] [0.82] [0.85] [0.87-0.88] [0.90-0.93]
                    [0.95-0.96] [0.98-1.00]                      1,1,1,2,4,2,3  4
committed  27.6703  [0.80-0.83] [0.85-0.88] [0.90-0.91] [0.93]
                    [0.95] [0.98] [1.00]                4,4,2,1,1,1,1  4
committed  30.4249  [0.84] [0.86-0.87] [0.89] [0.91-0.92] [0.94]
                    [0.96-0.97] [0.99-1.00]              1,2,1,2,1,2,2  2
committed  32.9351  [1.00]                                          1   1
ext        30.4249  [0.81-0.82] [0.84-0.85] [0.87] [0.89-0.92]
                    [0.94] [0.96]                            2,2,1,4,1,1  4
ext        37.5862  [0.83] [0.92] [0.95]                            1,1,1  1
ext        40.9187  [0.81-0.82] [0.85] [0.88] [0.91]              2,1,1,1  2
```

The committed health scales of the height-extension layer are single members
of these sets (gamma_7: `0.92`; gamma_8: `0.88`), which is why the
five-point sampling of record 1994 missed them and why record 1996's lane law
- sweep scale, never sample it - is what it is.  The band count is four to
seven per height and the maximal contiguous width is four grid steps (0.04).

## 3. Three structural findings

**(a) The health predicate is a comb, not a window.**  `C > 0` holds on 4-7
disjoint runs of the scale parameter per height, and its maximal contiguous
run in the committed layer falls `4, 4, 4, 4, 2, 1` from `gamma_1` to
`gamma_6`.  The committed layer is a *single-copy* width family
(`fourpoint_rh_reach_probe_1983.family_for_g`: one width per node), so the
oscillation is not an artefact of the two-copy fibre used by the cone layer;
it is a property of the committed per-node width scaling `a_j -> sc * a_j`.
The sign of `C` in this family has 4-7 crossings over 0.21 of scale rather
than one.

**(b) The binding obligation `D < 0` is scale-dependent below `gamma_6`.**  Of
the 190 measured cells, 43 have `D >= 0` - and all 43 are in the committed
layer at `gamma_1..gamma_5` (11, 12, 5, 4, 11 cells); `gamma_6` and every
certified EXT-layer cell have `D < 0` (0 of 75 certified cells across the four
EXT-layer heights and `gamma_6`).  So on this grid the host set - the
registered conjunction `C > 0 and D < 0 and det < 0` - is the *intersection* of
a comb with the complement of a region, and it exists at every height but
scattered: over the nine (layer, height) pairs the hosts form `3, 5, 7, 5, 3,
1, 6, 3, 4` maximal runs containing `7, 5, 9, 10, 4, 1, 11, 3, 5` cells.
Record 1996's "D < 0 on 33/33 cells" was a three-delta reading at
`gamma_7/gamma_8`, where this record also finds none; it was never a statement
about `gamma_1..gamma_5`.

**(c) The layer control fires (section A2).**  At the one height measured
through both layers, `gamma_5`, the committed layer gives 7 bands with maximal
width 2 and the EXT layer 6 bands with maximal width 4; the bands do not agree
position by position (`[0.91-0.92]` against `[0.89-0.92]`, `[0.99-1.00]`
against `[0.96]`).  The provisional host counts also differ by a factor near
three (4 against 11).  Per section A2, which fixed this before the run: **no
cross-height width law may be read from this data without a further control**,
and that is a registered reading and not a caveat.

## 4. Instrument

```text
rows            190 measured (189 registered + 1 anchor cell), 181 certified
anchors         1994 gamma_5 sc 0.92  dev_C 2.2e-08  dev_D 4.3e-08   pass
                1994 gamma_5 delta 0.20 sc 0.86  dev_C 5.2e-08  dev_D 1.5e-07  pass
                1994b gamma_5 sc 0.92  dev_C 2.9e-07 dev_D 1.7e-09  pass
                1996 gamma_7 sc 0.92  dev_C 1.6e-07 dev_D 1.9e-07   pass
                1996 gamma_8 sc 0.88  dev_C 2.8e-06 dev_D 3.5e-05   FAIL (K1)
route spread    every certified cell has spread_C <= 1.5e-03 and
                spread_D <= 1.63e-03; three routes present on all of them
sign unanimity  spread < 1 forces the certified routes to agree in sign
                (opposite signs give |max - min| / max(|max|,|min|) >= 1), so
                the whole band structure of section 2 is route-unanimous
K3 / F52        9 cells are INSTRUMENT-limited: sc = 0.98, 0.99, 1.00 in all
                three EXT-layer heights, with n_primes = 4235, 4661, 5121
                (the record-1994 cost guard drops route Ap above ~4000), and
                spread_D exactly 0.0 - one certified route, not agreement.
                The top two scale steps of the EXT layer are therefore
                UNREADABLE at this resolution (reading S5), and three positive
                C values sit inside them (gamma_7 sc 0.99; gamma_5-EXT sc 0.98
                and 1.00) that the registered rules exclude
```

The single K1 failure is a reference-precision artefact of this record's own
anchor table, and it is provable as such: the `gamma_8` reference was
transcribed to five significant digits (`6.6435e+02`, `-1.1113e+20`) from the
record-1996 audit prose, so it carries a granularity of `7.5e-06` on C and
`1e-04` on D against the registered `1e-06` bar, while the three references
that pass were taken to seven or more digits from `results/` artifacts and
reproduce at `1e-07` or better.  The fix is to read anchor tables from the
committed artifacts, never from prose, and the corrected check is registered
as part of record 2017's instrument rather than retro-fitted here.

## 5. What the verdict does and does not license

```text
does        closes the window-track route as the COVER currency (direction A
            of record 1998) on this data, and closes it twice over: the
            predicate is not an interval in scale, and (section A2) it is not
            even layer-stable at the one height where the layer is varied
does not    license direction C or E either - those were the PINCHING branch
            and PINCHING was not triggered.  The COVER layer's analytic
            currency is now an open question again, with direction A excluded
            by measurement and directions C/E/D not selected by the
            registered rules
does not    move the binding obligation, touch the F2 gate, or prove any sign
```

**The resolution caveat, stated as a registered reading.**  The band structure
above is read through the sign of `C`, which record 2014 section 5 showed to
be the cancelled coordinate: its resolution offset is the mass-level offset
amplified by `|2 + f|`.  On this grid `f` reaches `1.6e+06` (at `gamma_2`) and
`1.8e+05` (at `gamma_1`), against a maximum of `8.6e+04` at the four owners
where the amplification was actually measured.  The comb's *fine structure* -
and, at `gamma_2`, the sign of `C` itself - is therefore a `dxi = 0.004`
reading that has not been shown to survive a resolution change, and the route
spread cannot see this because it is a route spread, not a resolution spread
(all 181 cells are route-unanimous while a half-resolution offset of order
`|2+f| * eps` with `eps ~ 1e-06` would be `O(1)` at `gamma_2`).

This is the honest scope of the record: **KNOT_COMPLEX is measured at one
resolution, and the band-edge cells are the ones that must be re-read at
`dxi = 0.002` before any routing decision rests on the comb.**  That re-read
is registered as the next step, not performed here.

## 6. Artifacts

```text
results/2012_cover_window_law.json                 verdict + full width map
results/2012_cover_window_law_driver-uncorrected.json   first-pass artifact
results/2012_cover_scan_rows_width.json            the 190 measured rows
build-logs/2012_cover_width.log                    measurement pass
build-logs/2012_cover_verdictonly.log              corrected verdict pass
scripts/cover_window_floor_2012.py                 rig (--phase, --verdict-only)
```

Driver note, recorded because the artifacts must say how they were produced:
the measurement pass computed its verdict with the `gamma_5` EXT layer control
*inside* the "every height" clause of `WINDOW_STABLE`, which the registration
does not put there (the control is measured through the other layer at the
same height, so including it double-counts `gamma_5` and lets the layer
question decide the window law).  The verdict was recomputed from the measured
rows by `--verdict-only` with the control excluded
(`results/2012_cover_window_law.json`, with `verdict_keys` recording which
keys entered the clause).  Both passes give `KNOT_COMPLEX`; no cell was
re-measured, and the first-pass artifact is kept above.

## 7. Scope

Eight heights, one delta, one layer per height plus one layer control, one
resolution, a 21-point scale grid at step 0.01, the committed family only.
This is a measurement of the committed construction's scale-dependence; it is
not a theorem about the operator, it says nothing about unmeasured heights,
deltas or families, and it makes no RH claim.

See also: 1983 (the committed owner class), 1994/1994b/1996 (the layers, the
rescue, and the lane law), 1998 (the decision rules this record applies), 2010
and 2014 section 5 (the cancellation coordinate and its amplification), 2012
(this scan's registration), 2015 (the resolution ladder registered for the
four cone-layer owners), 2017 (the floor half).