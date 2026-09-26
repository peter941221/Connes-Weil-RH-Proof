# Record 2017 - COVER layer: delta-floor outcome

Date: 2026-09-27.

Status: outcome of the delta-floor half of the record-2012 pre-registration
(section 2a fixed the two-stage cost structure before the run).  Companion to
record 2016, which reported the width half.  No theorem, no Lean brick, no RH
claim.

## 1. Verdict

```text
registered verdict   FLOOR_UNIFORM   (precedence clause: floor <= 0.05 at
                                      every measured height)

floor(gamma)         0.02   at all eight registered heights
                     0.02   at the gamma_5 layer control as well
```

The registered rule, applied verbatim (record 2012 sections 4 and 2a): a
height's floor is the smallest delta of `{0.02, 0.05, 0.10, 0.15, 0.20, 0.30}`
carrying a certified host.  Every height has a host at the smallest registered
delta, so the uniform clause is decided by stage A alone - except at
`gamma_6`, where stage A found no host anywhere on the five-point grid and the
registered stage-B trigger fired (section 3b).

```text
record-1998 routing
  FLOOR_UNIFORM   the near-line side is not a wall; the Speiser split
                  (direction D) stays DOWN-GRADED
  FLOOR_RISING    not triggered (needs floor(gamma_7) > floor(gamma_1) or
                  floor(gamma_8) > floor(gamma_1); all three read 0.02)
```

## 2. The floor map (dxi = 0.004, five-point scale grid, stage B for gamma_6)

```text
layer      gamma      stage-A hosts per delta                     floor  read
                      .02 .05 .10 .15 .20 .30
committed  14.1347     2   2   2   2   2   2                        0.02  A
committed  21.0220     1   1   1   1   1   0                        0.02  A
committed  25.0109     2   2   2   2   2   2                        0.02  A
committed  27.6703     3   3   3   3   3   3                        0.02  A
committed  30.4249     2   2   2   2   2   2                        0.02  A
committed  32.9351     0   0   0   0   0   0  (five-point grid)     0.02  B
                       1   1   1   1   1   1  (full 21-point grid)
ext        30.4249     3   3   3   3   3   2                        0.02  A  (control)
ext        37.5862     1   1   1   1   1   1                        0.02  A
ext        40.9187     1   1   1   1   1   1                        0.02  A
```

## 3. Three structural findings

**(a) The host scale window is delta-stable; the C-comb of record 2016 is
not.**  The host predicate at a fixed height occupies a small, fixed set of
scales on the five-point grid, and that set barely moves over a factor-15
change in delta:

```text
height            host scales, delta 0.02 ... 0.30
committed 14.1347   {0.88, 0.90} at every delta
committed 21.0220   {0.88} at every delta except 0.30 (five-point grid only)
committed 25.0109   {0.88, 0.90} at every delta
committed 27.6703   {0.86, 0.88, 0.90} at every delta
committed 30.4249   {0.86, 0.92} at every delta
committed 32.9351   {1.00} at every delta (from the full sweep)
ext       30.4249   {0.90, 0.92, 0.94} at every delta, minus {0.90} at 0.30
ext       37.5862   {0.92} at every delta
ext       40.9187   {0.88} at every delta
```

So the 4-7 disjoint `C > 0` scale bands of record 2016 do not propagate to the
host set: on these heights the health witness is *selectable along the
near-line direction* at a fixed scale, and the two coordinates do different
work.  `C > 0` is scale-fragile and delta-robust; the host conjunction is
scale-specific and (within the sampled grid) delta-stable.

**(b) The stage-B trigger fired exactly where section 2a said it would.**
`gamma_6` has no host anywhere on the five-point grid at any delta, which is
the width scan's reading again (record 2016 section 2: `gamma_6`'s only
`C > 0` band sits at scale 1.00).  The registered sweep of the full 21-point
grid found one host at every delta, at scale 1.00, so the floor reads 0.02
through the sweep.  This is the second time the committed construction has
hidden its witness at a scale outside a five-point window, and it is the
record-1996 lane law - sweep scale, never sample it - doing real work rather
than being quoted.

**(c) The delta scan does not move the visible-prime set.**  Across all 366
rows, `n_primes` is a function of (layer, height, scale) alone: 61 distinct
(layer, height, scale) keys, zero of them carrying two different `n_primes`
values over the six deltas.  Moving the witness toward the line therefore
costs nothing in the visible-prime book - no prime enters or leaves the
support as delta decreases - which is the property the near-line direction
needed in order to be cheap at all.

## 4. Instrument

```text
rows            366 measured (270 stage A + 96 sweep), 366 certified,
                0 INSTRUMENT-limited, 0 UNRESOLVED
anchors         5 of 5 reproduce with dev_C = 0.0 and dev_D = 0.0 against
                references read from the committed artifacts at full
                precision (1996 gamma_7 sc 0.92; 1996 gamma_8 sc 0.88;
                1994 gamma_5 sc 0.92 and gamma_5 delta 0.20 sc 0.86;
                1994b gamma_5 EXT sc 0.92)
route spread    max spread_C 3.29e-03, max spread_D 6.96e-04 over the 366
                certified rows
pin / cond      max pin error 1.68e-10, max cond 5.17e+05, density finite
                on every row
cross-scan      45 cells are shared with record 2016's width scan (the nine
                heights at delta 0.10 on the five anchor scales); C and D
                agree BIT-EXACTLY on all 45, with no host or certification
                disagreement - the two scans were launched separately and
                reproduce each other cell for cell
np range        committed layer 86..332; ext layer 1368..2894 - the whole
                floor grid stays below the record-1994 cost guard, which is
                why no cell in this scan is instrument-limited
f on hosts      |f| in [2.97e+01, 1.885e+05]; the largest values are at
                gamma_1/gamma_2 (committed) and the EXT gamma_5 control
```

**Anchor erratum, closed.**  Record 2016 section 4 reported one K1 failure
(`gamma_8` sc 0.88, dev_C 2.8e-06, dev_D 3.5e-05) and diagnosed it as this
rig's own table carrying a five-significant-digit transcription of the
record-1996 value; it registered the fix as part of this record's instrument
rather than retro-fitting it there.  The fix is now applied - all five
references are read from `results/1996_gamma78_full_sweep.json`,
`results/1994_opposite_gates_height.json` and
`results/1994b_ext_convention_control.json` at full precision - and the
reproduction is exact to the last bit on all five.  The diagnosis was right
and the correction confirms it: every deviation record 2016 saw was the
reference's own rounding (its `gamma_7` deviation of 1.6e-07 is exactly the
half-ulp of `1.732980e+02`), not any difference between the runs.

Driver note, recorded because the artifacts must say how they were produced:
the first floor pass measured all 366 cells and then died at the verdict
stage - a stale identifier left in the shared verdict block by the same patch
series that added `--verdict-only`.  The width half escaped the same defect
only because its verdict had been recomputed through `--verdict-only`, which
carries its own block; any full run after that patch would have died the same
way.  The checkpoint had already been written and held the complete row set;
the rig was then fixed and given `--resume-from`, and the registered
verdict/artifact stage re-ran on the checkpoint: 0.1 s of wall time, every
log timestamp `0.0s`, i.e. **zero cells re-measured**.  The measurement is the
first pass's; the verdict and artifacts are the fixed rig's, from the same
rows through the same registered code path.  The first pass's checkpoint and
the archived floor rows are the identical row set (checked key by key).

## 5. What the verdict does and does not license

```text
does        reads the near-line side as wall-free down to delta = 0.02 at all
            eight measured heights, in the registered sense: a healthy host
            exists at the smallest registered delta, so the Speiser split
            (direction D of record 1998) stays down-graded and no COVER
            mechanism may be built on a near-line obstruction
does        make the combined picture of records 2016 and 2017 exact: the
            scale coordinate is where health is fragile, the near-line
            coordinate is where it is cheap
does not    answer the analytic near-line question.  "floor = 0.02" is the
            smallest REGISTERED delta, so the verdict is a statement about
            delta >= 0.02 - it cannot distinguish "no wall" from "a wall below
            0.02", and the desk's own FLOOR_UNIFORM phrasing ("the near-line
            side is not a wall") must be read with that quantifier.  A finer
            delta grid (0.005, 0.01, 0.02) on the four heights whose hosts sit
            inside the five-point grid is the registered way to attack
            delta -> 0, and it is a follow-up, not a result
does not    promote anything: FLOOR_RISING was not triggered, so direction D
            is not promoted; direction A stays closed by record 2016; C/E
            stay unselected.  The COVER layer's analytic currency remains an
            open question with two directions now measured and excluded
```

**A flagged observation, not a reading.**  Two heights lose a five-point host
at delta = 0.30: `gamma_2` (down to zero hosts) and the EXT `gamma_5` control
(keeps `{0.92, 0.94}`).  Section 2a is explicit that a negative may only be
taken from a full sweep, and neither height was swept at that delta, so this
is *not* a statement that health fails far from the line - it is a note that
the far-delta side is a different question, unmeasured, and that `gamma_6`'s
own behaviour (a host that lives only at scale 1.00) is exactly the shape that
would make a five-point negative wrong there too.

## 6. Artifacts

```text
results/2012_cover_delta_floor.json        verdict + floor map + anchors
results/2012_cover_scan_rows_floor.json    the 366 measured rows
build-logs/2012_cover_floor.log            measurement pass (the crashed one)
build-logs/2012_cover_floor_resume.log     verdict + corrected anchors, 0.1 s
scripts/cover_window_floor_2012.py         rig (--phase, --verdict-only,
                                           --resume-from)
docs/proofs/2012_cover_window_floor_scans_preregistration.md   the rules
```

## 7. Scope

Eight heights, one layer per height plus one layer control, six deltas, a
five-point scale grid (plus the full sweep at `gamma_6`), one resolution
(`dxi = 0.004`), the committed family only, `delta >= 0.02`.  This is a
measurement of the committed construction, not a theorem about the operator;
it says nothing about unmeasured heights, deltas below 0.02, or other
families.  The binding obligation (`D < 0` on the selected healthy owner) is
untouched, the F2 gate of record 1997 stands, stage 2 of record 2011 is not
licensed, and RH is not claimed.

See also: 1998 (the desk whose direction D this down-grades), 2012 (the
registration, including the section-2a cost structure and the anchor-fix
registration), 2016 (the width half and the K1 diagnosis this record closes),
1994/1994b/1996 (the anchors), 2014 (the amplification identity behind the
host `f` values), 2015 (the resolution ladder for the evaluation layer).