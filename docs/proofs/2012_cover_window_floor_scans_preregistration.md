# Record 2012 - COVER layer: health-window width law and delta-floor scans (pre-registration)

Date: 2026-09-26.

Status: pre-registration. Committed before the run. No theorem, no Lean
brick, and no RH claim.

## 1. Why these scans

Record 1998 fixed the decision rules for two scans of the COVER layer and they
have not been run. COVER - uniformity over all hypothetical off-line zeros - is
the only layer shared by every route
(`route/000_rh_mainline/README.md`: "The open layer shared by every route is
COVER"). The two verdicts decide which analytic currency pays for it:

```text
WINDOW_STABLE   the window-track theorem (1998 direction A) is desk-able
WINDOW_PINCHING redirects to direction C (family-covering with explicit
                Diophantine structure) or E (total positivity)
FLOOR_UNIFORM   the near-line side is not a wall; the Speiser split stays
                downgraded
FLOOR_RISING    the Speiser split (direction D) is promoted
```

Two registered amendments are added here, both instruments and neither a
change of any record-1998 threshold.

```text
A1 conditioning readout. Record 2010 section 4 shows that the health witness
   C > 0 is the residual of a cancellation of order f = mm / A (f between 51
   and 86087 on the four 2010 owners). A window measured only through the sign
   of C is therefore measured through the fragile coordinate. Every cell of
   both scans additionally records the record-1919 signed-mass statistics
   (mp, mm, f), so a pinched C-window can be compared against the same window
   read in the conditioned coordinate.

A2 layer control. Heights gamma_1..gamma_6 use the committed convention
   (record 1983 layer: 6-ordinate kill list, 13-node owners) and gamma_7 /
   gamma_8 use the height-extension layer (record 1994 EXT: 10-ordinate kill
   list, 17-node owners); record 1996 established that height reading. A width
   law across the eight heights would then confound height with layer, so
   gamma_5 is additionally scanned through the EXT layer (the record-1994b
   control shape). If the gamma_5 windows differ between layers, no
   cross-height width law may be read from this data without a further
   control, and that is a registered reading, not a caveat.
```

## 2. Registered objects

```text
width-law scan
  heights      gamma_1..gamma_6 (committed layer), gamma_7, gamma_8 (EXT),
               plus the gamma_5 EXT layer control
  delta        0.10
  scales       sc = 0.80, 0.81, ..., 1.00   (21 values, step 0.01)
  rows         6 x 21 + 2 x 21 + 1 x 21 = 189 + anchors

delta-floor scan
  heights      the same eight
  deltas       0.02, 0.05, 0.10, 0.15, 0.20, 0.30   (record 1998 set)
  scales       the same 21 values, swept and never sampled
  rows         6 x 8 x 21 = 1008, of which the delta = 0.10 slice is the
               width-law scan: 840 new rows
  cost structure  see section 2a: the floor scan runs in two registered
               stages so that no negative reading is ever taken from a
               five-point sample

gate settings  k = 30, n = 0, xi_max = 40, dxi = 0.004
```

`dxi = 0.004` is the published resolution of the 1994/1996 cells used as
anchors below; the resolution offset of a scan this size is a registered cost
choice, not a physics claim.

## 2a. Registered cost structure of the floor scan (amendment, pre-run)

Record 1996's lane law is "sweep scale, never sample it", and it exists because
a five-point sample missed the health window at gamma_7/gamma_8 entirely. The
same trap applies to the floor scan, but with one asymmetry that can be used
without weakening the rule:

```text
a POSITIVE reading (a certified host at some scale) is decisive - it cannot be
a sampling artefact, because the host is certified wherever it was found;
a NEGATIVE reading (no host at a delta) may only be taken from a full sweep.
```

So the floor scan is registered in two stages:

```text
stage A   6 deltas x 8 heights x the five-point grid {0.86, ..., 0.94}
          = 240 cells.  Only its positives are read.
          If every height has a host at delta = 0.02 in stage A, the verdict
          is FLOOR_UNIFORM immediately and stage B is empty: the floor cannot
          be below 0.02 and 0.02 <= 0.05 is the FLOOR_UNIFORM bar.
stage B   for every height whose stage-A floor candidate is greater than 0.05,
          sweep the FULL 21-point grid at delta = 0.02, at delta = 0.05, and
          at that candidate delta, and read the floor from the sweep.
          A height with no host anywhere in stage B keeps floor = "none" and
          that is the reading.
```

The floor read for every height is therefore either a certified positive (stage
A) or a swept reading (stage B); no floor value in this record is a
five-point-sampling negative. The delta = 0.10 width-law row is measured on
the full 21-point grid regardless (section 2).

## 3. Registered instrument checks

```text
K1  anchor reproduction at the same layer and the same dxi: the published
    record-1994 and record-1996 cells (gamma_7 sc 0.92 at delta 0.10,
    gamma_8 sc 0.88 at delta 0.10, gamma_5 rescue cells) are reproduced to
    <= 1e-6 relative on C and on D.
K2  row certification: density finite, pin errors <= 1e-6, cond <= 1e8,
    spread_D < 1/3.
K3  record-1994 instrument law: a row with n_primes > 4000 is
    INSTRUMENT-limited, never certifies, and its route spread of exactly 0.0
    means "one certified route", not agreement (law F52 shape).
K4  the record-1919 identity readout (A, f, mp, mm) is recorded on every
    finite cell.
```

## 4. Registered decision rules

`certified host` means a certified row with `C > 0`, `D < 0` and `det < 0`.
`width(height)` is the length of the maximal contiguous run of certified cells
with `C > 0` along the 21-point scale grid at `delta = 0.10`, in grid steps
(one step = 0.01).

Record-1998 rules, verbatim:

```text
WINDOW_STABLE    every height has width >= 3 steps
WINDOW_PINCHING  width at gamma_7 and gamma_8 <= 2 steps while
                 gamma_1 has width >= 5 steps
KNOT_COMPLEX     anything else (multiple narrow bands, drift)

FLOOR_UNIFORM    floor(height) <= 0.05 for every measured height
FLOOR_RISING     floor(height) grows with the ordinate
FLOOR-MIXED      neither regime holds; registered here because record 1998
                 named only the two regimes and the residual case must have a
                 name before the run (this is an addition, not a threshold
                 change)
```

Undefined terms in the record-1998 text are fixed here, before the run:
`width >= 0.03` is read as "at least 3 grid steps", and `width < 0.02` as "at
most 2 grid steps"; `floor(height)` is the smallest registered delta with at
least one certified host at that height.

Two further readings are fixed here, before the run, because the committed data
already shows that a single contiguous window is not the only possible shape
(at gamma_5, delta = 0.10, the five-point map of record 1994 reads the C-sign
pattern `+ - - + +`, i.e. two bands):

```text
multi-band cell      a height whose certified C > 0 cells split into two or
                     more maximal runs on the 21-point scale grid
width(height)        the maximal contiguous run, in grid steps, as registered
                     above; reported for every height even when multi-band

verdict precedence   WINDOW_PINCHING if gamma_7 and gamma_8 both have width
                     <= 2 steps while gamma_1 has width >= 5 steps, whether or
                     not other heights are multi-band (the record-1998 text
                     compares exactly these three heights);
                     WINDOW_STABLE if no height is multi-band and every height
                     has width >= 3 steps;
                     KNOT_COMPLEX otherwise (this is where the record-1998
                     parenthetical "multiple narrow bands, drift" lands)

FLOOR_UNIFORM        if floor(height) <= 0.05 at every measured height
                     (precedence over FLOOR_RISING);
FLOOR_RISING         otherwise, if floor(gamma_7) > floor(gamma_1) or
                     floor(gamma_8) > floor(gamma_1);
FLOOR-MIXED          otherwise
```

Both precedence orders are fixed before the run so that no verdict is chosen
after seeing the data.

Registered secondary readings (reported, not gating):

```text
S1  the C-sign map over the 21 scales for each of the eight heights
S2  f and the mass split at every certified host, and the f range over the
    window
S3  the window centre (median healthy scale) against the ordinate, which is
    the "drift" quantity behind KNOT_COMPLEX
S4  the gamma_5 committed-layer against gamma_5 EXT-layer windows (A2)
S5  the number of INSTRUMENT-limited cells (K3) and their location
```

## 5. Scope

These are measurements of the committed owner family at one resolution and one
delta per width question; they are not a theorem, they do not cover unmeasured
heights, and they do not touch the binding obligation (`D < 0` on the selected
healthy owner). A `WINDOW_STABLE` verdict licenses the record-1998 direction-A
desk; `WINDOW_PINCHING` routes to C/E; `FLOOR_RISING` promotes the Speiser
split. RH is not claimed.

## 6. Artifacts

```text
scripts/cover_window_floor_2012.py
results/2012_cover_window_law.json
results/2012_cover_delta_floor.json
results/2012_cover_window_law_smoke.json
```