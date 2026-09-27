# 107 — COVER layer: measured state of the (delta, gamma, scale) problem

Date: 2026-09-27.

Status: routing record. Subordinate to
[003](003_b1_b5_minimal_exit_route_selection.md) and
[004](004_endpoint_literature_interface_audit.md); it applies the decision
rules fixed in [1998](../proofs/1998_cover_strategy_desk.md) and pre-registered
in [2012](../proofs/2012_cover_window_floor_scans_preregistration.md) to the
measurements reported in [2016](../proofs/2016_cover_window_law_outcome.md)
and [2017](../proofs/2017_cover_delta_floor_outcome.md).  It proves nothing,
moves no gate, and does not touch the binding producer obligation.  RH is not
claimed.

## 1. What the layer is

COVER is the uniformity clause every route needs and no route's Lean source
currently states:

```text
hypothetical off-line zero rho = (1/2 + delta) + i*gamma
  -> a healthy selected CompactLog detector g for that rho
  -> qw(g) < 0
  -> prove qw(g) >= 0 for the same owner
  -> contradiction -> SourceRH -> Mathlib RiemannHypothesis
```

The producer lanes (map 104, 103/105/106) live in the second-to-last line.
COVER lives in the first: for every hypothetical `rho`, a witness must exist,
with the health screen `C > 0` (record 1931) and the binding sign `D < 0`
(records 1981/2014a) carried along.  The witness set is parameterized by three
coordinates - `delta` (distance from the line), `gamma` (ordinate), `scale`
(the family width multiplier) - so "is there a witness" is a question about
that three-dimensional set, not about a single detector.

## 2. Measured state

Both halves of the record-2012 pre-registration have now run on the committed
family.  The measurements are in `docs/proofs/`; this map records only what
they rule.

```text
coordinate      question                          reading        verdict
delta (2017)    smallest delta with a host        0.02 at all    FLOOR_UNIFORM
                at each height, scale swept       eight heights
scale (2016)    width of the C > 0 band per      4..1 grid      KNOT_COMPLEX
                height at delta = 0.10            steps; 4-7
                                                  bands/height
layer (2016)    gamma_5 through both layers      bands differ   control fires
                                                  cell by cell
```

Three readings carry the routing weight:

- the health predicate in `scale` is a comb, not an interval (4-7 disjoint
  `C > 0` runs per height, all in the single-copy committed family);
- the binding sign `D < 0` is scale-dependent below `gamma_6` (43 of 190 cells
  have `D >= 0`, all at `gamma_1..gamma_5`), so the host set is a comb
  intersected with a region;
- the `gamma_5` layer control disagrees between the committed and EXT layers,
  so no cross-height width law is licensed by this data.

Versus the coordinates that turned out benign: the host's *scale window* at a
fixed height is stable over the whole delta grid, and `n_primes` is a function
of (layer, height, scale) alone, so moving the witness toward the line costs
nothing in the visible-prime book.  The cost of the near-line direction is not
information, it is resolution.

The record-2020 currency desk then identified that book exactly and measured
the comb as a sequence:

```text
book (2020)     np(s) = #{n prime power : n <= exp(2*s*m_pool)} — an identity,
                27/27 committed cells; the book moves with the height too
                (m_pool 3.40 at gamma_1 vs 3.80 at gamma_2..gamma_6)
crossing (2020) one book step moves C by <= 0.574|C| (committed gamma_1@0.88,
                4 steps per 0.01 cell) and <= 0.0686|C| (ext gamma_7@0.92,
                227 steps per 0.01 cell)
comb (2020)     sign(C) along scale is white at the 0.01 grid: flip rate
                0.468 (C) / 0.409 (healthy) against independence references
                0.494 / 0.424, flat in h; healthy measure mu = 0.306 over 180
                certified cells -> H = 3.27 (per height 1.64 .. 21.0)
```

So the 2016 KNOT_COMPLEX is the run structure of a near-white sequence, the
healthy set's 0.01 window currency is measured absent, its *measure* currency
is measured (H = 3.27 at delta = 0.10), and the surviving requirement is
pointwise-in-scale certification at the measured cancellation depth.

Record 2022 then closed the two registered measurement debts on the other
axes:

```text
resolution (2022) re-read of the comb at dxi = 0.002: zero flips, zero
                  lost, zero appeared, zero missing over 189 cells, nine of
                  nine band censuses identical (COMB-RESOLUTION-STABLE);
                  r <= 8.87e-05 over the 42 gamma_1/gamma_2 cells
                  (RP-COMPLETE), eps 6.4e-06 .. 8.7e-04
delta (2022)      the floor refines: a certified host at delta = 0.005 on
                  all nine slots (FLOOR-REFINED-0.005; committed gamma_6 via
                  the registered stage-B sweep, host at scale 1.00)
```

The comb therefore survives the quadrature refinement at the certified cells
- it is a resolution fact, not a quadrature artifact - and FLOOR_UNIFORM is
no longer a statement about `delta >= 0.02` alone: at this refinement the
floor sits at the smallest registered delta on every measured slot.

Record 2023 (C1, the scale ladder) then read the scale side at the
crossing-resolving grid:

```text
ladder (2023)   WINDOW-LADDER: healthy flips at h = 0.002 run 9.85 sigma
                BELOW independence (81 percent same-sign persistence), so
                windows wider than 0.002 exist; the small-lag slope
                step/rate is a slot-specific band scale L (gamma_1 0.025,
                gamma_4 0.011, ext gamma_5 0.009, pooled 0.0125) reproduced
                by both fine grids; the 0.01 grid sits at h ~ L, which is
                why its pooled reading is white-looking; mu ladder agrees to
                0.06 sigma (H = 2.04 in this window)
```

So the record-2020 "white at 0.01" ruling now has its mechanism measured: the
0.01 grid is a one-step-per-band sample, not a white field, and the
certification granularity at a fixed slot is `L_slot`.

Record 2024 then registered the two debts record 2023 left open (the six
unmeasured slots; the delta axis), and record 2025 reads them:

```text
ladder (2025)   LADDER9-PARTIAL: the h = 0.002 healthy suppression holds on
                4 of the 6 unmeasured slots (dev -6.26, -5.86, -4.37, -3.46
                sigma; pooled -11.22 sigma over 300 pairs), misses on ext
                gamma_7 (-2.12 sigma) and is unreadable on committed
                gamma_6 (zero flips in the window, 50 + 20 pairs).  The
                registered nine now read L = 0.02500 (gamma_1), 0.02000
                (gamma_2), 0.01429 (gamma_3), 0.01111 (gamma_4), 0.01250
                (gamma_5 committed), no-flips (gamma_6), 0.01000 (gamma_7
                ext), 0.00833 (gamma_8 ext), with 0.00909 for the ext
                gamma_5 control.  counts_equal is a per-slot property, not
                a layer law: it holds on every committed slot (minimum
                consecutive-flip gap 0.006 .. 0.016, wider than the 0.005
                step) and fails on ext gamma_7 (gaps down to 0.002; 10
                flips at 0.002 vs 6 at 0.005) and ext gamma_8 (0.004 gap;
                12 vs 10) - those two windows carry sign excursions
                narrower than 0.005, whose double crossings a 0.005 pair
                merges to a net zero, so their L_005 (0.01667 / 0.01000)
                over-states L and only L_002 (0.01000 / 0.00833) is
                registered
delta (2025)    L-DELTA-STABLE: on the three C1 slots L is identical at
                delta = 0.02, 0.05, 0.10 (ratio 1.0000 against the
                registered bar 1.25), and so are the underlying C flip
                count, the healthy flip count and mu_healthy - the
                stability is a count identity, not a tolerance result.
                Beyond the registered clause (record 2025 section 4, read
                cell-by-cell from the committed rows): the sign of C, the
                sign of D and the healthy face are identical at delta =
                0.02 / 0.05 / 0.10 on every one of the 153 shared
                0.002-grid cells (3 slots x 51, 0 mismatches), while C's
                own magnitude moves by more than a factor of 30 across
                that delta range (gamma_1, scale 0.86: -2.06 / -9.68 /
                -66.94) - the sign pattern is a function of (layer,
                height, scale) alone and delta only scales the magnitudes
```

So the record-2023 granularity ruling is a function of the slot and not of
`delta` over the registered range, and the nine-slot table prices it: `L`
decreases with height from 0.025 at `gamma_1` to 0.008 at `gamma_8`, with the
layer as the one measured counterexample at a fixed height (`gamma_5`:
committed 0.0125 against ext 0.0091).

Record 2026 then registered three refinements, and two of them are read
(record 2027) while the third is registered and unread:

```text
resolution    U-CONVERGED: the stride-1 C flip count at delta = 0.10 is
(2027)        identical on the 0.001 grid and the 0.002 grid at all three EXT
              slots (10 / 10, 12 / 12, 11 / 11), so L_001 = L_002 exactly and
              the registered L_002 estimator is resolved rather than merely
              conservative; ext gamma_7 separates with zero margin (minimum
              flip gap 0.0020).  The 0.005 grid does merge those doublets:
              count_gain_001_005 = 4 / 2 / 0, so the registered L_005 was high
              by 1.6667 / 1.2000 / 1.0000.  The 0.001 grid adds no structure,
              so count-based L at these three slots cannot be lowered by
              refining this window further.
delta string  STRING-CENSUS-BREAKS: on the five-point scale set {0.86..0.94}
(2027)        seven of the nine registered slots carry one and the same C sign
              string at all six registered deltas; committed gamma_2 breaks
              from delta = 0.20 and the ext gamma_5 control from delta = 0.30,
              over 54/54 comparisons at full five-position coverage.  This is
              the five-point form only.
delta string  NOT READ: the 51-position fine-string comparison at the six P1
(2027, D)     slots was registered, launched on the heavy lock, and stopped
              unread after 81 of its 552 registered cells.  No verdict is
              claimed and the item stays open.
```

So U fixes the certified spacing at the three EXT slots at 0.002-grid
granularity, S registers the five-point delta invariance of the sign string,
and D - which was to register the fine-string form - is unread.  The
fine-string invariance of record 2025 section 4 therefore remains a labeled
post-hoc by-product rather than a registered finding, and the layer axis of
`L` (record 2025 section 7 item iii) is untouched.

## 3. Routing rulings

Only the registered precedence rules were applied, and they give:

```text
direction A   window-track theorem                 EXCLUDED by measurement
              (WINDOW_STABLE not met; the predicate is neither an interval in
              scale nor layer-stable at the one height where layers vary)
direction D   Speiser split (near-line winding)    STAYS DOWN-GRADED
              (FLOOR_UNIFORM; the near-line side is not a wall above the
              smallest registered delta)
directions    family-covering / Diophantine (C)     NOT SELECTED
C and E       total positivity / variation (E)      NOT SELECTED
              (both were the WINDOW_PINCHING branch, which did not trigger:
              PINCHING needs gamma_7 and gamma_8 at <= 2 steps AND gamma_1 at
              >= 5 steps; the data has gamma_7 at 1 and gamma_8 at 2 - the
              narrow end holds - but gamma_1 at 4, one step short of the
              anchor bar, so the branch fails on its wide-anchor clause)
```

The C ruling above is the *selector's* precedence read; record 2020 leaves it
standing and adds only that C is the shape the measured data leaves and that
its scale-side debt is now priced and registered (section 5, C1).

## 4. The live obligation

COVER's analytic currency is now an open question again, and that state is the
ruling: the witness cannot be produced by a *scale window* argument (A) and
cannot be produced by a *near-line obstruction* argument (D).  What survives
both measurements is the structure the data actually shows - a per-height,
scale-specific, delta-stable witness with a frozen visible-prime book - which
is exactly the shape direction C is priced for (a family-covering certificate
with explicit Diophantine control of the phase vectors `gamma*log p`).  The
record-2020 desk keeps that ruling and sharpens it: the book is exact at any
point (so pointwise-in-scale certification is finite and carries no book
error), the 0.01 interval currency is gone, and the operative currencies are
the measured healthy *measure* (H = 3.27 at delta = 0.10) and pointwise
certification at the measured cancellation depth.  Record 2023 adds the
granularity of that pointwise currency: the sign field has a band scale
`L_slot` (0.009 .. 0.025 at the three measured slots), the 0.01 grid samples
one step per band, and independent certification cells at a fixed slot should
be spaced `>= L_slot`.

Record 2025 extends that spacing rule to the registered nine and removes
`delta` from it: `L_slot` is a property of the slot (0.008 .. 0.025 over the
readable slots; committed `gamma_6` carries no band at all in this window) and
is unchanged over `delta` in {0.02, 0.05, 0.10}, so the spacing currency is
`L_slot` at any registered delta.  The two EXT slots' L values are read on the
0.002 grid only: their 0.005-grid readings merge sub-0.005 flip doublets and
over-state L (0.01667 / 0.01000 against 0.01000 / 0.00833), and count-based L
readings can only over-state L, so spacings taken from `L_002` stay
conservative.

This does not reorder the mainline.  COVER is downstream of the producer: the
binding obligation remains `D < 0` on the selected healthy owner (map 104,
records 1981/2014/2014a), the F2 gate of record 1997 stands, and no COVER
mechanism may be promoted while the producer's own margin is open.

## 5. Registered follow-up measurements

Two were registered, and both were measurements rather than mechanisms.
Both have now run and are read in record 2022:

```text
M1  the band-edge re-read at dxi = 0.002 (registered in 2016 section 5):
    the comb is a dxi = 0.004 reading of C, the cancelled coordinate whose
    offset is the mass-level offset amplified by |2 + f|, and f reaches
    1.6e+06 at gamma_2 against 8.6e+04 where record 2014 measured the
    amplification - so the comb's fine structure, and at gamma_2 the sign of C
    itself, must be re-read at half resolution before any decision rests on it
    read 2026-09-27: COMB-RESOLUTION-STABLE / EDGE-CONSERVED /
    BAND-REPRODUCED / RP-COMPLETE - zero flips, zero lost, zero appeared,
    zero missing over the 189-cell re-read set, nine of nine censuses
    identical, r in [1.79e-08, 8.87e-05] over the 42 gamma_1/gamma_2 cells
M2  a finer delta grid (0.005, 0.01, 0.02) on the heights whose hosts sit
    inside the five-point grid (registered in 2017 section 5): FLOOR_UNIFORM is
    a statement about delta >= 0.02 and cannot distinguish "no wall" from "a
    wall below 0.02"; M2 is the only registered way to move the near-line
    quantifier
    read 2026-09-27: FLOOR-REFINED-0.005 - all nine slots carry a certified
    host at delta = 0.005 (committed gamma_6 by the registered stage-B sweep,
    at scale 1.00); the floor of record 2017 refines at this resolution
```

The third axis - the scale side - was registered by record 2020 as C1, ran as
record 2021 (pre-registration ae03d687, launched on the lock M2 released), and
is read in record 2023:

```text
C1  the scale ladder: three slots (committed gamma_1, committed gamma_4,
    ext gamma_5), sub-window scale in [0.86, 0.96], grids step 0.005 (21
    cells) and 0.002 (51 cells) per slot
    read 2026-09-27: WINDOW-LADDER - the healthy-indicator flip rate at
    h = 0.002 is 28/150 = 0.187 against the independence reference 0.500,
    dev -9.85 sigma (C indicator -11.12 sigma): adjacent fine cells co-sign
    81 percent of the time, so windows wider than 0.002 exist
    quantitative reading: the small-lag slope step/rate gives a slot-specific
    band scale L (gamma_1 0.025, gamma_4 0.011, ext gamma_5 0.009, pooled
    0.0125), reproduced by both fine grids; the 0.01 grid sits at h ~ L
    (that is why its pooled reading is white-looking), and the per-slot
    classes of record 2020 (gamma_1 smooth, gamma_4 / ext gamma_5
    alternating) reproduce on these independent grids
```

A third, deliberately not registered: the far-delta side.  Two heights lose
their five-point host at `delta = 0.30`, and section 2a of the registration
forbids reading a negative from a five-point grid, so this is an observation
about an unmeasured question - the delta-interval question - not a finding.

Records 2024/2025 then registered and read the two debts record 2023 left
open.  Both are measurements, not mechanisms:

```text
P1  the nine-slot ladder (registered in 2024 section 5): complete the record
    2021 ladder on the six slots C1 did not measure
    read 2026-09-27: LADDER9-PARTIAL - 4 of 6 slots suppress the healthy
    indicator at h = 0.002 below -3 sigma (pooled -11.22 sigma); ext gamma_7
    misses at -2.12 sigma and committed gamma_6 has no flip to read; the
    nine-slot L table is 0.02500 / 0.02000 / 0.01429 / 0.01111 / 0.01250 /
    no-flips / 0.01000 / 0.00833 (committed gamma_1..gamma_6, ext
    gamma_7/gamma_8) plus 0.00909 for the ext gamma_5 control
P2  the delta axis (registered in 2024 section 5): L at delta = 0.02 and
    0.05 on the three C1 slots against the committed delta = 0.10 rows
    read 2026-09-27: L-DELTA-STABLE - ratio exactly 1.0000 (bar 1.25), with
    the C flip count, the healthy flip count and mu_healthy also identical
    across the three deltas; the labeled post-hoc extension shows the whole
    C sign string is delta-invariant between delta = 0.02 and 0.05
```

Both phases were instrument-clean (anchors 5/5 bit-exact, 432/432 book
identification, 18/18 bit-exact determinism, 0 missing).  The P1 reading was
re-derived by a no-measurement replay after its driver defect was caught by an
independent recomputation checker; the first-pass artifact is archived
(`results/2024_ladder9_driver-uncorrected.json`) and the replay measured zero
registered cells.  The two pre-registration errata (a 7.04e-7 transcription of
`gamma_3` and a field name) are in record 2025 section 7 and change no
reading.

Record 2026 then registered the record-2025 section 7 items (i) and (ii)
plus a census, and two of the three are read (record 2027):

```text
U   the sub-0.005 refinement at the three EXT slots (registered in 2026
    section 2)
    read 2026-09-27: U-CONVERGED - the stride-1 C flip count at delta = 0.10
    is identical on the 0.001 and the 0.002 grid at all three slots, so
    L_001 = L_002 exactly and the 0.002 estimator is resolved; the 0.001 grid
    adds no structure, so the count-based L there is final at 0.002-grid
    granularity.  The 0.005-grid understatement is quantified from the fine
    side: count_gain_001_005 = 4 / 2 / 0, i.e. L_005 was high by 1.6667 /
    1.2000 / 1.0000.
S   the five-point string census over the six registered deltas (registered
    in 2026 section 2; zero measured cells)
    read 2026-09-27: STRING-CENSUS-BREAKS - seven of the nine slots carry the
    same five-position C sign string at every registered delta; committed
    gamma_2 breaks from delta = 0.20 and the ext gamma_5 control from
    delta = 0.30, with full five-position coverage on 54/54 comparisons.
    The registered object is the five-point string, which is strictly weaker
    than the fine-string claim of record 2025 section 4.
D   the 51-position fine-string delta comparison at the six P1 slots
    (registered in 2026 section 2)
    NOT READ: launched on the heavy lock and stopped after 81 of its 552
    registered cells.  No verdict; item (i) stays open.
```

U closes the 0.002 estimator at the three EXT slots; S registers the
five-point delta invariance and cannot substitute for D in either direction
(a coarse string can agree while the fine string differs).  Neither promotes a
mechanism.

## 6. Boundaries

The rulings rest on registered decision rules applied to measurements on one
family, one layer per height plus one control, one resolution, eight heights
and `delta >= 0.02`.  They are not theorems about the operator, they do not
cover unmeasured heights or deltas, they cannot be promoted to the map as
numerical facts (map policy), and they change no Lean statement.  Any future
campaign that wants direction A or D back must produce either a new control
that repairs the layer disagreement or a measurement that moves the floor
below the registered grid - not a new reading of the same data.
