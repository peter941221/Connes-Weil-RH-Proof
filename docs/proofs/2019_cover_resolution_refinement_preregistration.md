# Record 2019 - COVER layer: resolution and delta-refinement follow-ups (pre-registration)

Date: 2026-09-27.

Status: pre-registration. Committed before the run. No theorem, no Lean brick,
and no RH claim.

## 1. Why these two passes

They are the three follow-ups the COVER records registered against themselves,
run together:

```text
record 2016 section 5   "KNOT_COMPLEX is measured at one resolution, and the
                        band-edge cells are the ones that must be re-read at
                        dxi = 0.002 before any routing decision rests on the
                        comb.  That re-read is registered as the next step,
                        not performed here."
record 2018 section 5   "the caveat must be re-priced with eps and r measured
                        at the committed layer's band edges (gamma_1/gamma_2),
                        which is a registered follow-up next to the
                        dxi = 0.002 re-read, not a result"
record 2017 section 5   "A finer delta grid (0.005, 0.01, 0.02) on the four
                        heights whose hosts sit inside the five-point grid is
                        the registered way to attack delta -> 0"
```

`M1` below is the 2016/2018 follow-up, `M2` the 2017 one.

**One correction, before the run.**  Record 2017 section 5 says "four heights".
The committed floor map does not contain four such heights: the stage-A
five-point hosts at `delta = 0.02` sit inside the grid on eight slots (the
height table of record 2017 section 2: `gamma_1..gamma_5` committed, the
`gamma_5` EXT control, `gamma_7`, `gamma_8`), and `gamma_6` is the only slot
whose host is outside the five-point grid (it lives at scale 1.00 and was
found by the already-registered sweep).  The mechanics are pinned by
`results/2019_registered_cells.json`, generated from the committed artifacts
by `scripts/cover_followup_cells_2019.py` (section 2.2), and the registered
intent - attack `delta -> 0` where the witness is or can be read - is carried
on all nine slots, `gamma_6` included.  This is a correction of the count in
the outcome prose, not of the registered rule; no threshold moves.

## 2. Registered objects

### 2.1 M1: the resolution re-read

```text
rig          scripts/cover_window_floor_2012.py, record-2019 extension:
             per-cell dxi (the row carries its own dxi and the cache is keyed
             by it), --phase=edges, --phase=floor2, multi-path --resume-from,
             and a fresh (force-measured) K1 anchor pass
cells        results/2019_registered_cells.json, generated FROM the committed
             artifacts (results/2012_scan_rows_width.json and the floor pair)
             by scripts/cover_followup_cells_2019.py - the cell list is
             generated, never typed (the rule of record 2018 section 4)
reading set  the complete delta = 0.10 slices of the nine registered slots
             (8 heights + the gamma_5 EXT layer control): 9 x 21 = 189 cells,
             m1.cells; the registered edge subset (m1.edge_cells, 125 cells)
             is the sub-reading of record 2016 section 5
resolution   dxi = 0.002 for the re-read, paired cell by cell with the
             committed dxi = 0.004 rows
0.004 half   imported from results/2012_scan_rows_width.json through
             --resume-from and read through Cache.peek - NEVER re-measured;
             a missing 0.004 counterpart is an instrument failure, not a
             silent re-measurement
anchors      the five K1 cells re-measured fresh at 0.004 in the same pass
             (force=True), because a cached read of a preloaded cell would be
             a no-op instead of a rig-identity check
```

Why the full slices and not only the edge cells: a lone sign flip inside a
same-sign run also rewrites the band census (it creates or removes a one-cell
band), and the census is the object record 2016's verdict is about.  The
full-slice re-read is a superset of the registered edge set, so it contains
the registered reading; the edge subset is reported separately.

Registered per-slot committed census (generated, from the 0.004 artifact), for
the reproduction clause of section 5:

```text
slot                      C-sign string (21 scales)   bands  widths  edges
committed gamma_1         ++++----+++----+---++          4   4,3,1,2   13
committed gamma_2         +--++--++++-++--++--+          6   1,2,4,2,2,1 19
committed gamma_3         +-+--+-++-++++-++-+++          7   1,1,1,2,4,2,3 18
committed gamma_4         ++++-++++-++-+-+--+-+          7   4,4,2,1,1,1,1 17
committed gamma_5         ----+-++-+-++-+-++-++          7   1,2,1,2,1,2,2 18
committed gamma_6         --------------------+          1   1           2
EXT gamma_5 control       -++-++-+-++++-+-+-uuu          6   2,2,1,4,1,1 16
EXT gamma_7               ---+--------+--+--uuu          3   1,1,1        9
EXT gamma_8               -++--+--+--+------uuu          4   2,1,1,1     13
```

(`u` = uncertified/instrument-limited cell; the 9 `u` cells are the
instrument-limited EXT window-edge cells of record 2016 section 4.)

### 2.2 M2: the delta refinement

```text
new deltas   0.005 and 0.01 (0.02 and above are the committed record-2012
             grid; none of those cells is re-measured)
slots        all nine (the eight five-point slots of record 2017 section 2
             plus the gamma_6 slot), from m2.slots
stage A      the five-point grid {0.86, 0.88, 0.90, 0.92, 0.94} (the
             record-2012 grid, artifact-sourced): 9 x 2 x 5 = 90 cells;
             only its POSITIVES are read (section 2a of record 2012)
stage B      for every slot with NO stage-A host at either new delta, the
             full 21-point sweep at delta = 0.005 (21 cells per slot; the
             five-point cells are cached, so 16 new rows each)
committed    the delta = 0.02 reading of each slot is imported from
             results/2012_cover_delta_floor.json (floor 0.02 at all nine);
             the committed rows are preloaded for the visibility check
```

The `delta = 0.01` column of a slot whose 0.005 sweep is empty stays
**unread** (a five-point negative is not a reading - record 2012 section 2a);
that gap is reported, not papered over.

## 3. Registered derived quantities

M1, per cell, from the pair `(r4, r2)` = (committed 0.004 row, fresh 0.002
row):

```text
conservation   sign of C at both resolutions, 'u' for uncertified:
               CONSERVED   both certified, same sign
               FLIPPED     both certified, opposite sign
               APPEARED    'u' at 0.004, certified at 0.002
               LOST        certified at 0.004, 'u' at 0.002
               REPORTED    'u' at both
C offset       |C_2 - C_4| / |C_2|          (likewise the D offset)
eps            max( |mp_4 - mp_2| / |mp_2| , |mm_4 - mm_2| / |mm_2| )
               the record-2015 section 3 mass-level offset, now read at the
               committed layer's own cells instead of the cone owners
r              C offset / ( eps * |2 + f_2| ),  f_2 = mm/A of the 0.002 row:
               the record-2014 amplification ratio, i.e. the fraction of the
               worst-case factor |2 + f| the pair attains
worst case     eps * |2 + f_2|, reported next to the measured C offset
census         per slot, the C>0 band census at 0.002 (n_bands and the band
               width list) against the committed 0.004 census
```

M2, per slot: `hosts_005`, `hosts_010` (certified host scales among the
measured cells of that delta), `swept_005` (whether the stage-B sweep ran),
and the refined floor = 0.005 if a host was found at 0.005 (stage A or swept),
else 0.01 if a stage-A host at 0.01, else the committed 0.02.

## 4. Registered instrument checks

```text
A1  the five K1 anchors, force-measured at 0.004 in each pass, reproduce the
    committed cells to <= 1e-6 relative on C and on D (bar unchanged from
    record 2012 section 3)
A2  every measured row satisfies the record-2012 K2/K3 certification clause
    (density finite, pins <= 1e-6, cond <= 1e8, spread_D < 1/3, no
    n_primes > 4000 cell certifies)
A3  M1 visibility: for every re-read cell, n_primes(0.002) == n_primes(0.004).
    Record 2017 section 3c established n_primes as a function of
    (layer, height, scale) alone over deltas; the ladder's S3 extended it over
    dxi.  A mismatch here is an instrument failure, not a reading.
A4  M2 visibility: for every fresh cell, n_primes equals the committed value
    for the same (layer, height, scale), imported from
    results/2012_scan_rows_floor.json.  A row in this phase cannot be
    instrument-limited: the committed np map puts every M2 cell below the
    record-1994 cost guard (committed layer 86..332, EXT 1368..2894), so an
    instrument-limited row here is a failure, not a floor.
A5  M1 completeness: every one of the 189 cells has both halves of the pair;
    the reader takes the 0.004 half through Cache.peek, so a missing half is
    reported (n_missing) and fails the verdict.
```

## 5. Registered decision rules

M1 (gated by A1-A5):

```text
EDGE-CONSERVED   zero FLIPPED cells over the 189-cell re-read set
EDGE-FLIPPED     one or more FLIPPED (each reported with both signs, |C| at
                 both resolutions, the C offset and r)
BAND-REPRODUCED  every slot's 0.002 census equals its committed 0.004 census
                 (same n_bands and same width list, in scale order)
BAND-SHIFTED     one or more slots differ (both censuses reported)

overall          COMB-RESOLUTION-STABLE   EDGE-CONSERVED and BAND-REPRODUCED
                 COMB-RESOLUTION-SHIFTED  otherwise
                 COMB-RESOLUTION-INSTRUMENT-FAIL  if a missing pair, a LOST
                 cell, an A3 mismatch or an anchor failure occurs (the census
                 is then not read; the instrument, not the comb, is the
                 finding)
r-table          RP-COMPLETE if eps and f are available on every
                 gamma_1/gamma_2 cell (42 cells), else RP-PARTIAL; the r
                 range is reported next to record 2014 section 5's
                 eps*r table and record 2018 section 4's identification
```

M2 (gated by A1, A2, A4):

```text
FLOOR-REFINED-0.005   every slot has a certified host at delta = 0.005
                      (stage A positive, or the stage-B sweep finds one) -
                      the floor moves to the smallest refined delta
FLOOR-REFINED-0.01    otherwise, every slot has a certified host at 0.005 or
                      0.01, and at least one slot's refined floor is 0.01
FLOOR-REFINED-MIXED   otherwise; the per-slot refined floors are the reading,
                      and every slot reading 0.02 is reported with its 0.005
                      (swept or unread) and 0.01 columns
FLOOR-REFINED-INSTRUMENT-FAIL   anchor, certification or A4 failure
```

Precedence is fixed here, before the run: the clauses are disjoint by
construction (0.005-success implies the second; the second's failure implies
the third), so no verdict depends on clause order.

## 6. Cost structure and driver discipline

```text
M1   189 cells x ~27 s (committed layer) to ~50 s (EXT layer) at
     dxi = 0.002, plus 5 anchors at 0.004:  100-115 min
M2   90 stage-A cells at ~13-25 s, plus 16 new rows per stage-B sweep
     (0 to 9 sweeps), plus 5 anchors at 0.004:  25-65 min

both passes run sequentially under the exclusive resource lock; each
checkpoints every 25 measured rows (2019_band_edges_partial.json,
2019_floor_refined_partial.json) and the final rows are archived; a crashed
pass resumes from its partial through --resume-from with zero re-measurement
(record 2017 section 4's driver rule)
```

## 7. What these passes do and do not settle

```text
settle      whether the comb reading of record 2016 survives its own
            registered refinement: sign conservation cell by cell and the
            band census per slot at dxi = 0.002 against 0.004 - the reading
            the routing ruling "direction A excluded" currently rests on
settle      whether the delta-floor of record 2017 stays at 0.02 or moves to
            0.005/0.01 on the nine registered slots: the near-line side
            measured one grid closer to delta = 0
settle      the measured eps and r at the committed layer's band edges,
            which re-prices record 2016 section 5's resolution caveat with
            the measured attainment instead of the factor 1 (record 2018
            section 5)
does not    prove a theorem or a bound; a 0.002 reading is stability at one
            resolution pair, and the record-2015 ladder showed the mass
            coordinate is still shrinking at the finest measured grids
does not    make the comb reading resolution-converged; it makes it
            resolution-checked.  A SHIFTED verdict would not by itself
            refute the layer - it would move the reading to the 0.002 grid
does not    read delta between 0.005 and 0.02 except at the registered
            positives, does not read delta < 0.005 at all, and says nothing
            about unmeasured heights
does not    touch the binding obligation (D < 0 on the selected healthy
            owner, map 104), the F2 gate of record 1997, or any gate sign
```

## 8. Scope and artifacts

Nine slots (8 heights + 1 layer control), the committed family and layers,
`delta = 0.10` for M1 and `delta in {0.005, 0.01}` for M2, `dxi` 0.004 and
0.002.  This is a measurement of the committed construction, not a theorem
about the operator.  RH is not claimed.

```text
scripts/cover_followup_cells_2019.py        the generated cell lists
results/2019_registered_cells.json          M1 cells + M2 slots (committed)
scripts/cover_window_floor_2012.py          rig (record-2019 extension)
results/2019_band_edges_reading.json        M1 verdict + per-cell pairs
results/2019_band_edges_rows.json           M1 measured rows
results/2019_floor_refined.json             M2 verdict + per-slot table
results/2019_floor_refined_rows.json        M2 measured rows
build-logs/2019_*.log                       run logs
```

See also: 1998 (the rules the scans serve), 2012 (the registration and cost
structure, the K1-K3 instrument), 2014/2014a (the amplification identity), 2015
(the ladder whose S3 discipline A3/A4 extend), 2016 (the comb and the caveat
this re-read is registered against), 2017 (the floor and the quantified
near-line reading M2 refines), 2018 (the eps/r identification the r-table
completes), map 107 (the routing rulings).