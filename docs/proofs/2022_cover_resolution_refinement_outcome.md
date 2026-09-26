# Record 2022 - COVER layer: resolution-refinement outcome (M1 comb re-read, M2 refined floor)

Date: 2026-09-27.

Status: outcome of the record-2019 pre-registration (committed c9cde2ef,
`docs/proofs/2019_cover_resolution_refinement_preregistration.md`).  Executes
the two registered follow-ups of the COVER track: M1 = the dxi = 0.002 re-read
of the comb (record 2016 section 5) and M2 = the refined delta grid
{0.005, 0.01} on the nine registered slots (record 2017 section 5).  Both
phases ran under the heavy lock on 2026-09-27; the C1 scale ladder (record
2021) was launched the moment the lock was released.  No theorem, no Lean
brick, no gate sign, no promotion, no RH claim.

## 1. Verdict

```text
M1  COMB-RESOLUTION-STABLE   flips 0 of 189 cells, edge flips 0 of 125
     /EDGE-CONSERVED         lost 0, appeared 0, missing 0
     /BAND-REPRODUCED        9 of 9 censuses identical (bands and widths)
     /RP-COMPLETE            r table complete on gamma_1/gamma_2 (42 cells)

M2  FLOOR-REFINED-0.005      every one of the nine slots has a certified
                             host at delta = 0.005
```

Both phases instrument-clean: the five K1 anchors re-measured fresh at
dxi = 0.004 in each phase reproduce their committed cells with dev_C = dev_D
= 0.0 exactly; zero np mismatches; zero missing pairs.

## 2. M1 - the resolution re-read

### 2.1 Instrument record

```text
cells        189 = 9 slots x 21 scales (delta = 0.10), paired with the
             committed dxi = 0.004 rows through Cache.peek (never re-measured)
anchors      5/5 pass, dev_C = dev_D = 0.0 (K1 cells 1994/1994b/1996)
missing      0 of 189 pairs
np           n_primes identical across resolutions on 189/189 (A3)
certification 180/189 rows certified at dxi = 0.002; the 9 uncertified rows
             are the ext-slot cells at scales 0.98..1.00 (see 2.3)
determinism  the four cells of the record-2019 smoke re-read in the full run
             reproduce the smoke bit-identically: dev_C = dev_D = 0.0
             exactly on all four (committed gamma_1, scales 0.80..0.83), with
             equal n_primes
cost         189 cells in 6202 s (about 33 s/cell; the pre-registration
             budgeted 100-115 min - measured 103 min)
```

### 2.2 Readings

Conservation over the certified cells: 180 CONSERVED (126 committed + 54 ext),
9 REPORTED, 0 FLIPPED, 0 LOST, 0 APPEARED.

```text
slot                     0.004 -> 0.002 bands   widths 0.004 -> 0.002
committed gamma_1        4 -> 4                [4, 3, 1, 2]    (identical)
committed gamma_2        6 -> 6                [1, 2, 4, 2, 2, 1]  (identical)
committed gamma_3        7 -> 7                [1, 1, 1, 2, 4, 2, 3]  (identical)
committed gamma_4        7 -> 7                [4, 4, 2, 1, 1, 1, 1]  (identical)
committed gamma_5        7 -> 7                [1, 2, 1, 2, 1, 2, 2]  (identical)
committed gamma_6        1 -> 1                [1]  (identical)
ext gamma_5 (control)    6 -> 6                [2, 2, 1, 4, 1, 1]  (identical)
ext gamma_7              3 -> 3                [1, 1, 1]  (identical)
ext gamma_8              4 -> 4                [2, 1, 1, 1]  (identical)
```

The r table (record 2014a section 4's amplification identity re-priced at the
committed layer's band edges, the registered follow-up of record 2018
section 5):

```text
cells      42 = the complete gamma_1 and gamma_2 slices (21 scales each)
eps        max relative mass offset |mp_4 - mp_2| / |mp| (and mm)
             gamma_1  9.05e-06 .. 5.89e-04
             gamma_2  6.36e-06 .. 8.65e-04
|2 + f|    3.23e+03 .. 1.59e+06
r          c_offset / (eps * |2 + f|):  gamma_1  6.72e-07 .. 3.74e-05
                                         gamma_2  1.79e-08 .. 8.87e-05
           (median 2.45e-06; every r <= 1, so c_offset <= eps |2 + f| holds
           on all 42 cells; the worst-case factor eps|2+f| ranges
           1.04e-01 .. 4.88e+02)
```

Reading: the C offset between the two resolutions is at most 8.9e-05 of the
worst-case amplification bound, i.e. the bound is loose by 4-5 orders at
these cells - the same shape as record 2014a's cone-owner erratum (r there:
1.06e-05 .. 3.69e-03), now measured at the committed layer's own band edges
with eps one order smaller.

### 2.3 The nine REPORTED cells

```text
ext gamma_5 control, ext gamma_7, ext gamma_8, scales 0.98 / 0.99 / 1.00
np 4235 .. 4661 > the record-1959 route guard -> single certified route,
spread exactly 0.0 (F52 shape) -> uncertified at BOTH resolutions
```

They are excluded from the flip count (a cell without two certified readings
cannot conserve a sign).  Their C values move by at most 1.03e-05 relative
between resolutions and their C sign happens to agree at both, but the rig
does not certify them, so this is a reported observation, not a conserved
cell.  The committed layer has no REPORTED cell: 126 of 126 certified and
conserved.

## 3. M2 - the refined delta grid

### 3.1 Instrument record

```text
cells        90 stage-A (9 slots x {0.005, 0.01} x 5 five-point scales)
             + 16 stage-B sweep rows (committed gamma_6, see 3.3)
             + the preloaded floor rows; rows artifact 472 rows
anchors      5/5 pass, dev_C = dev_D = 0.0
A4           0 np mismatches against the committed floor rows;
             0 uncertified rows (no row in this phase is instrument-limited)
cost         1668 s (about 28 min; the pre-registration budgeted 25-65 min)
```

### 3.2 Readings

```text
slot                    refined floor   hosts at 0.005      hosts at 0.01
committed gamma_1       0.005           0.88, 0.90           0.88, 0.90
committed gamma_2       0.005           0.88                 0.88
committed gamma_3       0.005           0.88, 0.90           0.88, 0.90
committed gamma_4       0.005           0.86, 0.88, 0.90     0.86, 0.88, 0.90
committed gamma_5       0.005           0.86, 0.92           0.86, 0.92
committed gamma_6       0.005           1.00                 (none)
ext gamma_5 (control)   0.005           0.90, 0.92, 0.94     0.90, 0.92, 0.94
ext gamma_7             0.005           0.92                 0.92
ext gamma_8             0.005           0.88                 0.88
```

The FLOOR_UNIFORM floor = 0.02 of record 2017 moves to 0.005 on every
registered slot, at the smallest registered refinement (the verdict clause
"every slot has a certified host at delta = 0.005" is satisfied by stage A
everywhere except committed gamma_6, which is satisfied by the registered
stage-B sweep).  Host scales are stage-A stable between 0.005 and 0.01 on
8 of 9 slots; only gamma_6 differs (its 0.005 host is reached by the sweep).

### 3.3 The committed gamma_6 sweep

The stage-B sweep (registered in record 2012 section 2a, triggered by the
measuring loop when a slot has no stage-A host at the new deltas) ran only
for committed gamma_6 - the slot record 2017 found outside the five-point
grid at delta = 0.02.  At delta = 0.005 the sweep over all 21 scales finds a
certified host at scale 1.00, so gamma_6's refined floor is 0.005 too.  The
16 sweep rows are in the rows artifact.

## 4. Errata (pre-registration bookkeeping, frozen text; corrections here)

```text
E1  names: prereg sections 2.1 and 4 cite results/2012_scan_rows_width.json
    and results/2012_scan_rows_floor.json; the committed artifact names carry
    the "cover_" infix (results/2012_cover_scan_rows_width.json,
    results/2012_cover_scan_rows_floor.json).  The rig reads the committed
    names; name-only erratum, no mechanism change.

E2  swept_005 annotation: prereg section 3 defines swept_005 as "whether the
    stage-B sweep ran"; as implemented the reading sets it only when a sweep
    ran and left no 0.005 host (its guard tests the host set for emptiness
    after the sweep's rows have entered the cache).  For committed gamma_6
    the reading therefore reports swept_005 = [] while the sweep ran and
    PRODUCED the host.  The facts are pinned by the log line
    ("floor2 committed:32.935062: no stage-A host at the new deltas -> sweep
    delta=0.005", t = 1377.9 s), by the host scale 1.00 lying outside the
    five-point grid {0.86..0.94}, and by the 16 extra measured rows.  The
    refined floor and the verdict are unaffected.
```

## 5. What this settles and what it does not

Settles, at delta = 0.10 on the nine registered slots over scales 0.80..1.00:

1. The sign(C) field and the band census of the comb are stable under the
   quadrature refinement dxi = 0.004 -> 0.002: every certified pair of the
   189-cell set is conserved (zero flips, zero lost, zero appeared, zero
   missing) and all nine censuses are identical.  At this resolution the
   comb is not a quadrature artifact; record 2018's ladder convergence (the
   two-step mass shrink, D converging at order 2, the inter-route spread
   collapsing at dxi^4) is the mechanism side of the same reading, and the
   measured eps (6.4e-06 .. 8.7e-04 relative) matches that order.

2. The delta-floor of record 2017 (0.02, the thickest registered layer)
   refines to 0.005: a certified host exists at delta = 0.005 on all nine
   slots (eight by stage A, committed gamma_6 by the registered stage-B
   sweep).  The floor reading was a one-resolution reading; at this
   refinement it moves.

3. The record 2018 section 5 caveat is re-priced: r <= 8.87e-05 at the
   committed band edges (RP-COMPLETE), so the amplification bound
   c_offset <= eps |2 + f| holds with 4-5 orders of slack on these cells.

Does not settle: other deltas, delta -> 0, heights beyond the nine slots,
gamma-uniformity of any of this, the far-delta region, the oddness of any
r beyond the measured cells; and nothing about the producer-side gate.  The
nine REPORTED ext cells stay uncertified (F52).  No COVER mechanism is
promoted; map 107 section 4 stands.

## 6. Artifacts

```text
prereg     docs/proofs/2019_cover_resolution_refinement_preregistration.md
           (committed c9cde2ef)
rig        scripts/cover_window_floor_2012.py, --phase=edges / --phase=floor2
cells      results/2019_registered_cells.json (generated, never typed)
M1         results/2019_band_edges_rows.json, 2019_band_edges_reading.json
M2         results/2019_floor_refined_rows.json, 2019_floor_refined.json
smoke      results/2019_band_edges_reading_smoke.json,
           results/2019_floor_refined_smoke.json (and the rows pair)
logs       build-logs/2019_band_edges.log (6202 s),
           build-logs/2019_floor_refined.log (1668 s)
```

Next in this track: the C1 scale ladder (pre-registered record 2021, commit
ae03d687) was launched on the released lock; its reading tests whether the
fair-sampler reading of record 2020 survives at the crossing-resolving grid
h = 0.002.

See also: records 2016 (the comb), 2017 (the floor), 2018 (the ladder
convergence), 2019 (this pre-registration), 2020 (the desk that priced the
remaining currency question and registered C1), 2021 (the C1
pre-registration), map 107.