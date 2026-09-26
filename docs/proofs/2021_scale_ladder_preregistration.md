# Record 2021 — C1 pre-registration: the scale ladder on three slots

Date: 2026-09-27.

Status: pre-registration, committed before the run.  Registers C1 of record
2020 section 8 (the desk record that priced the direction-C currency) on the
record-2012 rig.  No theorem, no Lean brick, no gate sign, no promotion, no
RH claim.  Committed while the record-2019 phases M1/M2 are still running, so
that the ladder can be launched on the heavy lock the moment M2 (phase
`floor2`) releases it.

## 1. Basis and object

Record 2020 measured the comb as a sequence and ruled:

```text
at delta = 0.10, the 0.01 grid carries no window currency for the healthy
set (sign(C) is white at that grid: pooled flip rate at the independence
reference 2*mu*(1-mu), flat in h = 0.01..0.04), while the healthy MEASURE is
measured and unbiased at the grid scale (mu = 0.306, H = 3.27 pooled; per
height 1.64 .. 21.0).
```

That reading is a statement about the 0.01 grid.  It is *explained* by the
book-crossing budget (single crossings carry up to 0.574|C| in the committed
layer, 0.0686|C| in EXT, with 4 / 227 crossings per 0.01 cell) but it is not
*tested* below 0.01.  C1 is the direct test: the coarse ladder on which the
committed layer's book crossings (step spacing 2.0e-3 - 3.4e-3 in scale) are
individually resolvable, i.e. grids 0.005 and 0.002.

## 2. The registered cells

```text
slots         committed gamma_1 = 14.134725141734695
              committed gamma_4 = 27.67032193035704
              ext gamma_5       = 30.424876125859512
              (gamma_1 is the slot record 2020 read as COMB-SMOOTH; gamma_4
              is the committed slot with the largest measured healthy
              fraction; ext gamma_5 is the EXT slot with the largest)
scale range   [0.86, 0.96]
grids         0.005: 21 points (0.860, 0.865, ..., 0.960)
              0.002: 51 points (0.860, 0.862, ..., 0.960)
delta         0.10   (the registered slice of all prior COVER scans)
dxi           0.004  (the rig default; NOT the M1 refinement target)
```

Cell census: 3 slots x 72 position-grid cells = 216; the two grids share
their 0.01-spaced sublattice (11 points per slot = 33 distinct cells), all of
which exist in the committed record-2012 width rows at this delta and are
preloaded through `--resume-from` (never re-measured): **150 new cells** (10
new in the 0.005 grid + 40 new in the 0.002 grid, per slot).

Pair census at full certification: h = 0.002: 150 pairs (0.002 grid stride
1); h = 0.005: 60 pairs (0.005 grid stride 1); h = 0.01: 57 pairs (0.005
grid stride 2) and 138 pairs (0.002 grid stride 5) - reported as two
estimators of the same distance.  An `INSTRUMENT` cell breaks the adjacency
and drops its pairs; the reading reports the actual pair count per estimator
(no cell in this window is expected to be instrument-limited: the largest
book in the window is ext gamma_5 at 0.96 with np ~ 3.4e+03, below the
record-1959 route guard).

## 3. Derived quantities

```text
per grid (per slot and pooled)   n_certified, mu_healthy = WIRE1 fraction,
                                 mu_c_pos = fraction with C > 0
flip rates R(h)                  C-sign and healthy (WIRE1) indicators,
                                 starters as in the pair census
independence references          ref = 2*mu*(1-mu) with mu the pooled
                                 healthy (or C+) fraction over the endpoints;
                                 sigma = sqrt(p*(1-p)/n_pairs) with p the
                                 OBSERVED rate (as implemented; the bar is
                                 approximate and the record will state the
                                 measured deviations, not only the class)
mu resolution clause             mu(0.002 grid) vs mu(0.01 sublattice-only),
                                 two-proportion sigma = sqrt(p1(1-p1)/n1 +
                                 p2(1-p2)/n2)
per-slot classes                 the same R ratios per slot (n is small:
                                 50/20 pairs per slot per estimator - the
                                 pooled class is the ruling, the per-slot
                                 classes are a spread)
```

## 4. Instrument checks (A1-A5, fixed now)

```text
A1  anchors    the five registered K1 anchors (records 1994/1994b/1996) are
                FORCE re-measured at the process dxi and must reproduce
                their committed references at dev <= 1e-6
A2  book       for every measured cell, n_primes must equal the record-2020
                identification #{n prime power <= exp(2*s*m_pool)} with
                m_pool the family width at s = 1 for that (layer, height) -
                cell by cell, 216 predictions; this also extends the
                identification's evidence by 150 new cells
A3  determinism the registered coincident cells (scales 0.88, 0.90, 0.92 at
                all three slots, preloaded from the committed width rows)
                are re-measured once and must reproduce the preloaded C and
                D BIT-IDENTICALLY (dev exactly 0.0; record-2017 pattern)
A4  coverage   every registered cell must be present in the cache; any
                missing cell is an instrument failure, not a finding
A5  pairing    the sublattice cells enter through the preloaded 0.004 rows;
                a missing counterpart fails loudly (peek never measures)
```

## 5. Decision rules (fixed now, precedence fixed pre-run)

```text
INSTRUMENT-FAIL          any of A1-A5 fails
SAMPLER-ALL-RESOLUTIONS  |R(0.002) - ref| <= 3 sigma and
                         |R(0.005) - ref| <= 3 sigma (healthy indicator,
                         pooled over the three slots) AND the mu resolution
                         clause reads <= 3 sigma
WINDOW-LADDER            R(0.002) <= ref - 3 sigma
ALTERNATING-LADDER       R(0.002) >= ref + 3 sigma
LADDER-MIXED             otherwise
```

Readings, not verdicts: the C-indicator R table, the two h = 0.01 estimators,
the per-slot classes, the mu ladder (0.002 / 0.005 grids), and H = 1/mu.

## 6. Cost

150 new cells at the measured per-cell cost of the record-2019 phases
(committed slots 22.6-25.2 s/cell median in the M1 log; the ext slot runs a
10-20x larger book in this window - the smoke's ext anchor re-reads at
np 1647-2393 cost 53 s each under machine contention - so ~75-95 min total)
under the heavy lock; plus 5 anchors and 3 determinism re-reads.  Launch
command (standard runner, after M2):

```text
scripts/run_resource_aware_task.sh --class heavy --log
  build-logs/2021_scale_ladder.log --
  python3 scripts/cover_window_floor_2012.py --phase=ladder
  --resume-from=results/2012_cover_scan_rows_width.json
```

## 7. What it settles and what it does not

Settles (at delta = 0.10, on three slots, over scale in [0.86, 0.96]):
whether the healthy set's flip rate stays at the independence reference down
to h = 0.002 - i.e. whether the record-2020 fair-sampler reading survives at
the crossing-resolving grid, or whether windows wider than 0.002 exist
(WINDOW-LADDER) or the fine structure alternates (ALTERNATING-LADDER).

Does not settle: other deltas, other heights, the far-delta region, the
gamma-uniformity of any of this, any mechanism, and any sign beyond the
measured cells.  No COVER mechanism may be promoted while the producer's
`D < 0` margin is open (map 107 section 4); nothing here touches that gate.

## 8. Artifacts

```text
rig        scripts/cover_window_floor_2012.py (--phase=ladder; the phase,
           its reading function and the preloading/determinism logic are
           committed together with this record; the module docstring lists
           the phase)
smoke      results/2021_scale_ladder_smoke.json, 2021_scale_ladder_rows_smoke.json
           (committed; the partial checkpoint is transient, as in record
           2019)
run        results/2021_scale_ladder.json, 2021_scale_ladder_rows.json
           (written by the run; the outcome record is separate)
```

Instrument history of the smoke (record-2018 section 4 pattern; all three
passes measured the same cells and agreed bit-for-bit on every forced
re-read, so nothing was misread at any point):

```text
pass 1 (as written)   the reading scanned all three slots while the smoke's
                      measuring loop was truncated to one: every absent cell
                      was reported, A4 fired and the verdict was
                      LADDER-INSTRUMENT-FAIL - the coverage check working,
                      not a measurement.  Repaired: the reading now applies
                      the same smoke truncation.
pass 2 (replay from   the missing-cell branch clears; the verdict stage hit
the pass-1 rows)      a real defect of the mu clause - dev_sigma is None
                      when the clause is degenerate (sigma = 0), and the
                      comparison crashed.  Repaired: a degenerate clause
                      passes only if the two mu agree exactly.
pass 3 (replay)       full path green: anchors 5/5 at dev 0.0, determinism
                      3/3 bit-identical, np 6/6 against the identification,
                      missing none, mu clause executed; verdict
                      SAMPLER-ALL-RESOLUTIONS on a 3-cell degenerate grid.
                      The pass-3 VERDICT IS NOT READABLE AS A FINDING (mu =
                      0 on all three cells of the truncated grid makes every
                      reference degenerate); only the machinery is validated.
```

See also: record 2020 (the desk that registered C1 and the identification
used by A2), record 2019 (M1/M2, running), records 2016/2017 (the scans whose
0.01 grid this ladder refines), map 107.