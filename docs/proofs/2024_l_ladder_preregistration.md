# Record 2024 — L-ladder pre-registration: the band scale over the nine slots and the delta axis

Date: 2026-09-27.

Status: pre-registration, committed before the run.  Registers the two
measurement debts left open by record 2023 section 6 ("whether L_slot is
stable in delta"; "heights beyond the three slots") on the record-2012 rig's
new phases `ladder9` (P1) and `deltaladder` (P2).  No theorem, no Lean brick,
no gate sign, no promotion, no RH claim.

## 1. Basis and object

Record 2023 read the record-2021 C1 ladder and found the small-lag law

```text
p_flip(h) = h / L_slot            (C indicator, healthy indicator alike)

L_slot := step / flip_rate, on both fine grids to the printed digits:

    committed gamma_1   0.0250      committed gamma_4   0.0111
    ext gamma_5         0.0091      pooled              0.0125
```

with the strongest instrument form: the per-slot flip COUNTS are identical
at the 0.005 and 0.002 grids (4 / 9 / 11 over the same 0.1 span), so the C
sign's total variation over the window is resolution-independent.  That
reading covers three slots at one delta (0.10).  Two questions were left
open, explicitly NOT registered:

```text
P1  does the ladder reading (healthy flips at h = 0.002 suppressed below
    independence) extend to the remaining six slots of the registered
    nine, and what is L_slot there?
P2  is L_slot stable in delta?  (0.10 is the only delta C1 measured.)
```

Record 2024 registers both, with the decision rules of section 5 fixed
below before any measurement.

## 2. The registered cells

```text
P1  slots   committed gamma_2 = 21.022039638771556
            committed gamma_3 = 25.010858284450420
            committed gamma_5 = 30.424876125859512
            committed gamma_6 = 32.935061587739189
            ext gamma_7       = 37.586178158825671
            ext gamma_8       = 40.918719012147495
    (the six slots C1 did not measure; together with the three C1 slots
    these are the registered nine of record 2017 section 3)

P2  slots   committed gamma_1 = 14.134725141734695
            committed gamma_4 = 27.67032193035704
            ext gamma_5       = 30.424876125859512
    (the three C1 slots, unchanged)
    deltas  0.02 and 0.05 new;  0.10 is the committed C1 reference
```

Common geometry (identical to C1):

```text
scale range   [0.86, 0.96]
grids         0.005: 21 points     0.002: 51 points   (11 shared positions)
dxi           0.004 (the rig default)
```

Cell census, GENERATED from the committed artifacts by
`scripts/cover_ladder_cells_2024.py` into `results/2024_registered_cells.json`
(never typed; preload lists recorded there and re-checked by A0):

```text
P1  preload   0.01-spaced sublattice {0.86, 0.87, ..., 0.96} (11 points)
              per slot, all present in results/2012_cover_scan_rows_width.json
              at delta 0.10 -> new: 10 (0.005 grid) + 40 (0.002 grid) = 50
              distinct cells per slot; 300 total
P2  preload   five-point cells {0.86, 0.88, 0.90, 0.92, 0.94} per (slot,
              delta), all present in results/2012_cover_scan_rows_floor.json
              at both new deltas -> new: 16 + 46 = 62 grid positions = 56
              distinct cells (6 positions shared between the grids) per
              (slot, delta); 336 total
    reference the delta = 0.10 rows for the delta table are the committed
              record-2021 C1 rows (results/2021_scale_ladder_rows.json),
              never re-measured; the census verifies the artifact holds 71
              cells per slot and covers all 61 union positions
```

Pair census at full certification (the record-2021 flip_rate pair rule; an
`INSTRUMENT` cell breaks adjacency and drops its pairs):

```text
P1  h = 0.002 (0.002 stride 1): 50 pairs per slot -> 300 pooled
    h = 0.005 (0.005 stride 1): 20 per slot -> 120
    h = 0.01 (0.005 stride 2): 19 per slot -> 114
    h = 0.01 (0.002 stride 5): 46 per slot -> 276
P2  h = 0.002 (0.002 stride 1): 50 pairs per (slot, delta)
```

## 3. The registered readings

P1, per slot and pooled over the six slots: the four estimator rows of C1
(c_rate, h_rate, the estimator's own endpoint reference 2*mu*(1-mu) and the
deviation in sigma), plus

```text
L_002 := 0.002 / c_rate(0.002 grid, stride 1)
L_005 := 0.005 / c_rate(0.005 grid, stride 1)
counts_equal      c_flip is the same integer at both grids (the
                  resolution-independence form of record 2023 section 4)
resolution_consistent  |L_002 - L_005| / max <= L_AGREE_BAR = 0.25
no_flips          a zero flip count is reported as a no-flips reading
                  (L not finite) - never conflated with a missing estimate
```

P2, per slot over the three deltas: L(delta) from the 0.002-grid stride-1 C
rate (50 pairs at each delta), the healthy rate, mu_healthy per (slot,
delta), and

```text
stability_ratio := max L / min L over (0.02, 0.05, 0.10);  finite iff all
                   three L are finite
```

The record-2023 L values at delta = 0.10 are the reference: the P2 question
is whether the two new deltas land within the registered bar of them (the
reference enters through the committed rows, so it is bit-identical to
record 2023 by construction, not by agreement).

## 4. Instrument checks (all must pass; any failure -> INSTRUMENT-FAIL)

```text
A0  census: the rig's slot sets vs results/2024_registered_cells.json
    (slot-for-slot), the artifact's own new-cell arithmetic reproduced from
    its recorded preload lists, and the P2 reference completeness.  The
    census is generated from the three committed artifacts by
    scripts/cover_ladder_cells_2024.py, never typed.
A1  anchors: the five K1 anchors (1994, 1994b, 1996 gamma_7/gamma_8) re-
    measured forced; pass iff dev_C = dev_D = 0.0 (bit-exact).
A2  book identification: every peeked cell's n_primes equals
    #{n prime power <= exp(2 s m_pool)} with m_pool from slot_book_width
    (record 2020 section 3); any mismatch fails the phase.
A3  determinism: forced re-reads at scales 0.88 / 0.90 / 0.92 of preloaded
    cells (P1: 3 x 6 slots, P2: 3 x 2 new deltas x 3 slots); pass iff
    dev_C = dev_D = 0.0 exactly (record-2021 clause, unchanged).
A4  coverage: every registered grid position must exist in the cache when
    the reading peeks it (missing -> fail); for P2 the reference rows must
    be complete (ref_incomplete empty).
A5  environment: all runs execute under the WSL lossless-mirror python3
    from the repository tree as seen by WSL (the Linux-side runner of every
    committed artifact of this protocol).  NEW clause,
    earned this wave: the identical committed rig measures the same cell at
    C = 0.20427422790089622 under Windows python (CPython 3.13, MSVCRT) vs
    C = 0.20427422790817218 under WSL python (glibc) - relative 3.6e-11 on
    C, 2.0e-12 on D, last-2-ulp libm differences.  The A3 bit-exact clause
    is a within-environment clause; a cross-environment rerun must be read
    as that, not as instrument failure.
```

## 5. Decision rules (fixed now)

```text
P1  LADDER9-UNIFORM      every one of the six slots has h = 0.002 healthy
                         dev <= -3 sigma (its own endpoint reference)
    LADDER9-PARTIAL      some but not all slots do
    LADDER9-NONE         none does
    LADDER9-INSTRUMENT-FAIL   any A0-A5 failure

    A slot whose h = 0.002 estimator is degenerate (no pairs or sigma = 0)
    reads unreadable and does not count as in the window; the fact is
    reported in the reading.  With all slots unreadable the verdict is NONE.

P2  L-DELTA-STABLE       all three slots have a finite stability_ratio
                         <= 1 + L_AGREE_BAR = 1.25
    L-DELTA-SHIFTED      some slot has a finite ratio > 1.25
    L-DELTA-DEGENERATE   no slot exceeds the bar but some slot has no
                         finite ratio (a no-flips window or a missing
                         estimate) - reported, not a stability finding
    L-DELTA-INSTRUMENT-FAIL   any A0-A5 failure
```

Reported regardless of verdict: the per-slot estimator tables (P1), the
per-delta L ladder (P2), pooled rates and references, mu values, np counts,
anchor and determinism cell lists.  The smoke verdicts are NOT readable (the
degenerate 3-cell smoke grids; the record-2021 C1 precedent).

## 6. Smoke history and cost

Both phases were smoke-executed end-to-end before the run committed here:
first pass 06:23-06:28, second pass after the no-flips clause fix 06:40-06:45
(logs `build-logs/2024_ladder9_smoke.log`,
`build-logs/2024_delta_ladder_smoke.log`).  Both passes: anchors 5/5 dev 0.0;
np 6 cells, 0 mismatches; determinism bit-identical (3/3 and 6/6); census A0
True; ref_incomplete empty.  The second pass's L-DELTA-DEGENERATE is the
no-flips clause reporting on a 2-pair grid, not a finding.

Cost estimate from the smoke's per-cell times (~11-14 s committed, ~22-25 s
EXT; C1 measured the same regime):

```text
P1  300 new + 18 det + 5 anchors   ~90 min   (budget 80-120 min)
P2  336 new + 18 det + 5 anchors   ~95 min   (budget 85-125 min)
```

Both run chained on the heavy lock (`scripts/run_resource_aware_task.sh
--class heavy`), P1 on `--resume-from=results/2012_cover_scan_rows_width.json`,
P2 on `--resume-from=results/2012_cover_scan_rows_floor.json`, logs
`build-logs/2024_ladder9.log` and `build-logs/2024_delta_ladder.log`.

Bookkeeping fixed before commit (no errata needed, nothing frozen yet):

```text
(a) the reading path computed L as `0.002 / rate if rate else None`, which
    silently turned a zero flip count into a missing estimate - replaced by
    fine_L/fmt_L with the explicit no-flips reading, and the P2 verdict
    gained the L-DELTA-DEGENERATE clause registered in section 5;
(b) the generator docstring said 67 new cells per (slot, delta) (it is 56)
    and its preload_source strings lacked the `cover_` infix (the record
    2022 erratum E1 defect class, caught at generation).
```

## 7. What this settles and what it does not

Settles, at dxi = 0.004 and scales 0.86..0.96: whether the h = 0.002 healthy
suppression (record 2023: 28/150 = 0.187 vs ref 0.500, -9.85 sigma pooled
over three slots) holds slot-by-slot across the registered nine (P1), the
nine-slot L table (with the resolution-independence counts), and whether
L_slot is delta-stable over {0.02, 0.05, 0.10} on the three C1 slots (P2)
within the registered 25 percent bar.

Does not settle: any mechanism; heights beyond gamma_8; deltas beyond the
three registered; scales outside [0.86, 0.96]; the far window; whether the
band scale has a dynamical origin; anything about the producer-side gate.
No COVER mechanism is promoted, the routing rulings of map 107 stand, and
nothing here touches the producer's binding `D < 0` obligation.  RH is not
claimed.

## 8. Artifacts

```text
prereg      docs/proofs/2024_l_ladder_preregistration.md (this file)
generator   scripts/cover_ladder_cells_2024.py
census      results/2024_registered_cells.json
rig         scripts/cover_window_floor_2012.py --phase=ladder9 / --phase=deltaladder
rows        results/2024_ladder9_rows.json, results/2024_delta_ladder_rows.json
readings    results/2024_ladder9.json, results/2024_delta_ladder.json
smoke       results/2024_ladder9_smoke.json, results/2024_ladder9_rows_smoke.json,
            results/2024_delta_ladder_smoke.json,
            results/2024_delta_ladder_rows_smoke.json
logs        build-logs/2024_ladder9.log, build-logs/2024_delta_ladder.log
            (gitignored)
```

See also: record 2020 (the desk that registered the follow-ups and the book
identification), record 2021 (the C1 pre-registration this extends), record
2022 (the M1/M2 outcome), record 2023 (the C1 outcome carrying the small-lag
law), records 2016/2017 (the scans both ladders refine), map 107.