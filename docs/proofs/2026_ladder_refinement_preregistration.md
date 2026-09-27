# Record 2026 - COVER refinement pre-registration: the sub-0.005 resolution at the EXT slots, the delta axis of the C sign string, and the five-point string census

Date: 2026-09-27.

Status: pre-registration, committed before the run.  Registers the three
refinement debts left open by record 2025 (the section-3 sampling edge and
the section-7 follow-up candidates) on the record-2012 rig's new phases
`ultrafine` (U), `stringdelta` (D) and `stringcensus` (S).  No theorem, no
Lean brick, no gate sign, no promotion, no RH claim.

## 1. Basis and object

Record 2023 read the small-lag C-flip law `p_flip(h) = h / L_slot` and its
strongest instrument form: the per-slot C-flip COUNTS are identical at the
0.005 and 0.002 grids, so the C sign's total variation over the window is
resolution-independent.  Record 2025 section 3 then measured exactly when
that form holds - the discriminator is the minimum scale gap between
consecutive C flips against the coarse step:

```text
committed gamma_2  min flip gap 0.016  counts 5 = 5    count preserved
committed gamma_3  min flip gap 0.006  counts 7 = 7    count preserved
committed gamma_5  min flip gap 0.006  counts 8 = 8    count preserved
ext gamma_7        gaps 0.002/0.004/0.004/0.004        count 10 -> 6 DROPS
ext gamma_8        gap 0.004                          count 12 -> 10 DROPS
```

so at the two EXT slots the 0.005 grid merges whole excursions, its count
drops, and `L_005 = 0.005 / c_rate` over-states the band scale (gamma_7
0.01667 against L_002 = 0.01000; gamma_8 0.01000 against 0.00833).  Record
2025 section 3 states the surviving registered estimator is L_002, notes
that count-based L can only over-state L, and leaves open - explicitly NOT
registered - whether the 0.002 grid is itself converged at those two slots:

```text
U  the EXT doublets sit AT the 0.002-grid limit (gaps 0.002 and 0.004), so
   a 0.001 grid is the first grid that can test whether L_002 is the
   converged band scale there or the 0.002 count is also short
   (record 2025 section 7 item (ii), section 3 sampling edge).
```

Record 2025 section 4 measured a second, independent invariance - the sign
of C, the sign of D and the healthy face identical across delta = 0.02 /
0.05 / 0.10 on every one of the 153 cells of the three C1 slots - and left
it UNREGISTERED (it is a by-product of P2's registration).  Record 2025
section 7 item (i) names the natural registration: the C sign string as a
function of delta at fixed (layer, height, scale):

```text
D  the delta axis of the C sign STRING on the six record-2024 P1 slots,
   at delta = 0.02 and 0.05 against the committed delta = 0.10 string.
S  the same object read as a CENSUS of the committed five-point cells over
   all six registered deltas on all nine slots - zero measurements, and the
   registered replacement for the 4-versus-3 delta comparability that
   record 2025 section 4 had to argue around.
```

Object of all three readings: the sign field of the certified gate
coordinate C, at dxi = 0.004, over the registered scale window
[0.86, 0.96] of the registered nine slots.  Nothing here is a mechanism, a
bound, or a producer premise.

## 2. The registered cells

```text
U  slots   ext gamma_7 = 37.586178158825671
           ext gamma_8 = 40.918719012147495
           ext gamma_5 = 30.424876125859512   (the EXT layer control)
   delta   0.10 (the C1/P1 delta)
   grids   0.005 (21 points) | 0.002 (51) | 0.001 (101)
D  slots   committed gamma_2 = 21.022039638771556
           committed gamma_3 = 25.010857580145689
           committed gamma_5 = 30.424876125859512
           committed gamma_6 = 32.935061587739189
           ext gamma_7, ext gamma_8 (as above)
           (the six record-2024 P1 slots)
   deltas  0.02 and 0.05 new;  0.10 is the committed P1 reference
   grid    0.002 (51 points)
S  slots   the registered nine: committed gamma_1..gamma_6, ext gamma_7,
           ext gamma_8, and the ext gamma_5 control
   deltas  0.02, 0.05, 0.10, 0.15, 0.20, 0.30
   scales  0.86, 0.88, 0.90, 0.92, 0.94 (the five-point cells)
```

Slot ordinates are carried by the census artifact and by the rig modules
(regenerated, never typed from prose - the record-2025 E1 defect class).

Cell census, GENERATED from the committed artifacts by
`scripts/cover_cells_2026.py` into `results/2026_registered_cells.json`
(never typed; the preload lists are recorded there and re-checked by A0):

```text
U  preload   0.005-and-0.002 lattice, 61 positions per slot, all present at
             delta 0.10 in results/2024_ladder9_rows.json (ext gamma_7,
             ext gamma_8) and in results/2021_scale_ladder_rows.json (the
             ext gamma_5 control, a C1 slot).  The census generator reads
             all three committed artifacts for this block; a resume list
             missing the C1 artifact would leave the control with 0 of 61
             preloaded positions and fail A4 loudly.
   new      101 - 61 = 40 cells per slot;  120 total
D  preload   the five-point cells at both new deltas, present in
             results/2012_cover_scan_rows_floor.json
   new      51 - 5 = 46 cells per (slot, delta);  552 total
   reference the delta = 0.10 0.002-grid rows for the six slots are the
             committed record-2024 P1 rows (results/2024_ladder9_rows.json),
             never re-measured; the census verifies the artifact holds all
             51 positions per slot (reference_present)
S  cells     nine slots x six deltas x five scales = 270 committed cells,
             0 measured
```

Pair census at full certification (the record-2021 flip_rate pair rule; an
INSTRUMENT cell breaks adjacency and drops its pairs):

```text
U  0.001 stride 1: 100 pairs per slot   0.001 stride 2 (h=0.002): 99
   0.001 stride 5 (h=0.005): 96         0.001 stride 10 (h=0.010): 91
   0.002 grid stride 1: 50              0.005 grid stride 1: 20
   (all 101/51/21 registered positions are certified at these slots in the
   committed artifacts; a lost position would show as a coverage failure)
D  0.002 grid stride 1: 50 pairs per (slot, delta)
```

## 3. The registered readings

U, per slot and per 0.001/0.002/0.005 grid: the stride-1 C and healthy flip
counts, rates, the grid's mu_healthy and mu_C, `L_step := step /
c_rate(step grid, stride 1)`, plus the stratified table.  The derivation of
the U verdict is the count identity:

```text
count_gain_001_002 := c_flip(0.001 grid, stride 1)
                      - c_flip(0.002 grid, stride 1)
count_gain_001_005 := c_flip(0.001 grid, stride 1)
                      - c_flip(0.005 grid, stride 1)
ratio_001_002      := max(L_001, L_002) / min(L_001, L_002)  (finite only)
min_flip_gap       := the smallest scale gap between consecutive C flips on
                      a grid (the record-2025 section 3 discriminator)
```

Structural note, part of the registration: the 0.002 lattice is a
sublattice of the 0.001 lattice, and a sign change across a coarse lag
forces distinct sign changes across the two fine lags it contains, so
`c_flip(0.001) >= c_flip(0.002)` and `count_gain_001_002 >= 0` ALWAYS.  The
clause is therefore one-sided: it can only be violated by a positive gain,
and `count_gain = 0` is exactly `L_001 = L_002` (equal counts over 100 and
50 pairs give `0.001 / (k/100) = 0.002 / (k/50)`).

D, per (slot, delta): the C sign string over the certified scales of the
0.002 grid (`+` if C > 0 else `-`; an INSTRUMENT or non-finite row is a GAP,
never guessed), the string of the committed delta = 0.10 reference, and

```text
disagreements  positions where the two strings differ over their COMMON
               certified scales (position-wise: a flip count is not a
               string comparison and is not registered here)
n_common       the number of compared positions
only_reference / only_new   the one-sided scales, reported: a coverage loss
               is not a sign change
flips          the internal consecutive sign changes of each string (the
               scale-ordered walk, a gap breaking adjacency)
mu_healthy, mu_C per delta
```

S, per slot: the six five-point strings, the position-wise comparison of
each against the delta = 0.02 string, the first delta at which a
disagreement appears, and the per-delta list of breaking slots.  The phase
measures nothing (Cache.peek only), so no verdict here is a measurement
finding.

## 4. Instrument checks (all must pass; any failure -> INSTRUMENT-FAIL)

```text
A0  census: the rig's registered slot sets and geometry (delta, step,
    deltas, scales) vs results/2026_registered_cells.json, slot-for-slot,
    the artifact's own new-cell arithmetic reproduced from its recorded
    preload lists, and the D reference completeness.  The census is
    generated from the three committed artifacts by
    scripts/cover_cells_2026.py, never typed.
A1  anchors: the five K1 anchors (1994, 1994b, 1996 gamma_7/gamma_8).
    U and D re-measure them forced; pass iff dev_C = dev_D = 0.0
    (bit-exact).  S measures NOTHING, so its A1 is the cached path - an
    artifact-versus-reference check of the preloaded committed cells against
    the 1994/1996/1994b references, not a rig-identity check (and S is only
    admitted with the cached-path anchor guard repaired; see section 6).
A2  book identification: every peeked cell's n_primes equals
    #{n prime power <= exp(2 s m_pool)} with m_pool from slot_book_width
    (record 2020 section 3); any mismatch fails the phase.
A3  determinism: forced re-reads at scales 0.88 / 0.90 / 0.92 of preloaded
    cells; pass iff dev_C = dev_D = 0.0 exactly (record-2021 clause,
    unchanged).  U: 3 x 3 slots.  D: 3 x 2 deltas x 6 slots.  S: none
    (it measures nothing; the clause is vacuous there and is reported so).
A4  coverage: every registered grid position must exist in the cache when
    the reading peeks it (missing -> fail); D additionally fails on a
    reference hole (ref_incomplete non-empty).
A5  environment: all runs execute under the WSL lossless-mirror python3
    from the repository tree as seen by WSL (the Linux-side runner of every
    committed artifact of this protocol).  The A3 bit-exact clause is a
    within-environment clause; a cross-environment rerun must be read as
    that, not as instrument failure (record-2024 A5).
```

## 5. Decision rules (fixed now)

```text
U-CONVERGED        every one of the three slots has count_gain_001_002 = 0
                   (equivalently L_001 = L_002 exactly)
U-UNRESOLVED       some slot has count_gain_001_002 > 0: the 0.001 grid
                   finds sign excursions the 0.002 grid merged, so L_002
                   over-states the band scale there.  The magnitude is
                   reported as count_gain_001_002 and ratio_001_002.
U-DEGENERATE       no slot is UNRESOLVED, but some slot has 0 flips on both
                   the 0.001 and 0.002 grids (the count identity is vacuous
                   there) - reported as a reading, not a stability finding
U-INSTRUMENT-FAIL  any A0-A5 failure

STRING-DELTA-STABLE       every (slot, delta) has 0 disagreements AND every
                          comparison covers all 51 reference positions
STRING-DELTA-BREAKS       some (slot, delta) has at least one disagreement
STRING-DELTA-INCOMPLETE   no disagreement, but some comparison loses a
                          position (n_common < n_reference): the clause is
                          then undecided on the missing positions
STRING-DELTA-INSTRUMENT-FAIL   any A0-A5 failure

STRING-CENSUS-UNIFORM      all nine slots have the same five-position
                           string at all six registered deltas
STRING-CENSUS-BREAKS       some slot disagrees with its delta = 0.02 string
                           at some registered delta with full coverage
STRING-CENSUS-INCOMPLETE   no disagreement, but some comparison loses a
                           position
STRING-CENSUS-INSTRUMENT-FAIL   any A0-A5 failure (including a missing
                           registered cell)
```

Smoke verdicts are NOT readable: the smoke grids are truncated to three
scales (`slot_delta_entry(..., smoke=True, limit=3)`), so U's 3-certified-
row grids and D's 3-position comparison are not the registered geometry.
Only the full runs produce registered verdicts.  Reported regardless of
verdict: the per-slot grid tables, the flip positions and minimum flip gaps,
the count gains and ratios, the per-(slot, delta) strings and comparison
blocks, the per-delta census table, np counts, anchor and determinism lists.

## 6. Smoke history and cost

All three phases were smoke-executed end-to-end under WSL python3 before the
run committed here, and the two measuring phases were re-smoked after the
reading-path change in this section (logs, gitignored:
`build-logs/2026_ultrafine_smoke.log`, `build-logs/2026_string_delta_smoke.log`,
`build-logs/2026_string_census_smoke.log`).  Post-fix results: U np 9 cells /
0 mismatches, determinism 3/3 bit-identical, census A0 True, anchors 5/5
dev 0.0; D np 3 / 0, determinism 3/3, census A0 True, ref_incomplete empty,
anchors 5/5 dev 0.0; S 0 measured cells, census A0 True, anchors 5/5 dev
0.0 through the cached path.  U's `U-DEGENERATE` and D's
`STRING-DELTA-STABLE` in the smoke are 1-slot 3-position artefacts and are
not readings.

Two defects were found and fixed BEFORE this pre-registration was committed
(nothing was frozen yet, so no erratum is needed):

```text
(a) A0 loaded the record-2024 census artifact for every phase, so the three
    new phases saw an empty census block and failed A0 outright (caught by
    the first `stringcensus` smoke, 0.1 s in).  `ladder_census_ok` now
    selects results/2026_registered_cells.json for the 2026 phases.
(b) the cached-path anchor guard in `anchor_block` tested the cache's
    6-decimal-rounded key gamma against the full-precision spec gamma at
    1e-9.  gamma_5 rounds to 30.424876, 1.26e-7 from 30.424876125859512, so
    the guard skipped ALL FIVE anchors whenever no forced re-measurement was
    requested - which is exactly the S phase's registered A1.  The first
    `stringcensus` smoke reported `anchors FAILED` with no anchor line
    printed at all (empty list).  The guard now tests the cache key itself,
    which is the lookup the guard exists to anticipate.  This is the
    "round a height only for lookup keys" rule met from the other side: the
    rounding is correct in the key and wrong in a 1e-9 comparison.  U and D
    were never affected (they force the anchors); the committed 2012 floor
    artifact already carries 5 anchors with dev 0.0, so the defect's history
    is not uniform and no committed artifact is re-derived by this fix.
```

Cost estimate from the smoke's per-cell times (~12 s committed, ~21 s EXT):

```text
U  120 new + 9 determinism + 5 anchors        ~45 min   (budget 45-100 min)
D  552 new + 36 determinism + 5 anchors       ~155 min  (budget 130-240 min)
S  0 new (census only)                        < 1 min
```

The two measuring phases run chained on the heavy lock
(`scripts/run_resource_aware_task.sh --class heavy`): U on
`--resume-from=results/2024_ladder9_rows.json,results/2021_scale_ladder_rows.json`
(its control slot is a C1 slot), D on
`--resume-from=results/2012_cover_scan_rows_floor.json,results/2024_ladder9_rows.json`,
logs `build-logs/2026_ultrafine.log` and `build-logs/2026_string_delta.log`;
S runs unlocked (zero measurements) on
`--resume-from=results/2012_cover_scan_rows_floor.json`.

A pre-flight preload probe was run against the two planned resume lists
before launching (not a smoke: a direct Cache.peek walk over every
registered preload position).  U: 61/61 preloaded and 40 new at each of the
three slots with the P1 + C1 list (the first plan, P1 alone, left the
control at 0/61 - caught here).  D: reference 51/51 and five-point 5/5 at
both new deltas for all six slots with the floor + P1 list.  S: the census
generator's own `missing` list is empty over the nine slots x six deltas x
five scales.

The independent recomputation checker
`scripts/check_ladder_readings_2026.py` is part of this commit: json + math
only, zero imports of the rig, its own pair walk, its own string walk and
its own verdicts, with the slot tables read from the generated census (the
anchor rule).  It is exercised against the three smoke artifacts here (0
field failures on all three) and is the instrument that must return 0 field
failures on the full readings of record 2027.  Writing it BEFORE the run is
the record-2025 lesson applied: the 2024 checker caught a unit-scale defect
within minutes of its first run, which is only possible if the checker
exists while the wave is still open.

## 7. What this settles and what it does not

Settles, at dxi = 0.004 and scales 0.86..0.96: whether the 0.002 grid is
converged at the two EXT slots where record 2025 measured sub-0.005 flip
doublets (U), and whether the C sign field at a fixed (layer, height,
scale) is a function of that triple alone rather than of delta, over
{0.02, 0.05, 0.10} on the six P1 slots (D) and over all six registered
deltas on the nine registered slots (S).

Does not settle: any mechanism or dynamical origin of the band scale;
heights beyond gamma_8; deltas beyond the six registered; scales outside
[0.86, 0.96]; the far window; whether the residual sub-0.001 structure
exists (a 0.0005 grid is not registered here); anything about the
producer-side gate.  U is a resolution statement about ONE delta (0.10) at
THREE slots; its L values are count-based and can only over-state L, so a
negative U result cannot lower L_002, only raise the certified spacing.
No COVER mechanism is promoted, the routing rulings of map 107 stand, and
nothing here touches the producer's binding `D < 0` obligation.  RH is not
claimed.

## 8. Artifacts

```text
prereg      docs/proofs/2026_ladder_refinement_preregistration.md (this file)
generator   scripts/cover_cells_2026.py
census      results/2026_registered_cells.json
checker     scripts/check_ladder_readings_2026.py (json + math only; run
            against the smoke and, in record 2027, the full readings)
rig         scripts/cover_window_floor_2012.py --phase=ultrafine /
            --phase=stringdelta / --phase=stringcensus
rows        results/2026_ultrafine_rows.json,
            results/2026_string_delta_rows.json,
            results/2026_string_census_rows.json
readings    results/2026_ultrafine.json, results/2026_string_delta.json,
            results/2026_string_census.json
smoke       results/2026_ultrafine_smoke.json,
            results/2026_ultrafine_rows_smoke.json,
            results/2026_string_delta_smoke.json,
            results/2026_string_delta_rows_smoke.json,
            results/2026_string_census_smoke.json,
            results/2026_string_census_rows_smoke.json
logs        build-logs/2026_ultrafine.log,
            build-logs/2026_string_delta.log (gitignored)
```

See also: record 2023 (the small-lag law and its resolution-independence
form), record 2024 (the nine-slot ladder and the delta axis this refines),
record 2025 (the L-ladder outcome carrying the sampling edge and the
unregistered sign-field invariance), record 2021 (the C1 pre-registration
both descend from), map 107.
