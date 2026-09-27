# Record 2027 - COVER layer: record-2026 refinement outcome (U the 0.001 EXT refinement, S the string census; D registered but not run)

Date: 2026-09-27.

Status: outcome of the record-2026 pre-registration (commit 9cf2fca5; the two
pre-freeze defects it records are restated in section 6).  Of the three
registered phases, U and S have run and are committed (32a36029, e5a7657e).
D was launched on the heavy lock and stopped deliberately before completing,
so this record leaves D registered and unread and claims no D verdict.  No
theorem, no Lean brick, no gate sign, no promotion, no RH claim.

## 1. Verdicts

```text
U   U-CONVERGED      the stride-1 C flip count at delta = 0.10 is identical
                     on the 0.001 grid and the 0.002 grid at all three EXT
                     slots, so count_gain_001_002 = 0 and L_001 = L_002
                     exactly.  The pre-registration's structural clause is
                     one-sided (only a positive gain can violate it) and
                     there is no gain, so record 2025 section 3's question is
                     answered in the negative: at the slots whose measured
                     doublets sit at the 0.002-grid limit, the 0.002 grid
                     does NOT merge excursions.  The 0.005 grid does merge
                     them: count_gain_001_005 = 4 / 2 / 0, so the registered
                     L_005 was high by 1.6667 / 1.2000 / 1.0000 while the
                     registered L_002 was exact.
S   STRING-CENSUS-   seven of the nine registered slots carry the same
    BREAKS           five-position C sign string at all six registered
                     deltas.  committed gamma_2 breaks from delta = 0.20 and
                     the ext gamma_5 control from delta = 0.30, with full
                     five-position coverage on 54/54 slot-delta comparisons
                     (n_common = 5 everywhere; no comparison loses a
                     position).
D   NOT READ         registered (6 slots x 2 deltas x 46 new scales = 552
                     new cells), launched, stopped at the operator's request
                     after 81 of the 552 registered cells had been measured
                     (46 at delta = 0.02 and 35 at delta = 0.05, both at
                     committed gamma_2).  No reading exists and no verdict is
                     claimed.
```

U is instrument-clean: census A0 True, the five K1 anchors re-measured forced
at dev_C = dev_D = 0.0, book identification 519/519, determinism 9/9
bit-identical, 0 missing, and both independent recomputations return 0 field
failures and re-derive U-CONVERGED.  S is clean in the weaker sense its
registration allows: it measures nothing, its census A0 is True, its five
anchors pass at dev 0.0 through the cached path, and its determinism clause is
vacuous.  D has no instrument record because it has no reading.

## 2. Instrument record

```text
cells        U: 120 new (3 slots x 40; the 0.005 and 0.002 grids preload
             from the committed floor rows and the committed P1 rows, so
             only the 0.001 grid is measured) + 9 determinism re-reads + 5
             anchors = 134 measurement lines
             S: 0 measured cells by registration (Cache.peek only)
             D: 81 of the 552 registered cells measured, never read
anchors      U 5/5, dev_C = dev_D = 0.0, forced re-measurement
             S 5/5, dev 0.0 through the cached path - an
             artifact-versus-reference check against the 1994 / 1994b /
             1996 cells, not a rig-identity check (pre-registration A1)
np           U 519/519 against np(s) = #{n prime power <= exp(2 s m_pool)}
             (record 2020 section 3), 0 mismatches
             S: no measured cells.  D: not read.
det          U 9/9 bit-identical at dev_C = dev_D = 0.0 exactly (scales 0.88
             / 0.90 / 0.92 per slot, forced re-read)
             S: vacuous (no measurement).  D: never reached.
census A0    U True, S True against results/2026_registered_cells.json
missing      U 0, S 0
cost         U 2966 s (~49.4 min; the pre-registration budgeted 45-100 min)
             D 1033 s (~17 min) at the stop; the registration budgeted
             130-240 min
environment  all runs under the WSL-mirror python3 from the repository tree
             (record-2024 A5: the environment is part of the instrument)
```

The U rows artifact is a phase cache dump, not a cell list: besides the
registered rows it carries the committed reuse rows the cache loaded from
earlier artifacts.  The reading consumes only the registered slices; a
consumer of the rows file must slice by (layer, gamma, delta, registered
scales).

## 3. U: the 0.001 refinement at the three EXT slots

The measured quantity is the stride-1 C flip count on each of the three grids
at delta = 0.10 over scales 0.86 .. 0.96.

```text
slot              height      c_flip 0.005/0.002/0.001  L_005    L_002    L_001
ext gamma_7       37.586178          6 / 10 / 10      0.01667  0.01000  0.01000
ext gamma_8       40.918719         10 / 12 / 12      0.01000  0.00833  0.00833
ext gamma_5 ctl   30.424876         11 / 11 / 11      0.00909  0.00909  0.00909

slot              ratio 001/002  ratio 001/005  min flip gap 0.002 / 0.001 grid
ext gamma_7              1.0000         1.6667             0.0020 / 0.0020
ext gamma_8              1.0000         1.2000             0.0040 / 0.0030
ext gamma_5 ctl          1.0000         1.0000             0.0080 / 0.0070
```

Readings:

- The 0.002 grid is converged at all three slots.  A sign change across a
  0.002 lag spans two 0.001 lags and forces at least one sign change among
  them, so c_flip(0.001) >= c_flip(0.002) holds structurally; the measured
  counts are equal (10 / 10, 12 / 12, 11 / 11), so the finer grid finds no
  excursion the registered grid merged.
- Each grid covers all of its rows: 21 / 51 / 101 certified rows for the
  0.005 / 0.002 / 0.001 grid, with no INSTRUMENT gap and no missing cell.
- h_flip equals c_flip on every grid of every slot, and mu_healthy equals
  mu_C to all printed digits: the healthy predicate at these three EXT slots
  is C-driven, exactly as record 2025 found.
- ext gamma_7 is resolved with zero margin: its minimum consecutive-flip gap
  is 0.0020 on both fine grids, i.e. a doublet sitting exactly at the 0.002
  step, and the 0.001 grid separates it without finding a third crossing.
- The 0.001 grid adds no structure at these slots.  A count-based L can only
  over-state L (record 2025 section 3), and the count is already stable
  between the 0.002 and 0.001 grids, so no further refinement of this window
  at these three slots can lower the certified spacing.
- On the record-2025 L * gamma commentary: L_002 * gamma reads 0.2766 (ctl)
  / 0.3410 (gamma_8) / 0.3759 (gamma_7).  Three points do not pin a law, and
  the layer counterexample of record 2025 section 3 still blocks a pure
  gamma law.

## 4. S: the five-point string census over the six registered deltas

The registered object is the C sign string over the five-point scale set
{0.86, 0.88, 0.90, 0.92, 0.94}, compared position-wise against the delta =
0.02 string, on the nine registered slots at all six registered deltas.  The
phase measures nothing: every cell is a committed floor cell read through
Cache.peek.

```text
slot                   delta  0.020  0.050  0.100  0.150  0.200  0.300  break
committed gamma_2             -+++-  -+++-  -+++-  -+++-  -+-+-  -----  0.200
ext gamma_5 control           --+++  --+++  --+++  --+++  --+++  ---++  0.300
the other seven slots         one and the same five-position string at every
                              registered delta; no break
```

- 54/54 slot-delta comparisons carry full five-position coverage, so no
  comparison is INCOMPLETE anywhere.
- committed gamma_2 is the first to break, at delta = 0.20, and it is the
  only slot with more than one disagreement (3 at delta = 0.30, where its
  five-point string is all-negative).
- the ext gamma_5 control breaks at delta = 0.30 by exactly one position:
  scale 0.90 turns negative.
- the remaining seven slots are position-wise identical at every registered
  delta.

This is the registered form of the record-2025 section 7 item (i) post-hoc
claim, reproduced on the committed cells.  The registered object is STRICTLY
WEAKER than the claim it replaces: record 2025's by-product was the sign field
on the 51-position 0.002 grid, while S registers five positions per slot.  S
therefore does not establish fine-string invariance at any slot; that is
exactly what D was registered to test, and D is unread (section 5).

## 5. D: registered, launched, and left unread

D was registered to close record 2025 section 7 item (i) properly: the C sign
STRING over the certified scales of the 0.002 grid (51 positions) for each of
the six record-2024 P1 slots, at delta = 0.02 and 0.05, against the committed
delta = 0.10 P1 string as reference.

```text
geometry   6 slots x 2 deltas (0.02, 0.05) x 46 new scales = 552 new cells.
           The five anchor scales of each (slot, delta) preload from the
           committed floor rows, and the whole delta = 0.10 reference string
           preloads from results/2024_ladder9_rows.json.
reference  51 positions per slot.  Independently checked here against the
           committed P1 rows: 51 certified, 0 missing, 0 INSTRUMENT gaps on
           all six slots, so the STABLE clause (n_common = n_reference = 51)
           is well posed.
rules      STRING-DELTA-STABLE / BREAKS / INCOMPLETE / INSTRUMENT-FAIL,
           fixed in the pre-registration section 5.
launch     bash scripts/run_resource_aware_task.sh --class heavy --log
           build-logs/2026_string_delta.log -- python3
           scripts/cover_window_floor_2012.py --phase=stringdelta
           --resume-from=results/2012_cover_scan_rows_floor.json,
           results/2024_ladder9_rows.json
stop       1033 s in, to close the wave on the operator's instruction
banked     81 of the 552 registered cells: delta = 0.02 complete at
           committed gamma_2 (46/46) and delta = 0.05 partial (35/46)
checkpoint the runner's phase cache dump, schema-identical to the committed
           rows artifacts (30 fields, every reading-critical key present),
           kept out of tree as build-logs/2026_string_delta_checkpoint.json
resume     append that path to --resume-from to bank the 81 cells
```

No D reading exists: `results/2026_string_delta.json` was never written and
no verdict is claimed.  Neither STRING-DELTA-STABLE nor STRING-DELTA-BREAKS
may be read from the five-point census of section 4 - the two phases compare
different objects (5 positions against 51) and the registered decision rule
for the fine string is untouched.

## 6. Errata and reading-path bookkeeping

Two defects were found by the pre-registration smokes and fixed BEFORE the
pre-registration was committed (they are recorded in its section 6; no
committed artifact is affected):

```text
(a) ladder_census_ok loaded the record-2024 census artifact for every phase,
    so the record-2026 phases saw an empty census block.  It now selects
    results/2026_registered_cells.json for the phases ultrafine /
    stringdelta / stringcensus.
(b) the cached-path anchor guard in anchor_block compared the cache's
    6-decimal-rounded key gamma against the full-precision spec gamma at
    1e-9, so it skipped all five anchors whenever force = False - exactly
    S's registered A1.  It now tests the exact cache key.  U and D force
    their anchors and were never affected; the committed artifacts are
    unaffected, because results/2012_cover_delta_floor.json already carries
    five anchors at dev 0.0.
```

Checker-side repairs, also made pre-commit and needing no erratum: JSON key
normalization (the artifacts mix "0.86" string keys with 0.86 float keys) and
smoke-scope handling for the D deltas (a smoke measures only delta = 0.02).

The independent checker `scripts/check_ladder_readings_2026.py` was
sensitivity-tested before this record was written: injected reading-side
mutations and a rows-side C sign flip each produce a non-zero return code, a
field-failure list and a changed re-derived verdict, and the injected
artifacts were then restored byte-identically (verified through git status).
On the committed artifacts it returns 0 field failures and reproduces
U-CONVERGED and STRING-CENSUS-BREAKS.

Erratum E(2027)-1, a status fact rather than a reading: the pre-registration
section 8 lists `results/2026_string_delta.json` and
`results/2026_string_delta_rows.json` among the expected artifacts.  Neither
exists, because D was stopped before its reading stage.  The registration is
not defective; the phase is simply unrun.

No reading erratum: U and S are both reproduced field-for-field from their
committed artifacts.

## 7. What this settles and what it does not

Settles, within the registered scope (scales 0.86 .. 0.96, dxi = 0.004,
delta = 0.10 for U, the six registered deltas for S):

- U: L_002 is converged at the three EXT slots.  Record 2025 section 3's
  doublet question is closed there - the 0.002 grid does not merge excursions
  at ext gamma_7 or ext gamma_8 - and the minimum flip gap at ext gamma_7 is
  0.0020, so the registered estimator is resolved rather than merely
  conservative.
- U: the registered L_005 of record 2025 was high by 1.6667 (ext gamma_7) and
  1.2000 (ext gamma_8) and exact at the control, so the 0.005-grid
  understatement is now quantified from the fine side as well.
- U: more resolution in this window cannot lower the count-based L at these
  three slots, so the certified spacing there is final at 0.002-grid
  granularity.
- S: on the five-point scale set the C sign string is delta-invariant on
  seven of the nine registered slots across all six registered deltas, and
  the two exceptions are named with their first breaking delta.

Does not settle:

- D's question.  Fine-grid (51-position) delta invariance at a P1 slot is
  unmeasured, and the five-point census is not a substitute in either
  direction: a coarse string can agree while the fine string differs.
- Any mechanism or dynamical origin of the band scale.  The layer axis of L
  (record 2025 section 7 item iii) remains the two-point gamma_5 contrast.
- Structure below 0.001 at ext gamma_7 (unregistered), heights beyond
  gamma_8, deltas beyond the six registered, scales outside [0.86, 0.96],
  the far window, and anything about the producer-side gate.
- Nothing promotes.  The producer's binding obligation D < 0 on the selected
  healthy owner (map 104) is untouched, the F2 gate stays as sequenced in
  record 1997, map 107's routing rulings stand unchanged, the COVER clause
  remains a measurement and not a theorem, and RH is not claimed.

## 8. Follow-up candidates

None of these is registered; each needs a pre-registration before it runs.

```text
(i)   relaunch D.  The registration, rig, census and checker are committed,
      the reference geometry is verified in section 5, and the aborted run
      leaves a resumable checkpoint, so this is one command plus its reading.
      It closes record 2025 section 7 item (i) at registered status on the
      fine grid.
(ii)  the L(gamma) layer axis (record 2025 section 7 item iii, still open):
      sweep L over further (layer, height) pairs to test whether the band
      scale has a layer law or only the two-point contrast.
(iii) sub-0.001 resolution at ext gamma_7.  Its doublet sits exactly at the
      0.0020 gap, so a 0.0005 grid is the only way to test whether a third
      crossing hides inside it.  The 0.001 grid found no structure, so the
      prior is low.
```

## 9. Artifacts

```text
pre-registration   docs/proofs/2026_ladder_refinement_preregistration.md
                   (9cf2fca5)
census             results/2026_registered_cells.json (9cf2fca5)
census generator   scripts/cover_cells_2026.py
rig                scripts/cover_window_floor_2012.py (phases ultrafine /
                   stringdelta / stringcensus; primitives and readings added
                   in 9cf2fca5)
checker            scripts/check_ladder_readings_2026.py (independent
                   recomputation; json + math only)
readings           results/2026_ultrafine.json (32a36029),
                   results/2026_string_census.json (e5a7657e)
rows               results/2026_ultrafine_rows.json (32a36029),
                   results/2026_string_census_rows.json (e5a7657e)
absent             results/2026_string_delta.json,
                   results/2026_string_delta_rows.json (D unread; see erratum
                   E(2027)-1)
checkpoint         build-logs/2026_string_delta_checkpoint.json (gitignored;
                   a resume source, not an evidence artifact)
smoke              results/2026_ultrafine_smoke.json,
                   results/2026_ultrafine_rows_smoke.json,
                   results/2026_string_delta_smoke.json,
                   results/2026_string_delta_rows_smoke.json,
                   results/2026_string_census_smoke.json,
                   results/2026_string_census_rows_smoke.json
logs               build-logs/2026_ultrafine.log,
                   build-logs/2026_string_delta.log (gitignored)
```

See also: record 2023 (the small-lag law and its resolution-independence
form), record 2024 (the nine-slot ladder and the delta axis), record 2025 (the
L-ladder outcome carrying items (i) and (ii) that record 2026 registered),
record 2021 (the C1 pre-registration both descend from), map 107.
