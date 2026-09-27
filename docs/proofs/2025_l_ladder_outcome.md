# Record 2025 - COVER layer: L-ladder outcome (P1 nine slots, P2 delta probe)

Date: 2026-09-27.

Status: outcome of the record-2024 pre-registration (commit 977cf384; census
artifact fixed pre-outcome in 8992a602; reading path fixed in ceeda554).  The
chained heavy run executed 2026-09-27 under the heavy lock (P1 log
`build-logs/2024_ladder9.log`, 5510 s; P2 log `build-logs/2024_delta_ladder.log`,
5548 s), plus a reading-only replay of P1 from the committed rows artifact
(log `build-logs/2024_ladder9_replay.log`, 374 s) after the reading-path fix
of section 5.  No theorem, no Lean brick, no gate sign, no promotion, no RH
claim.

## 1. Verdicts

```text
P1  LADDER9-PARTIAL     healthy dev at h = 0.002 (per-slot bar -3 sigma):
                        gamma_2 -6.26, gamma_3 -5.86, gamma_5 -4.37,
                        gamma_8 -3.46 clear the bar; ext gamma_7 misses
                        at -2.12; gamma_6 is degenerate (its window has
                        no host at any lag).  Pooled over the six slots
                        the healthy rate reads 0.140 vs reference 0.365,
                        dev -11.22 sigma (C coordinate: -17.48 sigma).
P2  L-DELTA-STABLE      L(0.002 grid) identical at delta = 0.02 / 0.05 /
                        0.10 - the per-slot flip counts 4 / 9 / 11 are
                        preserved for every delta, stability ratio
                        exactly 1.000 on 3/3 slots (bar 1.25).  Beyond
                        the registered clause: the entire 0.002-grid sign
                        field (sign C, sign D, healthy face) is
                        delta-invariant on all three slots (section 4).
```

Both phases instrument-clean: census A0 True; the five K1 anchors re-measured
fresh at dev_C = dev_D = 0.0; the book identification holds on 432/432 cells
in each phase; forced re-reads bit-identical on 18/18 cells in each phase; 0
missing cells; the P2 delta = 0.10 reference complete.  Two independent
recomputations (section 5) reproduce both readings field-for-field, 0
failures, verdicts re-derived from the registered clauses.

## 2. Instrument record

```text
cells        P1: 300 new (6 slots x 50; the 11-point 0.01 sublattice per
             slot preloaded from the width rows) + 18 determinism re-reads
             + 5 anchors = 323 measurement lines
             P2: 336 new (3 slots x 2 deltas x 56; the five-point
             {0.86..0.94} preloaded from the floor rows and the delta =
             0.10 reference read from the committed C1 rows) + 18 + 5 =
             359 measurement lines
replay       23 measurement lines, all forced re-reads (18 determinism + 5
             anchors); 0 of the 300 registered cells re-measured
anchors      5/5 both phases, dev_C = dev_D = 0.0
np           432/432 both phases against np(s) = #{n prime power <=
             exp(2 s m_pool)} (record 2020); P2 ref_incomplete []
det          18/18 both phases, dev_C = dev_D = 0.0 exactly (scales 0.88 /
             0.90 / 0.92 per slot, forced re-read against the run's own
             first pass)
census A0    both phases True against results/2024_registered_cells.json
             (slot sets and preload arithmetic reproduce from the census)
missing      0 (P1); reference incomplete [] (P2)
cost         P1 5510 s, P2 5548 s (~92 min each; the pre-registration
             budgeted 85-125 min each); replay 374 s
environment  all runs under WSL python from the repository tree
             (record-2024 A5; the committed cover preloads are WSL
             products, and the cross-consistency clauses are within-
             environment clauses)
```

Both rows artifacts are phase cache dumps, not cell lists: besides the
registered rows they carry committed-reuse preload rows the cache loaded from
earlier artifacts (P1: the committed width rows at the wider 0.80-1.00 grid
for all P1 slots, verified bit-identical to `2012_cover_scan_rows_width.json`;
P2: the committed five-point rows for all nine slots at the six floor deltas
0.02-0.30).  The readings only consume the registered slices; a consumer of
the rows files must slice by (layer, gamma, delta, registered scales).

## 3. P1: the nine-slot ladder readings

Pooled over the six slots (registered range [0.86, 0.96], delta = 0.10):

```text
estimator      n_pairs  C flips  C rate  ref_C   dev_C   H flips  H rate  ref_H   dev_H
h=0.002 str1      300    42/300   0.140  0.4902  -17.48    42/300   0.140  0.3648  -11.22
h=0.005 str1      120    36/120   0.300  0.4765   -4.22    34/120   0.283  0.3394   -1.36
h=0.01 str5       276   115/276   0.417  0.4910   -2.51    99/276   0.359  0.3658   -0.25
h=0.01 str2       114    48/114   0.421  0.4778   -1.23    42/114   0.368  0.3424   +0.58
```

Endpoint fractions on the 0.002 grid: mu_healthy = 144/600 = 0.240,
mu_{C>0} = 258/600 = 0.430 (the references are the 2 mu (1 - mu) independence
values).  The registered clause fires: at h = 0.002 the healthy indicator
persists across adjacent cells at -11.22 sigma below independence, and the
suppression is stronger than C1's (three slots, -9.85 sigma in record 2023).
By h = 0.005 the pooled reading is inside 1.4 sigma, and both 0.01-grid
readings are at independence: pooled saturation again sits at h ~ L.

Per slot at h = 0.002 (registered decision rule: per-slot healthy dev <= -3
sigma):

```text
slot (layer)         m_pool  C flips  H flips  ref_H   dev_H   L_002   L_005    ct_eq  rc
committed gamma_2     3.8     5/50     4/50    0.3200   -6.26  0.02000 0.02000  True   True
committed gamma_3     3.8     7/50     9/50    0.4982   -5.86  0.01429 0.01429  True   True
committed gamma_5     3.8     8/50     7/50    0.3542   -4.37  0.01250 0.01250  True   True
committed gamma_6     3.8     0/50     0/50    0.0000    n/a   no-flips no-flips True   *
ext gamma_7           5.4    10/50    10/50    0.3200   -2.12  0.01000 0.01667  False  False
ext gamma_8           5.4    12/50    12/50    0.4488   -3.46  0.00833 0.01000  False  True
```

C-coordinate devs: gamma_2 -8.63, gamma_3 -5.18, gamma_5 -5.31, gamma_7
-2.12, gamma_8 -3.46.

Three per-slot notes.

The degenerate slot: gamma_6 has C < 0 on 61/61 cells of the window (C from
-105.1 to -21701.4) and face NO_HOST on 61/61; zero flips at h = 0.002 and
h = 0.005 on both grids and at h = 0.01 (0/46).  This is a reading, not a
missing estimate: C is sign-constant over the whole registered window, so
L = infinity is reported as no-flips, the independence reference degenerates
to 0.0000 and the dev clause is undefined.  The registered clause treats the
slot as degenerate (neither pass nor fail).  The rc entry marked * above is
False because the resolution-consistency clause compares two L values and
neither exists - a no-L state, not a disagreement.  This is consistent with
the record-2016 width census (gamma_6 carries
the narrowest comb of all heights) and the record-2017 stage-B result (its
only host sits at scale 1.00, outside both registered grids).

The EXT contrast: at both EXT slots the C-flip and healthy-flip position sets
are identical (10/10 at gamma_7, 12/12 at gamma_8, index-for-index), so the
healthy predicate there is C-driven - the D and determinant gates hold
throughout the window.  At the three committed slots the two flip sets differ
(gamma_2: C {1,20,28,38,47} vs H {5,14,37,38}).

The sampling edge, measured exactly: the 0.005-grid count equals the
0.002-grid count on the committed slots and fails on both EXT slots, and the
discriminator is the minimum spacing between consecutive C flips on the fine
grid against the coarse step.  Committed slots: gamma_2 min gap 0.016,
gamma_3 0.006, gamma_5 0.006 - every sign excursion is wider than the 0.005
step, so no pair merges two flips, and every count is preserved.  EXT slots:
gamma_7 carries gaps 0.002 / 0.004 / 0.004 / 0.004 (five excursion
doublets), gamma_8 carries one 0.004 gap - a 0.005 pair can contain both
crossings of an excursion, whose net sign change is then zero, so the coarse
count drops (10 to 6, 12 to 10) and L_005 = 0.005 / rate over-states the band
scale (gamma_7 0.01667 vs 0.01000, gamma_8 0.01000 vs 0.00833).  So the
record-2023 strongest form - equal per-slot flip counts across grids, the C
sign's total variation over the window independent of the lag - holds iff the
coarse step resolves every individual excursion (in this wave: min flip gap
> step; the correlated h/L readings are 0.25 / 0.35 / 0.40 pass against 0.50
/ 0.60 fail).  L_002 is the registered band-scale estimator, and count-based
L estimates can only over-state L (merging reduces the rate), so certification
spacings taken from L_002 are conservative.

The band-scale table now spans nine registered slots (C indicator, 0.002
grid unless noted):

```text
height              L_slot          source
gamma_1  (14.135)   0.02500         record 2023 (C1)
gamma_2  (21.022)   0.02000         this record
gamma_3  (25.011)   0.01429         this record
gamma_4  (27.670)   0.01111         record 2023 (C1)
gamma_5c (30.425)   0.01250         this record
gamma_6  (32.935)   no-flips        this record (C < 0 on 61/61 cells)
gamma_7  (37.586)   0.01000         this record (EXT)
gamma_8  (40.919)   0.00833         this record (EXT)
gamma_5ext (30.425) 0.00909         record 2023 (C1, EXT layer control)
```

The band scale is a fact of the (layer, height) pair: it decreases roughly
monotonically with height over more than a factor of 3 (0.0250 down to
0.0083), with the committed gamma_5 (0.01250) sitting above gamma_4 (0.01111)
and the same height gamma_5 reading 0.01250 on the committed layer vs 0.00909
on the EXT layer.  gamma_6 is the exception in the strong sense (L = infinity
at delta = 0.10 in this window).  Incidental (post-hoc, motivating only):
L * gamma over the seven finite slots of the registered ladder excluding the
ext gamma_5 control reads 0.307 .. 0.420, mean 0.362, and the excluded
control (0.277) refutes a pure L = c / gamma law - the band scale is close
to, but is not, proportional to 1/height.

## 4. P2: the delta axis, and the delta-invariance of the sign field

Registered table (L from the 0.002-grid stride-1 C rate; delta = 0.10 read
from the committed C1 rows, never re-measured):

```text
slot                 delta 0.020   delta 0.050   delta 0.100   ratio
committed gamma_1      0.02500       0.02500       0.02500     1.000
committed gamma_4      0.01111       0.01111       0.01111     1.000
ext gamma_5 (EXT)      0.00909       0.00909       0.00909     1.000
```

The registered verdict L-DELTA-STABLE fires in its strongest possible form:
the flip counts behind L are 4 / 9 / 11 at every delta on their slots - not
merely within the 1.25 ratio bar, exactly equal.  The healthy rate and the
healthy endpoint fraction are also delta-invariant to full precision:
h_rate = 0.08 / 0.26 / 0.22 and mu = 18/51, 28/51, 29/51 for gamma_1 /
gamma_4 / ext gamma_5 at all three deltas.

Beyond the registered clause, the phase artifacts support a stronger
statement, verified cell-by-cell on the shared 51-point 0.002 grid (3 slots x
51 cells x 3 deltas = 153 cells): the sign of C, the sign of D and the
healthy face are identical across delta = 0.02 / 0.05 / 0.10 on every cell
(0 mismatches on any of the three sign fields).  The gate magnitudes move
strongly with delta, so this is a sign-field invariance, not a value
invariance - at gamma_1, scale 0.86: C = -2.0566 / -9.6819 / -66.9366 and
D = 6.4626e+07 / 3.0638e+08 / 2.1204e+09 at delta = 0.10 / 0.05 / 0.02
(ratios x4.71, x6.92 per delta step: a delta exponent between 2.1 and 2.25).

Cell provenance: 46 of the 51 cells per (slot, delta) are measurements of
this wave and 5 are the committed five-point preloads (which are themselves
committed measurements at the matching delta); the delta = 0.10 column is
the committed C1 rows.  So within delta in [0.02, 0.10], the COMB/health
structure at a fixed (layer, height, scale) is a fact of (layer, height,
scale) alone: delta only scales the magnitudes.  This is the sign-field
counterpart of the book identity (record 2020 law 6: the prime book is a
function of (layer, height, scale), independent of delta and dxi) and it
retroactively explains the record-2017 observation that the host scale
windows are delta-stable.

## 5. Errata and reading-path bookkeeping

E1 (pre-registration text, frozen; correction here).  The record-2024
pre-registration section 2 types the gamma_3 ordinate as 25.010858284450420;
the true ordinate is 25.010857580145689.  The run is unaffected: every slot
is resolved from the committed artifacts by its full-precision gamma (the
census carries the artifact values), and the preload/kill logic operates at
1e-9 on those values.  The typed constant appears only in the prereg prose.

E2 (generated artifact defect, fixed pre-outcome in 8992a602).  The first
revision of `results/2024_registered_cells.json` emitted the 6-decimal
lookup keys as the P1 slot gamma values; a numeric consumer comparing at
1e-9 (the checker, the rig) then sees empty slices.  The generator now
carries the full-precision gammas (keeping the rounded keys for preload
lookups); the census A0 check reproduces both ways.  Related bookkeeping in
the same commit: the independent checker initially typed its slot table
(and its gamma_3 slice silently came back empty - the anchor law's fourth
recurrence: tables generated, never typed); it now reads the slots from the
census artifact.

E3 (field-name divergence, frozen prereg text; correction here).  The
record-2024 pre-registration registers the no-flips flag as the single
field `no_flips` (section 3); the reading implements it per grid as
`no_flips_002` and `no_flips_005` (a zero count is a per-grid fact - one
grid can be flip-free while the other is not).  The divergence is
annotational: every no-flips verdict in this record is read from the
grid-suffixed fields, and no registered clause compares the flag across
grids beyond `counts_equal` itself.

B1 (reading-path defect; affects one derived field of the first P1 pass,
hence the archived first-pass artifact).  The reading path's `fine_L`
hard-coded the 0.002 step, so the registered L_005 = 0.005 / rate(0.005
grid) was computed as 0.002 / rate(0.005 grid) - a unit-scale error
invisible to any same-way-wrong reimplementation.  The independent
recomputation checker (written while the heavy chain ran, from the
pre-registration clauses) caught it on the committed smoke reading within
minutes of its first run; commit ceeda554 (07:10) gave `fine_L` an explicit
step, fixed both call sites, re-smoked both phases green and committed the
checker.  The already-running chain (launched 06:50 with the pre-fix code
in memory) then finished P1 at 08:19 and wrote the affected reading; that
artifact is archived as `results/2024_ladder9_driver-uncorrected.json`
(first-pass L_005 values: gamma_2 0.00800, gamma_3 0.00571, gamma_5 0.00500,
gamma_7 0.00667, gamma_8 0.00400).  The outcome reading was re-derived from
the committed rows artifact with zero re-measurement (replay 374 s, log
`build-logs/2024_ladder9_replay.log`), and every L_005 entry in this record
is the corrected one.  P2 is unaffected: its L uses the 0.002 fine grid,
where the pre-fix default was correct.  Both independent recomputations
(rows-only pair walk, verdicts re-derived from the pre-registration text)
now return 0 field failures on both phases.

## 6. What this settles and what it does not

Settles (within the registered scope: range [0.86, 0.96], delta 0.10 for P1,
delta in {0.02, 0.05, 0.10} for P2, the nine committed heights):

- The "windows wider than 0.002 exist" reading now covers nine slots per
  slot: it holds at the -3 sigma bar on four of the six new slots
  (gamma_2 -6.26, gamma_3 -5.86, gamma_5 -4.37, gamma_8 -3.46), pooled
  -11.22 sigma over the six, with the C coordinate at -17.48 sigma.  It does
  not hold at the bar on ext gamma_7 (-2.12: suppressed, 0.200 vs 0.320,
  but not registered-significant), and gamma_6 carries no host at all in
  this window at any lag up to 0.01 - its band scale exceeds the window.
- The band-scale table now spans nine slots (section 3): L is a (layer,
  height) fact, ranging 0.0250 down to 0.0083 over gamma_1..gamma_8, with
  gamma_6 infinite in this window.  The strong small-lag law (equal flip
  counts across grids) holds iff the coarse step resolves every individual
  sign excursion (min consecutive-flip gap > step: 0.006..0.016 on the four
  committed slots, 0.002/0.004 doublets at the two EXT slots); L_002 is the
  registered estimator and count-based L readings can only over-state L.
- The delta axis is inert for the sign field: L, the healthy rate, the
  healthy fraction and every C/D/face sign on the 0.002 grid are identical
  at delta = 0.02 / 0.05 / 0.10 (section 4), while the gate magnitudes
  scale like delta^-2.1..-2.25.  The COMB/health structure is therefore a
  function of (layer, height, scale) alone over the measured delta range.

Does not settle:

- Nothing promotes.  The producer-side binding obligation (D < 0 for the
  off-line zero, map 104) is untouched; the F2 gate stays as sequenced in
  record 1997; the COVER clause remains a measurement, not a theorem; RH is
  not claimed.
- Mechanism: why the bands sit where they sit, why gamma_6's window is
  host-free at delta = 0.10 while its host sits at scale 1.00, and why
  gamma_7's window is weakly suppressed while its neighbours are strong,
  are all open.
- Scope: delta > 0.10 and delta < 0.02 are untested here (the invariance
  is measured over [0.02, 0.10]); scales outside [0.86, 0.96]; heights
  beyond gamma_8; and the observation that L is (layer, height)-dependent
  (gamma_5 committed vs EXT at the same height) is a two-point contrast,
  not a law.

## 7. Follow-up candidates

Three candidates follow from this record's readings.  None was a registered
follow-up at the time this record was written and none was run as part of
it; items (i) and (ii) were registered afterwards as record 2026
(`docs/proofs/2026_ladder_refinement_preregistration.md`, phases
`stringdelta` / `stringcensus` and `ultrafine`), item (iii) is still open:

```text
(i)   the C sign string as a function of delta at fixed (layer, height,
      scale) - the section-4 by-product object, strictly stronger than the
      registered L-stability clause; the natural registration is a string
      comparison over a wider delta set (the preloaded delta columns
      0.15 .. 0.30 exist in the rows artifacts but were never registered)
(ii)  the sub-0.005 resolution question at ext gamma_7 / ext gamma_8 - the
      measured doublets (0.002 / 0.004 gaps) sit at the 0.002-grid limit,
      so a 0.001 grid would test whether L_002 itself is resolved
(iii) L(gamma) with a layer axis - L * gamma is flat-ish (0.307 .. 0.420)
      but the gamma_5 layer pair (committed 0.0125 vs ext 0.0091 at one
      height) blocks a pure gamma law; a registration would sweep L over
      more (layer, height) pairs
```

Item (iii) is not covered by record 2026 either: no wave sweeps L over
further (layer, height) pairs, so the layer axis of the band scale remains
the two-point gamma_5 contrast reported in section 3.

## 8. Artifacts

```text
pre-registration   docs/proofs/2024_l_ladder_preregistration.md (977cf384)
census             results/2024_registered_cells.json (8992a602)
rig                scripts/cover_window_floor_2012.py (phases ladder9 /
                   deltaladder; reading-path fix ceeda554)
census generator   scripts/cover_ladder_cells_2024.py
checker            scripts/check_ladder_readings_2024.py (independent
                   recomputation, json + math only)
rows               results/2024_ladder9_rows.json (replay re-dump)
                   results/2024_delta_ladder_rows.json
readings           results/2024_ladder9.json, results/2024_delta_ladder.json
archived           results/2024_ladder9_driver-uncorrected.json
smoke              results/2024_ladder9[_rows]_smoke.json,
                   results/2024_delta_ladder[_rows]_smoke.json
logs               build-logs/2024_ladder9.log (5510 s),
                   build-logs/2024_delta_ladder.log (5548 s),
                   build-logs/2024_ladder9_replay.log (374 s)
```
