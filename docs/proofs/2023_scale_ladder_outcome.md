# Record 2023 - COVER layer: scale-ladder outcome (C1)

Date: 2026-09-27.

Status: outcome of the record-2021 pre-registration (commit ae03d687), which
registered C1 of record 2020 section 8.  The run executed on 2026-09-27 under
the heavy lock (log `build-logs/2021_scale_ladder.log`, 2515 s), launched the
moment record 2019's M2 released the lock.  No theorem, no Lean brick, no gate
sign, no promotion, no RH claim.

## 1. Verdict

```text
C1  WINDOW-LADDER      the healthy-indicator flip rate at h = 0.002 sits at
                       ref - 9.85 sigma (C indicator: ref - 11.12 sigma), the
                       registered clause for "windows wider than 0.002 exist"
```

Instrument-clean: the five K1 anchors re-measured fresh reproduce their
committed cells at dev_C = dev_D = 0.0; the record-2020 book identification
holds on 216/216 cells; 0 missing cells; the 9 registered coincident cells
re-measured bit-identically (dev 0.0); the mu resolution clause reads 0.06
sigma.

## 2. Instrument record

```text
cells        150 new (3 slots x 72 grid positions - 33 preloaded per the
             record-2021 section 2 census) + 33 preloaded 0.01-sublattice
             cells through --resume-from (never re-measured)
anchors      5/5 pass, dev_C = dev_D = 0.0
np           216/216 against np(s) = #{n prime power <= exp(2 s m_pool)}
             (record 2020 section 3); 0 mismatches - the identification's
             evidence now covers 216 cells
det          committed gamma_1 and gamma_4, ext gamma_5 at scales 0.88 /
             0.90 / 0.92: dev_C = dev_D = 0.0 on 9/9 (record-2017 pattern)
missing      0 of 216
cost         150 cells + 9 det re-reads + 5 anchors in 2515 s (~42 min; the
             pre-registration budgeted 75-95 min - the committed slots ran
             at ~11-13 s/cell, the ext slot at ~21-23 s/cell, all below the
             smoke's contended readings)
```

## 3. The registered readings (pooled over the three slots)

```text
estimator      n_pairs   C flips  C rate  ref_C   dev_C    healthy  ref_H  dev_H
h = 0.002       150       24/150   0.160   0.4928  -11.12    28/150  0.4999  -9.85
h = 0.005        60       24/60    0.400   0.4861   -1.36    24/60   0.4994  -1.57
h = 0.01 str 5  138       88/138   0.638   0.4933   +3.53    78/138  0.4999  +1.55
h = 0.01 str 2   57       34/57    0.597   0.4875   +1.68    29/57   0.4994  +0.14
mu            mu(0.002 grid) = 0.4902  ->  H = 2.04 in this window
              mu(0.01 sublattice, n = 33) = 0.4848, clause dev 0.06 sigma
              (mu_c_pos = 0.5556)
```

The registered clause fires on the healthy indicator at h = 0.002: 28 flips in
150 pairs against an independence reference of 0.500 - the sign of the host
predicate persists across adjacent 0.002 cells far beyond chance (same-sign
persistence 81 percent; the C coordinate reads 84 percent).  By h = 0.005 the
suppression is mild (-1.6 sigma), and at h = 0.01 the pooled rate is at or
above independence.  The measure reading survives: the 0.002 grid and its own
0.01 sublattice agree on mu to 0.06 sigma, so the fair-sampler estimate of the
healthy measure still stands at the finer grid (H = 2.04 over this window,
which is denser than the 0.80..1.00 pooled read of record 2020, H = 3.27).

## 4. The per-slot classes and the small-lag law

The record-2021 section 3 registration includes a per-slot class table as a
reported reading; the implemented reading emitted only the slot keys (erratum
E1 below).  Recomputed here from the committed rows artifact with the rig's own
pair rule (n = 50 pairs per slot at h = 0.002 and on the 0.002 grid, 20 at
h = 0.005), the per-slot flip rates are:

```text
slot                h = 0.002 C     H     h = 0.005 C     H     h = 0.01 C (str 5)
committed gamma_1   0.080 (-5.9)  0.080   0.200 (-2.7)  0.200   0.370 (-1.7)
committed gamma_4   0.180 (-3.9)  0.260   0.450 (-0.2)  0.450   0.674 (+3.3)
ext gamma_5         0.220 (-3.9)  0.220   0.550 (+0.8)  0.550   0.870 (+5.2)
```

(deviation in sigma against the slot's own endpoint reference.)  The pooled
0.01 reading is the superposition of two classes: committed gamma_1 sits
below independence at every lag (COMB-SMOOTH, as record 2020 classified it),
while committed gamma_4 and the ext gamma_5 control sit far above it at h = 0.01
(COMB-ALTERNATING) - the record-2020 per-slot classes, reproduced here on
independent grids and a different window.

The two fine grids give the same quantity twice:

```text
L_slot := step / flip_rate (small-lag slope, C indicator)
committed gamma_1   0.002 / 0.080  = 0.02500    0.005 / 0.200  = 0.02500
committed gamma_4   0.002 / 0.180  = 0.01111    0.005 / 0.450  = 0.01111
ext gamma_5         0.002 / 0.220  = 0.00909    0.005 / 0.550  = 0.00909
pooled              0.002 / 0.160  = 0.01250    0.005 / 0.400  = 0.01250
```

Both grids agree per slot to the printed digits (healthy indicator: 2 of 3
slots; committed gamma_4 reads 0.0077 vs 0.0111 with only n = 20 pairs at
0.005).  In fact the per-slot flip COUNTS are identical at both grids - 4
(gamma_1), 9 (gamma_4), 11 (ext gamma_5) - over the same 0.1 span in scale
(50 steps of 0.002 against 20 steps of 0.005 per slot), so the C sign's total
variation over the window is resolution-independent at these two grids: the
strongest form of the L agreement, and an instrument check that the two grids
read the same object.  So the flip curve in the small-lag regime is linear in
h with a slot-specific slope 1/L: the sign field has a genuine band scale,
gamma_1's (0.025) twice gamma_4's (0.011), the control's (0.009) smallest.  The
h = 0.01 lag then sits at h/L = 0.40 (gamma_1), 0.90 (gamma_4), 1.10 (ext
gamma_5), and the measured 0.01 rates order exactly that way (0.37, 0.67,
0.87): one lag past the band scale the field is past independence, which is
what "alternating" means at this resolution.  The pooled 0.01 rate near
independence is saturation at h = L, not evidence of a white field.

Consistency with the record-2016 census: the committed gamma_1 census bands
[4, 3, 1, 2] at the 0.01 grid have mean width 2.5 steps = 0.025, equal to the
gamma_1 small-lag L; by gamma_4 the census [4, 4, 2, 1, 1, 1, 1] has mean 2.0
steps (0.020) against a small-lag L of 0.011 - the census is a coarse count
against its resolution floor, and the small-lag slope is the better width
estimate at these scales.

## 5. Errata (pre-registration bookkeeping, frozen text; corrections here)

```text
E1  per-slot class table: record 2021 section 3 registered "the same R ratios
    per slot ... the pooled class is the ruling, the per-slot classes are a
    spread" as a reported reading; the implemented reading emitted the slot
    keys only.  Corrected in section 4 above by recomputation from the
    committed rows artifact with the rig's own pair rule; no re-measurement,
    no threshold touched, no verdict clause affected.
```

## 6. What this settles and what it does not

Settles, at delta = 0.10 on committed gamma_1, committed gamma_4 and the ext
gamma_5 control over scales 0.86..0.96:

1. The healthy sign field is NOT white at the crossing-resolving grid:
   adjacent 0.002 cells co-sign 81 percent of the time (healthy) / 84 percent
   (C) against ~50 percent under independence - the registered WINDOW-LADDER
   clause ("windows wider than 0.002 exist") fires by 9.85 sigma.
2. The window question has a measured scale: the small-lag slope gives a
   slot-specific band scale L (gamma_1 0.025, gamma_4 0.011, ext gamma_5
   0.009, pooled 0.0125), reproduced by both fine grids; the 0.01 grid sits at
   h ~ L, which is why its pooled reading is white-looking and why pointwise
   0.01 sampling carries no interval currency (record 2020's ruling, now with
   its mechanism measured rather than inferred).
3. The healthy measure reading is untouched (mu ladder 0.06 sigma; H = 2.04
   in this window), so the pointwise-in-scale certification requirement stands
   as the operative currency, now with a granularity: independent cells at a
   fixed slot should be spaced >= L_slot.

Does not settle: any mechanism; heights beyond the three slots; deltas other
than 0.10; scales outside [0.86, 0.96]; whether L_slot is stable in delta (it
is a delta = 0.10 reading); the far window; anything about the producer-side
gate.  No COVER mechanism is promoted, the routing rulings of map 107 stand
(direction A excluded, D down-graded, C/E not selected), and map 107
section 4's ordering is unchanged: nothing here touches the producer's
binding `D < 0` obligation.

## 7. Artifacts

```text
prereg     docs/proofs/2021_scale_ladder_preregistration.md (commit ae03d687)
rig        scripts/cover_window_floor_2012.py --phase=ladder
rows       results/2021_scale_ladder_rows.json
reading    results/2021_scale_ladder.json
smoke      results/2021_scale_ladder_smoke.json,
           results/2021_scale_ladder_rows_smoke.json
log        build-logs/2021_scale_ladder.log (2515 s)
```

See also: record 2020 (the desk that registered C1 and the identification),
record 2021 (the C1 pre-registration), record 2022 (the M1/M2 outcome that
released this run's lock), records 2016/2017 (the scans this ladder refines),
map 107.