# 1374 - CB-PD1 phase calculator outcome: run-1 VOID (G1), amendment, official run-2

Date: 2026-09-13. Consumes the prereg
[1373](1373_phase_rig_prereg.md). Evidence class: MODEL (law 65), mapping
instrument only. This record contains: s1 the run-1 void, s2 the
pre-rerun amendment (locked BEFORE the official rerun, with a commit
boundary), s3 the official run-2 results, s4 harvest and limits.

## 1. Run-1 VOID

Run-1 (log 1373_phase_rig_run.log, first version) printed
`DONE gates=G1:FAIL,G2:PASS,G3:PASS`. Per prereg s3 a failed gate voids
the run. Root cause: the prereg's reference cell (d = 0.05, lgT = 13)
has baseline ratio 0.6631 (band OPEN, argmax n = 1); a KLOC x10 control
cannot drop a band that is already OPEN. This is a prereg DESIGN flaw
(reference cell not required to be non-OPEN), not a formula error; G2/G3
passed and the mapping tables were internally consistent. Per law 42
(no post-hoc rescoping) the prereg stands unedited and the repair goes
through this amendment. Implementation note: run-1's first launch also
hit a float overflow (10^1000) fixed by log-domain evaluation of the
identical formulas before any verdict was read; recorded for provenance.

## 2. Amendment (locked before the official rerun)

- A1: reference cell re-locked to d = 0.05, lgT = 20, rho_b = 0,
  (C_b, C_c, C_8) = (1, 3, 1), m = 1. Run-1's own log (read before this
  amendment was written) shows this cell PASSes at baseline, so the
  control has headroom to drop. The choice is admittedly informed by
  run-1; the gates carry instrument validity only, never candidate
  verdict weight, so no outcome bias enters.
- A2: gate condition sharpened: the control REQUIRES the baseline band
  to be MARGINAL or PASS (order >= MARGINAL) AND the KLOC x10 band
  strictly lower; the KLOC x10 ratio is RECOMPUTED through the formulas
  (kloc parameter), not obtained by dividing the baseline ratio.
- A3: grids, bands, formulas of 1373 s1-s2 are unchanged.

With the reference cell ratios r_base ~ 1.043 (PASS) and
r_scaled ~ 0.104 (OPEN), the amended control has a strict PASS->OPEN
drop. The official rerun is run-2 on the same WSL mirror with the
amended script; its log replaces run-1's log as the official artifact.

## 3. Official run-2 results

Official log: [1373_phase_rig_run.log](1373_phase_rig_run.log); raw cell
grid: [1373_phase_rig_results.json](1373_phase_rig_results.json).
Read back: `DONE gates=G1:PASS,G2:PASS,G3:PASS`. The instrument is valid;
all tables below are MODEL mapping of 1372 s3-s4 formulas with
placeholder constants.

Frontier — smallest lgT (t0 = 10^lgT) whose BEST-n cell reaches PASS,
best constant band (1,3,1), m = 1:

| d | rho_b = 0 | rho_b = 0.5 | rho_b = 1 |
|---|---|---|---|
| 0.005 | 20 | 20 | 20 |
| 0.01 | 20 | 20 | 20 |
| 0.02 | 20 | 30 | 30 |
| 0.05 | 20 | 30 | 40 |
| 0.1 | 30 | 40 | 100 |
| 0.2 | 30 | 100 | 1000 |
| 0.3 | 40 | 200 | NONE<=1000 |
| 0.45 | 60 | 1000 | NONE<=1000 |

Darkest corner (worst band (10,30,100), m = 3, rho_b = 0): all cells
OPEN through lgT = 40; PASS from lgT = 60 for d <= 0.1; from lgT = 100
for d <= 0.3; d = 0.45 MARGINAL at 100, PASS at 200. With rho_b = 1 in
that corner nothing PASSes below lgT = 60, and d = 0.45 stays OPEN even
at lgT = 1000 (ratio 0.04).

Seam: with the best band and m = 1 the only OPEN cells among
d <= 0.02 sit at lgT = 12 (the Platt-Trudgian verification frontier);
from lgT = 20 upward every d >= 0.005 cell is MARGINAL or PASS in that
combo. G4: argmax n <= 3 in 100% of cells across all rho_b — SMALL
splines dominate; the bridge penalty and the R/pi sinc constant both
push toward R = 3.

Reading (model-level, no theorem claimed):

1. The scoreboard concentrates the ENTIRE risk in the named tasks: the
   bridge coefficient rho_b alone moves the far-d frontier by 3-940
   height orders (rho_b = 0 vs 1 at d = 0.3: 40 vs >1000); the constant
   band (best to worst) and multiplicity m move it by ~40 orders.
2. Under the WEAKEST bridge credit (rho_b = 0) the model closes at
   heights as low as 10^20 for near-line d and 10^30-10^60 across all
   d in the best band; the worst band needs 10^60-10^200. These are far
   beyond tables for the worst corners but NOT absurdly so; the war is
   constants, as designed.
3. Far-d behavior INVERTS between bridge scenarios: with full generic
   bridge credit (rho_b = 1) larger d is HARDER (penalty
   e^(2 d (1 + (n+1) R))); with corr-only credit larger d is easier.
   N1 is therefore not a constant-fine-tuning task: it decides the SHAPE
   of the map.

## 4. Harvest and limits

Harvest:

- CB-PD1 has a valid mapping instrument (G1 negative control flips the
  band as required; F-PD1-3 satisfied) and a first phase map over 576
  primary cells x 6 m/band variants (run-1's tables, voided as official
  output, are reproduced bit-wise by run-2 since formulas were
  unchanged; only the control was relocked).
- Task ranking for the next analytic work, by scoreboard leverage:
  N1 (bridge) > N0' (two-sided tail leaf, formal prerequisite for the
  small-R cells the optimizer always picks) > N2 (sinc constant, ~1.5x)
  > N3 (density adapter) > N4 (certificates).

Limits (all MODEL, all to be re-derived as theorems before any formal
consumption):

- Every constant (C_b, C_c, C_8, KLOC, rho_b) is an unproved placeholder
  in a locked band. PASS cells are NOT theorems and OPEN cells do NOT
  kill CB-PD1 (the prereg's mapping-only clause).
- The absorption-negligibility is the PAPER sketch 1372 s3-S3; the R8
  error model and the eta(t0) lower bound are sketches; the killed
  ball's lost on-line gain is ignored (conservative) but the correction
  norm needed to ACHIEVE the anchor at small R is unmodeled — registered
  as gap N5 (anchor-achievability norm bound) in 1372's ledger.
- One implementation fix (float overflow, log-domain evaluation of the
  identical formulas) occurred between the first launch and run-1's
  verdict read; one prereg amendment (reference cell + exact control
  recomputation) occurred between run-1 VOID and run-2, with a commit
  boundary (d210045) before the official digits.
- RH is not claimed; the stop word is unchanged; the frozen namespaces
  and route authorities are untouched.
