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

(pending the rerun; this section is completed after run-2's DONE line is
read back)

## 4. Harvest and limits

(pending)
