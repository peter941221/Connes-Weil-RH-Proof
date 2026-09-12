# 1373 - Preregistration: CB-PD1 phase calculator (mapping instrument, MODEL evidence)

Date: 2026-09-12. Law 42: this file is committed BEFORE any digit. Law 65:
every number below is MODEL. Instrument class: MAPPING, not verdict — the
rig evaluates the PAPER formulas of
[1372](1372_phase_diagram_total_variant_attack.md) sections 3-4 over locked
grids and locked constant bands. Its output maps where the constant war
stands; it cannot kill or certify candidate CB-PD1 (its formulas contain
unproved placeholders by design). The only kill-power in this prereg is
over the INSTRUMENT ITSELF (gates G1-G3).

## 1. Locked model (the script must implement EXACTLY these formulas)

Fixed inputs per cell: `d`, `lgT` (= log10 t0), `n`, `rho_b`, `C_b`, `C_c`,
`C_8`, `m`. Derived: `R = n + 2`, `t0 = 10^lgT`, `KLOC = 1.5 * 2.13`.

```text
Gain    = exp(-2*d*(1 + rho_b*(n+1)*R)) * ln(t0/(2*pi)) / (2*KLOC*R)
Abs     = C_c^2 * C_b^(2n+2) * t0^(-(4n+2)) / (0.05*(4n+2))
R8err   = C_8 * (1 + ln(t0)) * C_c^2 * C_b^(2n+2) * t0^(-(4n+2))
ratio   = (Gain - Abs - R8err) / (2*m)          [cell = best n in 1..8]
```

Verdict bands (LOCKED): PASS if ratio >= 1.0; MARGINAL if 0.8 <= ratio <
1.0; OPEN if ratio < 0.8. Each cell reports argmax n and its ratio.

Interpretation lock: ratio/PASS cells are MODEL statements about PLACEHOLDER
constants; they are scoreboard entries only. No RH inference, no candidate
survival inference in either direction.

## 2. Locked grids and bands

- d in {0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45}
- lgT in {12, 20, 30, 40, 60, 100, 200, 1000}
- n in {1..8} (R = 3..10), argmax over n per cell
- rho_b in {0, 0.5, 1}
- (C_b, C_c, C_8) in {(1,3,1), (3,10,10), (10,30,100)}
- m in {1, 3}

Reference cell (for controls): d = 0.05, lgT = 13, rho_b = 0,
(C_b, C_c, C_8) = (1, 3, 1), m = 1.

## 3. Gates (instrument validity; a failed gate VOIDS the run, not the candidate)

- G1 NEGATIVE CONTROL (misscaled kernel): recompute the reference cell with
  KLOC x10. The band must DROP (PASS->MARGINAL/OPEN or MARGINAL->OPEN)
  relative to the unscaled reference. If not: INVALID-INSTRUMENT.
- G2 GAIN MONOTONICITY: Gain strictly increasing in lgT at fixed
  (d, n, rho_b, bands, m) — checked numerically at lgT in {12, 20, 30} for
  the reference cell. Any violation: INVALID-INSTRUMENT.
- G3 BRIDGE ORDERING: ratio(rho_b=0) >= ratio(rho_b=0.5) >= ratio(rho_b=1)
  at EVERY cell. Any violation: INVALID-INSTRUMENT.
- G4 (informational, no verdict weight): print the fraction of cells where
  argmax n <= 3 for rho_b = 1 vs rho_b = 0.

## 4. Outputs

- Per-combo phase maps (d x lgT, band + argmax n).
- Frontier table: per (d, combo), the SMALLEST lgT achieving PASS
  ("T1*(d)"), or NONE.
- Seam table: per (lgT, combo), the LARGEST d with OPEN among
  {0.005..0.02} ("d*(lgT)"), or NONE.
- All three gates + DONE sentinel printed at log end. Acceptance is
  log-based: the verdict parser requires the literal final line
  `DONE gates=G1:PASS,G2:PASS,G3:PASS` (or with FAIL entries naming the
  voided gate). Exit codes prove nothing (A2x rule).

## 5. Environment and protocol

WSL2 mirror /home/peter/rh (ext4). Sync the script from the Windows repo,
run `python3` inside WSL, capture stdout to
`docs/proofs/1373_phase_rig_run.log`, and results to
`docs/proofs/1373_phase_rig_results.json`. No shell variables inside
wsl.exe one-liners; read the log back and require the DONE line before
writing the outcome record
[1374](1374_phase_rig_outcome.md). Outcome record contains the tables,
gate results, harvest notes, and memory updates. No post-hoc rescoping of
grids, bands, or formulas (law 42); any model revision requires a NEW
record and a NEW prereg.
