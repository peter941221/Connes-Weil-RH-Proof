# 869 — Gamma spacing gap + center rigidity (Task 1 status)

Date: 2026-08-07. Status: precise obstacle inventory for the archimedean sign
`Re[Gamma(a + I/2)^4] >= 0`, plus the center facts now closed axiom-clean.

## Goal

Task 1 (``补 compact-strip arg-Gamma/Stirling 误差界 -> 关相位窗``) is to
certify `Re[Gamma(a + I/2)^4] >= 0` on a chosen physical band, by bounding the
fourth-power phase `arg(Gamma(a + I/2))` in `[-pi/8, pi/8]`.

## What mathlib v4.30 actually provides (evidence)

- `Complex.Gamma` exists, with `Gamma_mul_Gamma_one_sub` (reflection),
  `Gamma_ne_zero_of_re_pos`, `GammaSeq_tendsto_Gamma`,
  `Gamma_mul_Gamma_add_half` (duplication), `Gamma_conj`.
  (Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean)
- Real Gamma positivity: `Real.Gamma_pos_of_pos`, `Real.Gamma_nonneg_of_nonneg`.
- `continuousAt_Gamma s hs`/`differentiableAt_Gamma s hs` (pole-free points).
  (Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean:89)
- `Complex.arg`: principal argument with basic same-ray lemmas.

What is **absent** (so the phase window is not closed by the library today):
- `Gamma (1/2) : Real = Real.sqrt pi` (only a comment exists, no theorem:
  `BohrMollerup.lean`).  Because Gamma is non-computable (defined via the
  GammaIntegral), `norm_num` cannot decide `Re[Gamma]` either.
- No complex Gamma Stirling / asymptotic error bound (no `Tendsto` of
  `GammaSeq` with an error rate, no `arg Gamma` asymptotic).
- Therefore no `Complex.arg (Gamma (a + I/2))` phase bound, and no
  `Re[Gamma^4] >= 0` certification on any positive-width band.

Consequence: `Re[Gamma(a+I/2)^4] >= 0` is NOT `norm_num`-decidable and NOT
Stirling-closable in this mathlib; it needs a real mathlib extension
(a compact-strip Stirling error-bound for `log Gamma` or `arg Gamma`).

## What is now proven axiom-clean (this round)

`ConnesWeilRH/Dev/GammaCenterRealSolidity.lean` (new), verified on WSL:
- `gamma_center_one_half_im_zero : (Gamma ((1/2 : Real) : C)).im = 0`
- `gamma_center_one_half_re_pos : 0 < (Gamma ((1/2 : Real) : Complex)).re`
- `gamma_center_one_half_ne_zero : Complex.Gamma ... != 0`
- `critical_line_no_pole t : (1/2) + I*t != -(m:Complex)` (pole-free on Re=1/2)
axioms exactly `[propext, Classical.choice, Quot.sound]`.

These assert the phase `arg(Gamma(1/2 + I t)) = 0` at `t = 0` (real, positive)
and pole-freeness on the whole critical line (so Gamma continuous there).  They
are the center anchor; they do not carry the phase across a positive-width band.

## Route note (should not over-invest here)

AGENTS 850/859/860 already judge the Gamma-phase route as non-canonical: in the
Compact-log carrier the sign IS a theorem (`HS positivity`, `F^F` PSD is positive,
`detector_diagonal_re_nonneg`, A3) and the `weilForm` positivity that the sign
used to encode is re-typed there.  So the follow-up for Automotive-1 is a
mathlib PR adding a compact-strip Stirling arg-Gamma bound; the project-wide sign
does not depend on it anymore for the canonical HS gate.

## Next steps
1. (mathlib upstream) add `Complex` Gamma Stirling
   `abs (Gamma s) / (exp (Re(s) * log Re(s) - ...)) -> 1` + an
   error estimate, then a compact-strip `arg` enclosure.
2. Re-point the band sign to the CompactLog (Theorem A3) proof instead of the
   Gamma phase, per AGENTS 850.
3. Keep `GammaCenterRealSolidity` as the de-risked center anchor for checks.