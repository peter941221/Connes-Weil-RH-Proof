# 886 - In-repo Stirling / log|Gamma| remainder: the Lean construction plan

Date: 2026-08-08 (rev 2). Status: implementation plan, NOT an upstream math library
proposal.  This is how we will prove the arch phase inside this repo, with no external
dependency.

## Goal

Certify, axiom-clean in this repo,  0 <= Re[Gamma(1 + I/2)^4]  by bounding
|arg Gamma(1+I/2)| <= pi/8.  docs/888 gives the analytic reduction to the elementary
series sandwich S in [0.38218, 0.50842].  What Lean needs is a real, in-repo estimate on
log|Gamma(1+I/2)| (magnitude), together with the exact decimals of the constants
(gamma, pi, log, arctan).

## The single in-repo lemma we aim to prove

    | log |Gamma(s)| - ( (Re s - 1/2) log|s| - (Re s - 1) ) |  <=  C(W) / |Im s|,
    for  1/2 <= Re s <= 1,  |Im s| <= W.

with an explicit C(W).

## How to get it entirely from mathlib reals (no library addition)

Components already present in mathlib / the repo and usable as is:

- `Real.eulerMascheroniConstant` + the sandwich
  `eulerMascheroniSeq n < gamma < eulerMascheroniSeq' n` (n=6 gives decimal bounds).
- `Real.pi` decimal bounds (Wallis).
- `Real.log`, `Real.arctan` + `hasDerivAt_arctan` (for the S-sandwich atan values).
- `Complex.Gamma` defined by the Euler integral, `Gamma_gamma_seq`/`GammaIntegral`
  recurrence, `Gamma_conj`, `Gamma_ne_zero_of_re_pos`.

Plain path (self-contained):
 1. Use the Euler partial-product `GammaSeq s n ^ s n! / ∏(s+j)` -> Gamma(s)
    (present in mathlib, `GammaSeq_tendsto_Gamma`) to write log|Gamma(1+I/2)| as the
    limit of a finite log-sum; or use the integral `Gamma = ∫_0^∞ t^(-1) e^-t, dt`.
 2. Add an Euler-Maclaurin / Stirling remainder (log x! - (x+1/2)log x + x - log(2pi)/2)
    using mathlib's own Real.Stirling / log-factorial bounds (already defines `Sterling`
    real sequence + `log_stirlingSeq`).  Mathlib HAS Stirling-for-factorial already.
 3. Bound the phase via the exact atan sandwich S of 888; close |arg|<=pi/8 by
    nlinarith on decimal bounds.

## Cache of in-repo and upstream Stirling primitives

- In mathlib: `Stirling` (real factorial Stirling with effective lower bound
  `sqrt_pi_le_stirlingSeq` / `less_log_factorial_stirling`), real `log`/`arctan`/`gamma`.
- Not present and we build it: the COMPLEX bound log|Gamma| in a compact strip with an
  explicit remainder.  This is the one genuine starting point we must construct in-repo.

## Milestones (each compiles + axiom audit)

 M1: certified atan bounds at 1/2, 1/4, 1/6, 1/8 (from hasDerivAt_arctan + decimals).
 M2: certified gamma (Euler-Mascheroni) and pi decimal windows.
 M3: the log|Gamma(1+I/2)| magnitude two-sided from Stirling, then |arg|<=pi/8.
 M4: Re[Gamma(1+I/2)^4] >= 0 via ArchPhaseWindow.

## Status

- M1-M2 are standard real-analysis; M3 is the substantive construction.
- No RH is claimed until M4 + the rest of the route closes.
