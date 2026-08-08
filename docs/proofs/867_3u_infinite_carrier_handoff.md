# 867 - Gate 3U precise seam & verified lever (handoff)

Status: boundary audit + a verified analytic lever. Date: 2026-08-07.
Road entry: `canonicalRealGate3UAt` = `|Re Tr(sourceBasis finiteEulerTargetCommutatorResponse)| <= bound`

## What is (and is not) closed

- Route-A **finite-band** Gate is CLOSED on main:
  `bandTerminalGate` (RouteATailBandBound.lean) bounds the diagonal real trace
  by `card*|support| + card*C0*exp(-B/4)*prod`, via
  `inverseLowerFactorPhysicalRenewalTrace_split_bound` +
  `canonicalRealGate3UAt_of_tailNormBound`. Axiom-clean.
- The **infinite-carrier** Gate (docs/860 seam) is NOT closed. It needs the
  trace-class certificate `hfactor := Summable |sourceProlateHVFactor lambda (globalBasis i)|^2`,
  which every prolate-trace thread passes out as an assumption and has zero
  call-sites. Unit-scale it is `P_posHalfLine - transportedSonin` = difference
  of two infinite-rank projections, generically not trace-class (probes 819-824:
  no convergence, outer channel plateaus ~0.62 on transported-Sonin frame).

## Verified lever added this session (axiom-clean, WSL-green)

`ConnesWeilRH/Dev/GammaCriticalLineModulus.lean`:
  - `gamma_critical_line_reflection`:
    `Complex.Gamma (1/2 + I t) * Complex.Gamma (1/2 - I t) = Real.pi / Real.cosh (Real.pi*t)`.
  - `gamma_critical_line_modulus_real`:
    `0 < Real.pi / Real.cosh (Real.pi * t)` for every real t.
  Axioms `[propext, Classical.choice, Quot.sound]`. This splits the archimedean
  sign `Re[Gamma(a+I/2)^4]>=0` into an exact-closed modulus (done) and the
  still-open compact-interval **argument** bound.

## Remaining blocker for "break through 3U" (exact certificates)

| seam | needs | status |
|------|-------|--------|
| infinite trace-class | `hfactor` (prolate remainder trace-class) | not in mathlib; probes say genuinely non-trace at scales; needs new analytic Schatten bound |
| archimedean sign phase | `Re[Gamma(a+I/2)^4]>=0` | mathlib v4.30 has no arg-Gamma / complex Stirling; needs mathlib extension |
| A2 carrier non-trivial | operator/trace-class gate on a `legacy`-free carrier | A2 probe shows the bijection impossible; AGENTS §6 arch-boundary |

## Honest GO / NO-GO

Full "break 3U" (the infinite-carrier gate) is BLOCKED on real analytic results
that mathlib v4.30 does not ship: the prolate-remainder trace-class (`hfactor`)
and the compact-interval Stirling argument bound. Both are the genuine bottom;
they are not a Lean-only gap and not a numeric-toy.

The verified lever (Gamma modulus) is committed to the evidence chain but does
NOT cross 3U by itself. Next concrete options ranked by tractability:
  1. Add/expose a mathlib module with a compact-strip arg-Gamma error bound
     (`Stirling` for complex Gamma), then close the phase window.
  2. Supply `hfactor` via a genuine Schatten estimate on sourceProlateRemainder
     at a physical lambda with power growth (probes say on the true carrier it is
     not free; requires an exceptional damping/decay argument).

