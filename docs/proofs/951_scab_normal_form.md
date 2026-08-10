# 951 — SCB normal form: SCAL global-vs-restricted balance reduces to one pole/arch scalar target (axiom-clean)

Date: 2026-08-10. Status: verification note. RH NOT claimed.
Mirror: `cwr-lanb-archlift`. Build: `Dev/ScabNormalForm` 2928 jobs green,
axioms `[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 project axiom.

## What this closes

`SourceScopedArchimedeanContributionBalance` states `restricted = global` with

    restricted = arch(f*f) + polePairing(f) - restrictedSum
    global     = poleFunctional(f*f) - arch(f*f) - globalSum

New `Dev/ScabNormalForm.lean` proves the algebraic normal form:

  `scab_iff_pole_arch_target W f restrictedSum globalSum` :
      restricted = global  <==>  (ScabPoleArchTarget W f globalSum restrictedSum)
  where `ScabPoleArchTarget` is the single scalar identity
      `W.poleFunctional (W.convolutionStar f f) - W.polePairing f =
         2 * W.archimedeanTerm (W.convolutionStar f f) + (globalSum - restrictedSum)`

So the whole SCB collapses (by `ring`/`linarith`) to that ONE explicit-formula
identity — the WEIL-EXPLICIT-FORMULA content of Wall-A sub-step 1.4.  The two
cancelling `arch(f*f)` copies are stripped and the finite-prime sum difference
`globalSum - restrictedSum` is isolated on the right.

This is a normal form / target pinning, NOT a proof of the analytic identity.
It is exactly the turnover that an analytic proof must establish, stated
unambiguously.  On the healthy carrier the `arch(f*f)` there is
`totalArchimedean (healthyConvolutionStar f f)` (via HealthyArchData/950), so
this is the scalar target the healthy SCAB must discharge.  RH NOT claimed.