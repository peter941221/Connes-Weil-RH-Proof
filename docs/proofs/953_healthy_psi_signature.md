# 953 - healthy psi/qw identity closure (Wall-A data surface)

Date: 2026-08-10.  Status: definitional closure, WSL-verified axiom-clean.
RH NOT claimed.

## What

New file ConnesWeilRH/Dev/HealthyPsiBricks.lean closes the psi/qw defining
identities on the healthy carrier:

- healthyPsi_sign : PsiSignStatement healthySymbols
    psi F = poleFunctional F - archimedeanTerm F - sum_{global primes} finitePrimeTerm n F
- healthyQWDef : QWDefinitionStatement healthySymbols
    qw f g = psi (convolutionStar f g)

On the healthy carrier `SourceWeilFormData.psi` is *defined* as exactly that
explicit formula, and `qw` is its self-convolution, so both close by definitional
unfolding (the proofs are `unfold`+`simp`; no new math).

## Why it matters (honest scope)

This removes the Wall-A data objection "psi/qw are placeholders / ghosts": on the
healthy carrier the SCB statement now runs against the *real* explicit-formula
`psi`, not `fun _ => 0`.  It is data wiring, NOT the analytic scalar balance:

    poleFunctional(convolutionStar f) - polePairing(f)
        = 2*totalArchimedean(convolutionStar f) + (globalSum - restrictedSum)

That identity (Wall-A 1.4) is genuine analytic content (Weil-explicit formula /
Gamma / vonMangoldt) and stays OPEN.

## Verification

- Build: lake build ConnesWeilRH.Dev.HealthyPsiBricks : 2957 jobs green.
- print axioms healthyPsi_sign / healthyQWDef = [propext, Classical.choice, Quot.sound], 0 sorry, 0 new project axiom.
- Vendor "local changes" warnings = AGENTS 8b red herring (mathlib scripts/).

## Next on the lane

Wall-A 1.4 needs the analytic identity (open).  Wall-B / C1-RH still new math.
