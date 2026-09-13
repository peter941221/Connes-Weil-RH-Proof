/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PsiSectorSplit

/-!
# C1PsiSectorSplitAudit - axiom audit for the sector-split bundle

Every declaration of `C1PsiSectorSplit` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no
analytic black-box axiom enters the invariance lemmas. These lemmas
complete 1406 kill (a) as machine fact - `psi` is blind to the
reflection-odd sector for every test - asserting only symmetry
structure of the existing `psi` readouts: no sign, no positivity, no
RH content.
-/

open ConnesWeilRH.Source.C1PsiSectorSplit

#print axioms laplaceAt_reflection
#print axioms poleTerm_reflection
#print axioms finitePrimeTermComplex_reflection
#print axioms finitePrimeTerm_reflection
#print axioms mem_globalPrimeIndexSet_reflection_iff
#print axioms globalPrimeIndexSet_reflection_eq
#print axioms finitePrimeSum_reflection
#print axioms archimedeanNumerator_reflection
#print axioms archimedeanIntegrand_reflection
#print axioms archimedeanTerm_reflection
#print axioms psi_reflection
#print axioms evenSym2_apply
#print axioms oddDiff2_apply
#print axioms oddDiff2_odd
#print axioms psi_oddDiff2_eq_zero
#print axioms testAdd_evenSym2_oddDiff2
#print axioms psi_evenSym2
