/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PsiLinearity

/-!
# C1PsiLinearityAudit - axiom audit for the psi additivity bundle

Every declaration of `C1PsiLinearity` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom enters the linearity lemmas. These lemmas supply the
additivity that the 1406 kill (a) MODEL argument assumed; they assert
only linear algebra of the existing `psi` readouts - no sign, no
positivity, no RH content.
-/

open ConnesWeilRH.Source.C1PsiLinearity

#print axioms testAdd_apply
#print axioms testNeg_apply
#print axioms laplaceAt_testAdd
#print axioms laplaceAt_testNeg
#print axioms poleTerm_testAdd
#print axioms poleTerm_testNeg
#print axioms finitePrimeTermComplex_testAdd
#print axioms finitePrimeTermComplex_testNeg
#print axioms finitePrimeTerm_testAdd
#print axioms finitePrimeTerm_testNeg
#print axioms globalPrimeIndexSet_testAdd_subset
#print axioms finitePrimeTerm_eq_zero_of_not_mem
#print axioms finitePrimeSum_testAdd
#print axioms finitePrimeSum_testNeg
#print axioms archimedeanNumerator_testAdd
#print axioms archimedeanNumerator_testNeg
#print axioms archimedeanIntegrand_testAdd
#print axioms archimedeanIntegrand_testNeg
#print axioms archimedeanTerm_testAdd
#print axioms archimedeanTerm_testNeg
#print axioms psi_testAdd
#print axioms psi_testNeg
#print axioms psi_testAdd_convolutionSquare
