/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PsiBlindness

/-!
# C1PsiBlindnessAudit - axiom audit for the odd-annihilation bundle

Every declaration of `C1PsiBlindness` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom enters the blindness lemmas. These lemmas upgrade record
1406 kill (a) from MODEL argument to machine fact; they assert only
annihilation of odd tests by the existing `psi` readouts - no sign, no
positivity, no RH content.
-/

open ConnesWeilRH.Source.C1PsiBlindness

#print axioms test_eq_zero_of_odd
#print axioms laplaceAt_neg_eq_neg_of_odd
#print axioms poleTerm_eq_zero_of_odd
#print axioms finitePrimeTermComplex_eq_zero_of_odd
#print axioms finitePrimeSum_eq_zero_of_odd
#print axioms archimedeanNumerator_eq_zero_of_odd
#print axioms archimedeanIntegrand_eq_zero_of_odd
#print axioms archimedeanTerm_eq_zero_of_odd
#print axioms psi_eq_zero_of_odd
