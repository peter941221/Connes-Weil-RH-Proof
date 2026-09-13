/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowMellinIndependence

/-!
# C1WindowMellinIndependenceAudit - axiom audit for the 2c-tail leaf

Every declaration of `C1WindowMellinIndependence` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the independence/nonsingularity/`K_loc` chain.
-/

open ConnesWeilRH.Source.C1WindowMellinIndependence

#print axioms hasDerivAt_exp_mul_coe
#print axioms finiteExp_windowComb_eq_zero
#print axioms continuous_nonneg_windowIntegral_zero
#print axioms windowExpGramMatrix_mulVec_eq_zero
#print axioms windowExpGramMatrix_isUnit_of_injective
#print axioms solvedWindowGram_cost_le_compactLogL2sq
#print axioms windowGramInverse_cost_le_compactLogL2sq
