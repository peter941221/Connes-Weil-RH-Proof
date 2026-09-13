/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperCore

/-!
# C1WindowTaperCoreAudit - axiom audit for the component 3 core leaf

Every declaration of `C1WindowTaperCore` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the corrected-system chain.
-/

open ConnesWeilRH.Source.C1WindowTaperCore

#print axioms windowTaperGram_quadratic_eq_integral
#print axioms windowTaperGram_quadratic_re
#print axioms windowTaperGramMatrix_mulVec_eq_zero
#print axioms windowTaperGramMatrix_isUnit_of_injective
#print axioms windowTaperGram_solve_mulVec
#print axioms windowExpGram_pairing_eq_integral
#print axioms windowExpGram_pairing_csq
