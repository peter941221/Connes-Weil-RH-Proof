/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperLift

/-!
# C1WindowTaperLiftAudit - axiom audit for the component 3 tail leaf

Every declaration of `C1WindowTaperLift` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the taper lift chain.
-/

open ConnesWeilRH.Source.C1WindowTaperLift

#print axioms re_le_norm
#print axioms abs_re_le_norm
#print axioms abs_le_max_abs
#print axioms windowExpGram_energy
#print axioms windowTaperComb_smul
#print axioms windowExpGram_energy_smul
#print axioms windowTaperGram_energy_smul
#print axioms windowTaperGram_energy_continuous
#print axioms windowTaperGram_energy_strict_pos
#print axioms windowTaperGram_gap
#print axioms windowTaperGram_solve_norm_le_of_gap
#print axioms windowTaperCorrection_seminorm_zero_zero_le_of_gap
#print axioms windowTaperCorrection_seminorm_zero_zero_le_of_gap_realPart
#print axioms exists_windowTaperCorrection_seminorm_budget_of_flat_taper
#print axioms strict_taper_correction_of_gap_budget
#print axioms strict_taper_correction_of_gap_budget_realPart
#print axioms windowTaperComb_norm_bound
#print axioms windowTaperComb_norm_bound_of_realPart
#print axioms windowExpGram_energy_strict_pos
#print axioms windowExpGram_energy_continuous
#print axioms windowExpGram_gap
#print axioms windowTaperSliver_bound
#print axioms windowTaperCorrection_apply
#print axioms windowTaperCorrection_support
#print axioms windowTaperCorrection_seminorm_zero_zero_le
#print axioms windowTaperCorrection_seminorm_zero_zero_le_of_realPart
#print axioms matrixEntryNormSum
#print axioms matrix_mulVec_norm_le_entryNormSum
#print axioms windowTaperCorrection_seminorm_zero_zero_le_inverse_entryNormSum
#print axioms windowTaperCorrection_laplaceAt
#print axioms windowTaperCorrection_cost_le
#print axioms windowTaperCorrection_budget
#print axioms exists_windowTaperCorrection_cost_le_one_plus_eps
