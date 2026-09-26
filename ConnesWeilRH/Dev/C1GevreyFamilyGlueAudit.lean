/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyFamilyGlue

/-!
# Audit for the F1c shape-and-glue brick

Every declaration is checked to depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no custom axioms.
-/

namespace GevreyFamily.GlueAudit

#print axioms GevreyFamily.sinv_one_le_of_abs_lt
#print axioms GevreyFamily.pow_le_pow_left_real
#print axioms GevreyFamily.exp_pow_nat
#print axioms GevreyFamily.abs_pow_le_one_of_le
#print axioms GevreyFamily.abs_Bmon_le
#print axioms GevreyFamily.abs_map_sum_le
#print axioms GevreyFamily.abs_Bsum_le
#print axioms GevreyFamily.abs_deriv_iterate_gevreyInner_le
#print axioms GevreyFamily.exp_sinv_trade
#print axioms GevreyFamily.sqConst
#print axioms GevreyFamily.sqConst_pos
#print axioms GevreyFamily.abs_deriv_iterate_le_sq
#print axioms GevreyFamily.one_sub_sq_add_le
#print axioms GevreyFamily.iterate_zero_hasDerivAt_ext
#print axioms GevreyFamily.deriv_iterate_gevreyInner_of_one_le_abs
#print axioms GevreyFamily.hasDerivAt_iterate_gevreyInner_ext
#print axioms GevreyFamily.continuous_iterate_gevreyInner
#print axioms GevreyFamily.intervalIntegrable_iterate_gevreyInner

end GevreyFamily.GlueAudit
