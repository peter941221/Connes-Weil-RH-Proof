/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyFamilyIdentification

/-!
# Audit for the F1b identification brick

Every declaration is checked to depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no custom axioms.
-/

namespace GevreyFamily.Audit

#print axioms GevreyFamily.sinv
#print axioms GevreyFamily.Bmon
#print axioms GevreyFamily.Bsum
#print axioms GevreyFamily.dBmon
#print axioms GevreyFamily.dBsum
#print axioms GevreyFamily.gfun
#print axioms GevreyFamily.sinv_pos_of_abs_lt
#print axioms GevreyFamily.hasDerivAt_sinv
#print axioms GevreyFamily.hasDerivAt_sinv_pow
#print axioms GevreyFamily.hasDerivAt_Bmon
#print axioms GevreyFamily.hasDerivAt_map_sum
#print axioms GevreyFamily.children_Bmon_sum_eq
#print axioms GevreyFamily.sum_map_children_eq
#print axioms GevreyFamily.Bsum_step_eq
#print axioms GevreyFamily.hasDerivAt_expBsum_step
#print axioms GevreyFamily.Bsum_zero
#print axioms GevreyFamily.Bsum_one
#print axioms GevreyFamily.deriv_iterate_gevreyInner

end GevreyFamily.Audit
