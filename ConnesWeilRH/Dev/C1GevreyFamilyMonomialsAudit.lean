/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyFamilyMonomials

/-!
# Audit for `ConnesWeilRH.Dev.C1GevreyFamilyMonomials`

Every load-bearing theorem is checked to depend on exactly the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no
additional choice-like axioms.
-/

namespace GevreyFamily.Audit

#print axioms GevreyFamily.mem_children_of
#print axioms GevreyFamily.mem_monos_zero
#print axioms GevreyFamily.mem_children_seed
#print axioms GevreyFamily.children_invariant_step
#print axioms GevreyFamily.mono_invariant
#print axioms GevreyFamily.weight_nonneg
#print axioms GevreyFamily.weight_move1
#print axioms GevreyFamily.weight_move2
#print axioms GevreyFamily.weight_move3
#print axioms GevreyFamily.children_weight_sum_le
#print axioms GevreyFamily.Afunc_step
#print axioms GevreyFamily.Afunc_envelope_aux
#print axioms GevreyFamily.children_abs_sum_eq
#print axioms GevreyFamily.sumAbs_step
#print axioms GevreyFamily.sumAbs_le
#print axioms GevreyFamily.monos_one
#print axioms GevreyFamily.Afunc_one

end GevreyFamily.Audit
