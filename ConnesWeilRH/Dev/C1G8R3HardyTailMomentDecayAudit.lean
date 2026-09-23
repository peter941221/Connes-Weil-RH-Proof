import ConnesWeilRH.Dev.C1G8R3HardyTailMomentDecay

/-!
# C1G8R3HardyTailMomentDecayAudit

Audit module for `ConnesWeilRH.Dev.C1G8R3HardyTailMomentDecay`.
Verifies all declarations and dependencies compile with standard axioms
`[propext, Classical.choice, Quot.sound]` and zero `sorryAx`.
-/

namespace ConnesWeilRH
namespace Dev

#check @inv_sq_le_inv_sq_of_pos_le
#check @inv_sq_shift_log_le_inv_sq
#check @div_sq_le_div_sq_of_pos_le
#check @div_sq_shift_log_le_div_sq
#check @pointwise_normSq_le_sq_mul_div_sq
#check @riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq

#print axioms inv_sq_le_inv_sq_of_pos_le
#print axioms inv_sq_shift_log_le_inv_sq
#print axioms div_sq_le_div_sq_of_pos_le
#print axioms div_sq_shift_log_le_div_sq
#print axioms pointwise_normSq_le_sq_mul_div_sq
#print axioms riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq

end Dev
end ConnesWeilRH
