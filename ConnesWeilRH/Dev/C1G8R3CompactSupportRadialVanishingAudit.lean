/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing

/-!
# Audit of Compact Support Translation Vanishing for Radial Support Projection

Verifies standard axioms: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

namespace ConnesWeilRH
namespace Dev

#check @inner_eq_zero_of_ae_pointwise_zero
#check @inner_eq_zero_of_disjoint_support
#check @mem_orthogonal_of_ae_eq_zero_on_Ici
#check @starProjection_eq_zero_of_ae_eq_zero_on_Ici
#check @norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici
#check @norm_starProjection_translation_eq_zero_of_support_le
#check @riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq

#print axioms inner_eq_zero_of_ae_pointwise_zero
#print axioms inner_eq_zero_of_disjoint_support
#print axioms mem_orthogonal_of_ae_eq_zero_on_Ici
#print axioms starProjection_eq_zero_of_ae_eq_zero_on_Ici
#print axioms norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici
#print axioms norm_starProjection_translation_eq_zero_of_support_le
#print axioms riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq

end Dev
end ConnesWeilRH
