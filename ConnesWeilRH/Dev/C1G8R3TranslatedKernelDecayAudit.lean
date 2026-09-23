/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay

/-!
# Audit of Translated Kernel Radial Tail Reduction to Riemann Hypothesis

Verifies standard axioms: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

namespace ConnesWeilRH
namespace Dev

#check @sourceFourierSupportProjection_apply
#check @norm_sourceFourierSupportProjection
#check @sourceFourierSupportProjection_translation_norm_eq
#check @sourceFourierSupportProjection_translation_normSq_eq
#check @normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails
#check @sourceCompressedRoot_squareSum_of_translated_radial_tails
#check @riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq

#print axioms sourceFourierSupportProjection_apply
#print axioms norm_sourceFourierSupportProjection
#print axioms sourceFourierSupportProjection_translation_norm_eq
#print axioms sourceFourierSupportProjection_translation_normSq_eq
#print axioms normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails
#print axioms sourceCompressedRoot_squareSum_of_translated_radial_tails
#print axioms riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq

end Dev
end ConnesWeilRH
