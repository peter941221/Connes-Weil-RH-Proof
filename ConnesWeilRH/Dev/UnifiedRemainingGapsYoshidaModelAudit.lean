/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# Plan 016 Yoshida model import audit

This audit exposes the normalized additive/pole model and fixes the axiom
boundary of the Mellin-convolution rejection guard.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsYoshidaModelAudit

open Source
open Source.CC20YoshidaInterpolationNode

#check @NormalizedCC20MellinConvolutionLaw
#check @normalizedCC20TestSpace_is_additive_pole_model
#check @not_normalizedCC20MellinConvolutionLaw

#print NormalizedCC20MellinConvolutionLaw
#print normalizedCC20TestSpace_is_additive_pole_model
#print not_normalizedCC20MellinConvolutionLaw

#print axioms normalizedCC20TestSpace_is_additive_pole_model
#print axioms not_normalizedCC20MellinConvolutionLaw

end UnifiedRemainingGapsYoshidaModelAudit
end Dev
end ConnesWeilRH
