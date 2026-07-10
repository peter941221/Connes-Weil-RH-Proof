/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaTail

/-!
# Plan 016 Yoshida tail import audit
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsYoshidaTailAudit

open Source.CC20YoshidaTail

#check @mellinLogSliceRaw_support_subset
#check @mellin_eq_fourier_mellinLogSlice
#check @mellin_vertical_quadratic_decay
#check @mellinLogSliceRaw_iteratedFDeriv_eq_joint_comp
#check @continuousOn_mellinLogSliceRaw_iteratedFDeriv_integral
#check @exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
#check @fourier_mellinLogSlice_quadratic_decay_le_integrals
#check @exists_uniform_mellin_vertical_quadratic_decay

#print mellin_vertical_quadratic_decay
#print exists_uniform_mellin_vertical_quadratic_decay
#print axioms mellinLogSliceRaw_support_subset
#print axioms mellin_eq_fourier_mellinLogSlice
#print axioms mellin_vertical_quadratic_decay
#print axioms mellinLogSliceRaw_iteratedFDeriv_eq_joint_comp
#print axioms continuousOn_mellinLogSliceRaw_iteratedFDeriv_integral
#print axioms exists_uniform_mellinLogSliceRaw_iteratedFDeriv_integral_bound
#print axioms fourier_mellinLogSlice_quadratic_decay_le_integrals
#print axioms exists_uniform_mellin_vertical_quadratic_decay

end UnifiedRemainingGapsYoshidaTailAudit
end Dev
end ConnesWeilRH
