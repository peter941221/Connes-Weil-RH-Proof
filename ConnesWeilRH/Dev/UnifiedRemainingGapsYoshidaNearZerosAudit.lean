/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros

/-!
# Plan 016 nearby-zero interpolation import audit
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsYoshidaNearZerosAudit

open Source.CC20YoshidaNearZeros

#check @sourceNontrivialZerosInClosedBall_finite
#check @mem_sourceNontrivialZerosInClosedBallFinset
#check @finiteWeightedMellinKernel_log_window_independence
#check @exists_windowed_test_with_finite_kernel_integral_ne_zero
#check @windowedFiniteMellinVector_span_top
#check @fixed_window_finite_mellin_surjective
#check @fixed_window_nearby_zero_mellin_surjective

#print sourceNontrivialZerosInClosedBall_finite
#print fixed_window_finite_mellin_surjective
#print fixed_window_nearby_zero_mellin_surjective

#print axioms sourceNontrivialZerosInClosedBall_finite
#print axioms finiteWeightedMellinKernel_log_window_independence
#print axioms exists_windowed_test_with_finite_kernel_integral_ne_zero
#print axioms windowedFiniteMellinVector_span_top
#print axioms fixed_window_finite_mellin_surjective
#print axioms fixed_window_nearby_zero_mellin_surjective

end UnifiedRemainingGapsYoshidaNearZerosAudit
end Dev
end ConnesWeilRH
