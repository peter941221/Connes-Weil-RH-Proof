/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# Unscaled Yoshida selected-owner import audit
-/

namespace ConnesWeilRH
namespace Dev
namespace UnscaledYoshidaSelectedOwnerAudit

open Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

#check @selectedOwner
#check @selectedOwner_sourceTest
#check @selectedOwner_convolutionSquare
#check @selectedOwner_laplaceAt_convolutionSquare_eq_one
#check @selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
#check @selectedOwner_sourceTest_support_subset_Icc
#check @operatorSum_isCompactOperator
#check @operatorSum_isSelfAdjoint
#check @ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
#check @exists_fixedWindows_nearbyZero_selectedOwner

#print exists_fixedWindows_nearbyZero_selectedOwner
#print ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum

#print axioms selectedOwner_laplaceAt_convolutionSquare_eq_one
#print axioms selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
#print axioms operatorSum_isCompactOperator
#print axioms operatorSum_isSelfAdjoint
#print axioms ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
#print axioms exists_fixedWindows_nearbyZero_selectedOwner

end UnscaledYoshidaSelectedOwnerAudit
end Dev
end ConnesWeilRH
