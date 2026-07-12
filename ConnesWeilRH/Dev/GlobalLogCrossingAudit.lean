/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing

namespace ConnesWeilRH
namespace Dev

open Source CC20Concrete

#check @cc20PositiveHalfLineProjection
#check @cc20PositiveHalfLineProjection_coeFn
#check @cc20PositiveHalfLineProjection_idempotent
#check @norm_cc20PositiveHalfLineProjectionLinearMap_le
#check @cc20GlobalLogTranslation
#check @cc20GlobalLogTranslation_coeFn
#check @norm_cc20GlobalLogTranslation
#check @cc20GlobalLogTranslation_neg_apply
#check @cc20NegativeHalfLineProjection
#check @cc20SingleCrossingOperator
#check @cc20SingleCrossingOperator_apply
#check @cc20NegativeHalfLineProjection_coeFn

#print axioms cc20PositiveHalfLineProjection
#print axioms cc20PositiveHalfLineProjection_coeFn
#print axioms cc20PositiveHalfLineProjection_idempotent
#print axioms norm_cc20PositiveHalfLineProjectionLinearMap_le
#print axioms cc20GlobalLogTranslation
#print axioms cc20GlobalLogTranslation_coeFn
#print axioms norm_cc20GlobalLogTranslation
#print axioms cc20GlobalLogTranslation_neg_apply
#print axioms cc20NegativeHalfLineProjection
#print axioms cc20SingleCrossingOperator
#print axioms cc20SingleCrossingOperator_apply
#print axioms cc20NegativeHalfLineProjection_coeFn

end Dev
end ConnesWeilRH
