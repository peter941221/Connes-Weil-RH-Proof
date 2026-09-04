/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RationalPowerIntegral

namespace ConnesWeilRH
namespace Source
namespace C1RationalPowerIntegralAudit

open C1RationalPowerIntegral

#check rationalRadius
#check denominatorPower
#check rationalPowerPrimitive
#check rationalPowerPrimitive_hasDerivAt
#check rationalPowerIntervalValue
#check intervalIntegral_denominatorPower
#check finiteDenominatorPowerPolynomial
#check intervalIntegral_finiteDenominatorPowerPolynomial
#check denominatorPowerMomentValue
#check intervalIntegral_denominatorPowerMoment
#check finiteDenominatorPowerMomentPolynomial
#check intervalIntegral_finiteDenominatorPowerMomentPolynomial

#print axioms rationalPowerPrimitive_hasDerivAt
#print axioms intervalIntegral_denominatorPower
#print axioms intervalIntegral_finiteDenominatorPowerPolynomial
#print axioms intervalIntegral_denominatorPowerMoment
#print axioms intervalIntegral_finiteDenominatorPowerMomentPolynomial

example : rationalPowerIntervalValue 0 = (97 / 50 : ℝ) := by
  norm_num [rationalPowerIntervalValue, rationalRadius]

end C1RationalPowerIntegralAudit
end Source
end ConnesWeilRH
