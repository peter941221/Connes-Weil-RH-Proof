/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ConcreteClassMomentCertificate

namespace ConnesWeilRH
namespace Source
namespace C1ConcreteClassMomentCertificateAudit

open C1ConcreteClassMomentCertificate

#check rationalRadiusQ
#check taylorCoefficientQ
#check powerCoefficientQ
#check rationalPowerCoefficientQ
#check taylorScaledPolynomialQ_coeff
#check powerCoefficientQSlow_eq_polynomial_coeff
#check rationalPowerPolynomial_eq_map
#check rationalPowerCoefficient_eq_cast
#check taylorScaledPolynomial_eval
#check rationalPowerPolynomial_eval_eq_finite
#check scaledClassWeightApprox_eq_finiteDenominatorPowerPolynomial
#check comparisonIntegral0
#check comparisonIntegral2
#check q28_baseMoment_bounds_of_concrete_certificate
#check q28_hbox_of_concrete_certificate

#print axioms taylorScaledPolynomialQ_coeff
#print axioms powerCoefficientQSlow_eq_polynomial_coeff
#print axioms rationalPowerPolynomial_eq_map
#print axioms rationalPowerCoefficient_eq_cast
#print axioms taylorScaledPolynomial_eval
#print axioms rationalPowerPolynomial_eval_eq_finite
#print axioms scaledClassWeightApprox_eq_finiteDenominatorPowerPolynomial
#print axioms q28_baseMoment_bounds_of_concrete_certificate
#print axioms q28_hbox_of_concrete_certificate

example : rationalRadiusQ = (97 / 100 : ℚ) := by
  norm_num [rationalRadiusQ]

end C1ConcreteClassMomentCertificateAudit
end Source
end ConnesWeilRH
