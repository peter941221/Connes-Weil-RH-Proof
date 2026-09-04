/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ScaledExpRationalEnvelope

namespace ConnesWeilRH
namespace Source
namespace C1ScaledExpRationalEnvelopeAudit

open C1ScaledExpRationalEnvelope
open C1ClassGramMomentReduction

#check expTaylor20
#check expTaylor20Error
#check scaledClassWeightApprox
#check expTaylor20_error
#check expTaylor20_pow35_error
#check centralRadius97_scaled_argument_bounds
#check classUnitWeight_central_approx_error
#check classMomentIntegrand_central_approx_error

#print axioms expTaylor20_error
#print axioms expTaylor20_pow35_error
#print axioms centralRadius97_scaled_argument_bounds
#print axioms classUnitWeight_central_approx_error
#print axioms classMomentIntegrand_central_approx_error

example (x : ℝ)
    (hx : x ∈ Set.Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    |classUnitWeight x - scaledClassWeightApprox x| ≤
      (70 : ℝ) * expTaylor20Error :=
  classUnitWeight_central_approx_error x hx

end C1ScaledExpRationalEnvelopeAudit
end Source
end ConnesWeilRH
