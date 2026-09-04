/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentSharpTailBudget

namespace ConnesWeilRH.Source.C1ClassMomentSharpTailBudget

open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentCentralAssembly
open scoped BigOperators Interval

#print axioms norm_intervalIntegral_classMoment_rightTail_q99_lt_one_div_ten_pow_40
#print axioms norm_intervalIntegral_classMoment_leftTail_q99_lt_one_div_ten_pow_40
#print axioms classMomentIntegrand_nonneg_of_even
#print axioms classMoment_rightTail_nonneg_of_even
#print axioms classMoment_bounds_of_centralEnvelope_of_even_sharp
#print axioms q28Moment0_bounds_of_centralEnvelope
#print axioms q28Moment2_bounds_of_centralEnvelope
#print axioms q28_baseMoment_bounds_of_centralEnvelopes

example :
    ‖∫ x in (99 / 100 : ℝ)..1, classMomentIntegrand 0 x‖ <
      (1 / 10 ^ 40 : ℝ) :=
  norm_intervalIntegral_classMoment_rightTail_q99_lt_one_div_ten_pow_40 0

example {n : ℕ} (hn : Even n) {lo hi : ℝ}
    (h : centralMomentEnvelope n lo hi) :
    lo ≤ classMoment n ∧
      classMoment n < hi + (2 / 10 ^ 40 : ℝ) :=
  classMoment_bounds_of_centralEnvelope_of_even_sharp hn h

end ConnesWeilRH.Source.C1ClassMomentSharpTailBudget
