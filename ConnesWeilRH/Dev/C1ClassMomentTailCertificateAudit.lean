import ConnesWeilRH.Dev.C1ClassMomentTailCertificate

namespace ConnesWeilRH.Source.C1ClassMomentTailCertificate

open scoped BigOperators Interval
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate

#print axioms classUnitWeight_eq_exp_neg_two_div
#print axioms classUnitWeight_le_exp_of_abs_bounds
#print axioms classMomentIntegrand_norm_le_exp_of_abs_bounds
#print axioms norm_intervalIntegral_classMoment_rightTail_le
#print axioms norm_intervalIntegral_classMoment_leftTail_le
#print axioms norm_intervalIntegral_classMoment_rightTail_q99_lt
#print axioms norm_intervalIntegral_classMoment_leftTail_q99_lt

example (n : ℕ) :
    ‖∫ x in (99 / 100 : ℝ)..1, classMomentIntegrand n x‖ <
      (1 / 10 ^ 15 : ℝ) :=
  norm_intervalIntegral_classMoment_rightTail_q99_lt n

end ConnesWeilRH.Source.C1ClassMomentTailCertificate
