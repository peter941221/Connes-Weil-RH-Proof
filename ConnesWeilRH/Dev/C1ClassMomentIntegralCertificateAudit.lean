import ConnesWeilRH.Dev.C1ClassMomentIntegralCertificate

namespace ConnesWeilRH.Source.C1ClassMomentIntegralCertificate

#print axioms integral_bounds_of_integralEnvelope
#print axioms classMomentIntegrand_support_subset_Ioc
#print axioms classMoment_eq_intervalIntegral
#print axioms classMoment_bounds_of_integralEnvelope

example (n : ℕ) (lo hi : ℝ)
    (h : IntegralEnvelope (classMomentIntegrand n) (-1) 1 lo hi) :
    lo ≤ classMoment n ∧ classMoment n ≤ hi :=
  classMoment_bounds_of_integralEnvelope n lo hi h

end ConnesWeilRH.Source.C1ClassMomentIntegralCertificate
