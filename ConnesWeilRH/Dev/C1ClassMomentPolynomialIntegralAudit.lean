import ConnesWeilRH.Dev.C1ClassMomentPolynomialIntegral

namespace ConnesWeilRH.Source.C1ClassMomentPolynomialIntegral

open scoped BigOperators Interval

#print axioms finitePowerPolynomial_continuous
#print axioms finitePowerPolynomial_intervalIntegrable
#print axioms intervalIntegral_finitePowerPolynomial
#print axioms integralEnvelope_of_finitePowerBounds
#print axioms classMomentEnvelope_of_finitePowerBounds

example (s : Finset ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    (∫ x in a..b, finitePowerPolynomial s c x) =
      finitePowerIntegralValue s c a b :=
  intervalIntegral_finitePowerPolynomial s c a b

end ConnesWeilRH.Source.C1ClassMomentPolynomialIntegral
