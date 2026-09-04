/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentConsumer

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentConsumer

open C1ClassWindowObjects
open C1ClassGramScale
open C1ClassGramMomentReduction
open Polynomial
open scoped BigOperators

#print axioms classWeightedPolyIntegral
#print axioms classWeightedPolyIntegral_integrable
#print axioms classWeightedPolyIntegral_eq_moment_sum
#print axioms classWeightedPolyIntegral_add
#print axioms classWeightedPolyIntegral_sub
#print axioms classWeightedPolyIntegral_C_mul
#print axioms classWeightedPolyIntegral_mul_C
#print axioms classWeightedPolyIntegral_mul_nat
#print axioms classWeightedPolyIntegral_smul
#print axioms classWeightedPolyIntegral_monomial
#print axioms classWeightedPolyIntegral_X_pow
#print axioms classWeightedPolyIntegral_X_mul_X_pow
#print axioms classWeightedPolyIntegral_X_mul_add
#print axioms classWeightedPolyIntegral_X_mul_sub
#print axioms classWeightedPolyIntegral_X_mul_C_mul
#print axioms classWeightedPolyIntegral_X_mul_C
#print axioms classWeightedPolyIntegral_zero
#print axioms classWeightedPolyIntegral_one
#print axioms classWeightedPolyIntegral_C
#print axioms classWeightedPolyIntegral_X_mul_X
#print axioms classWeightedPolyIntegral_X
#print axioms classWeightedPolyIntegral_neg
#print axioms classPolynomial_X_mul_X
#print axioms classPolynomial_X_mul_X_pow
#print axioms classPolynomial_X_pow_mul_X
#print axioms classPolynomial_X_pow_mul_X_pow
#print axioms classPolynomial_X_pow_mul_C
#print axioms classPolynomial_X_pow_mul_C_mul
#print axioms classPolynomial_X_mul_add
#print axioms classPolynomial_X_mul_sub
#print axioms classPolynomial_X_mul_C_mul
#print axioms classGramUnitEntry_eq_weightedPolyIntegral
#print axioms classGramUnitEntry_eq_moment_sum

example (i j : Fin 8) :
    classGramUnitEntry i j =
      classWeightedPolyIntegral (legendrePoly (i : ℕ) * legendrePoly (j : ℕ)) :=
  classGramUnitEntry_eq_weightedPolyIntegral i j

end C1ClassGramMomentConsumer
end Source
end ConnesWeilRH
