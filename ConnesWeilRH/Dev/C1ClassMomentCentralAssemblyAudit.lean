/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentCentralAssembly

namespace ConnesWeilRH.Source.C1ClassMomentCentralAssembly

open MeasureTheory Set
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open scoped BigOperators Interval

#print axioms centralRadius_pos
#print axioms centralRadius_lt_one
#print axioms classMomentIntegrand_intervalIntegrable
#print axioms classBump_nonneg
#print axioms classBump_le_one
#print axioms classUnitWeight_le_one
#print axioms classMomentIntegrand_zero_nonneg
#print axioms classMomentIntegrand_zero_le_one
#print axioms classMomentIntegrand_neg_of_even
#print axioms classMoment_leftTail_eq_rightTail_of_even
#print axioms classMoment_eq_three_interval
#print axioms symbolicCentralEnvelopeZero
#print axioms centralMoment_bounds_of_centralEnvelope
#print axioms classMoment_bounds_of_centralEnvelope_of_even

example {n : ℕ} (hn : Even n) {lo hi : ℝ}
    (h : centralMomentEnvelope n lo hi) :
    lo - (2 / 10 ^ 15 : ℝ) < classMoment n ∧
      classMoment n < hi + (2 / 10 ^ 15 : ℝ) :=
  classMoment_bounds_of_centralEnvelope_of_even hn h

example :
    -(2 / 10 ^ 15 : ℝ) < classMoment 0 ∧
      classMoment 0 < 2 + (2 / 10 ^ 15 : ℝ) := by
  simpa using
    (classMoment_bounds_of_centralEnvelope_of_even
      (n := 0) (lo := 0) (hi := 2) ⟨0, rfl⟩ symbolicCentralEnvelopeZero)

end ConnesWeilRH.Source.C1ClassMomentCentralAssembly
