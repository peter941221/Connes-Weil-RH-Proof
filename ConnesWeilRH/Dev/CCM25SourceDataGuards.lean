/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# CCM25 source-data rejection guards

These guards reject source interfaces whose quantifiers force the concrete
finite-prime evaluator to vanish on every test.
-/

namespace ConnesWeilRH
namespace Dev
namespace CCM25SourceDataGuards

open Source
open Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode

/--
The current concrete source API cannot own finite-prime Weil data: its global
support carrier requires every indexed atom to be nonzero for every test,
including the zero test. A compact smooth test nonzero at `2` makes the
resulting contradiction explicit at the first prime.
-/
theorem not_nonempty_concreteSourceWeilFormData :
    ¬ Nonempty
      (Source.AnalyticCore.SourceWeilFormData
        Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra) := by
  rintro ⟨W⟩
  obtain ⟨p, _hsupport, _hnonnegative, _hreal, hp2⟩ :=
    exists_positive_interval_compact_test_real_bump
      (a := 1) (b := 3) (t := 2) (by norm_num) (by norm_num) (by norm_num)
  have hzero :=
    Source.AnalyticCore.SourceFinitePrimeExactSupportData.concrete_all_sourceFinitePrimeTerms_zero
      W.finitePrime.exactSupport p.test 2
  have hvalue2 : W.evaluation.valueAt p.test 2 = 1 := by
    rw [Source.AnalyticCore.SourceEvaluationData.valueAt_eq_norm, hp2]
    norm_num
  have hinv_nonnegative :
      0 ≤ W.evaluation.valueAt p.test ((2 : ℝ)⁻¹) := by
    exact norm_nonneg _
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hterm_pos :
      0 < W.evaluation.sourceFinitePrimeTerm 2 p.test := by
    rw [Source.AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    rw [hvalue2]
    exact mul_pos hlog
      (mul_pos (one_div_pos.mpr hsqrt) (by linarith))
  exact (ne_of_gt hterm_pos) hzero

end CCM25SourceDataGuards
end Dev
end ConnesWeilRH
