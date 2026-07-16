/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerGenerator

/-!
# Complete finite-S generator translation series

The operator-norm Euler generator series is evaluated on the common-log
`L²` carrier and read back as the exact signed prime-power translation
series.  The finite prime sum remains outside each convergent mode sum.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGeneratorTranslationSeries

open scoped BigOperators
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator

theorem summable_parameterizedPrimeEulerGeneratorMode
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    Summable (parameterizedPrimeEulerGeneratorMode alpha p) := by
  have hsummable : Summable
      (fun n : ℕ => parameterizedPrimeEulerContraction alpha p ^ n) :=
    summable_geometric_of_norm_lt_one
      (norm_parameterizedPrimeEulerContraction_lt_one alpha p halpha)
  simpa only [parameterizedPrimeEulerGeneratorMode] using
    hsummable.mul_left (-ccm24PrimeEulerContraction p)

theorem parameterizedPrimeEulerGenerator_tsum_apply
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    (∑' n : ℕ, parameterizedPrimeEulerGeneratorMode alpha p n) u =
      ∑' n : ℕ, parameterizedPrimeEulerGeneratorMode alpha p n u := by
  simpa using (ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum
    (summable_parameterizedPrimeEulerGeneratorMode alpha p halpha)

/-- The exact one-prime signed translation series evaluated on a vector. -/
noncomputable def parameterizedPrimeEulerTranslationSeries
    (alpha : ℝ) (p : CCM24VisiblePrime) (u : finiteSCarrier) :
    finiteSCarrier :=
  ∑' n : ℕ,
    (-((alpha : ℂ) ^ n) *
        (ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) •
      cc20GlobalLogTranslation
        (-((n + 1 : ℕ) : ℝ) * Real.log p) u

theorem parameterizedPrimeEulerGenerator_apply_eq_translationSeries
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedPrimeEulerGenerator alpha p u =
      parameterizedPrimeEulerTranslationSeries alpha p u := by
  rw [parameterizedPrimeEulerGenerator_eq_tsum_modes alpha p halpha,
    parameterizedPrimeEulerGenerator_tsum_apply alpha p halpha u]
  unfold parameterizedPrimeEulerTranslationSeries
  apply tsum_congr
  intro n
  exact parameterizedPrimeEulerGeneratorMode_apply alpha p n u

/-- The complete finite-S generator evaluated on a vector is the finite
signed sum of the genuine one-prime translation series. -/
theorem parameterizedFiniteEulerGenerator_apply_eq_translationSeries
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedFiniteEulerGenerator alpha S u =
      (S.map (fun p =>
        parameterizedPrimeEulerTranslationSeries alpha p u)).sum := by
  induction S with
  | nil =>
      simp [parameterizedFiniteEulerGenerator_nil]
  | cons p S ih =>
      rw [parameterizedFiniteEulerGenerator_cons,
        ContinuousLinearMap.add_apply, ih,
        parameterizedPrimeEulerGenerator_apply_eq_translationSeries
          alpha p halpha u]
      rfl

/-- The operator itself is the finite sum of the complete one-prime mode
series; no primewise norm has been introduced. -/
theorem parameterizedFiniteEulerGenerator_eq_modeSeries
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerGenerator alpha S =
      (S.map (fun p =>
        ∑' n : ℕ, parameterizedPrimeEulerGeneratorMode alpha p n)).sum := by
  induction S with
  | nil =>
      simp [parameterizedFiniteEulerGenerator_nil]
  | cons p S ih =>
      rw [parameterizedFiniteEulerGenerator_cons, ih,
        parameterizedPrimeEulerGenerator_eq_tsum_modes alpha p halpha]
      rfl

end CCM24FiniteSGeneratorTranslationSeries
end CCM25Concrete
end Source
end ConnesWeilRH
