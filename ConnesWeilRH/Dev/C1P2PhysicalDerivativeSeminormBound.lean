import ConnesWeilRH.Dev.C1P2BaseSeminormBound

namespace ConnesWeilRH
namespace Source
namespace C1P2PhysicalDerivativeSeminormBound

open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CCM25Concrete.SelectedYoshidaBridge
open C1HealthyYoshidaAffineCorrection

noncomputable section

/-!
# Physical derivative cost for a finite windowed source combination

This is the quantitative bridge needed by the variational selector.  It keeps
the exact finite source support and bounds the first physical derivative by
the coefficient-weighted derivative seminorms of the selected source tests.
-/

theorem source_combination_derivative_seminorm_le_coeff_weighted_sum
    {a b : Real}
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex) :
    SchwartzMap.seminorm Complex 0 0
        (SchwartzMap.derivCLM Complex Complex
          (normalizedCC20ConcreteTestAlgebra.legacy.encode
            (windowedPositiveIntervalCompactTestCombination c))) ≤
      (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (SchwartzMap.derivCLM Complex Complex
              (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test))) := by
  classical
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro x
  have hencode :
      normalizedCC20ConcreteTestAlgebra.legacy.encode
          (windowedPositiveIntervalCompactTestCombination c) =
        ∑ p ∈ c.support,
          c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test := by
    unfold windowedPositiveIntervalCompactTestCombination
    unfold positiveIntervalCompactTestCombination
    simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
    rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective]
    rw [Finsupp.sum]
  rw [hencode]
  simp only [map_sum, map_smul, SchwartzMap.sum_apply,
    SchwartzMap.smul_apply]
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
  calc
    ‖(∑ p ∈ c.support,
        c p •
          (SchwartzMap.derivCLM Complex Complex
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test))) x‖ =
      ‖∑ p ∈ c.support,
        c p •
          (SchwartzMap.derivCLM Complex Complex
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) x‖ := by
      simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply]
    _ ≤
        ∑ p ∈ c.support,
          ‖c p •
            (SchwartzMap.derivCLM Complex Complex
              (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) x‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ c.support,
          ‖c p‖ *
            ‖(SchwartzMap.derivCLM Complex Complex
              (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) x‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [smul_eq_mul, norm_mul]
    _ ≤ ∑ p ∈ c.support,
          ‖c p‖ *
            SchwartzMap.seminorm Complex 0 0
              (SchwartzMap.derivCLM Complex Complex
                (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_le_seminorm Complex
          (SchwartzMap.derivCLM Complex Complex
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) x)
        (norm_nonneg _)

end
end C1P2PhysicalDerivativeSeminormBound
end Source
end ConnesWeilRH
