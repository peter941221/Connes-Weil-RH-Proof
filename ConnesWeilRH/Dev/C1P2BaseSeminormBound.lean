/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# Quantitative zero-order seminorm bound for finite-window bases

This module exposes the missing quantitative interface behind the geometric
contraction route.  A compact-log pullback is bounded by the source test's
zero-order Schwartz seminorm, and a finite windowed combination is bounded by
the coefficient-weighted sum of its basis seminorms.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BaseSeminormBound

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CCM25Concrete.SelectedYoshidaBridge

noncomputable section

theorem compactLogTestOfWindow_seminorm_zero_zero_le_source
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : Real =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b) :
    SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow g ha hb hsupport).test ≤
      SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g) := by
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro x
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
    compactLogTestOfWindow_apply] using
    (SchwartzMap.norm_le_seminorm Complex
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g) (Real.exp x))

theorem source_combination_seminorm_zero_zero_le_coeff_weighted_sum
    {a b : Real}
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex) :
    SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode
          (windowedPositiveIntervalCompactTestCombination c)) ≤
      (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
  classical
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
  rw [show normalizedCC20ConcreteTestAlgebra.legacy.encode
      (windowedPositiveIntervalCompactTestCombination c) =
        ∑ p ∈ c.support,
          c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test by
    unfold windowedPositiveIntervalCompactTestCombination
    unfold positiveIntervalCompactTestCombination
    simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
    rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective]
    rw [Finsupp.sum]]
  calc
    ‖(∑ p ∈ c.support,
        c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ =
        ‖∑ p ∈ c.support,
          (c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ := by
      simp only [SchwartzMap.sum_apply]
    _ ≤
        ∑ p ∈ c.support,
          ‖(c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ c.support,
          ‖c p‖ *
            ‖normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test x‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [smul_eq_mul, norm_mul]
    _ ≤ ∑ p ∈ c.support,
          ‖c p‖ *
            SchwartzMap.seminorm Complex 0 0
              (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_le_seminorm Complex
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x)
        (norm_nonneg _)

theorem compactLogTestOfWindow_combination_seminorm_zero_zero_le_coeff_weighted_sum
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex) :
    SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test ≤
      (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
  exact (compactLogTestOfWindow_seminorm_zero_zero_le_source
    (windowedPositiveIntervalCompactTestCombination c) ha hb
    (windowedPositiveIntervalCompactTestCombination_support_subset c)).trans
    (source_combination_seminorm_zero_zero_le_coeff_weighted_sum c)

theorem strict_base_contraction_of_coeff_weighted_budget
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    {budget : Real}
    (hbudget :
      2 *
          (∑ p ∈ c.support,
            ‖c p‖ *
              SchwartzMap.seminorm Complex 0 0
                (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) <
        budget)
    (hbudget_half : budget ≤ 1 / 2) :
    2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test <
      1 := by
  have hbound :=
    compactLogTestOfWindow_combination_seminorm_zero_zero_le_coeff_weighted_sum
      ha hb c
  have hscaled := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : Real) ≤ 2)
  have hlt :
      2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test <
        budget := by
    exact hscaled.trans_lt hbudget
  linarith

end
end C1P2BaseSeminormBound
end Source
end ConnesWeilRH
