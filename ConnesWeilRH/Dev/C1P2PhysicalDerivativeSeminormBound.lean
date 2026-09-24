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

theorem compactLogTestOfWindow_derivative_seminorm_le_source_weighted_derivative
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : Real =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b) :
    SchwartzMap.seminorm Complex 0 0
        (SchwartzMap.derivCLM Complex Complex
          (compactLogTestOfWindow g ha hb hsupport).test) ≤
      SchwartzMap.seminorm Complex 1 0
        (SchwartzMap.derivCLM Complex Complex
          (normalizedCC20ConcreteTestAlgebra.legacy.encode g)) := by
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro u
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
    SchwartzMap.derivCLM_apply]
  change ‖deriv (fun v : Real =>
    normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp v)) u‖ ≤ _
  have htest :=
    ((normalizedCC20ConcreteTestAlgebra.legacy.encode g).smooth ⊤).differentiable
      (by simp) (Real.exp u)
  have htest' := htest.hasDerivAt
  have hderiv :=
    (htest'.scomp u (Real.hasDerivAt_exp u)).deriv
  have hderiv' :
      deriv (fun v : Real =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp v)) u =
        Complex.exp (u : Complex) *
          deriv (normalizedCC20ConcreteTestAlgebra.legacy.encode g) (Real.exp u) := by
    simpa [Function.comp_def] using hderiv
  rw [hderiv']
  have hsource :=
    SchwartzMap.norm_pow_mul_le_seminorm Complex
      (SchwartzMap.derivCLM Complex Complex
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g)) 1
      (Real.exp u)
  simpa [SchwartzMap.derivCLM_apply, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos u), pow_one, Complex.norm_real] using hsource

end
end C1P2PhysicalDerivativeSeminormBound
end Source
end ConnesWeilRH
