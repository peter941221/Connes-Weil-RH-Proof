import ConnesWeilRH.Dev.C1ExplicitSmoothSeed
import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction.CompactLogTest

noncomputable section

 theorem smoothSeed_l1Mass_le_four :
    l1Mass smoothSeed ≤ 4 := by
  have hleft : Integrable (fun x : ℝ => ‖smoothSeed.test x‖) :=
    smoothSeed.test.integrable.norm
  let bound : ℝ → ℝ := Set.indicator (Set.Icc (-2 : ℝ) 2) (fun _ => 1)
  have hright : Integrable bound := by
    exact (integrableOn_const (μ := volume) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; norm_num) (by norm_num)).integrable_indicator
      measurableSet_Icc
  have hpoint : ∀ x : ℝ, ‖smoothSeed.test x‖ ≤ bound x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
    · simp only [bound, Set.indicator_of_mem hx]
      simpa [smoothSeed_apply, smoothSeedComplex, abs_of_nonneg
        (smoothSeedRaw_nonneg x)] using smoothSeedRaw_le_one x
    · simp only [bound, Set.indicator, hx, ↓reduceIte]
      have hzero : smoothSeed.test x = 0 := by
        rw [smoothSeed_apply, smoothSeedComplex]
        apply congrArg Complex.ofReal
        by_contra hne
        exact hx (smoothSeedRaw_support_subset (Function.mem_support.mpr hne))
      simp [hzero]
  calc
    l1Mass smoothSeed = ∫ x : ℝ, ‖smoothSeed.test x‖ := rfl
    _ ≤ ∫ x : ℝ, bound x :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = 4 := by
      rw [show bound = Set.indicator (Set.Icc (-2 : ℝ) 2) (fun _ => 1) by rfl]
      rw [integral_indicator measurableSet_Icc]
      norm_num [Real.volume_Icc]


theorem l1Mass_exponentialWeight_le_of_support
    (f : CCM25Concrete.CompactLogConvolution.CompactLogTest) (B : ℝ)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) (a : ℂ) :
    l1Mass (exponentialWeight f a) ≤ Real.exp (|a.re| * B) * l1Mass f := by
  have hleft : Integrable (fun x : ℝ => ‖(exponentialWeight f a).test x‖) :=
    (exponentialWeight f a).test.integrable.norm
  have hright : Integrable (fun x : ℝ =>
      Real.exp (|a.re| * B) * ‖f.test x‖) :=
    f.test.integrable.norm.const_mul _
  have hpoint (x : ℝ) :
      ‖(exponentialWeight f a).test x‖ ≤
        Real.exp (|a.re| * B) * ‖f.test x‖ := by
    by_cases hx : f.test x = 0
    · simp [exponentialWeight_apply, hx]
    · have hxs : x ∈ Set.Icc (-B) B := hsupport (Function.mem_support.mpr hx)
      have habs : |x| ≤ B := by
        rw [abs_le]
        exact ⟨by linarith [hxs.1], hxs.2⟩
      rw [exponentialWeight_apply, norm_mul, Complex.norm_exp]
      have hre : (a * (x : ℂ)).re = a.re * x := by simp
      rw [hre]
      have harg : a.re * x ≤ |a.re| * B := by
        calc
          a.re * x ≤ |a.re * x| := le_abs_self _
          _ = |a.re| * |x| := by rw [abs_mul]
          _ ≤ |a.re| * B := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg)
        (norm_nonneg _)
  calc
    l1Mass (exponentialWeight f a) =
        ∫ x : ℝ, ‖(exponentialWeight f a).test x‖ := rfl
    _ ≤ ∫ x : ℝ, Real.exp (|a.re| * B) * ‖f.test x‖ :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = Real.exp (|a.re| * B) * l1Mass f := by
      rw [integral_const_mul]
      rfl

theorem l1Mass_exponentialWeight_smoothSeed_le (a : ℂ) :
    l1Mass (exponentialWeight smoothSeed a) ≤
      4 * Real.exp (2 * |a.re|) := by
  calc
    l1Mass (exponentialWeight smoothSeed a) ≤
        Real.exp (|a.re| * 2) * l1Mass smoothSeed :=
      l1Mass_exponentialWeight_le_of_support smoothSeed 2
        smoothSeedComplex_support_subset a
    _ ≤ Real.exp (|a.re| * 2) * 4 :=
      mul_le_mul_of_nonneg_left smoothSeed_l1Mass_le_four (Real.exp_nonneg _)
    _ = 4 * Real.exp (2 * |a.re|) := by
      rw [mul_comm]
      congr 1
      ring

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
