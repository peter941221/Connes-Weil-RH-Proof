import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

/-!
# Compact-support Laplace bounds

The explicit finite-node correction has compact support, but its vertical
budget is stated for arbitrary complex Laplace parameters. This file records
the elementary reduction from that budget to the support radius and the L1
mass of the underlying test.
-/

namespace ConnesWeilRH.Source.CC20YoshidaCriticalContraction.CompactLogTest

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open scoped ComplexConjugate

noncomputable section

theorem norm_laplaceAt_le_exp_mul_l1Mass
    (f : CCM25Concrete.CompactLogConvolution.CompactLogTest) (B : ℝ)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s : ℂ) :
    ‖laplaceAt f s‖ ≤ Real.exp (|s.re| * B) * l1Mass f := by
  have hpoint (x : ℝ) :
      ‖(exponentialWeight f s).test x‖ ≤
        Real.exp (|s.re| * B) * ‖f.test x‖ := by
    by_cases hx : f.test x = 0
    · simp [exponentialWeight_apply, hx]
    · have hxs : x ∈ Set.Icc (-B) B := hsupport (Function.mem_support.mpr hx)
      have habs : |x| ≤ B := by
        rw [abs_le]
        exact ⟨by linarith [hxs.1], hxs.2⟩
      rw [exponentialWeight_apply, norm_mul, Complex.norm_exp]
      have hre : (s * (x : ℂ)).re = s.re * x := by
        simp
      rw [hre]
      have harg : s.re * x ≤ |s.re| * B := by
        calc
          s.re * x ≤ |s.re * x| := le_abs_self _
          _ = |s.re| * |x| := by rw [abs_mul]
          _ ≤ |s.re| * B := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (norm_nonneg _)
  have hleft : Integrable (fun x : ℝ => ‖(exponentialWeight f s).test x‖) :=
    (exponentialWeight f s).test.integrable.norm
  have hright : Integrable (fun x : ℝ => Real.exp (|s.re| * B) * ‖f.test x‖) :=
    f.test.integrable.norm.const_mul _
  calc
    ‖laplaceAt f s‖ ≤ ∫ x : ℝ, ‖(exponentialWeight f s).test x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, Real.exp (|s.re| * B) * ‖f.test x‖ :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = Real.exp (|s.re| * B) * l1Mass f := by
      rw [integral_const_mul]
      rfl

end
end ConnesWeilRH.Source.CC20YoshidaCriticalContraction.CompactLogTest
