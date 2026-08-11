import ConnesWeilRH.Dev.Wall14PlateauBounds

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set

/-! Integral assembly for the hI closure.  RH NOT claimed. -/

lemma int_tail_gate_le (R : ℝ) (hR : 2 ≤ R) :
    (∫ y in Ioi R, |plateauArchG y|) ≤
        (2 * plateauA) * ((1 / tailC) * Real.exp (-R)) := by
  have hmeas : MeasurableSet (Set.Ioi R) := isOpen_Ioi.measurableSet
  have hsyn : (fun y : ℝ => |plateauArchG y|) =ᵐ[volume.restrict (Set.Ioi R)]
      (fun y : ℝ => (2 * plateauA) * (1 / den y)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    have hyR : R < y := by simpa using hy
    have hb : |plateauArchG y| = 2 * plateauA / den y :=
      plateauG_abs_tail y (by nlinarith)
    rw [hb]
    ring
  calc
    (∫ y in Ioi R, |plateauArchG y|) = ∫ y in Ioi R, (2 * plateauA) * (1 / den y) := by
      apply MeasureTheory.integral_congr_ae
      exact hsyn
    _ = (2 * plateauA) * (∫ y in Ioi R, 1 / den y) := by
      rw [integral_const_mul]
    _ ≤ (2 * plateauA) * ((1 / tailC) * Real.exp (-R)) := by
      exact mul_le_mul_of_nonneg_left (integral_inv_den_Ioi_le R hR)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (le_of_lt plateauA_pos))



/-! `norm` of the integrand equals `|g|` on the positive half-line, because the
integrand is real-valued with real part `plateauArchG`. -/
lemma norm_integrand_eq_abs_g (y : ℝ) (hy : 0 < y) :
    ‖plateauOwner.archimedeanIntegrand y‖ = |plateauArchG y| := by
  have heq : plateauOwner.archimedeanIntegrand y = (plateauArchG y : ℂ) := by
    apply Complex.ext
    · simp [archimedeanIntegrand_re_eq_plateauArchG y hy]
    · simpa using plateauOwner.archimedeanIntegrand_im_eq_zero y
  rw [heq]
  simp


/-! Bridge: `|(Int f).re| <= Int |g|` for the archimedean integrand on `(0,inf)`,
via `|z.re| <= ||z||`, `||Int f|| <= Int ||f||`, and equality `||f|| = |g|`. -/
lemma abs_re_int_Ioi_le :
    |(∫ y in Set.Ioi (0 : ℝ), plateauOwner.archimedeanIntegrand y).re|
        <= ∫ y in Set.Ioi (0 : ℝ), |plateauArchG y| := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hmeas0 : MeasurableSet (Set.Ioi (0 : ℝ)) := isOpen_Ioi.measurableSet
  have hchain : |(∫ y : ℝ, plateauOwner.archimedeanIntegrand y ∂mu).re|
          <= ∫ y : ℝ, |plateauArchG y| ∂mu := by
    calc
      |(∫ y : ℝ, plateauOwner.archimedeanIntegrand y ∂mu).re|
          <= ‖∫ y : ℝ, plateauOwner.archimedeanIntegrand y ∂mu‖ :=
            Complex.abs_re_le_norm _
      _ <= ∫ y : ℝ, ‖plateauOwner.archimedeanIntegrand y‖ ∂mu :=
            MeasureTheory.norm_integral_le_integral_norm (fun y : ℝ => plateauOwner.archimedeanIntegrand y)
      _ = ∫ y : ℝ, |plateauArchG y| ∂mu := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas0] with y hy
            have hy0 : 0 < y := by simpa using hy
            exact norm_integrand_eq_abs_g y hy0
  change |(∫ y : ℝ, plateauOwner.archimedeanIntegrand y ∂mu).re| <=
            ∫ y : ℝ, |plateauArchG y| ∂mu
  exact hchain

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
