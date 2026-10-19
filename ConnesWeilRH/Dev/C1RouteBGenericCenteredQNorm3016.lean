import ConnesWeilRH.Dev.C1RouteBGenericExpPos3015
import ConnesWeilRH.Dev.C1RouteBCenteredQExpForm3013
import ConnesWeilRH.Dev.C1RouteBCauchyRemainder2891

namespace ConnesWeilRH.Dev

theorem routeBCenteredQNormBoundOfSmallT3016 {t : ℂ}
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) :
    ‖routeBCenteredQ2900 t‖ ≤ Real.exp ((80 : ℝ) / 399) := by
  let a : ℂ := 2 * t / (1 - t ^ 2)
  have hden : 1 - t ^ 2 ≠ 0 :=
    routeBDenominatorNonzero2900 t ht
  have ha : ‖a‖ ≤ (40 : ℝ) / 399 := by
    dsimp [a]
    exact routeBArgumentNormBound2900 t ht hden
  have h2a : ‖2 * a‖ ≤ (80 : ℝ) / 399 := by
    rw [norm_mul]
    norm_num
    nlinarith
  have hpos : 0 < (Complex.exp (2 * a)).re :=
    complex_exp_re_pos_of_norm_le3015 h2a
  have hplus : 1 < ‖Complex.exp (2 * a) + 1‖ :=
    complex_norm_add_one_gt_one_of_re_pos3010 hpos
  have hnum : ‖Complex.exp (2 * a)‖ ≤ Real.exp ((80 : ℝ) / 399) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans h2a)
  rw [routeBCenteredQ_exp_form3013]
  change ‖Complex.exp (2 * a) / (Complex.exp (2 * a) + 1)‖ ≤ _
  rw [norm_div]
  have hdenpos : 0 < ‖Complex.exp (2 * a) + 1‖ := by linarith
  apply (div_le_iff₀ hdenpos).2
  have hone : 1 ≤ ‖Complex.exp (2 * a) + 1‖ := hplus.le
  nlinarith [hnum, norm_nonneg (Complex.exp (2 * a))]

end ConnesWeilRH.Dev
