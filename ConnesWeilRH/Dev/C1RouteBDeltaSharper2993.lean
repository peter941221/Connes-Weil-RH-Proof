import ConnesWeilRH.Dev.C1RouteBDeltaBounds2980
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ConnesWeilRH.Dev

theorem routeBDeltaSharper2993 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    (3 : ℝ) / 200 < Real.sin δ ∧ Real.sin δ < (1 : ℝ) / 50 ∧
      (999 : ℝ) / 1000 < Real.cos δ ∧ Real.cos δ ≤ 1 := by
  have hδpos : 0 < δ := by linarith [hδlo, Real.pi_pos]
  have hδsmall : δ < (1 : ℝ) / 50 := by
    nlinarith [hδhi, Real.pi_lt_d2]
  have hδlower : (1 : ℝ) / 64 < δ := by
    nlinarith [hδlo, Real.pi_gt_three]
  have hslo := Real.sin_gt_sub_cube hδpos (by nlinarith [hδsmall])
  have hshi := Real.sin_le hδpos.le
  have hclo := Real.one_sub_sq_div_two_lt_cos (ne_of_gt hδpos)
  have hsq : δ ^ 2 < ((1 : ℝ) / 50) ^ 2 := by
    nlinarith [sq_nonneg (δ - (1 : ℝ) / 50),
      sq_nonneg (δ + (1 : ℝ) / 50), hδpos, hδsmall]
  constructor
  · nlinarith [hslo, hδlower, hsq]
  constructor
  · exact lt_of_le_of_lt hshi hδsmall
  constructor
  · nlinarith [hclo, hsq]
  · exact Real.cos_le_one δ

end ConnesWeilRH.Dev
