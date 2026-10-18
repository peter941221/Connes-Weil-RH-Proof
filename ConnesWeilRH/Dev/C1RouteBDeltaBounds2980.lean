import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBDeltaBounds2980 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    0 < Real.sin δ ∧ Real.sin δ < (1 : ℝ) / 50 ∧
      (99 : ℝ) / 100 < Real.cos δ ∧ Real.cos δ ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hδpos : 0 < δ := by linarith [hδlo, hpi]
  have hδone : δ ≤ 1 := by
    nlinarith [hδhi, Real.pi_lt_four]
  have hδpi : δ < Real.pi := by
    calc
      δ ≤ Real.pi / 192 + Real.pi / 1024 := hδhi
      _ < Real.pi := by nlinarith [hpi]
  have hsinpos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδpos hδpi
  have hsupper : Real.sin δ ≤ δ := Real.sin_le hδpos.le
  have hcoslower : 1 - δ ^ 2 / 2 < Real.cos δ :=
    Real.one_sub_sq_div_two_lt_cos (ne_of_gt hδpos)
  have hδsmall : δ < (1 : ℝ) / 50 := by
    nlinarith [hδhi, Real.pi_lt_d2]
  constructor
  · exact hsinpos
  constructor
  · exact lt_of_le_of_lt hsupper (lt_of_lt_of_le hδsmall (by norm_num))
  constructor
  · have hsq : δ ^ 2 < ((1 : ℝ) / 10) ^ 2 := by
      nlinarith [sq_nonneg (δ - (1 : ℝ) / 10),
        sq_nonneg (δ + (1 : ℝ) / 10), hδpos, hδsmall]
    nlinarith [hcoslower, hsq]
  · exact Real.cos_le_one δ

end ConnesWeilRH.Dev
