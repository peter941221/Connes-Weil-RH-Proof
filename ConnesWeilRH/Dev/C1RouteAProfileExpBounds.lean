import Mathlib.Analysis.SpecialFunctions.Exp

namespace ConnesWeilRH.Dev

theorem profile_exp_interval2442 {qlo q qhi : ℝ}
    (hqlo : 0 < qlo) (hlo : qlo ≤ q) (hhi : q ≤ qhi) :
    Real.exp (-30 / qlo) ≤ Real.exp (-30 / q) ∧
      Real.exp (-30 / q) ≤ Real.exp (-30 / qhi) := by
  constructor
  · apply Real.exp_le_exp.mpr
    have hq : 0 < q := hqlo.trans_le hlo
    exact (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 30)
      hqlo hq).2 (le_of_ge hlo)
  · apply Real.exp_le_exp.mpr
    have hqhi : 0 < qhi := (hqlo.trans hlo).trans hhi
    exact (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 30)
      hq hqhi).2 hhi

end ConnesWeilRH.Dev
