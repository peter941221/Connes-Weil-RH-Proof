import ConnesWeilRH.Dev.C1RouteBExpArgumentDouble2947
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ConnesWeilRH.Dev

theorem routeBDoubleACosBounds2949 {y : ℝ}
    (hyLo : (-1715760948859532 : ℝ) / 10 ^ 16 ≤ y)
    (hyHi : y ≤ (-1712505045774558 : ℝ) / 10 ^ 16) :
    (985 : ℝ) / 1000 < Real.cos y ∧ Real.cos y ≤ 1 := by
  have habs : |y| ≤ (172 : ℝ) / 1000 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hsq : y ^ 2 ≤ ((172 : ℝ) / 1000) ^ 2 := by
    exact (sq_le_sq).2 (by
      simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 172 / 1000)] using habs)
  constructor
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := y)
    nlinarith
  · exact Real.cos_le_one y

end ConnesWeilRH.Dev
