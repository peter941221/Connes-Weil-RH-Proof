import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBNonnegProductBounds2939 {a x b c y d : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x) (hxb : x ≤ b)
    (hc : 0 ≤ c) (hy : c ≤ y) (hyd : y ≤ d) :
    a * c ≤ x * y ∧ x * y ≤ b * d := by
  constructor
  · exact mul_le_mul hx hy hc (by positivity)
  · exact mul_le_mul hxb hyd hc (by positivity)

theorem routeBNonposProductBounds2939 {a x b c y d : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x) (hxb : x ≤ b)
    (hd : d ≤ 0) (hcd : c ≤ y) (hyd : y ≤ d) :
    b * c ≤ x * y ∧ x * y ≤ a * d := by
  constructor
  · exact mul_le_mul_of_nonpos_right hxb (by linarith)
  · exact mul_le_mul_of_nonpos_right hx hd

end ConnesWeilRH.Dev
