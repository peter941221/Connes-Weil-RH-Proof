import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBNonnegProductBounds2939 {a x b c y d : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x) (hxb : x ≤ b)
    (hc : 0 ≤ c) (hy : c ≤ y) (hyd : y ≤ d) :
    a * c ≤ x * y ∧ x * y ≤ b * d := by
  have hx0 : 0 ≤ x := ha.trans hx
  have hy0 : 0 ≤ y := hc.trans hy
  have hb0 : 0 ≤ b := hx0.trans hxb
  constructor
  · exact mul_le_mul hx hy hc hx0
  · exact mul_le_mul hxb hyd hy0 hb0

theorem routeBNonposProductBounds2939 {a x b c y d : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x) (hxb : x ≤ b)
    (hd : d ≤ 0) (hcd : c ≤ y) (hyd : y ≤ d) :
    b * c ≤ x * y ∧ x * y ≤ a * d := by
  have hx0 : 0 ≤ x := ha.trans hx
  have hc0 : c ≤ 0 := hcd.trans (hyd.trans hd)
  constructor
  · exact (mul_le_mul_of_nonpos_right hxb hc0).trans
      (mul_le_mul_of_nonneg_left hcd hx0)
  · exact (mul_le_mul_of_nonneg_left hyd hx0).trans
      (mul_le_mul_of_nonpos_right hx hd)

end ConnesWeilRH.Dev
