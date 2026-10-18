import ConnesWeilRH.Dev.C1RouteBDeltaBounds2980

namespace ConnesWeilRH.Dev

theorem routeBThetaTrigCoarse2981 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    -(88 : ℝ) / 100 < Real.sin (5 * Real.pi / 3 + δ) ∧
      Real.sin (5 * Real.pi / 3 + δ) < -(84 : ℝ) / 100 ∧
      (48 : ℝ) / 100 < Real.cos (5 * Real.pi / 3 + δ) ∧
      Real.cos (5 * Real.pi / 3 + δ) < (55 : ℝ) / 100 := by
  have hd := routeBDeltaBounds2980 hδlo hδhi
  have hsqrt0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by norm_num
  have hsqrtlo : (17 : ℝ) / 10 < Real.sqrt 3 := by nlinarith
  have hsrqhi : Real.sqrt 3 < (18 : ℝ) / 10 := by nlinarith
  have hsinbase : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3) / 2 := by
    have harg : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [harg, Real.sin_two_pi_sub, Real.sin_pi_div_three]
    ring
  have hcosbase : Real.cos (5 * Real.pi / 3) = (1 : ℝ) / 2 := by
    have harg : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [harg, Real.cos_two_pi_sub, Real.cos_pi_div_three]
  rw [Real.sin_add, Real.cos_add, hsinbase, hcosbase]
  rcases hd with ⟨hspos, hslt, hclo, hcle⟩
  have hcpos : 0 < Real.cos δ := by linarith
  have hsqrtpos : 0 < Real.sqrt 3 := lt_of_lt_of_le (by norm_num) hsqrtlo.le
  constructor
  · nlinarith [mul_nonneg hsqrt0 hcpos.le]
  constructor
  · nlinarith [mul_nonneg hsqrt0 hcpos.le]
  constructor
  · nlinarith [mul_nonneg hsqrt0 hspos.le]
  · nlinarith [mul_lt_mul_of_pos_left hslt hsqrtpos]

end ConnesWeilRH.Dev
