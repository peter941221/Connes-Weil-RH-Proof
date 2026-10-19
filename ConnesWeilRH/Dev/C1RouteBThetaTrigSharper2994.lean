import ConnesWeilRH.Dev.C1RouteBDeltaSharper2993

namespace ConnesWeilRH.Dev

theorem routeBThetaTrigSharper2994 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    -(86 : ℝ) / 100 < Real.sin (5 * Real.pi / 3 + δ) ∧
      Real.sin (5 * Real.pi / 3 + δ) < -(85 : ℝ) / 100 ∧
      (51 : ℝ) / 100 < Real.cos (5 * Real.pi / 3 + δ) ∧
      Real.cos (5 * Real.pi / 3 + δ) < (52 : ℝ) / 100 := by
  have hd := routeBDeltaSharper2993 hδlo hδhi
  have hsqrt0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrtlo : (1732 : ℝ) / 1000 < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hsqrthi : Real.sqrt 3 < (1733 : ℝ) / 1000 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hsinbase : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3) / 2 := by
    have harg : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [harg, Real.sin_two_pi_sub, Real.sin_pi_div_three]
    ring
  have hcosbase : Real.cos (5 * Real.pi / 3) = (1 : ℝ) / 2 := by
    have harg : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [harg, Real.cos_two_pi_sub, Real.cos_pi_div_three]
  rw [Real.sin_add, Real.cos_add, hsinbase, hcosbase]
  rcases hd with ⟨hslo, hshi, hclo, hchi⟩
  have hcpos : 0 < Real.cos δ := by linarith
  have hspos : 0 < Real.sin δ := by linarith
  have hp1 : ((1732 : ℝ) / 1000) * ((999 : ℝ) / 1000) <
      Real.sqrt 3 * Real.cos δ := by
    exact (mul_lt_mul_of_pos_right hsqrtlo (by norm_num)).trans
      (mul_lt_mul_of_pos_left hclo (by positivity))
  have hp2 : Real.sqrt 3 * Real.cos δ < (1733 : ℝ) / 1000 := by
    have hh := mul_le_mul_of_nonneg_left hchi
      (by norm_num : (0 : ℝ) ≤ (1733 : ℝ) / 1000)
    have hh' : (1733 : ℝ) / 1000 * Real.cos δ ≤ (1733 : ℝ) / 1000 := by
      simpa using hh
    exact (mul_lt_mul_of_pos_right hsqrthi hcpos).trans_le hh'
  have hp3 : ((1732 : ℝ) / 1000) * ((3 : ℝ) / 200) <
      Real.sqrt 3 * Real.sin δ := by
    exact (mul_lt_mul_of_pos_right hsqrtlo (by norm_num)).trans
      (mul_lt_mul_of_pos_left hslo (by nlinarith [hsqrtlo]))
  have hp4 : Real.sqrt 3 * Real.sin δ <
      ((1733 : ℝ) / 1000) * ((1 : ℝ) / 50) := by
    exact (mul_lt_mul_of_pos_right hsqrthi hspos).trans
      (mul_lt_mul_of_pos_left hshi (by norm_num))
  norm_num at hp1 hp2 hp3 hp4 ⊢
  constructor
  · nlinarith [hp1, hp2, hp3, hp4]
  constructor
  · nlinarith [hp1, hp2, hp3, hp4]
  constructor
  · nlinarith [hp1, hp2, hp3, hp4]
  · nlinarith [hp1, hp2, hp3, hp4]

end ConnesWeilRH.Dev
