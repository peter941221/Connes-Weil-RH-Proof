import ConnesWeilRH.Dev.C1RouteAMultiplicityBound

namespace ConnesWeilRH.Dev

noncomputable def tailAcceptanceRatio2354 (rhoBound D4 D2 q lambda : ℝ)
    (iterate shell : ℕ) : ℝ :=
  (3 / 2 : ℝ) * 4 * (128.65 : ℝ) * (3 / 4 : ℝ) ^ shell *
    (3 + rhoBound) ^ 4 * (1 + (3 + rhoBound) ^ 4 / lambda) ^ 2 *
    (q ^ iterate * (D4 * D2)) ^ 2

theorem angular_tail_normalization2354 (D4 D2 q : ℝ) (iterate : ℕ) :
    (2 * Real.pi) ^ 12 *
      (q ^ iterate * ((D4 / (2 * Real.pi) ^ 4) * (D2 / (2 * Real.pi) ^ 2))) ^ 2 =
      (q ^ iterate * (D4 * D2)) ^ 2 := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hpi]

theorem tailAcceptanceRatio2354_eq_scaled_budget
    (rhoBound D4 D2 q lambda : ℝ) (iterate shell : ℕ) (hlambda : lambda ≠ 0) :
    tailAcceptanceRatio2354 rhoBound D4 D2 q lambda iterate shell =
      ((3 / 2 : ℝ) * 4 * (128.65 : ℝ) * (3 / 4 : ℝ) ^ shell *
        (3 + rhoBound) ^ 4 * ((3 + rhoBound) ^ 4 + lambda) ^ 2 *
        (q ^ iterate * (D4 * D2)) ^ 2) / lambda ^ 2 := by
  unfold tailAcceptanceRatio2354
  field_simp [hlambda]
  ring

theorem tailAcceptanceRatio2354_lambda_monotone
    (rhoBound D4 D2 q lower lambda : ℝ) (iterate shell : ℕ)
    (hlower : 0 < lower) (hlambda : lower ≤ lambda) :
    tailAcceptanceRatio2354 rhoBound D4 D2 q lambda iterate shell ≤
      tailAcceptanceRatio2354 rhoBound D4 D2 q lower iterate shell := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le hlower hlambda
  have hquotient : (3 + rhoBound) ^ 4 / lambda ≤ (3 + rhoBound) ^ 4 / lower :=
    div_le_div_of_nonneg_left (by positivity) hlower hlambda
  have hpower : (1 + (3 + rhoBound) ^ 4 / lambda) ^ 2 ≤
      (1 + (3 + rhoBound) ^ 4 / lower) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  unfold tailAcceptanceRatio2354
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity)

theorem tailAcceptanceRatio2354_n2_lane (lambda : ℝ) (hlambda : 256 ≤ lambda) :
    tailAcceptanceRatio2354 41 746785658244 71280628476
      (1 / 4503599627370496) lambda 2 6 < 1 := by
  have hbound := tailAcceptanceRatio2354_lambda_monotone
    41 746785658244 71280628476 (1 / 4503599627370496) 256 lambda 2 6
    (by norm_num) hlambda
  have hanchor : tailAcceptanceRatio2354 41 746785658244 71280628476
      (1 / 4503599627370496) 256 2 6 < 1 := by
    norm_num [tailAcceptanceRatio2354]
  exact lt_of_le_of_lt hbound hanchor

theorem tailAcceptanceRatio2354_n3_lane (lambda : ℝ)
    (hlambda : (1 / 10000000000000 : ℝ) ≤ lambda) :
    tailAcceptanceRatio2354 41 746785658244 71280628476
      (1 / 4503599627370496) lambda 3 6 < 1 := by
  have hbound := tailAcceptanceRatio2354_lambda_monotone
    41 746785658244 71280628476 (1 / 4503599627370496)
    (1 / 10000000000000) lambda 3 6 (by norm_num) hlambda
  have hanchor : tailAcceptanceRatio2354 41 746785658244 71280628476
      (1 / 4503599627370496) (1 / 10000000000000) 3 6 < 1 := by
    norm_num [tailAcceptanceRatio2354]
  exact lt_of_le_of_lt hbound hanchor

end ConnesWeilRH.Dev
