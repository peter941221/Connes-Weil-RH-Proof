import ConnesWeilRH.Dev.C1RouteBThetaQuotientCircleReduction3001

namespace ConnesWeilRH.Dev

theorem routeBThetaRealQuotientBounds3002
    {x d : ℝ}
    (hxlo : (255 : ℝ) / 10000 ≤ x)
    (hxhi : x ≤ (26 : ℝ) / 1000)
    (hd : 0 < d)
    (hdEq : d = ((401 : ℝ) / 400) ^ 2 - 4 * x ^ 2) :
    (10231836241932215 : ℝ) / 10 ^ 17 ≤
        ((399 : ℝ) / 100) * x / d ∧
      ((399 : ℝ) / 100) * x / d ≤ (103 : ℝ) / 1000 := by
  constructor
  · apply (le_div_iff₀ hd).2
    rw [hdEq]
    nlinarith [sq_nonneg (x - (255 : ℝ) / 10000),
      sq_nonneg (x - (26 : ℝ) / 1000)]
  · apply (div_le_iff₀ hd).2
    rw [hdEq]
    nlinarith [sq_nonneg (x - (255 : ℝ) / 10000),
      sq_nonneg (x - (26 : ℝ) / 1000)]

end ConnesWeilRH.Dev
