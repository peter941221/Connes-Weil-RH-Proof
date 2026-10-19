import ConnesWeilRH.Dev.C1RouteBThetaQuotientCircleReduction3001

namespace ConnesWeilRH.Dev

theorem routeBThetaImagQuotientBounds3003
    {x y d : ℝ}
    (hxlo : (255 : ℝ) / 10000 ≤ x)
    (hxhi : x ≤ (26 : ℝ) / 1000)
    (hylo : -(43 : ℝ) / 1000 ≤ y)
    (hyhi : y ≤ -(425 : ℝ) / 10000)
    (hcircle : x ^ 2 + y ^ 2 = (1 : ℝ) / 400)
    (hd : 0 < d)
    (hdEq : d = ((401 : ℝ) / 400) ^ 2 - 4 * x ^ 2) :
    -(1715760948859532 : ℝ) / 10 ^ 16 ≤
        ((401 : ℝ) / 100) * y / d ∧
      ((401 : ℝ) / 100) * y / d ≤
        -(1712505045774558 : ℝ) / 10 ^ 16 := by
  constructor
  · apply (le_div_iff₀ hd).2
    rw [hdEq]
    nlinarith [hcircle,
      sq_nonneg (x - (255 : ℝ) / 10000),
      sq_nonneg (x - (26 : ℝ) / 1000),
      sq_nonneg (y + (43 : ℝ) / 1000),
      sq_nonneg (y + (425 : ℝ) / 10000)]
  · apply (div_le_iff₀ hd).2
    rw [hdEq]
    nlinarith [hcircle,
      sq_nonneg (x - (255 : ℝ) / 10000),
      sq_nonneg (x - (26 : ℝ) / 1000),
      sq_nonneg (y + (43 : ℝ) / 1000),
      sq_nonneg (y + (425 : ℝ) / 10000)]

end ConnesWeilRH.Dev
