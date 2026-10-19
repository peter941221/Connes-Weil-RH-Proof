import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBThetaQuotientRealNumeratorCircle3001
    {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = (1 : ℝ) / 400) :
    4 * x * (1 - x ^ 2 + y ^ 2) - 8 * x * y ^ 2 =
      ((399 : ℝ) / 100) * x := by
  nlinarith [hcircle]

theorem routeBThetaQuotientImagNumeratorCircle3001
    {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = (1 : ℝ) / 400) :
    4 * y * (1 + x ^ 2 + y ^ 2) =
      ((401 : ℝ) / 100) * y := by
  nlinarith [hcircle]

theorem routeBThetaQuotientDenominatorCircle3001
    {x y : ℝ} (hcircle : x ^ 2 + y ^ 2 = (1 : ℝ) / 400) :
    (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 =
      ((401 : ℝ) / 400) ^ 2 - 4 * x ^ 2 := by
  nlinarith [hcircle]

end ConnesWeilRH.Dev
