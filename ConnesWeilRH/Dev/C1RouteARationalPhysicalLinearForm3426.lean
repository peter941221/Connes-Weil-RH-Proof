import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332

namespace ConnesWeilRH.Dev

theorem ratCoefficientFamily4LinearForm_le3426
    {realLower imagUpper : ℚ}
    (hreal : -(32 / 10 ^ 18 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤ realLower)
    (himag : imagUpper ≤ 32 / 10 ^ 18 + 1 / 10 ^ 25 + 1 / 10 ^ 33) :
    (-(6001732121601251 : ℚ) / 32) * realLower -
      (-(6739580861423611 : ℚ) / 128) * imagUpper ≤ 1 / 100 := by
  linarith

end ConnesWeilRH.Dev
