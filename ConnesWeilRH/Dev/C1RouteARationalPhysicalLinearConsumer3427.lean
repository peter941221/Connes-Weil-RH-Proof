import ConnesWeilRH.Dev.C1RouteARationalPhysicalLinearForm3426

namespace ConnesWeilRH.Dev

theorem ratWeightedPhysicalTerm_cell1_family4_le_of_linear3427
    {realLower imagUpper : ℚ}
    (hidentity :
      (ratWeightedPhysicalTermRect3310 2 1 4).reHi =
        (-(6001732121601251 : ℚ) / 32) * realLower -
          (-(6739580861423611 : ℚ) / 128) * imagUpper)
    (hreal : -(32 / 10 ^ 18 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤ realLower)
    (himag : imagUpper ≤ 32 / 10 ^ 18 + 1 / 10 ^ 25 + 1 / 10 ^ 33) :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 1 / 100 := by
  rw [hidentity]
  exact ratCoefficientFamily4LinearForm_le3426 hreal himag

end ConnesWeilRH.Dev
