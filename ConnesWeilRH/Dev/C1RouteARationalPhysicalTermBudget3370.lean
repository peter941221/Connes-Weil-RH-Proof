import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateBound3342
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetInterval3369

namespace ConnesWeilRH.Dev

theorem ratWeightedPhysicalTermRect3310_family4_reHi_le_of_coordinate_budgets3370
    (cell : ℕ)
    (hre : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reHi)
    (him : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi)
    (realBudget imagBudget : ℚ)
    (hreal : ratRectRealEndpointAbsBound3342
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)) ≤ realBudget)
    (himag : ratRectImagEndpointAbsBound3342
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)) ≤ imagBudget) :
    (ratWeightedPhysicalTermRect3310 2 cell 4).reHi ≤
      (-((ratCoefficientRect3282 4).reHi)) * realBudget +
      (-((ratCoefficientRect3282 4).imHi)) * imagBudget := by
  have hcoordinate := ratWeightedPhysicalTermRect3310_family4_reHi_le_coordinate_bound3342
    cell hre him
  exact le_trans hcoordinate (add_le_add
    (mul_le_mul_of_nonneg_left hreal
      (neg_nonneg.mpr (ratCoefficientRect3282_family4_signs3332.1.le)))
    (mul_le_mul_of_nonneg_left himag
      (neg_nonneg.mpr (ratCoefficientRect3282_family4_signs3332.2.le))))

end ConnesWeilRH.Dev
