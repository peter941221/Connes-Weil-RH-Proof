import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310

namespace ConnesWeilRH.Dev

theorem ratWeightedUnitJetSumRect3310_order2_eq
    (cell : ℕ) (family : Fin 30) :
    ratWeightedUnitJetSumRect3310 2 cell family =
      RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell family)
          (ratWeightedUnitJetRect3310 2 1 cell family))
        (ratWeightedUnitJetRect3310 2 2 cell family) := by
  simp [ratWeightedUnitJetSumRect3310, RatRect3276.sumFinset,
    Finset.sum_range_succ, RatRect3276.add]

theorem ratWeightedPhysicalTermRect3310_order2_eq
    (cell : ℕ) (family : Fin 30) :
    ratWeightedPhysicalTermRect3310 2 cell family =
      RatRect3276.mul
        (ratCoefficientRect3282 family)
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell family)
            (ratWeightedUnitJetRect3310 2 1 cell family))
          (ratWeightedUnitJetRect3310 2 2 cell family)) := by
  simp [ratWeightedPhysicalTermRect3310,
    ratWeightedUnitJetSumRect3310_order2_eq]

end ConnesWeilRH.Dev
