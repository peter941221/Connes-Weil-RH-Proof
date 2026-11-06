import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386

namespace ConnesWeilRH.Dev

theorem ratWeightedPhysicalTerm_cell1_family4_identity3428 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi =
      (-(6001732121601251 : ℚ) / 32) *
          (((ratWeightedUnitJetRect3310 2 0 1 4).add
            (ratWeightedUnitJetRect3310 2 1 1 4)).add
            (ratWeightedUnitJetRect3310 2 2 1 4)).reLo -
        (-(6739580861423611 : ℚ) / 128) *
          (((ratWeightedUnitJetRect3310 2 0 1 4).add
            (ratWeightedUnitJetRect3310 2 1 1 4)).add
            (ratWeightedUnitJetRect3310 2 2 1 4)).imHi := by
  exact ratWeightedPhysicalTermRect3310_family4_reHi_signed3332
    1 ratWeightedJetSumRect_cell1_order2_family4_ordered3386.1
      ratWeightedJetSumRect_cell1_order2_family4_ordered3386.2

end ConnesWeilRH.Dev
