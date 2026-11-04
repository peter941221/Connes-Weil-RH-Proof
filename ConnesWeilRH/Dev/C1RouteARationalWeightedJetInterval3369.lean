import ConnesWeilRH.Dev.C1RouteARationalJetEndpoint3341
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3368

namespace ConnesWeilRH.Dev

theorem signed_jet_sum_interval3369_cell0_order2_family4 :
    (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 0 4)
          (ratWeightedUnitJetRect3310 2 1 0 4))
        (ratWeightedUnitJetRect3310 2 2 0 4)).reLo ≤ 0 ∧
    (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 0 4)
          (ratWeightedUnitJetRect3310 2 1 0 4))
        (ratWeightedUnitJetRect3310 2 2 0 4)).reHi ≤ 1 / 10 ^ 14 := by
  constructor
  · exact signed_jet_sum3341_cell0_order2_reLo_le_zero
  · exact signed_jet_sum_endpoint3368_cell0_order2_family4_reHi_le

end ConnesWeilRH.Dev