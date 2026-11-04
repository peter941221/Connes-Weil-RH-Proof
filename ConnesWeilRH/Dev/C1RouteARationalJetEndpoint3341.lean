import ConnesWeilRH.Dev.C1RouteARationalJetEndpoint3340

namespace ConnesWeilRH.Dev

theorem signed_jet_sum3341_cell0_order2_reLo_le_zero :
    (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 0 4)
          (ratWeightedUnitJetRect3310 2 1 0 4))
        (ratWeightedUnitJetRect3310 2 2 0 4)).reLo ≤ 0 := by
  simp only [RatRect3276.add]
  linarith [
    signed_jet_endpoint3338_cell0_order2_index0_reLo_le_zero,
    signed_jet_endpoint3340_cell0_order2_index1_reLo_le_zero,
    signed_jet_endpoint3339_cell0_order2_index2_reLo_le_zero]

end ConnesWeilRH.Dev
