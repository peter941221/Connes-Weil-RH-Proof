import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3363
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3365
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3367

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 10000000 in
theorem signed_jet_sum_endpoint3368_cell0_order2_family4_reHi_le :
    (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 0 4)
          (ratWeightedUnitJetRect3310 2 1 0 4))
        (ratWeightedUnitJetRect3310 2 2 0 4)).reHi ≤ 1 / 10 ^ 14 := by
  simp only [RatRect3276.add]
  linarith [
    signed_jet_endpoint3363_cell0_order2_index0_family4_reHi_le,
    signed_jet_endpoint3365_cell0_order2_index1_family4_reHi_le,
    signed_jet_endpoint3367_cell0_order2_index2_family4_reHi_le]

end ConnesWeilRH.Dev