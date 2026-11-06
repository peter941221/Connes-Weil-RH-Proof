import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3424
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3424Im
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpointAbs3395
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371
import ConnesWeilRH.Dev.C1RouteARationalPhysicalLinearConsumer3427
import ConnesWeilRH.Dev.C1RouteARationalPhysicalIdentity3428

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3429 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 1 / 100 := by
  have h1abs := ratWeightedUnitJetRect_cell1_order2_index1_family4_endpointAbs_le3395
  have h2abs := ratWeightedUnitJetRect_cell1_order2_index2_family4_endpointAbs_le3395
  have h1abs' := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2abs' := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1 := ratRect_reLo_ge_neg_abs_bound3342
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2 := ratRect_reLo_ge_neg_abs_bound3342
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1bound : -(1 / 10 ^ 25 : ℚ) ≤
      (ratWeightedUnitJetRect3310 2 1 1 4).reLo := by
    linarith [h1, h1abs'.trans h1abs]
  have h2bound : -(1 / 10 ^ 33 : ℚ) ≤
      (ratWeightedUnitJetRect3310 2 2 1 4).reLo := by
    linarith [h2, h2abs'.trans h2abs]
  have h1absI := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2absI := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1I := ratRect_imHi_le_abs_bound3342
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2I := ratRect_imHi_le_abs_bound3342
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1boundI :
      (ratWeightedUnitJetRect3310 2 1 1 4).imHi ≤ 1 / 10 ^ 25 := by
    linarith [h1I, h1absI.trans h1abs]
  have h2boundI :
      (ratWeightedUnitJetRect3310 2 2 1 4).imHi ≤ 1 / 10 ^ 33 := by
    linarith [h2I, h2absI.trans h2abs]
  have hrealLo : -(32 / 10 ^ 18 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo := by
    unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    linarith [signed_coordinate_jet_endpoint3424_cell1_order2_index0_family4_reLo_ge,
      h1bound, h2bound]
  have himagHi : (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi ≤
      32 / 10 ^ 18 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
    unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    linarith [signed_coordinate_jet_endpoint3424_cell1_order2_index0_family4_imHi_le,
      h1boundI, h2boundI]
  apply ratWeightedPhysicalTerm_cell1_family4_le_of_linear3427
    (realLower := (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo)
    (imagUpper := (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi)
  · exact ratWeightedPhysicalTerm_cell1_family4_identity3428
  · exact hrealLo
  · exact himagHi

end ConnesWeilRH.Dev
