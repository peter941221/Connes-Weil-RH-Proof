import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3393
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3394
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpointAbs3395
import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermBudget3370
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedJetSumRect_cell1_order2_family4_reLo_ge3396 :
    -(64 / 10 ^ 16 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo := by
  have h0 := signed_coordinate_jet_endpoint3393_cell1_order2_index0_family4_reLo_ge
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
  unfold ratWeightedJetSumRect_cell1_order2_family4_3386
  simp [RatRect3276.add]
  linarith [h0, h1bound, h2bound]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedJetSumRect_cell1_order2_family4_imHi_le3396 :
    (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi ≤
      64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
  have h0 := signed_coordinate_jet_endpoint3394_cell1_order2_index0_family4_imHi_le
  have h1abs := ratWeightedUnitJetRect_cell1_order2_index1_family4_endpointAbs_le3395
  have h2abs := ratWeightedUnitJetRect_cell1_order2_index2_family4_endpointAbs_le3395
  have h1abs' := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2abs' := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1 := ratRect_imHi_le_abs_bound3342
    (ratWeightedUnitJetRect3310 2 1 1 4)
  have h2 := ratRect_imHi_le_abs_bound3342
    (ratWeightedUnitJetRect3310 2 2 1 4)
  have h1bound : (ratWeightedUnitJetRect3310 2 1 1 4).imHi ≤
      1 / 10 ^ 25 := by
    linarith [h1, h1abs'.trans h1abs]
  have h2bound : (ratWeightedUnitJetRect3310 2 2 1 4).imHi ≤
      1 / 10 ^ 33 := by
    linarith [h2, h2abs'.trans h2abs]
  unfold ratWeightedJetSumRect_cell1_order2_family4_3386
  simp [RatRect3276.add]
  linarith [h0, h1bound, h2bound]

theorem ratWeightedJetSumRect_cell1_order2_family4_ordered3396 :
    (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).reHi ∧
    (ratWeightedJetSumRect_cell1_order2_family4_3386).imLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi :=
  ratWeightedJetSumRect_cell1_order2_family4_ordered3386

end ConnesWeilRH.Dev