import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3411
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateJetEndpoint3411Im
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpointAbs3395
import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3412 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 1 := by
  have hordered := ratWeightedJetSumRect_cell1_order2_family4_ordered3386
  have h0re := signed_coordinate_jet_endpoint3411_cell1_order2_index0_family4_reLo_ge
  have h0im := signed_coordinate_jet_endpoint3411_cell1_order2_index0_family4_imHi_le
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
  have hrealLo :
      -(32 / 10 ^ 16 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤
        (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo := by
    unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    linarith [h0re, h1bound, h2bound]
  have himagHi :
      (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi ≤
        32 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
    unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    linarith [h0im, h1boundI, h2boundI]
  have hphysical := ratWeightedPhysicalTermRect3310_family4_reHi_signed3332
    1 hordered.1 hordered.2
  rw [hphysical]
  norm_num [ratCoefficientRect3282, Matrix.cons_val_four] at ⊢
  have hrealLoExplicit : -(32 / 10 ^ 16 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤
      (((ratWeightedUnitJetRect3310 2 0 1 4).add
        (ratWeightedUnitJetRect3310 2 1 1 4)).add
        (ratWeightedUnitJetRect3310 2 2 1 4)).reLo := by
    simpa [ratWeightedJetSumRect_cell1_order2_family4_3386] using hrealLo
  have himagHiExplicit :
      (((ratWeightedUnitJetRect3310 2 0 1 4).add
        (ratWeightedUnitJetRect3310 2 1 1 4)).add
        (ratWeightedUnitJetRect3310 2 2 1 4)).imHi ≤
      32 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
    simpa [ratWeightedJetSumRect_cell1_order2_family4_3386] using himagHi
  nlinarith [hrealLoExplicit, himagHiExplicit]

end ConnesWeilRH.Dev






