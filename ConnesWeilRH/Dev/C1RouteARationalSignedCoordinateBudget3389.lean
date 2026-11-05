import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermBudget3370
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateBound3342
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetAbsBudget3388
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386

namespace ConnesWeilRH.Dev

def ratWeightedJetSumRect_cell1_order2_family4_3389 : RatRect3276 :=
  RatRect3276.add
    (RatRect3276.add
      (ratWeightedUnitJetRect3310 2 0 1 4)
      (ratWeightedUnitJetRect3310 2 1 1 4))
    (ratWeightedUnitJetRect3310 2 2 1 4)

theorem ratWeightedJetSumRect_cell1_order2_family4_eq3389 :
    ratWeightedJetSumRect_cell1_order2_family4_3389 =
      ratWeightedJetSumRect_cell1_order2_family4_3386 := by
  rfl

theorem ratWeightedJetSumRect_cell1_order2_family4_ordered3389 :
    (ratWeightedJetSumRect_cell1_order2_family4_3389).reLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3389).reHi ∧
    (ratWeightedJetSumRect_cell1_order2_family4_3389).imLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3389).imHi := by
  rw [ratWeightedJetSumRect_cell1_order2_family4_eq3389]
  exact ratWeightedJetSumRect_cell1_order2_family4_ordered3386

theorem ratWeightedJetSumRect_cell1_order2_family4_reLo_ge3389 :
    -(27 / 10 ^ 15 : ℚ) ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3389).reLo := by
  rw [ratWeightedJetSumRect_cell1_order2_family4_eq3389]
  have habs := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3386)
  exact le_trans
    (neg_le_neg ratWeightedUnitJetSumRect_cell1_order2_family4_endpointAbs_le3388)
    (le_trans (neg_le_neg habs)
      (ratRect_reLo_ge_neg_abs_bound3342
        (ratWeightedJetSumRect_cell1_order2_family4_3386)))

theorem ratWeightedJetSumRect_cell1_order2_family4_imHi_le3389 :
    (ratWeightedJetSumRect_cell1_order2_family4_3389).imHi ≤
      27 / 10 ^ 15 := by
  rw [ratWeightedJetSumRect_cell1_order2_family4_eq3389]
  have habs := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3386)
  exact le_trans
    (ratRect_imHi_le_abs_bound3342
      (ratWeightedJetSumRect_cell1_order2_family4_3386))
    (le_trans habs
      ratWeightedUnitJetSumRect_cell1_order2_family4_endpointAbs_le3388)

theorem ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3389 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 7 := by
  have hordered := ratWeightedJetSumRect_cell1_order2_family4_ordered3389
  have hreal0 := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3389)
  have himag0 := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3389)
  have hbudget := ratWeightedUnitJetSumRect_cell1_order2_family4_endpointAbs_le3388
  have hreal : ratRectRealEndpointAbsBound3342
      (ratWeightedJetSumRect_cell1_order2_family4_3389) ≤ 27 / 10 ^ 15 :=
    hreal0.trans hbudget
  have himag : ratRectImagEndpointAbsBound3342
      (ratWeightedJetSumRect_cell1_order2_family4_3389) ≤ 27 / 10 ^ 15 :=
    himag0.trans hbudget
  have hphysical :=
    ratWeightedPhysicalTermRect3310_family4_reHi_le_of_coordinate_budgets3370
      1 hordered.1 hordered.2 (27 / 10 ^ 15) (27 / 10 ^ 15) hreal himag
  exact le_trans hphysical (by norm_num [ratCoefficientRect3282, Matrix.cons_val_four])

end ConnesWeilRH.Dev
