import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermBudget3370
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetAbsBudget3388

namespace ConnesWeilRH.Dev

theorem ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3387 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 7 := by
  have hordered := ratWeightedJetSumRect_cell1_order2_family4_ordered3386
  have hreal0 := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3386)
  have himag0 := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell1_order2_family4_3386)
  have hbudget := ratWeightedUnitJetSumRect_cell1_order2_family4_endpointAbs_le3388
  have hreal : ratRectRealEndpointAbsBound3342
      (ratWeightedJetSumRect_cell1_order2_family4_3386) ≤ 27 / 10 ^ 15 :=
    hreal0.trans hbudget
  have himag : ratRectImagEndpointAbsBound3342
      (ratWeightedJetSumRect_cell1_order2_family4_3386) ≤ 27 / 10 ^ 15 := by
    exact himag0.trans hbudget
  exact le_trans
    (ratWeightedPhysicalTermRect3310_family4_reHi_le_of_coordinate_budgets3370
      1 hordered.1 hordered.2 (27 / 10 ^ 15) (27 / 10 ^ 15) hreal himag)
    (by norm_num [ratCoefficientRect3282, Matrix.cons_val_four])

end ConnesWeilRH.Dev
