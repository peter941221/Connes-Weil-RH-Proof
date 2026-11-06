import ConnesWeilRH.Dev.C1RouteARationalCellBudgetSensitivity3419
import ConnesWeilRH.Dev.C1RouteARationalSignedJetBlockManifest3312

namespace ConnesWeilRH.Dev

theorem routea_block0_manifest3312_lt_one_e12_3420 :
    routeASignedJetRectBlockUpper3312 0 < 1 / 10 ^ 12 := by
  norm_num [routeASignedJetRectBlockUpper3312]

theorem routea_cell1_second_unit_cost_gt_block0_manifest3312_3420 :
    (routeASignedJetRectBlockUpper3312 0 : ℝ) <
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 / 24 := by
  have hmanifest : (routeASignedJetRectBlockUpper3312 0 : ℝ) <
      (1 / 10 ^ 12 : ℚ) := by
    exact_mod_cast routea_block0_manifest3312_lt_one_e12_3420
  exact hmanifest.trans (by
    norm_num [record2680Grid3212, diagnosticRadius3201])

end ConnesWeilRH.Dev
