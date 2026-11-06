import ConnesWeilRH.Dev.C1RouteARationalSignedJetBlockManifest3312

namespace ConnesWeilRH.Dev

open scoped BigOperators

def routeASignedJetRectBlockDelta3436 : ℚ :=
  (((2 * (65536001 : ℚ) / (10000000 * 40960)) ^ 3) / 2400)

theorem routeASignedJetRectBlockDelta3436_cast_eq_grid_cost :
    (routeASignedJetRectBlockDelta3436 : ℝ) =
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 / 2400 := by
  norm_num [routeASignedJetRectBlockDelta3436, record2680Grid3212,
    diagnosticRadius3201]

noncomputable def routeASignedJetRectBlockUpper3436 (block : Fin 160) : ℚ :=
  if block = 0 then
    routeASignedJetRectBlockUpper3312 block +
      routeASignedJetRectBlockDelta3436
  else
    routeASignedJetRectBlockUpper3312 block

theorem routeASignedJetRectBlockUpper3436_sum_lt_zero :
    (∑ block : Fin 160, routeASignedJetRectBlockUpper3436 block) < 0 := by
  norm_num [routeASignedJetRectBlockUpper3436, routeASignedJetRectBlockUpper3312,
    routeASignedJetRectBlockDelta3436, Fin.sum_univ_succ]

end ConnesWeilRH.Dev
