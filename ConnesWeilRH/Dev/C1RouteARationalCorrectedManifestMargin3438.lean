import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309
import ConnesWeilRH.Dev.C1RouteARationalBlockAdjustedMargin3436

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def routeACorrectedSignedBlockUpper3438 (block : Fin 160) : ℚ :=
  if block = 0 then
    routeACorrectedSignedBlockUpper3309 block +
      routeASignedJetRectBlockDelta3436
  else
    routeACorrectedSignedBlockUpper3309 block

theorem routeACorrectedSignedBlockUpper3438_sum_lt_zero :
    (∑ block : Fin 160, routeACorrectedSignedBlockUpper3438 block) < 0 := by
  norm_num [routeACorrectedSignedBlockUpper3438,
    routeACorrectedSignedBlockUpper3309, routeASignedJetRectBlockDelta3436,
    Fin.sum_univ_succ]

end ConnesWeilRH.Dev
