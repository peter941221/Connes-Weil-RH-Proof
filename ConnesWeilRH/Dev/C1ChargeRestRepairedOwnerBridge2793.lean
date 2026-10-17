import ConnesWeilRH.Dev.C1KnownErrorAboveRepairedCharge2792
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem chargeRest_le_knownError_of_repaired_owner_bridge2793
    {chargeRest repairedTotal : ℝ}
    (hchargeRest : chargeRest ≤ repairedTotal)
    (hrepairedTotal : repairedTotal < 10000) :
    chargeRest ≤ knownError2109 := by
  have htotal : repairedTotal < knownError2109 :=
    repairedOwnerTotal_lt_knownError2109_2792 hrepairedTotal
  linarith

theorem chargeRest_le_knownError_of_repaired_owner_identity2793
    {chargeRest repairedTotal : ℝ}
    (hidentity : chargeRest = repairedTotal)
    (hrepairedTotal : repairedTotal < 10000) :
    chargeRest ≤ knownError2109 := by
  apply chargeRest_le_knownError_of_repaired_owner_bridge2793
    (chargeRest := chargeRest) (repairedTotal := repairedTotal)
  · simpa [hidentity]
  · exact hrepairedTotal

end ConnesWeilRH.Dev
