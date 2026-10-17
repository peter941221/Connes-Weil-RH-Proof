import ConnesWeilRH.Dev.C1ChargeRestRecord2686Identity2800

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem record2686RepairedOwnerTotal_lt_knownError2109_2801 :
    record2686RepairedOwnerTotal2800 < knownError2109 := by
  exact repairedOwnerTotal_lt_knownError2109_2792
    record2686RepairedOwnerTotal_lt_10000_2800

theorem chargeRest_le_knownError_of_record2686_total_le2801
    {chargeRest : ℝ}
    (hchargeRest : chargeRest ≤ record2686RepairedOwnerTotal2800) :
    chargeRest ≤ knownError2109 := by
  exact hchargeRest.trans (le_of_lt record2686RepairedOwnerTotal_lt_knownError2109_2801)

end ConnesWeilRH.Dev
