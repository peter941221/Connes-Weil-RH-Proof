import ConnesWeilRH.Dev.C1RouteAWeightedPartitionAverage2794

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem record2687GridAverageCharge_lt_40000_2795 :
    ((((record2687CellTotalBits.map binary64Value2674).sum : ℚ) : ℝ) / 2048) <
      40000 := by
  have h := record2687GridAverageChargeBelowKnownError2794
  have hknown : knownError2109 / 2048 < (40000 : ℝ) := by
    norm_num [knownError2109]
  exact h.trans hknown

end ConnesWeilRH.Dev
