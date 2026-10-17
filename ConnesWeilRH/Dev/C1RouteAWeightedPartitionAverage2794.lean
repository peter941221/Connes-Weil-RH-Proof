import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2687

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem record2687GridAverageChargeBelowKnownError2794 :
    ((((record2687CellTotalBits.map binary64Value2674).sum : ℚ) : ℝ) / 2048) <
      knownError2109 / 2048 := by
  have h := record2687GridChargeBelowKnownError
  have hp : (0 : ℝ) < 2048 := by norm_num
  exact (div_lt_div_of_pos_right h hp)

end ConnesWeilRH.Dev
