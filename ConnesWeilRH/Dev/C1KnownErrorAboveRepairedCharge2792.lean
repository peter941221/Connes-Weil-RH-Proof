import ConnesWeilRH.Dev.C1RepairedOwnerCellIntegralTotalUpper2791
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem knownError2109_gt_10000_2792 :
    (10000 : ℝ) < knownError2109 := by
  norm_num [knownError2109]

theorem repairedOwnerTotal_lt_knownError2109_2792
    {total : ℝ} (htotal : total < 10000) :
    total < knownError2109 := by
  exact htotal.trans knownError2109_gt_10000_2792

end ConnesWeilRH.Dev
