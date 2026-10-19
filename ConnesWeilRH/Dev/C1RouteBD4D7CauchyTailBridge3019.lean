import ConnesWeilRH.Dev.C1RouteBCauchyGlobalBound3018
import ConnesWeilRH.Dev.C1RouteBLedgerAggregate2811

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeB_d4d7_cauchy_tail_bridge3019
    {finite4 finite7 tail4 tail7 : ℝ}
    (hfinite4 : finite4 ≤ routeBD4LedgerAggregate2811)
    (hfinite7 : finite7 ≤ routeBD7LedgerAggregate2811)
    (htail4 : 0 ≤ tail4)
    (htail7 : 0 ≤ tail7)
    (htail4_small : tail4 < 1 / 10 ^ 13)
    (htail7_small : tail7 < 1 / 10 ^ 13) :
    finite4 + tail4 < 1500 ∧
    finite7 + tail7 < 2000000000 := by
  constructor
  · have hmargin : routeBD4LedgerAggregate2811 + 1 / 10 ^ 13 < 1500 := by
      norm_num [routeBD4LedgerAggregate2811]
    linarith
  · have hmargin : routeBD7LedgerAggregate2811 + 1 / 10 ^ 13 <
        2000000000 := by
      norm_num [routeBD7LedgerAggregate2811]
    linarith

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
