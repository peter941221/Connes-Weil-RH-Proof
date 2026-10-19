import ConnesWeilRH.Dev.C1RouteBFrontierCenteredQBound3017
import ConnesWeilRH.Dev.C1RouteBCauchyRemainder2891

namespace ConnesWeilRH.Dev

theorem routeBCenteredQ_closedBall_bound3018
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) (1 / 20 : ℝ)) :
    ‖routeBCenteredQ2900 z‖ ≤ Real.exp ((80 : ℝ) / 399) :=
  routeBCenteredQ_norm_le_of_frontier_bound2901
    (Real.exp ((80 : ℝ) / 399)) routeBCenteredQ_frontier_bound3017 hz

theorem routeBCenteredQ_closedBall_bound_three3018
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) (1 / 20 : ℝ)) :
    ‖routeBCenteredQ2900 z‖ ≤ 3 := by
  have h := routeBCenteredQ_closedBall_bound3018 hz
  have he : Real.exp ((80 : ℝ) / 399) < 3 := by
    apply lt_of_lt_of_le (Real.exp_lt_exp.mpr (by norm_num))
    exact routeBExpOneLtThree2943.le
  linarith

theorem routeBCauchyTailGlobalBound3018 :
    (3 : ℝ) * ((1 : ℝ) / 5) ^ 22 / (1 - (1 : ℝ) / 5) <
      1 / 10 ^ 13 := by
  apply routeBCauchyTailOfCircleBound2891
  · norm_num
  · norm_num

end ConnesWeilRH.Dev
