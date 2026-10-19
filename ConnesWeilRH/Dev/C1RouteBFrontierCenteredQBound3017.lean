import ConnesWeilRH.Dev.C1RouteBGenericCenteredQNorm3016

namespace ConnesWeilRH.Dev

theorem routeBCenteredQ_frontier_bound3017 :
    ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 20 : ℝ)),
      ‖routeBCenteredQ2900 z‖ ≤ Real.exp ((80 : ℝ) / 399) := by
  intro z hz
  have hs : z ∈ Metric.sphere (0 : ℂ) (1 / 20 : ℝ) :=
    Metric.frontier_ball_subset_sphere hz
  have hnorm : ‖z‖ = (1 : ℝ) / 20 := by
    rw [← dist_zero_right]
    exact (Metric.mem_sphere'.mp hs)
  apply routeBCenteredQNormBoundOfSmallT3016
  rw [hnorm]

end ConnesWeilRH.Dev
