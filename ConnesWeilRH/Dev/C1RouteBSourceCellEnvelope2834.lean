import ConnesWeilRH.Dev.C1RouteBEndpointAdapter2833
import ConnesWeilRH.Dev.C1RouteBSeedRectCornerNorm2810

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable def routeBSourceNorm2834 (i : ℕ) (n : ℕ) : ℝ :=
  (seedTransitionJetInterval2734 (routeBSeedCell2809 i) n).endpointAbsMax

noncomputable def routeBSourceCharge2834 (i : ℕ) (n : ℕ) : ℝ :=
  4 * (routeBSeedEndpoint2833 (i + 1) - routeBSeedEndpoint2833 i) *
    routeBSourceNorm2834 i n

theorem routeBSourceCharge_eq_width_norm2834 (i n : ℕ) :
    routeBSourceCharge2834 i n =
      4 * ((2047 : ℝ) / 33554432) * routeBSourceNorm2834 i n := by
  unfold routeBSourceCharge2834
  rw [routeBSeedEndpoint2833_cell_width]

theorem routeBSourceNorm_nonneg2834 (i n : ℕ) :
    0 ≤ routeBSourceNorm2834 i n := by
  unfold routeBSourceNorm2834 RealInterval2429.endpointAbsMax
  positivity

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
