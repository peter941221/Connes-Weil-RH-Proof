import ConnesWeilRH.Dev.C1RouteBSeedCellGeometry2809
import Mathlib.Tactic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

def routeBSeedEndpoint2833 (i : ℕ) : ℝ :=
  (8192 + 2047 * i : ℝ) / 33554432

theorem routeBSeedEndpoint2833_mono {i j : ℕ} (hij : i ≤ j) :
    routeBSeedEndpoint2833 i ≤ routeBSeedEndpoint2833 j := by
  change (8192 + 2047 * (i : ℝ)) / 33554432 ≤
    (8192 + 2047 * (j : ℝ)) / 33554432
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 33554432)).2
  nlinarith

theorem routeBSeedEndpoint2833_cell_eq {i : ℕ} :
    routeBSeedEndpoint2833 i = (routeBSeedCell2809 i).lo := by
  rfl

theorem routeBSeedEndpoint2833_cell_width {i : ℕ} :
    routeBSeedEndpoint2833 (i + 1) - routeBSeedEndpoint2833 i =
      (2047 : ℝ) / 33554432 := by
  unfold routeBSeedEndpoint2833
  norm_num [Nat.cast_add]
  ring

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
