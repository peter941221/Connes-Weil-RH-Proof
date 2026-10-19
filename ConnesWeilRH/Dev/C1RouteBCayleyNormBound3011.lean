import ConnesWeilRH.Dev.C1RouteBExpPlusOneNormLower3010
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem complex_cayley_norm_le_add_one3011 {w : ℂ}
    (hden : 1 < ‖w + 1‖) :
    ‖(w - 1) / (w + 1)‖ ≤ ‖w‖ + 1 := by
  have hpos : 0 < ‖w + 1‖ := by linarith
  rw [norm_div]
  apply (div_le_iff₀ hpos).2
  calc
    ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le w 1
    _ = ‖w‖ + 1 := by rw [norm_one]
    _ ≤ (‖w‖ + 1) * ‖w + 1‖ := by
      have hone : 1 ≤ ‖w + 1‖ := le_of_lt hden
      nlinarith [norm_nonneg w]

end ConnesWeilRH.Dev
