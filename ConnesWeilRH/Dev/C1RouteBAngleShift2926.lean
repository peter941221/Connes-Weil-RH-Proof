import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBLocalAngleShiftBounds2926 :
    -(Real.pi / 2) < (107 : ℝ) * Real.pi / 64 - 2 * Real.pi ∧
      (107 : ℝ) * Real.pi / 64 - 2 * Real.pi < Real.pi / 2 ∧
      -(Real.pi / 2) < (107 : ℝ) * Real.pi / 64 + Real.pi / 1024 - 2 * Real.pi ∧
      (107 : ℝ) * Real.pi / 64 + Real.pi / 1024 - 2 * Real.pi < Real.pi / 2 := by
  constructor <;> nlinarith [Real.pi_pos]

theorem routeBLocalAngleShiftInterval2926 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024) :
    -(Real.pi / 2) < θ - 2 * Real.pi ∧ θ - 2 * Real.pi < Real.pi / 2 := by
  rcases routeBLocalAngleShiftBounds2926 with ⟨hl, _, _, hr⟩
  constructor <;> linarith

end ConnesWeilRH.Dev
