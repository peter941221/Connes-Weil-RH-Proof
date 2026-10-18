import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBIteratedDerivSinNorm_le_one2918 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 := by
  obtain h | h := n.even_or_odd
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_even_sin]
    simp [abs_sin_le_one]
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_odd_sin]
    simp [abs_cos_le_one]

theorem routeBIteratedDerivCosNorm_le_one2918 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  obtain h | h := n.even_or_odd
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_even_cos]
    simp [abs_cos_le_one]
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_odd_cos]
    simp [abs_sin_le_one]

end ConnesWeilRH.Dev
