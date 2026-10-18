import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBIteratedDerivSinNorm_le_one2918 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 := by
  obtain h | h := n.even_or_odd
  · obtain ⟨k, rfl⟩ := h
    rw [show k + k = 2 * k by omega, Real.iteratedDeriv_even_sin]
    simpa [Real.norm_eq_abs] using (abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩)
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_odd_sin]
    simpa [Real.norm_eq_abs] using (abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)

theorem routeBIteratedDerivCosNorm_le_one2918 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  obtain h | h := n.even_or_odd
  · obtain ⟨k, rfl⟩ := h
    rw [show k + k = 2 * k by omega, Real.iteratedDeriv_even_cos]
    simpa [Real.norm_eq_abs] using (abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
  · obtain ⟨k, rfl⟩ := h
    rw [Real.iteratedDeriv_odd_cos]
    simpa [Real.norm_eq_abs] using (abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩)

end ConnesWeilRH.Dev
