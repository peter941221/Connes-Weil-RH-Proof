import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBSinIteratedDerivEvenZero2951 (k : ℕ) :
    iteratedDeriv (2 * k) Real.sin 0 = 0 := by
  rw [Real.iteratedDeriv_even_sin]
  simp

theorem routeBSinIteratedDerivOddZero2951 (k : ℕ) :
    iteratedDeriv (2 * k + 1) Real.sin 0 = (-1 : ℝ) ^ k := by
  rw [Real.iteratedDeriv_odd_sin]
  simp

theorem routeBCosIteratedDerivEvenZero2951 (k : ℕ) :
    iteratedDeriv (2 * k) Real.cos 0 = (-1 : ℝ) ^ k := by
  rw [Real.iteratedDeriv_even_cos]
  simp

theorem routeBCosIteratedDerivOddZero2951 (k : ℕ) :
    iteratedDeriv (2 * k + 1) Real.cos 0 = 0 := by
  rw [Real.iteratedDeriv_odd_cos]
  simp

end ConnesWeilRH.Dev
