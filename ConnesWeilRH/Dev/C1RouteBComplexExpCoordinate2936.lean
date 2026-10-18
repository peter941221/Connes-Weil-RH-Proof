import Mathlib.Analysis.Complex.Trigonometric

namespace ConnesWeilRH.Dev

theorem routeBComplexExpReCoordinate2936 (z : ℂ) :
    (Complex.exp z).re = Real.exp z.re * Real.cos z.im := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp [mul_add, mul_comm, mul_left_comm, mul_assoc]

theorem routeBComplexExpImCoordinate2936 (z : ℂ) :
    (Complex.exp z).im = Real.exp z.re * Real.sin z.im := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp [mul_add, mul_comm, mul_left_comm, mul_assoc]

end ConnesWeilRH.Dev
