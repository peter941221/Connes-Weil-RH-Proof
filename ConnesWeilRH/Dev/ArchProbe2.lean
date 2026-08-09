import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
#check Complex.exp_ofReal_mul_I_re
#check Complex.exp_ofReal_mul_I_im
example (z : ℂ) : (((‖z‖ : ℂ) ^ 4) * Complex.exp (((4 * z.arg) : ℝ) * Complex.I)).re = ‖z‖ ^ 4 * Real.cos (4 * z.arg) := by
  rw [← Complex.ofReal_pow, Complex.mul_re]
  rw [Complex.ofReal_im]
  rw [Complex.exp_ofReal_mul_I_im]
  rw [Complex.ofReal_re]
  rw [Complex.exp_ofReal_mul_I_re]
  simp
