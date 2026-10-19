import ConnesWeilRH.Dev.C1RouteBCayleyNormBound3011
import Mathlib.Analysis.Complex.Trigonometric

namespace ConnesWeilRH.Dev

theorem complex_tanh_eq_exp_cayley3012 {z : ℂ} :
    Complex.tanh z =
      (Complex.exp (2 * z) - 1) / (Complex.exp (2 * z) + 1) := by
  rw [Complex.tanh, Complex.sinh, Complex.cosh]
  have hexp : Complex.exp (-z) ≠ 0 := Complex.exp_ne_zero _
  have hsum : Complex.exp z + Complex.exp (-z) ≠ 0 := by
    intro h
    have hmul := congrArg (fun w : ℂ => w * Complex.exp z) h
    rw [add_mul, ← Complex.exp_add, ← Complex.exp_add] at hmul
    simp [Complex.exp_ne_zero] at hmul
  field_simp [hsum, hexp]
  rw [← Complex.exp_add]
  ring_nf

end ConnesWeilRH.Dev
