import ConnesWeilRH.Dev.C1RouteBComplexTanhExpCayley3012
import ConnesWeilRH.Dev.C1RouteBCauchyRemainder2891

namespace ConnesWeilRH.Dev

theorem complex_centered_cayley_exp_form3013 {z : ℂ} :
    (1 + Complex.tanh z) / 2 =
      Complex.exp (2 * z) / (Complex.exp (2 * z) + 1) := by
  rw [complex_tanh_eq_exp_cayley3012]
  have hden : Complex.exp (2 * z) + 1 ≠ 0 := by
    intro h
    have hneg : Complex.exp (2 * z) = -1 := by linarith
    have hmul := congrArg Complex.norm hneg
    rw [Complex.norm_exp] at hmul
    norm_num at hmul
  field_simp [hden]
  ring

theorem routeBCenteredQ_exp_form3013 {z : ℂ} :
    routeBCenteredQ2900 z =
      Complex.exp (2 * z) / (Complex.exp (2 * z) + 1) := by
  rw [routeBCenteredQ2900, complex_centered_cayley_exp_form3013]

end ConnesWeilRH.Dev
