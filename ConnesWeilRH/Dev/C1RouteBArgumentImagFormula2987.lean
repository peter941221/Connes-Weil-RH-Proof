import ConnesWeilRH.Dev.C1RouteBArgumentRealFormula2945

namespace ConnesWeilRH.Dev

theorem routeBArgumentImagFormula2987 {x y : ℝ}
    (hden : (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 ≠ 0) :
    (2 * ((x : ℂ) + (y : ℝ) * Complex.I) /
        (1 - ((x : ℂ) + (y : ℝ) * Complex.I) ^ 2)).im =
      (2 * y * (1 + x ^ 2 + y ^ 2)) /
        ((1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    pow_two, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, zero_sub, one_mul, mul_one,
    Complex.normSq_apply]
  norm_num
  field_simp [hden]
  ring_nf

end ConnesWeilRH.Dev
