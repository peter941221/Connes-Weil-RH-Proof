import ConnesWeilRH.Dev.C1RouteBCauchyRemainder2891

namespace ConnesWeilRH.Dev

theorem routeBArgumentRealFormula2945 {x y : ℝ}
    (hden : (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 ≠ 0) :
    (2 * ((x : ℂ) + (y : ℝ) * Complex.I) /
        (1 - ((x : ℂ) + (y : ℝ) * Complex.I) ^ 2)).re =
      (2 * x * (1 - x ^ 2 + y ^ 2) - 4 * x * y ^ 2) /
        ((1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.pow_two, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, zero_sub, one_mul, mul_one]
  field_simp [hden]
  ring

end ConnesWeilRH.Dev
