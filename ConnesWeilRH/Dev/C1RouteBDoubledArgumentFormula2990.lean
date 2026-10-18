import ConnesWeilRH.Dev.C1RouteBArgumentImagFormula2987

namespace ConnesWeilRH.Dev

theorem routeBDoubledArgumentReFormula2990 {x y : ℝ}
    (hden : (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 ≠ 0) :
    (4 * ((x : ℂ) + (y : ℝ) * Complex.I) /
        (1 - ((x : ℂ) + (y : ℝ) * Complex.I) ^ 2)).re =
      (4 * x * (1 - x ^ 2 + y ^ 2) - 8 * x * y ^ 2) /
        ((1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2) := by
  have h := routeBArgumentRealFormula2945 (x := x) (y := y) hden
  convert congrArg (fun z : ℝ => 2 * z) h using 1 <;>
    norm_num [div_eq_mul_inv] <;> ring

theorem routeBDoubledArgumentImFormula2990 {x y : ℝ}
    (hden : (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 ≠ 0) :
    (4 * ((x : ℂ) + (y : ℝ) * Complex.I) /
        (1 - ((x : ℂ) + (y : ℝ) * Complex.I) ^ 2)).im =
      (4 * y * (1 + x ^ 2 + y ^ 2)) /
        ((1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2) := by
  have h := routeBArgumentImagFormula2987 (x := x) (y := y) hden
  convert congrArg (fun z : ℝ => 2 * z) h using 1 <;>
    norm_num [div_eq_mul_inv] <;> ring

end ConnesWeilRH.Dev
