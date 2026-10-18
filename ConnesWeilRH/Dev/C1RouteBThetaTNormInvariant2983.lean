import ConnesWeilRH.Dev.C1RouteBThetaTCoarse2982

namespace ConnesWeilRH.Dev

theorem routeBThetaTRe2983 (θ : ℝ) :
    (routeBThetaTCoarse2982 θ).re = (1 / 20 : ℝ) * Real.cos θ := by
  simp [routeBThetaTCoarse2982, Complex.mul_re, Complex.add_re,
    Complex.I_re, Complex.I_im]
  have h := congrArg Complex.re (Complex.ofReal_cos θ)
  simpa only [Complex.ofReal_re] using h.symm

theorem routeBThetaTIm2983 (θ : ℝ) :
    (routeBThetaTCoarse2982 θ).im = (1 / 20 : ℝ) * Real.sin θ := by
  simp [routeBThetaTCoarse2982, Complex.mul_im, Complex.add_im,
    Complex.I_re, Complex.I_im]
  have h := congrArg Complex.re (Complex.ofReal_sin θ)
  simpa only [Complex.ofReal_re] using h.symm

theorem routeBThetaTNormInvariant2983 (θ : ℝ) :
    ‖routeBThetaTCoarse2982 θ‖ = (1 : ℝ) / 20 := by
  rw [Complex.norm_def, Complex.normSq_apply, routeBThetaTRe2983,
    routeBThetaTIm2983]
  rw [← Real.sin_sq_add_cos_sq θ]
  have htrig := Real.sin_sq_add_cos_sq θ
  rw [htrig]
  norm_num
  have hnon : 0 ≤ (1 / 20 : ℝ) * Real.cos θ * (1 / 20 * Real.cos θ) +
      1 / 20 * Real.sin θ * (1 / 20 * Real.sin θ) := by
    nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  have hsq := Real.sq_sqrt hnon
  nlinarith [Real.sqrt_nonneg
    ((1 / 20 : ℝ) * Real.cos θ * (1 / 20 * Real.cos θ) +
      1 / 20 * Real.sin θ * (1 / 20 * Real.sin θ))]

end ConnesWeilRH.Dev
