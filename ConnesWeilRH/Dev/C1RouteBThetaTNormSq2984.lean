import ConnesWeilRH.Dev.C1RouteBThetaTNormInvariant2983

namespace ConnesWeilRH.Dev

theorem routeBThetaTNormSq2984 (θ : ℝ) :
    Complex.normSq (routeBThetaTCoarse2982 θ) = (1 : ℝ) / 400 := by
  rw [Complex.normSq_apply, routeBThetaTRe2983, routeBThetaTIm2983]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem routeBThetaTNonzero2984 (θ : ℝ) :
    routeBThetaTCoarse2982 θ ≠ 0 := by
  intro h
  have hs := congrArg Complex.normSq h
  rw [routeBThetaTNormSq2984] at hs
  norm_num at hs

end ConnesWeilRH.Dev
