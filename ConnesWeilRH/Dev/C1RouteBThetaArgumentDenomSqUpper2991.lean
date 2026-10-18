import ConnesWeilRH.Dev.C1RouteBThetaArgumentDenomSq2989

namespace ConnesWeilRH.Dev

theorem routeBThetaArgumentDenomNormSqUpper2991 (θ : ℝ) :
    Complex.normSq (1 - (routeBThetaTCoarse2982 θ) ^ 2) ≤
      ((401 : ℝ) / 400) ^ 2 := by
  have ht := routeBThetaTNormInvariant2983 θ
  have htri : ‖1 - (routeBThetaTCoarse2982 θ) ^ 2‖ ≤
      ‖(1 : ℂ)‖ + ‖(routeBThetaTCoarse2982 θ) ^ 2‖ := by
    exact norm_sub_le _ _
  rw [norm_one, norm_pow, ht] at htri
  rw [← Complex.sq_norm]
  nlinarith [htri,
    sq_nonneg (‖1 - (routeBThetaTCoarse2982 θ) ^ 2‖ - (401 : ℝ) / 400),
    norm_nonneg (1 - (routeBThetaTCoarse2982 θ) ^ 2)]

end ConnesWeilRH.Dev
