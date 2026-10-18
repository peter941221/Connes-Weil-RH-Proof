import ConnesWeilRH.Dev.C1RouteBThetaArgumentNorm2986

namespace ConnesWeilRH.Dev

theorem routeBThetaArgumentDenomNormSqLower2989 (θ : ℝ) :
    ((399 : ℝ) / 400) ^ 2 ≤
      Complex.normSq (1 - (routeBThetaTCoarse2982 θ) ^ 2) := by
  have h := routeBThetaArgumentNorm2986 θ
  have hden := routeBThetaArgumentDenomNonzero2985 θ
  have hnorm : (399 : ℝ) / 400 ≤
      ‖1 - (routeBThetaTCoarse2982 θ) ^ 2‖ := by
    have ht := routeBThetaTNormInvariant2983 θ
    have htri : ‖(1 : ℂ)‖ ≤
        ‖1 - (routeBThetaTCoarse2982 θ) ^ 2‖ +
          ‖(routeBThetaTCoarse2982 θ) ^ 2‖ := by
      have hh := norm_add_le
        (1 - (routeBThetaTCoarse2982 θ) ^ 2)
        ((routeBThetaTCoarse2982 θ) ^ 2)
      convert hh using 1 <;> ring_nf
    rw [norm_one, norm_pow, ht] at htri
    nlinarith [htri]
  rw [← Complex.sq_norm]
  nlinarith [sq_nonneg (‖1 - (routeBThetaTCoarse2982 θ) ^ 2‖)]

end ConnesWeilRH.Dev
