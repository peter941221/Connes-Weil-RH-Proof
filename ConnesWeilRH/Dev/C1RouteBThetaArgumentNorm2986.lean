import ConnesWeilRH.Dev.C1RouteBThetaArgumentDenom2985

namespace ConnesWeilRH.Dev

theorem routeBThetaArgumentNorm2986 (θ : ℝ) :
    ‖2 * routeBThetaTCoarse2982 θ /
        (1 - (routeBThetaTCoarse2982 θ) ^ 2)‖ ≤ (40 : ℝ) / 399 := by
  let t : ℂ := routeBThetaTCoarse2982 θ
  have ht : ‖t‖ = (1 : ℝ) / 20 := routeBThetaTNormInvariant2983 θ
  have hdenpos : 0 < ‖1 - t ^ 2‖ := by
    exact norm_pos_iff.mpr (routeBThetaArgumentDenomNonzero2985 θ)
  have htri : ‖(1 : ℂ)‖ ≤ ‖1 - t ^ 2‖ + ‖t ^ 2‖ := by
    have h := norm_add_le (1 - t ^ 2) (t ^ 2)
    convert h using 1 <;> ring_nf
  have hdenlo : (399 : ℝ) / 400 ≤ ‖1 - t ^ 2‖ := by
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    rw [h1, norm_pow, ht] at htri
    nlinarith [htri]
  rw [norm_div, norm_mul]
  norm_num
  rw [ht]
  apply (div_le_iff₀ hdenpos).2
  nlinarith [hdenlo]

end ConnesWeilRH.Dev
