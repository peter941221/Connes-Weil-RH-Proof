import ConnesWeilRH.Dev.C1RouteBThetaTNormSq2984

namespace ConnesWeilRH.Dev

theorem routeBThetaArgumentDenomNonzero2985 (θ : ℝ) :
    1 - (routeBThetaTCoarse2982 θ) ^ 2 ≠ 0 := by
  intro h
  have h2 : (routeBThetaTCoarse2982 θ) ^ 2 = (1 : ℂ) := by
    exact (sub_eq_zero.mp h).symm
  have hsq := congrArg norm h2
  have ht := routeBThetaTNormInvariant2983 θ
  rw [norm_pow, ht] at hsq
  norm_num at hsq

theorem routeBThetaArgumentDefined2985 (θ : ℝ) :
    2 * routeBThetaTCoarse2982 θ /
        (1 - (routeBThetaTCoarse2982 θ) ^ 2) ∈ Set.univ := by
  trivial

end ConnesWeilRH.Dev
