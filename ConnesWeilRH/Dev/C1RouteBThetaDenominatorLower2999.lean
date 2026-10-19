import ConnesWeilRH.Dev.C1RouteBThetaArgumentDenomSq2989

namespace ConnesWeilRH.Dev

theorem routeBThetaDoubledDenominatorLower2999 (θ : ℝ) :
    ((399 : ℝ) / 400) ^ 2 ≤
      (1 - (routeBThetaTCoarse2982 θ).re ^ 2 +
          (routeBThetaTCoarse2982 θ).im ^ 2) ^ 2 +
        (2 * (routeBThetaTCoarse2982 θ).re *
          (routeBThetaTCoarse2982 θ).im) ^ 2 := by
  have h := routeBThetaArgumentDenomNormSqLower2989 θ
  simpa [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.pow_two] using h

end ConnesWeilRH.Dev
