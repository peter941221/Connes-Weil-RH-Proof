import ConnesWeilRH.Dev.C1RouteBThetaSharpCoordinates2998
import ConnesWeilRH.Dev.C1RouteBThetaTNormSq2984

namespace ConnesWeilRH.Dev

/- The coordinate box is constrained to the exact circle inherited from the
   sine/cosine parameterization.  This correlation is required by the
   doubled-argument quotient proof; independent corners are not admissible. -/
theorem routeBThetaTSharperCircle2999 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    let z := routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)
    z.re ^ 2 + z.im ^ 2 = (1 : ℝ) / 400 := by
  dsimp
  have hnorm := routeBThetaTNormSq2984 (5 * Real.pi / 3 + δ)
  simpa [routeBThetaTSharper2996, routeBThetaTCoarse2982,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_two] using hnorm

end ConnesWeilRH.Dev
