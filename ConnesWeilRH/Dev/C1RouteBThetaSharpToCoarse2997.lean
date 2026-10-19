import ConnesWeilRH.Dev.C1RouteBThetaTSharper2996
import ConnesWeilRH.Dev.C1RouteBThetaTCoarse2982

namespace ConnesWeilRH.Dev

/- The sharp theta rectangle is a strict refinement of the coarse rectangle
   consumed by the existing argument chain.  This bridge keeps the numerical
   tightening usable without duplicating the downstream quotient proofs. -/
theorem routeBThetaTSharperMemCoarse2997 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ))
      routeBThetaTCoarseRect2982 := by
  have hs := routeBThetaTSharperMem2996 hδlo hδhi
  change routeBThetaTCoarseRect2982.reLo ≤
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).re ≤
      routeBThetaTCoarseRect2982.reHi ∧
    routeBThetaTCoarseRect2982.imLo ≤
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).im ∧
    (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).im ≤
      routeBThetaTCoarseRect2982.imHi
  simp only [routeBThetaTCoarseRect2982, ComplexRect2427.mk,
    routeBThetaTCoarse2982, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im] at hs ⊢
  norm_num at hs ⊢
  rcases hs with ⟨hlo, hhi, himlo, himhi⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end ConnesWeilRH.Dev
