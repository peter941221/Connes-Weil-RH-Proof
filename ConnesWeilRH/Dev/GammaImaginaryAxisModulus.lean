import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace GammaImaginaryAxisModulus

noncomputable section

/-- sin (pi * I/2) = I * Real.sinh (pi/2): a pure imaginary of real hyperbolic size.
This is the trig identity at the heart of the Euler reflection for Gamma(I/2),
which fixes the modulus of Gamma(1+I/2) = (I/2)*Gamma(I/2) on the arch band. -/
theorem sin_pi_im_top :
    Complex.sin ((Real.pi : ℂ) * (Complex.I / 2)) =
      Complex.I * (Real.sinh (Real.pi / 2) : ℂ) := by
  have hx : (Real.pi : ℂ) * (Complex.I / 2) = 0 + (((Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div]
    ring_nf
    norm_num
  rw [hx, Complex.sin_add_mul_I 0 (((Real.pi / 2) : ℝ) : ℂ)]
  simp only [Complex.sin_zero, Complex.cos_zero, one_mul, zero_add, zero_mul]
  have href : Complex.sinh ((((Real.pi / 2) : ℝ) : ℂ)) = (Real.sinh (Real.pi / 2) : ℂ) := by
    refine Complex.ext ?re ?im <;> simp only [Complex.ofReal_re, Complex.ofReal_im,
      Complex.sinh_ofReal_re, Complex.sinh_ofReal_im]
  rw [href]
  ring

/-- Pure imaginary half-point is nonzero (a pole-check for the future Gamma recurrence). -/
lemma im_half_ne_zero : (Complex.I / 2 : ℂ) ≠ 0 := by
  norm_num

end

end GammaImaginaryAxisModulus
end Dev
end Source
end ConnesWeilRH
