import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Basic

/-!
Critical-line Gamma modulus (866-accredited analytic brick for the archimedean sign).

862 pinned the band-test sign slot to `Re[Gamma(a + I/2)^4] >= 0`. This module
separates the trivial *modulus* side as an exact closed form:

    Gamma(1/2 + I t) * Gamma(1/2 - I t) = pi / cosh(pi t)     (reflection)

with the right side a positive real for real t. Built off the library
`Complex.Gamma_mul_Gamma_one_sub` + sine-sum on the critical line, it verifies
axiom-clean off `[propext, Classical.choice, Quot.sound]` and reduces the open
sign problem to exactly the argument (phase) bound -- the only remaining content.

Target axioms: [propext, Classical.choice, Quot.sound].
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace GammaCriticalLineModulus

noncomputable section
open Complex

/-- `sin (pi/2) = 1` as a complex number. -/
lemma sin_pi_half_complex : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
  rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_sin]
  simp [Real.sin_pi_div_two]

/-- `cos (pi/2) = 0` as a complex number. -/
lemma cos_pi_half_complex : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
  rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cos]
  simp [Real.cos_pi_div_two]

/-- `sin (pi*(1/2 + I t)) = cosh(pi*t)`, a positive real for real t. -/
theorem sin_pi_half_add_i (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  have harg : (Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) =
      (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul]
    ring
  rw [harg]
  rw [Complex.sin_add_mul_I ((Real.pi : ℂ) / 2) ((Real.pi * t : ℝ) : ℂ)]
  rw [sin_pi_half_complex, cos_pi_half_complex]
  simp

/-- Gamma reflection on the critical line: `Gamma(1/2 + i t) * Gamma(1/2 - i t)
   = pi / cosh(pi*t)` (complex identity, right side real positive). -/
theorem gamma_critical_line_reflection (t : ℝ) :
    Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
      Complex.Gamma ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
        (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := by
  let z : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have href : Complex.Gamma z * Complex.Gamma (1 - z) =
      (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) :=
    Complex.Gamma_mul_Gamma_one_sub z
  have harg : (Real.pi : ℂ) * z = (Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    rfl
  have hzsub : 1 - z = (1 / 2 : ℂ) - Complex.I * (t : ℂ) := by
    dsimp [z]
    ring_nf
  rw [hzsub, harg] at href
  rw [sin_pi_half_add_i t] at href
  exact href

/-- Positive real modulus: `Real.pi / Real.cosh (Real.pi * t) > 0` for every real
   t. This is the closed-form content the critical-line reflection pins down. -/
theorem gamma_critical_line_modulus_real (t : ℝ) :
    0 < Real.pi / Real.cosh (Real.pi * t) :=
  div_pos Real.pi_pos (Real.cosh_pos (Real.pi * t))

end
end GammaCriticalLineModulus
end Dev
end Source
end ConnesWeilRH
