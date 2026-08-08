import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

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

/-- `Real.sinh (pi/2) > 0` by hand, without importing the hyperbolic
positivity lemmas that live in the not-(pre)built `DerivHyp` module.  Proved from
`exp` strict monotonicity + positivity: `exp(pi/2) > exp(-pi/2)`. -/
lemma real_sinh_pi_div_two_pos : (0 : ℝ) < Real.sinh (Real.pi / 2) := by
  rw [Real.sinh_eq]
  rw [Real.exp_neg (Real.pi / 2)]
  have hgt : (1 : ℝ) < Real.exp (Real.pi / 2) := by
    have hp0 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
    simpa using Real.exp_strictMono hp0
  have hposR : (0 : ℝ) < Real.exp (Real.pi / 2) := Real.exp_pos _
  have hgtInvR : (Real.exp (Real.pi / 2))⁻¹ < (1 : ℝ) := (inv_lt_one₀ hposR).mpr hgt
  have hinvR : (Real.exp (Real.pi / 2))⁻¹ < Real.exp (Real.pi / 2) :=
    lt_trans hgtInvR hgt
  exact div_pos (sub_pos.mpr hinvR) (by norm_num)

/-- Pure-imaginary Euler reflection: `Gamma(I/2) * Gamma(-I/2) = 2*pi/sinh(pi/2)`
as a positive real.  This pinches the modulus of `Gamma(1+I/2) = (I/2)*Gamma(I/2)`
(the critical-line arch band factor): the real side is `2*pi/sinh(pi/2)` and the
phase is `Re[Gamma(1+I/2)^4] >= 0` (Burnol-ownership sign gate). -/
theorem Gamma_pure_half_reflection :
    Complex.Gamma (Complex.I / 2) * Complex.Gamma (-(Complex.I / 2)) =
      ((2 * Real.pi / Real.sinh (Real.pi / 2) : ℝ) : ℂ) := by
  let S : ℂ := (Real.sinh (Real.pi / 2) : ℂ)
  let z : ℂ := Complex.I / 2
  let u : ℂ := -z
  have hz : z ≠ 0 := by norm_num [z]
  have hu : u ≠ 0 := by norm_num [u, z]
  have hsu : 1 - z = u + 1 := by
    dsimp [u]
    ring
  have hrecur : Complex.Gamma (1 - z) = u * Complex.Gamma u := by
    rw [hsu]
    exact Complex.Gamma_add_one u hu
  have hsinpi : Complex.sin ((Real.pi : ℂ) * z) = Complex.I * S := by
    simpa [S, z] using sin_pi_im_top
  have hmain : Complex.Gamma z * (u * Complex.Gamma u) =
      (Real.pi : ℂ) / (Complex.I * S) := by
    have hsub : Complex.Gamma z * Complex.Gamma (1 - z) =
        (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by
      simpa [z] using Complex.Gamma_mul_Gamma_one_sub z
    rw [hrecur, hsinpi] at hsub
    simpa using hsub
  have h2 : (Complex.Gamma z * Complex.Gamma u) * u = (Real.pi : ℂ) / (Complex.I * S) := by
    rw [← hmain]
    ring
  have hp_real : (0 : ℝ) < Real.sinh (Real.pi / 2) := real_sinh_pi_div_two_pos
  have hS : S ≠ 0 := by
    dsimp [S]
    rw [← Complex.ofReal_zero]
    intro h
    exact (ne_of_gt hp_real) (Complex.ofReal_inj.mp h)
  have hw : u * (2 * Complex.I) = 1 := by
    dsimp [u, z]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hG : Complex.Gamma z * Complex.Gamma u = (2 * (Real.pi : ℂ)) / S := by
    calc
      Complex.Gamma z * Complex.Gamma u
          = (Complex.Gamma z * Complex.Gamma u) * 1 := by rw [mul_one]
      _ = (Complex.Gamma z * Complex.Gamma u) * (u * (2 * Complex.I)) := by
            rw [← hw]
      _ = ((Complex.Gamma z * Complex.Gamma u) * u) * (2 * Complex.I) := by
            ring
      _ = ((Real.pi : ℂ) / (Complex.I * S)) * (2 * Complex.I) := by
            rw [h2]
      _ = (2 * (Real.pi : ℂ)) / S := by
            field_simp [Complex.I_ne_zero, hS]
  simpa [S, u, z] using hG

end

end GammaImaginaryAxisModulus
end Dev
end Source
end ConnesWeilRH
