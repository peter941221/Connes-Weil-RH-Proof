import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ConnesWeilRH.Dev.PhaseGateSandwich

noncomputable section

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ArchPhaseZFourthNonneg

/-!
# Arch-phase 4th-power nonneg sector lemma

Closes the single generic sub-lemma tracked in `docs/proofs/904`: for any
non-zero complex `z` with `|z.arg| < pi/8`, the real part of its fourth power is
nonnegative.  Numeric anchor: Re[Gamma(1+I/2)^4] = +0.26097... > 0.

Polar proof route:

    z     = ‖z‖ * exp (z.arg * I)                  (Complex.norm_mul_exp_arg_mul_I)
    z^4   = ‖z‖^4 * exp ((4 * z.arg) * I)           (mul_pow + Complex.exp_nat_mul)
    (z^4).re = ‖z‖^4 * Real.cos (4 * z.arg)         (Complex.mul_re + Complex.exp_ofReal_mul_I_re)
    |z.arg| < pi/8  =>  |4 * z.arg| < pi/2
                         =>  Real.cos (4 * z.arg) > 0   (Real.cos_pos_of_mem_Ioo)
    ‖z‖^4 > 0  (z != 0)
    => (z^4).re > 0, hence 0 <= (z^4).re.
-/

/-- Polar-form fourth power as a ℂ equality. -/
lemma z_pow4_eq_norm_pow4_mul_exp (z : Complex) :
    z ^ 4 = (‖z‖ : ℂ) ^ 4 * Complex.exp (((4 * z.arg) : ℝ) * Complex.I) := by
  have hxp : Complex.exp (z.arg * Complex.I) ^ 4
      = Complex.exp (((4 * z.arg) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    norm_cast
    ring
  calc
    z ^ 4 = ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)) ^ 4 := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    _ = (‖z‖ : ℂ) ^ 4 * Complex.exp (((4 * z.arg) : ℝ) * Complex.I) := by
      rw [mul_pow, hxp]

/-- Real part of `z^4` in polar coordinates. -/
lemma re_z_pow4_eq_norm_pow4_mul_cos (z : Complex) :
    (z ^ 4).re = ‖z‖ ^ 4 * Real.cos (4 * z.arg) := by
  rw [z_pow4_eq_norm_pow4_mul_exp z]
  rw [← Complex.ofReal_pow, Complex.mul_re]
  rw [Complex.ofReal_im]
  rw [Complex.exp_ofReal_mul_I_im]
  rw [Complex.ofReal_re]
  rw [Complex.exp_ofReal_mul_I_re]
  simp

/-- Sector lemma: with `z != 0` and `|arg z| < pi/8`, `(z^4).re` is positive. -/
theorem re_pow4_pos_of_abs_arg_lt_pi_eighth
    {z : Complex} (hz : z ≠ 0) (h : |z.arg| < Real.pi / 8) :
    0 < (z ^ 4).re := by
  rw [re_z_pow4_eq_norm_pow4_mul_cos z]
  have h4 : |4 * z.arg| < Real.pi / 2 := by
    have h4abs : |4 * z.arg| = 4 * |z.arg| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 4)]
    rw [h4abs]
    have h48 : 4 * (Real.pi / 8) = Real.pi / 2 := by ring
    rw [← h48]
    exact mul_lt_mul_of_pos_left h (by norm_num)
  have hcos : 0 < Real.cos (4 * z.arg) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp h4)
  have hzn : 0 < ‖z‖ := (norm_pos_iff).mpr hz
  have hpow : 0 < (‖z‖ : ℝ) ^ 4 := pow_pos hzn 4
  exact mul_pos hpow hcos

/-- Gate-facing nonnegative form. -/
theorem re_pow4_nonneg_of_abs_arg_lt_pi_eighth
    {z : ℂ} (hz : z ≠ 0) (h : |z.arg| < Real.pi / 8) :
    0 ≤ (z ^ 4).re := by
  exact le_of_lt (re_pow4_pos_of_abs_arg_lt_pi_eighth hz h)

end ArchPhaseZFourthNonneg
end Dev
end Source
end ConnesWeilRH
end









