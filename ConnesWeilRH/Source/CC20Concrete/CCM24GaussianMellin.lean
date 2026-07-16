/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24ArchimedeanCarrier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian producers for the CCM24 Fourier--Mellin bridge

This module builds a concrete dilation family on which the genuine additive
Fourier transform and the independently constructed Hardy--Titchmarsh
multiplier can be compared without a stored functional-equation premise.

The family is

`g_a(x) = exp (-pi * a * x^2)`, with `a > 0`.

Its Fourier transform is the reciprocal-width Gaussian, while its Mellin
transform is an explicit real Gamma factor.  The standard member `g_1` then
satisfies the critical Fourier--Mellin functional equation unconditionally.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped FourierTransform

/-- The complex-width Gaussian in Mathlib's `2*pi` Fourier normalization. -/
noncomputable def ccm24ComplexGaussian (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi * b * x ^ 2))

theorem ccm24ComplexGaussian_even (b : ℂ) (x : ℝ) :
    ccm24ComplexGaussian b (-x) = ccm24ComplexGaussian b x := by
  simp [ccm24ComplexGaussian]

/-- The genuine additive Fourier transform sends width `b` to reciprocal
width `b⁻¹`, with the principal square-root normalization. -/
theorem ccm24ComplexGaussian_fourier {b : ℂ} (hb : 0 < b.re) :
    𝓕 (ccm24ComplexGaussian b) =
      fun t : ℝ =>
        1 / b ^ (1 / 2 : ℂ) *
          Complex.exp (-Real.pi / b * t ^ 2) := by
  have hfun : ccm24ComplexGaussian b =
      fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2) := by
    funext x
    simp only [ccm24ComplexGaussian]
    congr 1
    ring
  rw [hfun]
  exact fourier_gaussian_pi hb

/-- The positive-real Gaussian dilation family. -/
noncomputable def ccm24RealGaussian (a : ℝ) (x : ℝ) : ℂ :=
  ccm24ComplexGaussian (a : ℂ) x

theorem ccm24RealGaussian_even (a x : ℝ) :
    ccm24RealGaussian a (-x) = ccm24RealGaussian a x :=
  ccm24ComplexGaussian_even (a : ℂ) x

theorem ccm24RealGaussian_fourier {a : ℝ} (ha : 0 < a) :
    𝓕 (ccm24RealGaussian a) =
      fun t : ℝ =>
        1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp (-Real.pi / (a : ℂ) * t ^ 2) := by
  exact ccm24ComplexGaussian_fourier (by simpa using ha)

theorem ccm24RealGaussian_eq_scaledExponential_square (a : ℝ) :
    ccm24RealGaussian a =
      fun x : ℝ => Complex.exp (-((Real.pi * a) * x ^ 2 : ℝ)) := by
  funext x
  simp only [ccm24RealGaussian, ccm24ComplexGaussian,
    Complex.ofReal_mul, Complex.ofReal_pow]

/-- The unit exponential has a convergent Mellin transform in the right
half-plane. -/
theorem ccm24UnitExponential_mellinConvergent
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => Complex.exp (-x)) s := by
  rw [MellinConvergent]
  simpa only [smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_exp,
    mul_comm] using Complex.GammaIntegral_convergent hs

/-- Scaling the exponential preserves Mellin convergence. -/
theorem ccm24ScaledExponential_mellinConvergent
    {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun x : ℝ => Complex.exp (-(r * x : ℝ))) s := by
  have hunit := ccm24UnitExponential_mellinConvergent hs
  have hscaled :=
    (MellinConvergent.comp_mul_left
      (f := fun x : ℝ => Complex.exp (-x)) (s := s) hr).2 hunit
  simpa only [neg_mul] using hscaled

/-- Exact Mellin/Gamma readback for a positive scaled exponential. -/
theorem ccm24ScaledExponential_mellin_eq_gamma
    {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => Complex.exp (-(r * x : ℝ))) s =
      (1 / r : ℂ) ^ s * Complex.Gamma s := by
  rw [mellin]
  simpa only [smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_exp] using
    (Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr)

/-- Every positive-real Gaussian has a convergent Mellin transform throughout
the right half-plane. -/
theorem ccm24RealGaussian_mellinConvergent
    {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (ccm24RealGaussian a) s := by
  have hs2 : 0 < (s / (2 : ℝ)).re := by
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    linarith
  have hbase := ccm24ScaledExponential_mellinConvergent
    (mul_pos Real.pi_pos ha) hs2
  have hsquare :=
    (MellinConvergent.comp_rpow
      (f := fun y : ℝ =>
        Complex.exp (-((Real.pi * a) * y : ℝ)))
      (s := s) (show (2 : ℝ) ≠ 0 by norm_num)).2 hbase
  rw [ccm24RealGaussian_eq_scaledExponential_square]
  simpa only [Real.rpow_two] using hsquare

/-- Mellin transform of the positive-real Gaussian. -/
theorem ccm24RealGaussian_mellin_eq_gamma
    {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (ccm24RealGaussian a) s =
      (1 / 2 : ℂ) *
        (1 / (Real.pi * a) : ℂ) ^ (s / 2) *
          Complex.Gamma (s / 2) := by
  have hs2 : 0 < (s / (2 : ℝ)).re := by
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    linarith
  have hbase := ccm24ScaledExponential_mellin_eq_gamma
    (mul_pos Real.pi_pos ha) hs2
  have hsquare := mellin_comp_rpow
    (fun y : ℝ => Complex.exp (-((Real.pi * a) * y : ℝ))) s 2
  rw [hbase] at hsquare
  rw [ccm24RealGaussian_eq_scaledExponential_square]
  norm_num [Real.rpow_two, smul_eq_mul, Complex.ofReal_mul] at hsquare ⊢
  simpa only [mul_assoc] using hsquare

/-- The standard self-dual Gaussian. -/
noncomputable def ccm24StandardGaussian : ℝ → ℂ :=
  ccm24RealGaussian 1

theorem ccm24StandardGaussian_fourier :
    𝓕 ccm24StandardGaussian = ccm24StandardGaussian := by
  rw [ccm24StandardGaussian, ccm24RealGaussian_fourier (by norm_num)]
  funext x
  simp only [ccm24RealGaussian, ccm24ComplexGaussian]
  norm_num

/-- The standard Gaussian Mellin transform is one half of the completed real
Gamma factor. -/
theorem ccm24StandardGaussian_mellin_eq_half_GammaR
    {s : ℂ} (hs : 0 < s.re) :
    mellin ccm24StandardGaussian s =
      (1 / 2 : ℂ) * Complex.Gammaℝ s := by
  rw [ccm24StandardGaussian,
    ccm24RealGaussian_mellin_eq_gamma (by norm_num) hs]
  simp only [Complex.Gammaℝ]
  have hpiArg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_nonneg]
    exact Real.pi_pos.ne
  norm_num only [Complex.ofReal_one, mul_one]
  simp only [one_div]
  change
    (2 : ℂ)⁻¹ * ((Real.pi : ℂ)⁻¹ ^ (s / 2)) *
        Complex.Gamma (s / 2) =
      (2 : ℂ)⁻¹ *
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))
  rw [Complex.inv_cpow _ _ hpiArg, ← Complex.cpow_neg]
  have hexponent : -(s / 2) = -s / 2 := by ring
  rw [hexponent]
  ring

/-- The genuine additive Fourier transform of the standard Gaussian satisfies
the CCM24 critical Fourier--Mellin functional equation. -/
theorem ccm24StandardGaussian_criticalFourierMellinFunctionalEquation :
    CCM24CriticalFourierMellinFunctionalEquation
      ccm24StandardGaussian (𝓕 ccm24StandardGaussian) := by
  rw [ccm24StandardGaussian_fourier]
  intro xi
  have hs : 0 < (ccm24CriticalMellinParameter xi).re := by
    rw [ccm24CriticalMellinParameter_re]
    norm_num
  have honeSub : 0 < (1 - ccm24CriticalMellinParameter xi).re := by
    rw [← ccm24CriticalMellinParameter_neg]
    rw [ccm24CriticalMellinParameter_re]
    norm_num
  rw [ccm24StandardGaussian_mellin_eq_half_GammaR hs,
    ccm24StandardGaussian_mellin_eq_half_GammaR honeSub]
  have hden : Complex.Gammaℝ
      (1 - ccm24CriticalMellinParameter xi) ≠ 0 := by
    intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    rcases hzero with ⟨n, h⟩
    have hre := congrArg Complex.re h
    rw [← ccm24CriticalMellinParameter_neg,
      ccm24CriticalMellinParameter_re] at hre
    norm_num at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [ccm24ArchimedeanScatteringPhase_eq_factor_ratio]
  change
    (1 / 2 : ℂ) * Complex.Gammaℝ (ccm24CriticalMellinParameter xi) =
      (Complex.Gammaℝ (ccm24CriticalMellinParameter xi) /
          Complex.Gammaℝ (ccm24CriticalMellinParameter (-xi))) *
        ((1 / 2 : ℂ) *
          Complex.Gammaℝ (1 - ccm24CriticalMellinParameter xi))
  rw [ccm24CriticalMellinParameter_neg]
  field_simp [hden]

/-- Equality of the source Fourier and Hardy--Titchmarsh operators can be
closed on any dense concrete family; the family need not be all Schwartz
vectors. -/
theorem ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_of_denseRange
    {ι : Type*} (v : ι → cc20GlobalLogCrossingL2)
    (hv : DenseRange v)
    (hEq : ∀ i,
      ccm24ArchimedeanSourceFourier (v i) =
        ccm24ArchimedeanHardyTitchmarsh (v i)) :
    ccm24ArchimedeanSourceFourier =
      ccm24ArchimedeanHardyTitchmarsh := by
  apply DFunLike.ext _ _
  intro u
  apply DenseRange.induction_on (p := fun w : cc20GlobalLogCrossingL2 =>
      ccm24ArchimedeanSourceFourier w =
        ccm24ArchimedeanHardyTitchmarsh w) hv u
  · exact isClosed_eq ccm24ArchimedeanSourceFourier.continuous
      ccm24ArchimedeanHardyTitchmarsh.continuous
  · exact hEq

/-! ## The normalized Gaussian dilation orbit -/

/-- Positive-real Gaussians are genuinely integrable on the additive line. -/
theorem integrable_ccm24RealGaussian {a : ℝ} (ha : 0 < a) :
    Integrable (ccm24RealGaussian a) volume := by
  have h := integrable_cexp_neg_mul_sq
    (b := (Real.pi * a : ℝ)) (by simpa using mul_pos Real.pi_pos ha)
  rw [ccm24RealGaussian_eq_scaledExponential_square]
  convert h using 1
  funext x
  congr 1
  push_cast
  ring

theorem continuous_ccm24RealGaussian (a : ℝ) :
    Continuous (ccm24RealGaussian a) := by
  unfold ccm24RealGaussian ccm24ComplexGaussian
  fun_prop

theorem norm_ccm24RealGaussian (a x : ℝ) :
    ‖ccm24RealGaussian a x‖ = Real.exp (-(Real.pi * a) * x ^ 2) := by
  rw [congrFun (ccm24RealGaussian_eq_scaledExponential_square a) x]
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  congr 1
  ring

/-- The positive-real Gaussian is an actual `L²` function, not merely an
integrable Fourier kernel. -/
theorem memLp_two_ccm24RealGaussian {a : ℝ} (ha : 0 < a) :
    MemLp (ccm24RealGaussian a) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_ccm24RealGaussian a).aestronglyMeasurable]
  have hdouble :=
    (integrable_ccm24RealGaussian (a := 2 * a) (mul_pos (by norm_num) ha)).norm
  convert hdouble using 1
  funext x
  rw [norm_ccm24RealGaussian, norm_ccm24RealGaussian]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The unit-normalized logarithmic dilation orbit.  The factor `exp(c/2)`
is exactly what makes Fourier act by `c -> -c` and makes its half-density a
pure translation. -/
noncomputable def ccm24GaussianOrbit (c x : ℝ) : ℂ :=
  Real.exp (c / 2) • ccm24RealGaussian (Real.exp (2 * c)) x

theorem ccm24GaussianOrbit_even (c x : ℝ) :
    ccm24GaussianOrbit c (-x) = ccm24GaussianOrbit c x := by
  rw [ccm24GaussianOrbit, ccm24GaussianOrbit]
  exact congrArg (fun z : ℂ => Real.exp (c / 2) • z)
    (ccm24RealGaussian_even (Real.exp (2 * c)) x)

theorem integrable_ccm24GaussianOrbit (c : ℝ) :
    Integrable (ccm24GaussianOrbit c) volume := by
  have h := (integrable_ccm24RealGaussian (Real.exp_pos (2 * c))).const_mul
    (Real.exp (c / 2) : ℂ)
  simpa only [ccm24GaussianOrbit, Complex.real_smul] using h

theorem continuous_ccm24GaussianOrbit (c : ℝ) :
    Continuous (ccm24GaussianOrbit c) := by
  unfold ccm24GaussianOrbit
  exact continuous_const.smul
    (continuous_ccm24RealGaussian (Real.exp (2 * c)))

theorem memLp_two_ccm24GaussianOrbit (c : ℝ) :
    MemLp (ccm24GaussianOrbit c) 2 volume :=
  (memLp_two_ccm24RealGaussian (Real.exp_pos (2 * c))).const_smul
    (Real.exp (c / 2))

theorem ccm24_exp_two_mul_c_cpow_half (c : ℝ) :
    (Real.exp (2 * c) : ℂ) ^ (1 / 2 : ℂ) = Real.exp c := by
  have hsq : (Real.exp (2 * c) : ℂ) = (Real.exp c : ℂ) ^ (2 : ℕ) := by
    norm_cast
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  simpa only [one_div] using
    (Complex.sq_cpow_two_inv
      (x := (Real.exp c : ℂ)) (by simpa using Real.exp_pos c))

/-- Fourier acts on the normalized Gaussian orbit by reflecting the log
width parameter. -/
theorem ccm24GaussianOrbit_fourier (c : ℝ) :
    𝓕 (ccm24GaussianOrbit c) = ccm24GaussianOrbit (-c) := by
  have horbit : ccm24GaussianOrbit c =
      (Real.exp (c / 2) : ℂ) •
        ccm24RealGaussian (Real.exp (2 * c)) := by
    funext x
    simp only [ccm24GaussianOrbit, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul]
  rw [horbit]
  have hfourScalar :=
    VectorFourier.fourierIntegral_const_smul 𝐞 volume
      (innerₗ ℝ) (ccm24RealGaussian (Real.exp (2 * c)))
      (Real.exp (c / 2) : ℂ)
  change 𝓕 ((Real.exp (c / 2) : ℂ) •
      ccm24RealGaussian (Real.exp (2 * c))) =
    (Real.exp (c / 2) : ℂ) •
      𝓕 (ccm24RealGaussian (Real.exp (2 * c))) at hfourScalar
  rw [hfourScalar]
  rw [
    ccm24RealGaussian_fourier (Real.exp_pos (2 * c))]
  funext x
  simp only [Pi.smul_apply, ccm24GaussianOrbit,
    Complex.real_smul, smul_eq_mul,
    ccm24RealGaussian, ccm24ComplexGaussian]
  rw [ccm24_exp_two_mul_c_cpow_half]
  have hinv : (Real.exp (2 * c) : ℂ)⁻¹ =
      (Real.exp (-2 * c) : ℝ) := by
    push_cast
    rw [← Complex.exp_neg]
    congr 1
    ring
  simp only [div_eq_mul_inv]
  rw [hinv]
  have hnegwidth : Real.exp (2 * -c) = Real.exp (-2 * c) := by
    congr 1
    ring
  rw [hnegwidth]
  have hscalar : (Real.exp (c / 2) : ℂ) *
      (Real.exp c : ℂ)⁻¹ = Real.exp (-c / 2) := by
    push_cast
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  have hscalar' : (Real.exp (c * 2⁻¹) : ℂ) *
      (Real.exp c : ℂ)⁻¹ = Real.exp (-c * 2⁻¹) := by
    simpa only [div_eq_mul_inv] using hscalar
  simp only [one_mul]
  rw [← mul_assoc, hscalar']
  congr 1
  congr 1
  push_cast
  ring

/-- The orbit is the standard Gaussian composed with the positive dilation
`x -> exp(c) x`, followed by its unitary normalization. -/
theorem ccm24GaussianOrbit_eq_scaledStandard (c x : ℝ) :
    ccm24GaussianOrbit c x =
      Real.exp (c / 2) • ccm24StandardGaussian (Real.exp c * x) := by
  simp only [ccm24GaussianOrbit, ccm24StandardGaussian,
    ccm24RealGaussian, ccm24ComplexGaussian]
  congr 2
  have hexp : Real.exp (2 * c) = Real.exp c ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  push_cast
  ring

/-- Complex powers of a positive real exponential have no branch ambiguity. -/
theorem ccm24_ofReal_exp_cpow (c : ℝ) (s : ℂ) :
    (Real.exp c : ℂ) ^ s = Complex.exp ((c : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by simp)]
  rw [← Complex.ofReal_log (Real.exp_pos c).le, Real.log_exp]

/-- Mellin weight of the normalized Gaussian orbit. -/
noncomputable def ccm24GaussianOrbitMellinWeight (c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((c / 2 : ℝ) - (c : ℂ) * s)

theorem ccm24GaussianOrbit_mellin_eq_weight
    (c : ℝ) (s : ℂ) :
    mellin (ccm24GaussianOrbit c) s =
      ccm24GaussianOrbitMellinWeight c s *
        mellin ccm24StandardGaussian s := by
  have hfun : ccm24GaussianOrbit c = fun x : ℝ =>
      Real.exp (c / 2) • ccm24StandardGaussian (Real.exp c * x) := by
    funext x
    exact ccm24GaussianOrbit_eq_scaledStandard c x
  rw [hfun, mellin_const_smul,
    mellin_comp_mul_left ccm24StandardGaussian s (Real.exp_pos c)]
  simp only [ccm24GaussianOrbitMellinWeight]
  rw [ccm24_ofReal_exp_cpow]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem ccm24GaussianOrbitMellinWeight_neg
    (c : ℝ) (s : ℂ) :
    ccm24GaussianOrbitMellinWeight (-c) s =
      ccm24GaussianOrbitMellinWeight c (1 - s) := by
  simp only [ccm24GaussianOrbitMellinWeight]
  congr 1
  push_cast
  ring

/-- Every normalized Gaussian dilation, not just the self-dual member,
satisfies the genuine critical Fourier--Mellin functional equation. -/
theorem ccm24GaussianOrbit_criticalFourierMellinFunctionalEquation
    (c : ℝ) :
    CCM24CriticalFourierMellinFunctionalEquation
      (ccm24GaussianOrbit c) (𝓕 (ccm24GaussianOrbit c)) := by
  rw [ccm24GaussianOrbit_fourier]
  intro xi
  rw [ccm24GaussianOrbit_mellin_eq_weight,
    ccm24GaussianOrbit_mellin_eq_weight,
    ccm24GaussianOrbitMellinWeight_neg]
  have hstandard :=
    ccm24StandardGaussian_criticalFourierMellinFunctionalEquation xi
  rw [ccm24StandardGaussian_fourier] at hstandard
  rw [hstandard]
  ring

/-- Absolute Mellin convergence for every normalized Gaussian orbit in the
whole right half-plane. -/
theorem ccm24GaussianOrbit_mellinConvergent
    (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (ccm24GaussianOrbit c) s := by
  exact (ccm24RealGaussian_mellinConvergent
    (Real.exp_pos (2 * c)) hs).const_smul (Real.exp (c / 2) : ℂ)

set_option maxHeartbeats 4000000 in
-- Mellin convergence unfolds a large change-of-variables proof during elaboration.
/-- The critical logarithmic Mellin profile of a Gaussian orbit is an actual
`L1` function, obtained from its genuine Mellin convergence rather than from
a formal change of variables. -/
theorem integrable_ccm24GaussianOrbit_criticalMellinLogProfile
    (c : ℝ) :
    Integrable
      (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c)) volume := by
  have hconv : MellinConvergent (ccm24GaussianOrbit c) ((1 / 2 : ℝ) : ℂ) :=
    ccm24GaussianOrbit_mellinConvergent c (by norm_num)
  have h := integrable_mellinLogProfile_of_mellinConvergent
    (ccm24GaussianOrbit c) (1 / 2 : ℝ) hconv
  convert h using 1
  funext t
  rw [ccm24CriticalMellinLogProfile]
  congr 1
  ring

/-- Pointwise derivative of the genuine normalized Gaussian orbit. -/
theorem hasDerivAt_ccm24GaussianOrbit (c x : ℝ) :
    HasDerivAt (ccm24GaussianOrbit c)
      ((-2 * Real.pi * Real.exp (2 * c) * x : ℝ) •
        ccm24GaussianOrbit c x) x := by
  have hgaussian : HasDerivAt (ccm24RealGaussian (Real.exp (2 * c)))
      ((-2 * Real.pi * Real.exp (2 * c) * x : ℝ) •
        ccm24RealGaussian (Real.exp (2 * c)) x) x := by
    rw [ccm24RealGaussian_eq_scaledExponential_square]
    have hcomplex :=
      (((hasDerivAt_pow 2 (x : ℂ)).const_mul
        (-((Real.pi : ℂ) * (Real.exp (2 * c) : ℂ)))).cexp).comp_ofReal
    convert hcomplex using 1
    · funext y
      congr 2 <;> push_cast <;> ring
    · simp only [Complex.real_smul]
      push_cast
      ring
  convert hgaussian.const_smul (Real.exp (c / 2) : ℂ) using 1
  simp only [ccm24GaussianOrbit, Complex.real_smul]
  ring

theorem differentiable_ccm24GaussianOrbit (c : ℝ) :
    Differentiable ℝ (ccm24GaussianOrbit c) :=
  fun x => (hasDerivAt_ccm24GaussianOrbit c x).differentiableAt

theorem deriv_ccm24GaussianOrbit (c x : ℝ) :
    deriv (ccm24GaussianOrbit c) x =
      ((-2 * Real.pi * Real.exp (2 * c) * x : ℝ) •
        ccm24GaussianOrbit c x) :=
  (hasDerivAt_ccm24GaussianOrbit c x).deriv

/-- The `5/2` Mellin profile controls the chain-rule part of the derivative
of the critical `1/2` profile. -/
noncomputable def ccm24GaussianOrbitHighMellinLogProfile
    (c t : ℝ) : ℂ :=
  Real.exp (-(5 / 2 : ℝ) * t) •
    ccm24GaussianOrbit c (Real.exp (-t))

set_option maxHeartbeats 4000000 in
-- Mellin convergence unfolds a large change-of-variables proof during elaboration.
theorem integrable_ccm24GaussianOrbitHighMellinLogProfile
    (c : ℝ) :
    Integrable (ccm24GaussianOrbitHighMellinLogProfile c) volume := by
  have hconv : MellinConvergent (ccm24GaussianOrbit c) ((5 / 2 : ℝ) : ℂ) :=
    ccm24GaussianOrbit_mellinConvergent c (by norm_num)
  have h := integrable_mellinLogProfile_of_mellinConvergent
    (ccm24GaussianOrbit c) (5 / 2 : ℝ) hconv
  convert h using 1

theorem ccm24GaussianOrbit_criticalProfileChainDeriv_eq
    (c t : ℝ) :
    ccm24CriticalMellinLogProfileFunctionChainDeriv
        (ccm24GaussianOrbit c) t =
      (2 * Real.pi * Real.exp (2 * c) : ℝ) •
        ccm24GaussianOrbitHighMellinLogProfile c t := by
  rw [ccm24CriticalMellinLogProfileFunctionChainDeriv,
    deriv_ccm24GaussianOrbit]
  simp only [ccm24GaussianOrbitHighMellinLogProfile, smul_smul]
  congr 1
  have hExp :
      Real.exp (-t / 2) * Real.exp (-t) * Real.exp (-t) =
        Real.exp (-(5 / 2 : ℝ) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show
    Real.exp (-t / 2) * (-Real.exp (-t) *
        (-2 * Real.pi * Real.exp (2 * c) * Real.exp (-t))) =
      (2 * Real.pi * Real.exp (2 * c)) *
        (Real.exp (-t / 2) * Real.exp (-t) * Real.exp (-t)) by ring]
  rw [hExp]

theorem integrable_ccm24GaussianOrbit_criticalProfileChainDeriv
    (c : ℝ) :
    Integrable
      (ccm24CriticalMellinLogProfileFunctionChainDeriv
        (ccm24GaussianOrbit c)) volume := by
  have h := (integrable_ccm24GaussianOrbitHighMellinLogProfile c).const_mul
    ((2 * Real.pi * Real.exp (2 * c) : ℝ) : ℂ)
  apply h.congr
  filter_upwards with t
  rw [ccm24GaussianOrbit_criticalProfileChainDeriv_eq]
  simpa only [Complex.real_smul]

theorem integrable_deriv_ccm24GaussianOrbit_criticalMellinLogProfile
    (c : ℝ) :
    Integrable
      (deriv (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c))) volume := by
  have hchain :=
    integrable_ccm24GaussianOrbit_criticalProfileChainDeriv c
  have hweight :=
    (integrable_ccm24GaussianOrbit_criticalMellinLogProfile c).const_mul
      ((-1 / 2 : ℝ) : ℂ)
  have hsum : Integrable
      (fun t =>
        ccm24CriticalMellinLogProfileFunctionChainDeriv
            (ccm24GaussianOrbit c) t +
          ((-1 / 2 : ℝ) : ℂ) *
            ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c) t) volume :=
    hchain.add hweight
  apply hsum.congr
  filter_upwards with t
  rw [(hasDerivAt_ccm24CriticalMellinLogProfile_of_differentiable
    (ccm24GaussianOrbit c) (differentiable_ccm24GaussianOrbit c) t).deriv]
  congr 1
  change
    ((-1 / 2 : ℝ) : ℂ) *
        ((Real.exp (-t / 2) : ℂ) *
          ccm24GaussianOrbit c (Real.exp (-t))) =
      (((-1 / 2 : ℝ) * Real.exp (-t / 2) : ℝ) : ℂ) *
        ccm24GaussianOrbit c (Real.exp (-t))
  push_cast
  ring

theorem memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile
    (c : ℝ) :
    MemLp
      (𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c)))
      2 volume :=
  memLp_two_fourier_of_integrable_deriv
    (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c))
    (integrable_ccm24GaussianOrbit_criticalMellinLogProfile c)
    (fun t =>
      (hasDerivAt_ccm24CriticalMellinLogProfile_of_differentiable
        (ccm24GaussianOrbit c) (differentiable_ccm24GaussianOrbit c) t).differentiableAt)
    (integrable_deriv_ccm24GaussianOrbit_criticalMellinLogProfile c)

/-- The normalized Gaussian orbit as an actual additive `L²` vector. -/
noncomputable def ccm24GaussianOrbitL2 (c : ℝ) :
    cc20GlobalLogCrossingL2 :=
  (memLp_two_ccm24GaussianOrbit c).toLp (ccm24GaussianOrbit c)

theorem ccm24GaussianOrbitL2_coeFn (c : ℝ) :
    (ccm24GaussianOrbitL2 c : ℝ → ℂ) =ᵐ[volume]
      ccm24GaussianOrbit c :=
  (memLp_two_ccm24GaussianOrbit c).coeFn_toLp

/-- The same vector in the genuine even additive carrier. -/
noncomputable def ccm24GaussianOrbitToEven
    (c : ℝ) : ccm24EvenAdditiveL2 :=
  ⟨ccm24GaussianOrbitL2 c, by
    change ccm24GaussianOrbitL2 c ∈ ccm24EvenAdditiveClosedSubspace
    rw [mem_ccm24EvenAdditiveClosedSubspace_iff_ae_even]
    have hcoe := ccm24GaussianOrbitL2_coeFn c
    have hcoeNeg :=
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hcoe
    filter_upwards [hcoe, hcoeNeg] with x hx hxNeg
    simp only [Function.comp_apply] at hxNeg
    rw [hxNeg, hx]
    exact ccm24GaussianOrbit_even c x⟩

/-- The normalized Gaussian orbit on the actual common logarithmic carrier. -/
noncomputable def ccm24GaussianOrbitToLog
    (c : ℝ) : cc20GlobalLogCrossingL2 :=
  ccm24EvenLogCarrierEquiv (ccm24GaussianOrbitToEven c)

theorem ccm24GaussianOrbitToLog_coeFn (c : ℝ) :
    (ccm24GaussianOrbitToLog c : ℝ → ℂ) =ᵐ[volume]
      ccm24NormalizedLogHalfDensityFunction (ccm24GaussianOrbit c) := by
  rw [ccm24GaussianOrbitToLog, ccm24EvenLogCarrierEquiv_apply]
  have hrep := ccm24EvenAdditiveRepresentative_ae_eq
    (ccm24GaussianOrbitToEven c)
  have hrepOrbit :
      ccm24EvenAdditiveRepresentative (ccm24GaussianOrbitToEven c)
        =ᵐ[volume] ccm24GaussianOrbit c :=
    hrep.symm.trans (ccm24GaussianOrbitL2_coeFn c)
  exact (ccm24EvenToLogHalfDensity_coeFn
      (ccm24GaussianOrbitToEven c)).trans
    (ccm24NormalizedLogHalfDensityFunction_congr_ae
      (stronglyMeasurable_ccm24EvenAdditiveRepresentative
        (ccm24GaussianOrbitToEven c))
      (continuous_ccm24GaussianOrbit c).stronglyMeasurable
      hrepOrbit)

/-- The Gaussian critical Mellin profile is an actual `L2` function because
it is the reflected normalized half-density on the genuine common-log
carrier. -/
theorem memLp_two_ccm24GaussianOrbit_criticalMellinLogProfile
    (c : ℝ) :
    MemLp
      (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c)) 2 volume := by
  have hhalfDensity : MemLp
      (ccm24NormalizedLogHalfDensityFunction (ccm24GaussianOrbit c))
      2 volume :=
    (memLp_congr_ae (ccm24GaussianOrbitToLog_coeFn c)).mp
      (Lp.memLp (ccm24GaussianOrbitToLog c))
  have hreflected := hhalfDensity.comp_measurePreserving
    (Measure.measurePreserving_neg volume)
  have hscaled := hreflected.const_smul (1 / Real.sqrt 2 : ℂ)
  apply (memLp_congr_ae ?_).mpr hscaled
  filter_upwards [] with t
  simpa only [Pi.smul_apply, Function.comp_apply] using
    ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity
      (ccm24GaussianOrbit c) t

noncomputable def ccm24GaussianOrbitCriticalMellinProfileL2
    (c : ℝ) : cc20GlobalLogCrossingL2 :=
  (memLp_two_ccm24GaussianOrbit_criticalMellinLogProfile c).toLp
    (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c))

theorem ccm24GaussianOrbitCriticalMellinProfileL2_coeFn
    (c : ℝ) :
    (ccm24GaussianOrbitCriticalMellinProfileL2 c : ℝ → ℂ) =ᵐ[volume]
      ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c) :=
  (memLp_two_ccm24GaussianOrbit_criticalMellinLogProfile c).coeFn_toLp

theorem ccm24GaussianOrbitCriticalMellinProfileL2_eq_reflection
    (c : ℝ) :
    ccm24GaussianOrbitCriticalMellinProfileL2 c =
      (1 / Real.sqrt 2 : ℂ) •
        ccm24LogSpectralReflection (ccm24GaussianOrbitToLog c) := by
  rw [Lp.ext_iff]
  have hlogNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (ccm24GaussianOrbitToLog_coeFn c)
  filter_upwards
    [ccm24GaussianOrbitCriticalMellinProfileL2_coeFn c,
     Lp.coeFn_smul (1 / Real.sqrt 2 : ℂ)
      (ccm24LogSpectralReflection (ccm24GaussianOrbitToLog c)),
     ccm24LogSpectralReflectionEquiv_coeFn
      (ccm24GaussianOrbitToLog c), hlogNeg] with
      t hprofile hsmul hreflect hlogNegAt
  simp only [Function.comp_apply] at hlogNegAt
  rw [hprofile, hsmul]
  simp only [Pi.smul_apply]
  rw [hreflect, hlogNegAt]
  exact ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity
    (ccm24GaussianOrbit c) t

theorem ccm24GaussianOrbitCriticalMellinProfile_fourierTransformL2_eq_classical
    (c : ℝ) :
    Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24GaussianOrbitCriticalMellinProfileL2 c) =
      (memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile c).toLp
        (𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c))) := by
  exact ccm24_fourierTransformL2_eq_classical_toLp
    (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c))
    (integrable_ccm24GaussianOrbit_criticalMellinLogProfile c)
    (memLp_two_ccm24GaussianOrbit_criticalMellinLogProfile c)
    (memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile c)

/-- Plancherel readback of the genuine additive Fourier transform on the
normalized Gaussian orbit. -/
theorem ccm24GaussianOrbitL2_fourierTransform (c : ℝ) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24GaussianOrbitL2 c) =
      ccm24GaussianOrbitL2 (-c) := by
  have hf2 : MemLp (𝓕 (ccm24GaussianOrbit c)) 2 volume := by
    rw [ccm24GaussianOrbit_fourier]
    exact memLp_two_ccm24GaussianOrbit (-c)
  simpa only [ccm24GaussianOrbitL2, ccm24GaussianOrbit_fourier] using
    ccm24_fourierTransformL2_eq_classical_toLp
      (ccm24GaussianOrbit c)
      (integrable_ccm24GaussianOrbit c)
      (memLp_two_ccm24GaussianOrbit c)
      hf2

theorem ccm24EvenAdditiveFourier_gaussianOrbit (c : ℝ) :
    ccm24EvenAdditiveFourier (ccm24GaussianOrbitToEven c) =
      ccm24GaussianOrbitToEven (-c) := by
  apply Subtype.ext
  exact ccm24GaussianOrbitL2_fourierTransform c

/-- The genuine transported source Fourier involution reflects the Gaussian
log-width parameter.  This conclusion uses the independently constructed
additive Plancherel transform, not the Hardy--Titchmarsh multiplier. -/
theorem ccm24ArchimedeanSourceFourier_gaussianOrbit (c : ℝ) :
    ccm24ArchimedeanSourceFourier (ccm24GaussianOrbitToLog c) =
      ccm24GaussianOrbitToLog (-c) := by
  rw [ccm24GaussianOrbitToLog, ccm24ArchimedeanSourceFourier_apply,
    ccm24EvenLogCarrierEquiv.symm_apply_apply,
    ccm24EvenAdditiveFourier_gaussianOrbit]
  rfl

/-- The pointwise Gaussian Fourier--Mellin equation upgraded to an equality
of actual Plancherel `L2` vectors. -/
theorem ccm24GaussianOrbitCriticalMellinProfile_spectralEquation (c : ℝ) :
    ccm24LogSpectralReflection
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (ccm24GaussianOrbitCriticalMellinProfileL2 (-c))) =
      ccm24ArchimedeanScatteringMultiplier
        (Lp.fourierTransformₗᵢ ℝ ℂ
          (ccm24GaussianOrbitCriticalMellinProfileL2 c)) := by
  have hFE := ccm24GaussianOrbit_criticalFourierMellinFunctionalEquation c
  rw [ccm24GaussianOrbit_fourier] at hFE
  have hlog :=
    (ccm24CriticalFourierMellinFunctionalEquation_iff_logFourier
      (ccm24GaussianOrbit c) (ccm24GaussianOrbit (-c))).1 hFE
  have hleftRead :=
    (memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile
      (-c)).coeFn_toLp
  rw [← ccm24GaussianOrbitCriticalMellinProfile_fourierTransformL2_eq_classical]
    at hleftRead
  have hleftNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      hleftRead
  have hrightRead :=
    (memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile
      c).coeFn_toLp
  rw [← ccm24GaussianOrbitCriticalMellinProfile_fourierTransformL2_eq_classical]
    at hrightRead
  rw [Lp.ext_iff]
  filter_upwards
    [ccm24LogSpectralReflectionEquiv_coeFn
      (Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24GaussianOrbitCriticalMellinProfileL2 (-c))),
     hleftNeg,
     ccm24ArchimedeanScatteringMultiplier_coeFn
      (Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24GaussianOrbitCriticalMellinProfileL2 c)),
     hrightRead] with xi hreflect hleft hmul hright
  simp only [Function.comp_apply] at hleft
  rw [hreflect, hleft, hmul, hright]
  exact hlog xi

theorem ccm24LogSpectralReflection_fourier_reflection
    (u : cc20GlobalLogCrossingL2) :
    ccm24LogSpectralReflection
        (Lp.fourierTransformₗᵢ ℝ ℂ (ccm24LogSpectralReflection u)) =
      Lp.fourierTransformₗᵢ ℝ ℂ u := by
  rw [ccm24_fourier_reflection_eq_fourierInv,
    ccm24_fourierInv_eq_reflection_fourier]
  change ccm24LogSpectralReflectionLinearIsometry
      (ccm24LogSpectralReflectionLinearIsometry
        (Lp.fourierTransformₗᵢ ℝ ℂ u)) =
    Lp.fourierTransformₗᵢ ℝ ℂ u
  exact ccm24LogSpectralReflection_involutive _

/-- Spectral scattering equation on the actual common-log Gaussian orbit. -/
theorem ccm24GaussianOrbitToLog_fourier_scattering (c : ℝ) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24GaussianOrbitToLog (-c)) =
      ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection
          (Lp.fourierTransformₗᵢ ℝ ℂ (ccm24GaussianOrbitToLog c))) := by
  have hspec := ccm24GaussianOrbitCriticalMellinProfile_spectralEquation c
  rw [ccm24GaussianOrbitCriticalMellinProfileL2_eq_reflection,
    ccm24GaussianOrbitCriticalMellinProfileL2_eq_reflection] at hspec
  simp only [map_smul] at hspec
  rw [ccm24LogSpectralReflection_fourier_reflection,
    ccm24_fourier_reflection_eq_fourierInv,
    ccm24_fourierInv_eq_reflection_fourier] at hspec
  have hscalar : (1 / Real.sqrt 2 : ℂ) ≠ 0 := by
    exact div_ne_zero one_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne')
  exact smul_right_injective cc20GlobalLogCrossingL2 hscalar hspec

/-- The independently constructed Hardy--Titchmarsh operator reflects the
same Gaussian log-width parameter. -/
theorem ccm24ArchimedeanHardyTitchmarsh_gaussianOrbit (c : ℝ) :
    ccm24ArchimedeanHardyTitchmarsh (ccm24GaussianOrbitToLog c) =
      ccm24GaussianOrbitToLog (-c) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  exact (ccm24GaussianOrbitToLog_fourier_scattering c).symm

theorem ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_gaussianOrbit
    (c : ℝ) :
    ccm24ArchimedeanSourceFourier (ccm24GaussianOrbitToLog c) =
      ccm24ArchimedeanHardyTitchmarsh (ccm24GaussianOrbitToLog c) := by
  rw [ccm24ArchimedeanSourceFourier_gaussianOrbit,
    ccm24ArchimedeanHardyTitchmarsh_gaussianOrbit]

/-- The explicit half-density of the normalized orbit is a pure translate of
the standard half-density. -/
theorem ccm24GaussianOrbit_halfDensity_eq_translate
    (c t : ℝ) :
    ccm24NormalizedLogHalfDensityFunction (ccm24GaussianOrbit c) t =
      ccm24NormalizedLogHalfDensityFunction (ccm24GaussianOrbit 0) (t + c) := by
  have hamp : Real.exp (t / 2) * Real.exp (c / 2) =
      Real.exp ((t + c) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hwidth : Real.exp (2 * c) * Real.exp t ^ 2 =
      Real.exp (t + c) ^ 2 := by
    rw [pow_two, pow_two, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    ring
  have hampC : (Real.exp (t / 2) : ℂ) * (Real.exp (c / 2) : ℂ) =
      (Real.exp ((t + c) / 2) : ℂ) := by
    exact_mod_cast hamp
  have hwidthC : (Real.exp (2 * c) : ℂ) * (Real.exp t : ℂ) ^ 2 =
      (Real.exp (t + c) : ℂ) ^ 2 := by
    exact_mod_cast hwidth
  have hkernel : (Real.pi : ℂ) * (Real.exp (2 * c) : ℂ) *
      (Real.exp t : ℂ) ^ 2 =
        (Real.pi : ℂ) * (Real.exp (t + c) : ℂ) ^ 2 := by
    rw [mul_assoc, hwidthC]
  simp only [ccm24NormalizedLogHalfDensityFunction,
    ccm24GaussianOrbit, ccm24RealGaussian, ccm24ComplexGaussian,
    Complex.real_smul, Real.exp_zero, zero_div, one_smul]
  simp only [Complex.ofReal_mul]
  norm_num only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul, mul_one]
  rw [hkernel, ← hampC]
  ring

/-- On the actual Hilbert carrier, the full normalized Gaussian dilation
family is exactly the translation orbit of its standard member. -/
theorem ccm24GaussianOrbitToLog_eq_translation (c : ℝ) :
    ccm24GaussianOrbitToLog c =
      cc20GlobalLogTranslation c (ccm24GaussianOrbitToLog 0) := by
  rw [Lp.ext_iff]
  have hzeroShift :=
    (measurePreserving_add_right volume c).quasiMeasurePreserving.ae_eq
      (ccm24GaussianOrbitToLog_coeFn 0)
  filter_upwards
    [ccm24GaussianOrbitToLog_coeFn c,
     cc20GlobalLogTranslation_coeFn c (ccm24GaussianOrbitToLog 0),
     hzeroShift] with t hc htrans hzero
  simp only [Function.comp_apply] at hzero
  rw [hc, htrans, hzero]
  exact ccm24GaussianOrbit_halfDensity_eq_translate c t

/-- On Mellin profiles the same orbit is right translation by `-c`. -/
theorem ccm24GaussianOrbit_criticalMellinLogProfile_eq_translate
    (c t : ℝ) :
    ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c) t =
      ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0) (t - c) := by
  rw [ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity,
    ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity]
  congr 1
  rw [ccm24GaussianOrbit_halfDensity_eq_translate]
  congr 1
  ring

theorem ccm24GaussianOrbit_zero_eq_standard :
    ccm24GaussianOrbit 0 = ccm24StandardGaussian := by
  funext x
  simp [ccm24GaussianOrbit, ccm24StandardGaussian]

/-- The classical Fourier transform of the standard critical Gaussian
profile has no zero.  Its value is a nonzero real Gamma factor. -/
theorem ccm24GaussianCriticalProfile_fourier_ne_zero (xi : ℝ) :
    𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi ≠ 0 := by
  rw [← ccm24_mellin_one_sub_eq_fourier_criticalLogProfile]
  rw [ccm24GaussianOrbit_zero_eq_standard]
  have hre : 0 < (1 - ccm24CriticalMellinParameter xi).re := by
    rw [← ccm24CriticalMellinParameter_neg,
      ccm24CriticalMellinParameter_re]
    norm_num
  rw [ccm24StandardGaussian_mellin_eq_half_GammaR hre]
  apply mul_ne_zero
  · norm_num
  · intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    rcases hzero with ⟨n, hn⟩
    have hreal := congrArg Complex.re hn
    rw [← ccm24CriticalMellinParameter_neg,
      ccm24CriticalMellinParameter_re] at hreal
    norm_num at hreal
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Uniform `L∞` bound for the same classical Fourier representative. -/
theorem norm_ccm24GaussianCriticalProfile_fourier_le (xi : ℝ) :
    ‖𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi‖ ≤
      ∫ t : ℝ,
        ‖ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0) t‖ ∂volume :=
  VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ)
    (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi

theorem ccm24GaussianOrbit_criticalProfile_fourier_translate (c : ℝ) :
    𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c)) =
      fun xi : ℝ => 𝐞 ((-c) * xi) •
        𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi := by
  have hprofile :
      ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c) =
        ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0) ∘
          fun t : ℝ => t + (-c) := by
    funext t
    simpa only [Function.comp_apply, add_neg] using
      ccm24GaussianOrbit_criticalMellinLogProfile_eq_translate c t
  rw [hprofile]
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0) ∘
        fun t : ℝ => t + -c) =
    fun xi : ℝ => 𝐞 (-c * xi) •
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
        (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi
  have h := VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℝ)
    (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) (-c)
  convert h using 1
  funext xi
  congr 2
  rw [innerₗ_apply_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

theorem ccm24GaussianOrbitCriticalMellinProfile_fourierL2_coeFn
    (c : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24GaussianOrbitCriticalMellinProfileL2 c) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit c)) := by
  have h :=
    (memLp_two_fourier_ccm24GaussianOrbit_criticalMellinLogProfile c).coeFn_toLp
  rw [← ccm24GaussianOrbitCriticalMellinProfile_fourierTransformL2_eq_classical]
    at h
  exact h

noncomputable def ccm24GaussianCyclicProduct
    (u : cc20GlobalLogCrossingL2) (xi : ℝ) : ℂ :=
  inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ u) xi)
    (𝓕 (ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0)) xi)

theorem integrable_ccm24GaussianCyclicProduct
    (u : cc20GlobalLogCrossingL2) :
    Integrable (ccm24GaussianCyclicProduct u) volume := by
  have h := L2.integrable_inner (𝕜 := ℂ)
    (Lp.fourierTransformₗᵢ ℝ ℂ u)
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (ccm24GaussianOrbitCriticalMellinProfileL2 0))
  apply h.congr
  filter_upwards
    [ccm24GaussianOrbitCriticalMellinProfile_fourierL2_coeFn 0] with xi hxi
  rw [ccm24GaussianCyclicProduct, hxi]

theorem memLp_two_ccm24GaussianCyclicProduct
    (u : cc20GlobalLogCrossingL2) :
    MemLp (ccm24GaussianCyclicProduct u) 2 volume := by
  let C : ℝ := ∫ t : ℝ,
    ‖ccm24CriticalMellinLogProfile (ccm24GaussianOrbit 0) t‖ ∂volume
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hmajor : MemLp
      (fun xi : ℝ => C *
        ‖(Lp.fourierTransformₗᵢ ℝ ℂ u) xi‖) 2 volume :=
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ u)).norm.const_mul C
  apply hmajor.mono'
    (integrable_ccm24GaussianCyclicProduct u).aestronglyMeasurable
  filter_upwards with xi
  calc
    ‖ccm24GaussianCyclicProduct u xi‖ ≤
        ‖(Lp.fourierTransformₗᵢ ℝ ℂ u) xi‖ *
          ‖𝓕 (ccm24CriticalMellinLogProfile
            (ccm24GaussianOrbit 0)) xi‖ := norm_inner_le_norm _ _
    _ ≤ ‖(Lp.fourierTransformₗᵢ ℝ ℂ u) xi‖ * C := by
      gcongr
      exact norm_ccm24GaussianCriticalProfile_fourier_le xi
    _ = C * ‖(Lp.fourierTransformₗᵢ ℝ ℂ u) xi‖ := mul_comm _ _

/-- Orthogonality to every translated critical Gaussian profile forces the
cyclic product's classical Fourier transform to vanish pointwise. -/
theorem ccm24GaussianCyclicProduct_fourier_eq_zero
    (u : cc20GlobalLogCrossingL2)
    (hu : u ∈ (Submodule.span ℂ
      (Set.range ccm24GaussianOrbitCriticalMellinProfileL2))ᗮ) :
    𝓕 (ccm24GaussianCyclicProduct u) = 0 := by
  funext c
  simp only [Pi.zero_apply]
  have hgenerator : ccm24GaussianOrbitCriticalMellinProfileL2 c ∈
      Submodule.span ℂ
        (Set.range ccm24GaussianOrbitCriticalMellinProfileL2) :=
    Submodule.subset_span ⟨c, rfl⟩
  have horth : inner ℂ u
      (ccm24GaussianOrbitCriticalMellinProfileL2 c) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hgenerator hu
  have hprofileRead :=
    ccm24GaussianOrbitCriticalMellinProfile_fourierL2_coeFn c
  have hzero : inner ℂ
      (Lp.fourierTransformₗᵢ ℝ ℂ u)
      (Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24GaussianOrbitCriticalMellinProfileL2 c)) = 0 := by
    rw [(Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map]
    exact horth
  rw [L2.inner_def] at hzero
  rw [Real.fourier_eq]
  calc
    (∫ xi : ℝ, 𝐞 (-inner ℝ xi c) •
        ccm24GaussianCyclicProduct u xi ∂volume) =
        ∫ xi : ℝ,
          inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ u) xi)
            ((Lp.fourierTransformₗᵢ ℝ ℂ
              (ccm24GaussianOrbitCriticalMellinProfileL2 c)) xi) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hprofileRead] with xi hread
      rw [hread, ccm24GaussianOrbit_criticalProfile_fourier_translate,
        ccm24GaussianCyclicProduct]
      change ((𝐞 (-inner ℝ xi c) : Circle) : ℂ) •
          inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ u) xi)
            (𝓕 (ccm24CriticalMellinLogProfile
              (ccm24GaussianOrbit 0)) xi) =
        inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ u) xi)
          (((𝐞 (-c * xi) : Circle) : ℂ) •
            𝓕 (ccm24CriticalMellinLogProfile
            (ccm24GaussianOrbit 0)) xi)
      rw [inner_smul_right]
      congr 2
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring
    _ = 0 := hzero

/-- Wiener-type cyclicity for the normalized Gaussian: the algebraic span of
its translated critical Mellin profiles is dense in whole-line `L2`.  The
proof uses the nonvanishing Gamma representative and never assumes a raw
orbit map has dense range. -/
theorem dense_span_ccm24GaussianOrbitCriticalMellinProfileL2 :
    Dense (Submodule.span ℂ
      (Set.range ccm24GaussianOrbitCriticalMellinProfileL2) : Set
        cc20GlobalLogCrossingL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff,
    Submodule.orthogonal_closure]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  let q := ccm24GaussianCyclicProduct u
  have hq1 : Integrable q volume := integrable_ccm24GaussianCyclicProduct u
  have hq2 : MemLp q 2 volume := memLp_two_ccm24GaussianCyclicProduct u
  have hqFourierZero : 𝓕 q = 0 :=
    ccm24GaussianCyclicProduct_fourier_eq_zero u hu
  have hqFourier2 : MemLp (𝓕 q) 2 volume := by
    rw [hqFourierZero]
    exact MemLp.zero
  have hbridge := ccm24_fourierTransformL2_eq_classical_toLp
    q hq1 hq2 hqFourier2
  have hqL2Zero : hq2.toLp q = 0 := by
    apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
    simpa only [hqFourierZero, MemLp.toLp_zero, map_zero] using hbridge
  have hqZero : q =ᵐ[volume] 0 := by
    have hcoe := hq2.coeFn_toLp
    rw [hqL2Zero] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have huFourierZero :
      (Lp.fourierTransformₗᵢ ℝ ℂ u : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hqZero] with xi hzero
    change inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ u) xi)
      (𝓕 (ccm24CriticalMellinLogProfile
        (ccm24GaussianOrbit 0)) xi) = 0 at hzero
    simp only [RCLike.inner_apply] at hzero
    simpa using (mul_eq_zero.mp hzero |>.resolve_left
      (ccm24GaussianCriticalProfile_fourier_ne_zero xi))
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [map_zero, Lp.ext_iff]
  exact huFourierZero.trans (Lp.coeFn_zero ℂ 2 volume).symm

theorem ccm24LogSpectralReflection_gaussianCriticalProfile (c : ℝ) :
    ccm24LogSpectralReflection
        (ccm24GaussianOrbitCriticalMellinProfileL2 c) =
      (1 / Real.sqrt 2 : ℂ) • ccm24GaussianOrbitToLog c := by
  rw [ccm24GaussianOrbitCriticalMellinProfileL2_eq_reflection, map_smul]
  congr 1
  change ccm24LogSpectralReflectionLinearIsometry
      (ccm24LogSpectralReflectionLinearIsometry
        (ccm24GaussianOrbitToLog c)) = ccm24GaussianOrbitToLog c
  exact ccm24LogSpectralReflection_involutive _

/-- The actual Gaussian half-density orbit has dense algebraic span.  It is
the unitary reflection of the already-proved dense critical-profile span. -/
theorem dense_span_ccm24GaussianOrbitToLog :
    Dense (Submodule.span ℂ (Set.range ccm24GaussianOrbitToLog) : Set
      cc20GlobalLogCrossingL2) := by
  let profileSpan : Submodule ℂ cc20GlobalLogCrossingL2 :=
    Submodule.span ℂ
      (Set.range ccm24GaussianOrbitCriticalMellinProfileL2)
  let orbitSpan : Submodule ℂ cc20GlobalLogCrossingL2 :=
    Submodule.span ℂ (Set.range ccm24GaussianOrbitToLog)
  have hprofile : Dense (profileSpan : Set cc20GlobalLogCrossingL2) :=
    dense_span_ccm24GaussianOrbitCriticalMellinProfileL2
  have himage :
      ccm24LogSpectralReflection ''
          (profileSpan : Set cc20GlobalLogCrossingL2) ⊆ orbitSpan := by
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨c, rfl⟩ := hz
      rw [ccm24LogSpectralReflection_gaussianCriticalProfile]
      exact orbitSpan.smul_mem (1 / Real.sqrt 2 : ℂ)
        (Submodule.subset_span ⟨c, rfl⟩)
    · simpa only [map_zero] using orbitSpan.zero_mem
    · intro x y hx hy hxmem hymem
      simpa only [map_add] using orbitSpan.add_mem hxmem hymem
    · intro a x hx hxmem
      simpa only [map_smul] using orbitSpan.smul_mem a hxmem
  have hdenseImage : Dense
      (ccm24LogSpectralReflection ''
        (profileSpan : Set cc20GlobalLogCrossingL2)) :=
    ccm24LogSpectralReflection.surjective.denseRange.dense_image
      ccm24LogSpectralReflection.continuous hprofile
  exact hdenseImage.mono himage

/-- Continuous linear operators equal on a family with dense algebraic span
are equal everywhere. -/
theorem ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_of_denseSpan
    {ι : Type*} (v : ι → cc20GlobalLogCrossingL2)
    (hv : Dense (Submodule.span ℂ (Set.range v) : Set
      cc20GlobalLogCrossingL2))
    (hEq : ∀ i,
      ccm24ArchimedeanSourceFourier (v i) =
        ccm24ArchimedeanHardyTitchmarsh (v i)) :
    ccm24ArchimedeanSourceFourier =
      ccm24ArchimedeanHardyTitchmarsh := by
  apply DFunLike.ext _ _
  intro u
  let inclusion : (Submodule.span ℂ (Set.range v)) →
      cc20GlobalLogCrossingL2 := fun y => y
  have hinclusion : DenseRange inclusion := by
    change Dense (Set.range inclusion)
    refine hv.mono ?_
    intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  refine DenseRange.induction_on hinclusion u
    (isClosed_eq ccm24ArchimedeanSourceFourier.continuous
      ccm24ArchimedeanHardyTitchmarsh.continuous) ?_
  · intro y
    change ccm24ArchimedeanSourceFourier (y : cc20GlobalLogCrossingL2) =
      ccm24ArchimedeanHardyTitchmarsh (y : cc20GlobalLogCrossingL2)
    refine Submodule.span_induction ?_ ?_ ?_ ?_ y.property
    · intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact hEq i
    · simp only [map_zero]
    · intro x y hx hy hxeq hyeq
      simpa only [map_add, hxeq, hyeq]
    · intro a x hx hxeq
      simpa only [map_smul, hxeq]


/-- The Fourier--Mellin core equation: the genuine additive even Fourier
transform transported to the common-log carrier is exactly the independently
constructed archimedean Hardy--Titchmarsh involution on all of `L2`. -/
theorem ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh :
    ccm24ArchimedeanSourceFourier =
      ccm24ArchimedeanHardyTitchmarsh :=
  ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_of_denseSpan
    ccm24GaussianOrbitToLog dense_span_ccm24GaussianOrbitToLog
    ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_gaussianOrbit

end CC20Concrete
end Source
end ConnesWeilRH
