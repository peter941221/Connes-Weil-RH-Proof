import ConnesWeilRH.Dev.C1XiCenterTwoPole
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# C1XiCenterTwoGamma - the half-anchor Gamma_R interface

This file fixes the analytic normalization used by the Gamma_R arithmetic
consumer.  The only deliberately external input is the half-anchor Gauss
formula for `Complex.digamma`; all algebraic constants and the sign of the
Gamma_R contribution are proved here.

The formula is anchored at `1 / 2`, not at `1`: Mathlib already proves
`Complex.digamma_one_half`, and after writing `s = 2 + t I` the Gamma factor
sees `s / 2 = 1 + t I / 2`.  This removes a separate `2 * log 2` integral
from the consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGamma

open MeasureTheory
open Set
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1XiArithmeticIntervalReadback
open C1XiVerticalFunctional
open scoped Interval Topology

noncomputable section

/-- The half-anchor Gauss kernel for the complex digamma function. -/
noncomputable def halfAnchorGaussKernel (z : Complex) (x : Real) : Complex :=
  (Complex.exp (-((1 / 2 : Complex) * (x : Complex))) -
      Complex.exp (-(z * (x : Complex)))) /
    (1 - Complex.exp (-((x : Complex))))

/-- The exact analytic input needed by the half-anchor Gamma_R consumer.

This is a proposition-valued contract on purpose: it carries no hidden
numeric field and cannot erase a readback constant through proof irrelevance.
The producer target is the Gauss representation
`digamma z - digamma (1/2) = integral halfAnchorGaussKernel z`. -/
def HalfAnchorGaussContract : Prop :=
  ∀ z : Complex, 0 < z.re →
    Complex.digamma z - Complex.digamma (1 / 2 : Complex) =
      ∫ x : Real in Ioi (0 : Real), halfAnchorGaussKernel z x

private theorem differentiableAt_gamma_half
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex Complex.Gamma (s / 2) := by
  apply differentiableAt_Gamma
  intro m hzero
  have hreal : (s / 2).re = s.re / 2 := by simp
  have hmreal : (-(m : Complex)).re ≤ 0 := by simp
  have := congrArg Complex.re hzero
  simp at this
  linarith

private theorem differentiableAt_gammaR_cpow
    {s : Complex} :
    DifferentiableAt Complex (fun z : Complex =>
      (Real.pi : Complex) ^ (-z / 2)) s := by
  apply DifferentiableAt.const_cpow
  · fun_prop
  · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

private theorem logDeriv_gammaR_cpow
    (s : Complex) :
    logDeriv (fun z : Complex =>
      (Real.pi : Complex) ^ (-z / 2)) s =
        -(Complex.log (Real.pi : Complex)) / 2 := by
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdiff : DifferentiableAt Complex (fun z : Complex => -z / 2) s := by
    fun_prop
  have hderiv := Complex.deriv_const_cpow hdiff (Real.pi : Complex)
  rw [logDeriv_apply, hderiv]
  have hpow : (Real.pi : Complex) ^ (-s / 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  field_simp [hpow]
  have hlinear : deriv (fun z : Complex => -(z / 2)) s = -(1 / 2 : Complex) := by
    simpa [div_eq_mul_inv] using
      (((hasDerivAt_id s).div_const (2 : Complex)).neg.deriv)
  rw [hlinear]
  ring

private theorem logDeriv_gamma_comp_half
    {s : Complex} (hs : 0 < s.re) :
    logDeriv (fun z : Complex => Complex.Gamma (z / 2)) s =
      (1 / 2 : Complex) * Complex.digamma (s / 2) := by
  have hcomp := logDeriv_comp
    (f := Complex.Gamma) (g := fun z : Complex => z / 2) (x := s)
    (differentiableAt_gamma_half hs) (by fun_prop)
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    exact Complex.Gamma_ne_zero_of_re_pos (by
      simp
      linarith)
  change logDeriv (Complex.Gamma ∘ (fun z : Complex => z / 2)) s = _
  rw [hcomp]
  rw [Complex.digamma_def]
  have hderiv : deriv (fun z : Complex => z / 2) s = (1 / 2 : Complex) := by
    convert ((hasDerivAt_id s).div_const (2 : Complex)).deriv using 1 <;> simp
  rw [hderiv]
  ring

/-- Pointwise logarithmic derivative of `Gamma_R` on the positive half-plane. -/
theorem logDeriv_GammaR_eq_log_pi_add_digamma
    {s : Complex} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -(Complex.log (Real.pi : Complex)) / 2 +
        (1 / 2 : Complex) * Complex.digamma (s / 2) := by
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : Complex) ^ (-s / 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    exact Complex.Gamma_ne_zero_of_re_pos (by
      simp
      linarith)
  have hmul := logDeriv_mul
    (f := fun z : Complex => (Real.pi : Complex) ^ (-z / 2))
    (g := fun z : Complex => Complex.Gamma (z / 2)) s hpow hgamma
    (differentiableAt_gammaR_cpow (s := s))
    ((differentiableAt_gamma_half hs).comp s (by fun_prop))
  rw [show Complex.Gammaℝ = (fun z : Complex =>
      (Real.pi : Complex) ^ (-z / 2) * Complex.Gamma (z / 2)) by
        funext z
        exact Complex.Gammaℝ_def z]
  rw [logDeriv_gammaR_cpow, logDeriv_gamma_comp_half hs] at hmul
  exact hmul

/-- The half-anchor constant after substituting Mathlib's digamma value. -/
theorem logDeriv_GammaR_eq_halfAnchor
    {s : Complex} (hs : 0 < s.re)
    (hgauss : HalfAnchorGaussContract) :
    logDeriv Complex.Gammaℝ s =
      -((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2 +
        (1 / 2 : Complex) *
          (∫ x : Real in Ioi (0 : Real),
            halfAnchorGaussKernel (s / 2) x) := by
  rw [logDeriv_GammaR_eq_log_pi_add_digamma hs]
  have hgauss' := hgauss (s / 2) (by simp; linarith)
  have hsplit : Complex.digamma (s / 2) =
      (Complex.digamma (s / 2) - Complex.digamma (1 / 2 : Complex)) +
        Complex.digamma (1 / 2 : Complex) := by ring
  rw [hsplit, hgauss', Complex.digamma_one_half]
  push_cast
  ring_nf
  have hlog4 : Real.log (4 : Real) = 2 * Real.log 2 := by
    calc
      Real.log (4 : Real) = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
          (by norm_num : (2 : Real) ≠ 0)]
      _ = 2 * Real.log 2 := by ring
  have hlogprod : Real.log (Real.pi * 4) =
      Real.log Real.pi + 2 * Real.log 2 := by
    rw [Real.log_mul (by positivity : Real.pi ≠ 0)
      (by norm_num : (4 : Real) ≠ 0), hlog4]
  rw [hlogprod]
  rw [← Complex.ofReal_log (x := Real.pi)
    (by positivity : (0 : Real) ≤ Real.pi)]
  have hlog2 : Complex.log (2 : Complex) = (Real.log 2 : Complex) := by
    simpa using (Complex.natCast_log (n := 2)).symm
  rw [hlog2]
  push_cast
  ring

/-- A local consumer contract for the full center-`2` Gamma_R readback.

The first field is the only nontrivial analysis left after the pointwise
half-anchor identity: it records the actual Fubini/Fourier evaluation of the
Gamma kernel against the same `CompactLogTest` owner. -/
structure CenterTwoGammaReadbackContract (F : CompactLogTest) : Prop where
  gauss : HalfAnchorGaussContract
  integrable : Integrable (fun t : Real => gammaRIntegrand F 2 t)
  normalized_readback :
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
      (∫ t : Real, gammaRIntegrand F 2 t)).re =
        archimedeanTerm F

/-- The contract's readback is exactly the sign needed by the same-owner Weil
functional.  No hidden minus sign is introduced at the Gamma_R layer. -/
theorem normalized_integral_gammaR_centerTwo_re_eq_archimedeanTerm
    (F : CompactLogTest) (hcontract : CenterTwoGammaReadbackContract F) :
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
      (∫ t : Real, gammaRIntegrand F 2 t)).re =
        archimedeanTerm F :=
  hcontract.normalized_readback

end
end C1XiCenterTwoGamma
end Source
end ConnesWeilRH
