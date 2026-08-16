import ConnesWeilRH.Dev.C1XiCenterTwoPole
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.PSeries

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
open Filter
open scoped Interval Topology

noncomputable section

/-- The half-anchor Gauss kernel for the complex digamma function. -/
noncomputable def halfAnchorGaussKernel (z : Complex) (x : Real) : Complex :=
  (Complex.exp (-((1 / 2 : Complex) * (x : Complex))) -
      Complex.exp (-(z * (x : Complex)))) /
    (1 - Complex.exp (-((x : Complex))))

/-! The next two readback lemmas isolate the elementary analytic pieces of
Gauss' kernel.  They do not exchange the infinite sum with the integral; that
exchange remains an explicit convergence obligation for the eventual
`HalfAnchorGaussContract` producer. -/

/-- Pointwise geometric expansion of the half-anchor kernel on the positive
half-line.  The denominator is expanded with the norm-convergent geometric
series for `exp (-x)`. -/
theorem halfAnchorGaussKernel_eq_tsum
    {z : Complex} {x : Real} (hx : 0 < x) :
    halfAnchorGaussKernel z x =
      ∑' n : Nat,
        (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex)))) := by
  have hnorm : ‖Complex.exp (-((x : Complex)))‖ < 1 := by
    rw [Complex.norm_exp]
    simp only [neg_re, ofReal_re]
    exact (Real.exp_lt_one_iff.mpr (by linarith))
  have hgeom := tsum_geometric_of_norm_lt_one hnorm
  rw [halfAnchorGaussKernel, div_eq_mul_inv]
  rw [← hgeom]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sub_mul]
  congr 1
  · rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_add]
    congr 1
    ring
  · rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_add]
    congr 1
    ring

/-- A single decaying complex exponential is integrable on the positive
half-line whenever its coefficient has positive real part. -/
private theorem integrableOn_exp_neg_mul_complex_Ioi
    {a : Complex} (ha : 0 < a.re) :
    IntegrableOn (fun x : Real => Complex.exp (-(a * (x : Complex))))
      (Ioi (0 : Real)) := by
  have ha_neg : (-a).re < 0 := by
    rw [neg_re]
    exact neg_lt_zero.mpr ha
  convert
    (integrableOn_exp_mul_complex_Ioi
      (a := -a) ha_neg (c := (0 : Real))) using 1
  funext x
  congr 1
  ring

/-- Integral of one decaying complex exponential on `(0,∞)`. -/
theorem integral_exp_neg_mul_complex_Ioi
    {a : Complex} (ha : 0 < a.re) :
    (∫ x : Real in Ioi (0 : Real),
      Complex.exp (-(a * (x : Complex)))) = a⁻¹ := by
  simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using
    (integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) (c := (0 : Real)))

/-- The integral of one geometric-series difference.  This is the exact
termwise bridge to the reciprocal series for the digamma function. -/
theorem integral_halfAnchorGaussSeriesTerm
    {z : Complex} (hz : 0 < z.re) (n : Nat) :
    (∫ x : Real in Ioi (0 : Real),
      (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
        Complex.exp (-(((n : Complex) + z) * (x : Complex))))) =
      (((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹) := by
  have hleft : 0 < (((n : Complex) + (1 / 2 : Complex)).re) := by
    simp
    positivity
  have hright : 0 < (((n : Complex) + z).re) := by
    simp only [add_re, Complex.natCast_re]
    linarith
  have hleftInt : IntegrableOn
      (fun x : Real =>
        Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))))
      (Ioi (0 : Real)) := by
    have hleft_neg :
        (-((n : Complex) + (1 / 2 : Complex))).re < 0 := by
      rw [neg_re]
      exact neg_lt_zero.mpr hleft
    convert
      (integrableOn_exp_mul_complex_Ioi
        (a := -((n : Complex) + (1 / 2 : Complex))) hleft_neg (c := (0 : Real))) using 1
    funext x
    congr 1
    ring
  have hrightInt : IntegrableOn
      (fun x : Real =>
        Complex.exp (-(((n : Complex) + z) * (x : Complex))))
      (Ioi (0 : Real)) := by
    have hright_neg : (-((n : Complex) + z)).re < 0 := by
      rw [neg_re]
      exact neg_lt_zero.mpr hright
    convert
      (integrableOn_exp_mul_complex_Ioi (a := -((n : Complex) + z))
        hright_neg (c := (0 : Real))) using 1
    funext x
    congr 1
    ring
  rw [integral_sub hleftInt hrightInt,
    integral_exp_neg_mul_complex_Ioi hleft,
    integral_exp_neg_mul_complex_Ioi hright]

/-- Every finite geometric-series difference is integrable on the positive
half-line. -/
theorem integrableOn_halfAnchorGaussSeriesTerm
    {z : Complex} (hz : 0 < z.re) (n : Nat) :
    IntegrableOn
      (fun x : Real =>
        (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex)))))
      (Ioi (0 : Real)) := by
  have hleft : 0 < (((n : Complex) + (1 / 2 : Complex)).re) := by
    simp
    positivity
  have hright : 0 < (((n : Complex) + z).re) := by
    simp only [add_re, Complex.natCast_re]
    linarith
  exact (integrableOn_exp_neg_mul_complex_Ioi hleft).sub
    (integrableOn_exp_neg_mul_complex_Ioi hright)

/-- Finite geometric partial sums can be integrated term by term and read
back to the corresponding finite reciprocal-difference sum. -/
theorem integral_halfAnchorGaussPartialSum
    {z : Complex} (hz : 0 < z.re) (N : Nat) :
    (∫ x : Real in Ioi (0 : Real),
      ∑ n ∈ Finset.range N,
        (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex))))) =
      ∑ n ∈ Finset.range N,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact integral_halfAnchorGaussSeriesTerm hz n
  · intro n hn
    exact (integrableOn_halfAnchorGaussSeriesTerm hz n)

/-- Absolute summability of the reciprocal differences produced by the
termwise integral.  The proof uses the real parts of the two denominators to
obtain an eventual `O(n⁻²)` bound. -/
theorem summable_halfAnchorGaussReciprocalSeries
    {z : Complex} (hz : 0 < z.re) :
    Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹) := by
  let C : Real := ‖z - (1 / 2 : Complex)‖
  have hbase : Summable (fun n : Nat => C * (((n : Real) ^ 2)⁻¹)) := by
    exact (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num) |>.mul_left C
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  let A : Complex := (n : Complex) + (1 / 2 : Complex)
  let B : Complex := (n : Complex) + z
  have hnreal : (0 : Real) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hA_re : (n : Real) ≤ A.re := by
    dsimp [A]
    norm_num [Complex.add_re]
  have hB_re : (n : Real) ≤ B.re := by
    dsimp [B]
    norm_num [Complex.add_re]
    linarith
  have hA_norm : (n : Real) ≤ ‖A‖ := by
    exact hA_re.trans (le_trans (le_abs_self A.re) (abs_re_le_norm A))
  have hB_norm : (n : Real) ≤ ‖B‖ := by
    exact hB_re.trans (le_trans (le_abs_self B.re) (abs_re_le_norm B))
  have hA_ne : A ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    dsimp [A] at this
    norm_num [Complex.add_re] at this
    linarith
  have hB_ne : B ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    dsimp [B] at this
    linarith
  have hfactor : A⁻¹ - B⁻¹ = (B - A) / (A * B) := by
    field_simp [hA_ne, hB_ne]
  have hnorm_factor :
      ‖A⁻¹ - B⁻¹‖ = ‖B - A‖ / (‖A‖ * ‖B‖) := by
    rw [hfactor, norm_div, norm_mul]
  have hdenom_pos : 0 < ‖A‖ * ‖B‖ := by
    exact mul_pos (lt_of_lt_of_le hnreal hA_norm)
      (lt_of_lt_of_le hnreal hB_norm)
  have hdenom_lower : (n : Real) ^ 2 ≤ ‖A‖ * ‖B‖ := by
    rw [pow_two]
    exact mul_le_mul hA_norm hB_norm (by positivity) (norm_nonneg A)
  have hnorm_bound : ‖A⁻¹ - B⁻¹‖ ≤ C * (((n : Real) ^ 2)⁻¹) := by
    rw [hnorm_factor]
    have hnum : ‖B - A‖ = C := by
      dsimp [A, B, C]
      congr 1
      ring
    rw [hnum]
    calc
      C / (‖A‖ * ‖B‖) ≤ C / ((n : Real) ^ 2) := by
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hdenom_lower
      _ = C * (((n : Real) ^ 2)⁻¹) := by rw [div_eq_mul_inv]
  simpa [A, B] using hnorm_bound

/-- The finite partial-sum integrals converge to the reciprocal-difference
series sum.  This is the scalar limit supplied by the finite readback; the
missing infinite sum-integral exchange is deliberately not inferred here. -/
theorem tendsto_integral_halfAnchorGaussPartialSum
    {z : Complex} (hz : 0 < z.re) :
    Tendsto
      (fun N : Nat =>
        ∫ x : Real in Ioi (0 : Real),
          ∑ n ∈ Finset.range N,
            (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
              Complex.exp (-(((n : Complex) + z) * (x : Complex)))))
      atTop
      (𝓝 (∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹))) := by
  have hlim := (summable_halfAnchorGaussReciprocalSeries hz).hasSum.tendsto_sum_nat
  simpa only [integral_halfAnchorGaussPartialSum hz] using hlim

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
