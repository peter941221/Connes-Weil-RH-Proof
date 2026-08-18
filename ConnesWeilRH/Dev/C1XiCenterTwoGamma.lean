import ConnesWeilRH.Dev.C1XiCenterTwoPole
import ConnesWeilRH.Dev.C1XiGammaEulerProduct
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
open C1XiGammaEulerProduct
open C1XiVerticalFunctional
open Filter
open scoped Interval Topology
open scoped FourierTransform

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

private theorem norm_exp_neg_mul_sub_le
    {a b : Complex} {x : Real} (hx : 0 ≤ x) :
    ‖Complex.exp (-(a * (x : Complex))) -
      Complex.exp (-(b * (x : Complex)))‖ ≤
      ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by
  let f : Real → Complex := fun t =>
    Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))
  let f' : Real → Complex := fun t =>
    Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex))) *
      (-((b - a) * (x : Complex)))
  have hderiv : ∀ t : Real, HasDerivAt f
      (f' t) t := by
    intro t
    have hcast : HasDerivAt (fun y : Real => (y : Complex)) (1 : Complex) t := by
      simpa using (hasDerivAt_id (t : Complex)).comp_ofReal
    have hinner : HasDerivAt
        (fun y : Real => a + (y : Complex) * (b - a)) (b - a) t := by
      convert (hcast.mul_const (b - a)).const_add a using 1 <;> ring
    have hscaled : HasDerivAt
        (fun y : Real => -((a + (y : Complex) * (b - a)) * (x : Complex)))
        (-((b - a) * (x : Complex))) t := by
      convert (hinner.mul_const (x : Complex)).neg using 1 <;> ring
    simpa only [f, f'] using hscaled.cexp
  have hbound : ∀ t ∈ Ico (0 : Real) 1,
      ‖f' t‖ ≤ ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hmin : min a.re b.re ≤
        (a + (t : Complex) * (b - a)).re := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_re, sub_im,
        zero_mul, sub_zero, add_zero]
      calc
        min a.re b.re ≤ (1 - t) * min a.re b.re + t * min a.re b.re := by
          have heq : (1 - t) * min a.re b.re + t * min a.re b.re =
              min a.re b.re := by ring
          rw [heq]
        _ ≤ (1 - t) * a.re + t * b.re := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ht1))
            (mul_le_mul_of_nonneg_left (min_le_right _ _) ht0)
        _ = a.re + t * (b.re - a.re) := by ring
    have hmin' : min a.re b.re ≤ a.re + t * (b.re - a.re) := by
      simpa only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_re, sub_im,
        zero_mul, sub_zero, add_zero] using hmin
    have hexp : ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))‖ ≤
        Real.exp (-(min a.re b.re) * x) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
        add_re, sub_re, zero_mul, add_zero]
      have hprod : 0 ≤
          ((a.re + t * (b.re - a.re) - min a.re b.re) * x) :=
        mul_nonneg (sub_nonneg.mpr hmin') hx
      nlinarith
    change ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex))) *
      (-((b - a) * (x : Complex)))‖ ≤ _
    rw [norm_mul]
    have hderivnorm : ‖-((b - a) * (x : Complex))‖ = ‖a - b‖ * x := by
      rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
        norm_sub_rev]
    rw [hderivnorm]
    calc
      ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))‖ *
          (‖a - b‖ * x) ≤
          Real.exp (-(min a.re b.re) * x) *
            (‖a - b‖ * x) := by
        exact mul_le_mul_of_nonneg_right hexp (mul_nonneg (norm_nonneg _) hx)
      _ = ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := f) (f' := f') (C :=
      ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x))
    (fun t ht => (hderiv t).hasDerivWithinAt) hbound
  simpa [f, norm_sub_rev] using hmv

private theorem norm_halfAnchorGaussSeriesTerm_le
    {z : Complex} (hz : 0 < z.re) {n : Nat}
    {x : Real} (hx : 0 ≤ x) :
    ‖(Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
        Complex.exp (-(((n : Complex) + z) * (x : Complex))))‖ ≤
      ‖z - (1 / 2 : Complex)‖ * x * Real.exp (-((n : Real) * x)) := by
  let a : Complex := (n : Complex) + (1 / 2 : Complex)
  let b : Complex := (n : Complex) + z
  have hbase := norm_exp_neg_mul_sub_le (a := a) (b := b) hx
  have hA_re : (n : Real) ≤ a.re := by
    dsimp [a]
    norm_num [Complex.add_re]
  have hB_re : (n : Real) ≤ b.re := by
    dsimp [b]
    norm_num [Complex.add_re]
    linarith
  have hmin : (n : Real) ≤ min a.re b.re := le_min hA_re hB_re
  have hexp : Real.exp (-(min a.re b.re) * x) ≤
      Real.exp (-((n : Real) * x)) := by
    apply Real.exp_le_exp.mpr
    have hprod : 0 ≤ ((min a.re b.re - (n : Real)) * x) :=
      mul_nonneg (sub_nonneg.mpr hmin) hx
    nlinarith
  have hnum : ‖a - b‖ = ‖z - (1 / 2 : Complex)‖ := by
    dsimp [a, b]
    have hdiff : (n : Complex) + (1 / 2 : Complex) - ((n : Complex) + z) =
        -(z - (1 / 2 : Complex)) := by ring
    rw [hdiff, norm_neg]
  rw [hnum] at hbase
  calc
    ‖(Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
        Complex.exp (-(((n : Complex) + z) * (x : Complex))))‖ ≤
        ‖z - (1 / 2 : Complex)‖ * x *
          Real.exp (-(min a.re b.re) * x) := by
      simpa [a, b] using hbase
    _ ≤ ‖z - (1 / 2 : Complex)‖ * x *
          Real.exp (-((n : Real) * x)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (norm_nonneg _) hx)

private theorem integrableOn_halfAnchorGaussMajorant
    (C : Real) {n : Nat} (hn : 0 < n) :
    IntegrableOn
      (fun x : Real => C * x * Real.exp (-((n : Real) * x)))
      (Ioi (0 : Real)) := by
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : Real)) (s := (1 : Real)) (b := (n : Real))
    (by norm_num) (by norm_num) hnreal
  have hbase' : IntegrableOn
      (fun x : Real => x * Real.exp (-((n : Real) * x)))
      (Ioi (0 : Real)) := by
    simpa [Real.rpow_one] using hbase
  simpa [mul_assoc] using hbase'.const_mul C

private theorem integral_halfAnchorGaussMajorant
    (C : Real) {n : Nat} (hn : 0 < n) :
    (∫ x : Real in Ioi (0 : Real),
      C * x * Real.exp (-((n : Real) * x))) =
        C * (((n : Real) ^ 2)⁻¹) := by
  have hbase :
      (∫ x : Real in Ioi (0 : Real),
        x * Real.exp (-((n : Real) * x))) = (((n : Real) ^ 2)⁻¹) := by
    have hnreal : 0 < (n : Real) := by exact_mod_cast hn
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : Real)) (r := (n : Real)) (by norm_num) hnreal
    norm_num [Real.Gamma_nat_eq_factorial] at hgamma
    simpa [div_eq_mul_inv] using hgamma
  rw [show (fun x : Real => C * x * Real.exp (-((n : Real) * x))) =
      (fun x : Real => C * (x * Real.exp (-((n : Real) * x)))) by
        funext x
        ring]
  rw [integral_const_mul, hbase]

/-! The norm-integral summability is the majorant needed for the genuine
infinite sum-integral exchange below. -/
theorem summable_halfAnchorGaussIntegralNorm
    {z : Complex} (hz : 0 < z.re) :
    Summable (fun n : Nat =>
      ∫ x : Real in Ioi (0 : Real),
        ‖(Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex))))‖) := by
  let C : Real := ‖z - (1 / 2 : Complex)‖
  have hbase : Summable (fun n : Nat => C * (((n : Real) ^ 2)⁻¹)) := by
    exact (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num) |>.mul_left C
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hterm : IntegrableOn
      (fun x : Real =>
        (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex)))))
      (Ioi (0 : Real)) := integrableOn_halfAnchorGaussSeriesTerm hz n
  have hmajorant : IntegrableOn
      (fun x : Real => C * x * Real.exp (-((n : Real) * x)))
      (Ioi (0 : Real)) := integrableOn_halfAnchorGaussMajorant C hnpos
  have hpoint : ∀ᵐ x : Real ∂(volume.restrict (Ioi (0 : Real))),
      ‖(Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex))))‖ ≤
        C * x * Real.exp (-((n : Real) * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_halfAnchorGaussSeriesTerm_le hz (le_of_lt hx)
  have hle := integral_mono_ae hterm.norm hmajorant hpoint
  rw [integral_halfAnchorGaussMajorant C hnpos] at hle
  have hnonneg : 0 ≤
      ∫ x : Real in Ioi (0 : Real),
        ‖(Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
          Complex.exp (-(((n : Complex) + z) * (x : Complex))))‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [C] using hle

/-! The pointwise kernel expansion can now be exchanged with the integral on
`(0,∞)`, because the preceding norm-integral series is summable. -/
theorem integral_halfAnchorGaussKernel_eq_tsum_integral
    {z : Complex} (hz : 0 < z.re) :
    (∫ x : Real in Ioi (0 : Real), halfAnchorGaussKernel z x) =
      ∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹) := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : Real)))
    (F := fun (n : Nat) (x : Real) =>
      Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
        Complex.exp (-(((n : Complex) + z) * (x : Complex))))
    (fun n => integrableOn_halfAnchorGaussSeriesTerm hz n)
    (summable_halfAnchorGaussIntegralNorm hz)
  calc
    (∫ x : Real in Ioi (0 : Real), halfAnchorGaussKernel z x) =
        ∫ x : Real in Ioi (0 : Real), ∑' n : Nat,
          (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
            Complex.exp (-(((n : Complex) + z) * (x : Complex)))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact halfAnchorGaussKernel_eq_tsum (z := z) (x := x) (show 0 < x from hx)
    _ = ∑' n : Nat,
        (∫ x : Real in Ioi (0 : Real),
          (Complex.exp (-(((n : Complex) + (1 / 2 : Complex)) * (x : Complex))) -
            Complex.exp (-(((n : Complex) + z) * (x : Complex))))) := hswap.symm
    _ = ∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ - ((n : Complex) + z)⁻¹) := by
      apply tsum_congr
      intro n
      exact integral_halfAnchorGaussSeriesTerm hz n

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

/-! The Euler-product module gives the convergent digamma series only after
shifting its parameter into `Re z > 0`.  The next lemmas use the explicit
`3 / 2` base point to bridge that shift back to the half-anchor `1 / 2`. -/

private theorem correctedEulerReciprocalSeries_eq_negEuler_sub_digamma
    {z : Complex} (hz : 1 < z.re) :
    ∑' n : Nat, (1 / ((n : Complex) + z) -
      1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma z := by
  have h := correctedEulerDigammaSeries (z := z - 1) (by
    norm_num [Complex.sub_re]
    linarith)
  convert h using 1
  · apply tsum_congr
    intro n
    congr 1 <;> ring
  · congr 1 <;> ring

theorem halfAnchorShiftReciprocalSeries_eq_two :
    ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (3 / 2 : Complex))⁻¹) = (2 : Complex) := by
  let u : Nat → Complex := fun n =>
    ((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) + (3 / 2 : Complex))⁻¹
  have hu : Summable u := by
    simpa [u] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (3 / 2 : Complex)) (by norm_num))
  have hpartial : ∀ N : Nat,
      ∑ n ∈ Finset.range N, u n =
        (2 : Complex) - ((N : Complex) + (1 / 2 : Complex))⁻¹ := by
    intro N
    induction N with
    | zero => norm_num [u]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [u]
        have hshift : (N : Complex) + (3 / 2 : Complex) =
            ((N + 1 : Nat) : Complex) + (1 / 2 : Complex) := by
          push_cast
          ring
        rw [hshift]
        ring
  have hreal : Tendsto
      (fun N : Nat => (((N : Real) + (1 / 2 : Real))⁻¹ : Complex)) atTop
      (𝓝 (0 : Complex)) := by
    have hr : Tendsto
        (fun N : Nat => ((N : Real) + (1 / 2 : Real))⁻¹) atTop
        (𝓝 (0 : Real)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 / 2 : Real)
          tendsto_natCast_atTop_atTop)
    convert (Complex.continuous_ofReal.tendsto (0 : Real)).comp hr using 1
    funext N
    simp [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_add]
  have hcomplex : Tendsto
      (fun N : Nat => ((N : Complex) + (1 / 2 : Complex))⁻¹) atTop
      (𝓝 (0 : Complex)) := by
    refine hreal.congr' ?_
    filter_upwards [] with N
    have hsum : (((N : Real) + (1 / 2 : Real) : Real) : Complex) =
        (N : Complex) + (1 / 2 : Complex) := by
      push_cast
      ring
    simpa only [Complex.ofReal_inv, Complex.ofReal_add] using
      congrArg (fun w : Complex => w⁻¹) hsum
  have hlim : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range N, u n) atTop
      (𝓝 (2 : Complex)) := by
    have heq : (fun N : Nat => ∑ n ∈ Finset.range N, u n) =
        (fun N : Nat => (2 : Complex) -
          ((N : Complex) + (1 / 2 : Complex))⁻¹) := by
      funext N
      exact hpartial N
    rw [heq]
    simpa using (tendsto_const_nhds.sub hcomplex)
  exact tendsto_nhds_unique (hu.hasSum.tendsto_sum_nat) hlim

theorem halfAnchorGaussReciprocalSeries_eq_digamma_sub_half
    {z : Complex} (hz : 1 < z.re) :
    ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) =
      Complex.digamma z - Complex.digamma (1 / 2 : Complex) := by
  have hzpos : 0 < z.re := lt_trans (by norm_num) hz
  have hbase : Summable (fun n : Nat =>
      1 / ((n : Complex) + (3 / 2 : Complex)) -
        1 / ((n : Complex) + (1 : Complex))) := by
    have hone := summable_halfAnchorGaussReciprocalSeries
      (z := (1 : Complex)) (by norm_num)
    have hthree := summable_halfAnchorGaussReciprocalSeries
      (z := (3 / 2 : Complex)) (by norm_num)
    have hsub := hone.sub hthree
    convert hsub using 1
    funext n
    ring
  have hzseries : Summable (fun n : Nat =>
      1 / ((n : Complex) + z) -
        1 / ((n : Complex) + (1 : Complex))) := by
    have hone := summable_halfAnchorGaussReciprocalSeries
      (z := (1 : Complex)) (by norm_num)
    have hz' := summable_halfAnchorGaussReciprocalSeries hzpos
    have hsub := hone.sub hz'
    convert hsub using 1
    funext n
    ring
  have hbaseValue :=
    correctedEulerReciprocalSeries_eq_negEuler_sub_digamma
      (z := (3 / 2 : Complex)) (by norm_num)
  have hzValue := correctedEulerReciprocalSeries_eq_negEuler_sub_digamma hz
  have hdiff : ∑' n : Nat,
      (1 / ((n : Complex) + (3 / 2 : Complex)) -
        1 / ((n : Complex) + z)) =
      (∑' n : Nat, (1 / ((n : Complex) + (3 / 2 : Complex)) -
        1 / ((n : Complex) + (1 : Complex)))) -
        ∑' n : Nat, (1 / ((n : Complex) + z) -
          1 / ((n : Complex) + (1 : Complex))) := by
    calc
      ∑' n : Nat, (1 / ((n : Complex) + (3 / 2 : Complex)) -
          1 / ((n : Complex) + z)) =
          ∑' n : Nat,
            ((1 / ((n : Complex) + (3 / 2 : Complex)) -
              1 / ((n : Complex) + (1 : Complex))) -
              (1 / ((n : Complex) + z) -
                1 / ((n : Complex) + (1 : Complex)))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := hbase.tsum_sub hzseries
  have hsum : ∑' n : Nat,
      (1 / ((n : Complex) + (1 / 2 : Complex)) -
        1 / ((n : Complex) + z)) =
      (∑' n : Nat, (1 / ((n : Complex) + (1 / 2 : Complex)) -
        1 / ((n : Complex) + (3 / 2 : Complex)))) +
      ∑' n : Nat, (1 / ((n : Complex) + (3 / 2 : Complex)) -
        1 / ((n : Complex) + z)) := by
    have hanchor : Summable (fun n : Nat =>
        1 / ((n : Complex) + (1 / 2 : Complex)) -
          1 / ((n : Complex) + (3 / 2 : Complex))) := by
      simpa only [one_div] using
        (summable_halfAnchorGaussReciprocalSeries
          (z := (3 / 2 : Complex)) (by norm_num))
    have hdiff' : Summable (fun n : Nat =>
        1 / ((n : Complex) + (3 / 2 : Complex)) -
          1 / ((n : Complex) + z)) := by
      exact hbase.sub hzseries |>.congr (fun n => by ring)
    rw [← hanchor.tsum_add hdiff']
    apply tsum_congr
    intro n
    ring
  have hanchorValue : ∑' n : Nat,
      (1 / ((n : Complex) + (1 / 2 : Complex)) -
        1 / ((n : Complex) + (3 / 2 : Complex))) = (2 : Complex) := by
    simpa only [one_div] using halfAnchorShiftReciprocalSeries_eq_two
  have hdivTarget : ∑' n : Nat,
      (1 / ((n : Complex) + (1 / 2 : Complex)) -
        1 / ((n : Complex) + z)) =
      Complex.digamma z - Complex.digamma (1 / 2 : Complex) := by
    rw [hsum, hanchorValue, hdiff, hbaseValue, hzValue]
    have hrec := Complex.digamma_apply_add_one (1 / 2 : Complex) (by
      intro m hm
      have hre : (1 / 2 : Real) = -(m : Real) := by
        simpa using congrArg Complex.re hm
      have hmnonneg : (0 : Real) ≤ (m : Real) := by positivity
      linarith)
    norm_num at hrec
    rw [hrec]
    ring
  simpa only [one_div] using hdivTarget

/-! The recurrence extension below is independent of the right-half-plane
series identity above.  It uses one explicit telescoping shift and the
corrected Euler series at `z`, which is already valid for `0 < Re z`. -/

private theorem halfAnchorShiftReciprocalSeries_eq_inv
    {z : Complex} (hz : 0 < z.re) :
    ∑' n : Nat,
      (((n : Complex) + z)⁻¹ - ((n : Complex) + (z + 1))⁻¹) = z⁻¹ := by
  let u : Nat → Complex := fun n =>
    ((n : Complex) + z)⁻¹ - ((n : Complex) + (z + 1))⁻¹
  have hu : Summable u := by
    have hz1 : 0 < (z + 1).re := by
      norm_num [Complex.add_re]
      linarith
    have hleft := summable_halfAnchorGaussReciprocalSeries (z := z) hz
    have hright := summable_halfAnchorGaussReciprocalSeries (z := z + 1) hz1
    have hsub := hright.sub hleft
    exact hsub.congr (fun n => by
      dsimp [u]
      ring)
  have hpartial : ∀ N : Nat,
      ∑ n ∈ Finset.range N, u n = z⁻¹ - ((N : Complex) + z)⁻¹ := by
    intro N
    induction N with
    | zero => simp [u]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [u]
        have hshift : (N : Complex) + (z + 1) =
            ((N + 1 : Nat) : Complex) + z := by
          push_cast
          ring
        rw [hshift]
        ring
  have htail : Tendsto
      (fun N : Nat => ((N : Complex) + z)⁻¹) atTop (𝓝 (0 : Complex)) := by
    have hdiv := tendsto_natCast_div_add_atTop (𝕜 := Complex) z
    have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := Complex)
    have hmul := hinv.mul hdiv
    have hmul' : Tendsto
        (fun N : Nat => (N : Complex)⁻¹ * ((N : Complex) / ((N : Complex) + z)))
        atTop (𝓝 (0 : Complex)) := by
      simpa using hmul
    refine hmul'.congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with N hN
    have hNcomplex : (N : Complex) ≠ 0 := by exact_mod_cast hN
    have hden : (N : Complex) + z ≠ 0 := by
      intro hzero
      have hreal := congrArg Complex.re hzero
      simp only [Complex.add_re, Complex.natCast_re] at hreal
      norm_num at hreal
      linarith
    field_simp [hNcomplex, hden]
  have hlim : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range N, u n) atTop (𝓝 z⁻¹) := by
    have heq : (fun N : Nat => ∑ n ∈ Finset.range N, u n) =
        (fun N : Nat => z⁻¹ - ((N : Complex) + z)⁻¹) := by
      funext N
      exact hpartial N
    rw [heq]
    simpa using (tendsto_const_nhds.sub htail)
  exact tendsto_nhds_unique (hu.hasSum.tendsto_sum_nat) hlim

private theorem correctedEulerReciprocalSeries_eq_negEuler_sub_digamma_of_pos
    {z : Complex} (hz : 0 < z.re) :
    ∑' n : Nat, (1 / ((n : Complex) + z) - 1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma z := by
  have hz1 : 0 < (z + 1).re := by
    norm_num [Complex.add_re]
    linarith
  have hanchor : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) := by
    simpa only [one_div] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (1 : Complex)) (by norm_num))
  have hzA : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) := by
    exact summable_halfAnchorGaussReciprocalSeries hz
  have hz1A : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (z + 1))⁻¹) := by
    exact summable_halfAnchorGaussReciprocalSeries hz1
  have hB : Summable (fun n : Nat =>
      1 / ((n : Complex) + (z + 1)) -
        1 / ((n : Complex) + (1 : Complex))) := by
    exact (hanchor.sub hz1A).congr (fun n => by ring)
  have hD : Summable (fun n : Nat =>
      1 / ((n : Complex) + z) -
        1 / ((n : Complex) + (z + 1))) := by
    exact (hz1A.sub hzA).congr (fun n => by ring)
  have hBValue : ∑' n : Nat,
      (1 / ((n : Complex) + (z + 1)) -
        1 / ((n : Complex) + (1 : Complex))) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma (z + 1) := by
    convert correctedEulerDigammaSeries hz using 1
    · apply tsum_congr
      intro n
      congr 1 <;> ring
  have hDValue : ∑' n : Nat,
      (1 / ((n : Complex) + z) -
        1 / ((n : Complex) + (z + 1))) = z⁻¹ := by
    simpa only [one_div] using halfAnchorShiftReciprocalSeries_eq_inv hz
  have hsum : ∑' n : Nat,
      (1 / ((n : Complex) + z) - 1 / ((n : Complex) + 1)) =
      (∑' n : Nat,
        (1 / ((n : Complex) + (z + 1)) -
          1 / ((n : Complex) + (1 : Complex)))) +
        ∑' n : Nat,
          (1 / ((n : Complex) + z) -
            1 / ((n : Complex) + (z + 1))) := by
    rw [← hB.tsum_add hD]
    apply tsum_congr
    intro n
    ring
  rw [hsum, hBValue, hDValue]
  have hrec := Complex.digamma_apply_add_one z (by
    intro m hm
    have hreal := congrArg Complex.re hm
    norm_num at hreal
    have hmnonneg : (0 : Real) ≤ (m : Real) := by positivity
    linarith)
  rw [hrec]
  ring

theorem halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos
    {z : Complex} (hz : 0 < z.re) :
    ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) =
      Complex.digamma z - Complex.digamma (1 / 2 : Complex) := by
  have hanchor : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) := by
    simpa only [one_div] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (1 : Complex)) (by norm_num))
  have hzA : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    summable_halfAnchorGaussReciprocalSeries hz
  have hcz : Summable (fun n : Nat =>
      1 / ((n : Complex) + z) - 1 / ((n : Complex) + (1 : Complex))) := by
    exact (hanchor.sub hzA).congr (fun n => by ring)
  have hsum : ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) =
      (∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + (1 : Complex))⁻¹)) -
        ∑' n : Nat,
          (1 / ((n : Complex) + z) -
            1 / ((n : Complex) + (1 : Complex))) := by
    rw [← hanchor.tsum_sub hcz]
    apply tsum_congr
    intro n
    ring
  rw [hsum]
  have hbase : ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) =
      -(Real.eulerMascheroniConstant : Complex) -
        Complex.digamma (1 / 2 : Complex) := by
    simpa only [one_div] using
      correctedEulerReciprocalSeries_eq_negEuler_sub_digamma_of_pos
        (z := (1 / 2 : Complex)) (by norm_num)
  have hzValue := correctedEulerReciprocalSeries_eq_negEuler_sub_digamma_of_pos hz
  rw [hbase, hzValue]
  ring

theorem halfAnchorGaussContract_of_one_lt_re
    {z : Complex} (hz : 1 < z.re) :
    Complex.digamma z - Complex.digamma (1 / 2 : Complex) =
      ∫ x : Real in Ioi (0 : Real), halfAnchorGaussKernel z x := by
  rw [integral_halfAnchorGaussKernel_eq_tsum_integral (lt_trans (by norm_num) hz)]
  exact (halfAnchorGaussReciprocalSeries_eq_digamma_sub_half hz).symm

/-- The exact analytic input needed by the half-anchor Gamma_R consumer.

This is a proposition-valued contract on purpose: it carries no hidden
numeric field and cannot erase a readback constant through proof irrelevance.
The producer target is the Gauss representation
`digamma z - digamma (1/2) = integral halfAnchorGaussKernel z`. -/
def HalfAnchorGaussContract : Prop :=
  ∀ z : Complex, 0 < z.re →
    Complex.digamma z - Complex.digamma (1 / 2 : Complex) =
      ∫ x : Real in Ioi (0 : Real), halfAnchorGaussKernel z x

theorem halfAnchorGaussContract_of_pos : HalfAnchorGaussContract := by
  intro z hz
  rw [integral_halfAnchorGaussKernel_eq_tsum_integral hz]
  exact (halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos hz).symm

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

/-! The full right-half-plane Gauss contract now gives an explicit convergent
reciprocal series for the Gamma_R logarithmic derivative on the center-`2`
line.  The series keeps the same `verticalPoint` coordinate owner as the
arithmetic integrand; it is a pointwise readback brick, not yet the full
line-integral/Fubini theorem. -/

theorem logDeriv_GammaR_centerTwo_eq_reciprocalSeries
    (t : Real) :
    logDeriv Complex.Gammaℝ (verticalPoint 2 t) =
      -((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2 +
        (1 / 2 : Complex) *
          (∑' n : Nat,
            (((n : Complex) + (1 / 2 : Complex))⁻¹ -
              ((n : Complex) + (verticalPoint 2 t / 2))⁻¹)) := by
  have hs : 0 < (verticalPoint 2 t).re := by
    simp [verticalPoint]
  have hz : 0 < (verticalPoint 2 t / 2).re := by
    simp [verticalPoint]
  have hlog := logDeriv_GammaR_eq_halfAnchor
    (s := verticalPoint 2 t) hs halfAnchorGaussContract_of_pos
  have hseries := integral_halfAnchorGaussKernel_eq_tsum_integral
    (z := verticalPoint 2 t / 2) hz
  rw [hseries] at hlog
  exact hlog

/-- One reciprocal-series summand on the center-`2` line, retaining the
same-owner symmetrized weight and the vertical `t` coordinate. -/
noncomputable def gammaRReciprocalTerm
    (F : CompactLogTest) (n : Nat) (t : Real) : Complex :=
  (((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) + (verticalPoint 2 t / 2))⁻¹) *
    symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I

private theorem centerTwo_halfResolvent_eq
    (n : Nat) (t : Real) :
    (n : Complex) + verticalPoint 2 t / 2 =
      ((((2 * ((n : Real) + 1) : Real) : Complex) +
          (t : Complex) * Complex.I) / 2) := by
  simp [verticalPoint]
  push_cast
  ring

private theorem centerTwo_fullResolvent_ne
    (n : Nat) (t : Real) :
    (((2 * ((n : Real) + 1) : Real) : Complex) +
      (t : Complex) * Complex.I) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero] at hre
  norm_num at hre
  linarith

private theorem centerTwo_halfResolvent_inv_eq
    (n : Nat) (t : Real) :
    ((n : Complex) + (verticalPoint 2 t / 2))⁻¹ =
      (2 : Complex) *
        ((((2 * ((n : Real) + 1) : Real) : Complex) +
            (t : Complex) * Complex.I)⁻¹) := by
  rw [centerTwo_halfResolvent_eq]
  have hne := centerTwo_fullResolvent_ne n t
  field_simp [hne]

/-- Every reciprocal-series summand is integrable on the full center-`2`
line.  This is a single-term result; no infinite sum/integral exchange is
claimed here. -/
theorem integrable_gammaRReciprocalTerm
    (F : CompactLogTest) (n : Nat) :
    Integrable (fun t : Real => gammaRReciprocalTerm F n t) := by
  have hweight :=
    C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F
  have hdiv :=
    C1XiCenterTwoPole.integrable_symmetrizedLaplaceWeight_centerTwo_div_vertical
      F (a := 2 * ((n : Real) + 1)) (by positivity)
  have hdivHalf : Integrable (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t) /
        ((n : Complex) + (verticalPoint 2 t / 2))) := by
    have heq : (fun t : Real =>
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          ((n : Complex) + (verticalPoint 2 t / 2))) =
        (fun t : Real =>
          (2 : Complex) *
            (symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I)))) := by
      funext t
      rw [div_eq_mul_inv, centerTwo_halfResolvent_inv_eq]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact hdiv.const_mul (2 : Complex)
  have hleft : Integrable (fun t : Real =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ *
        symmetrizedLaplaceWeight F (verticalPoint 2 t)) :=
    hweight.const_mul (((n : Complex) + (1 / 2 : Complex))⁻¹)
  have hsub := hleft.sub hdivHalf
  have hmul := hsub.mul_const Complex.I
  apply hmul.congr
  filter_upwards with t
  change
    (((n : Complex) + (1 / 2 : Complex))⁻¹ *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) -
      symmetrizedLaplaceWeight F (verticalPoint 2 t) /
        ((n : Complex) + (verticalPoint 2 t / 2))) * Complex.I =
      gammaRReciprocalTerm F n t
  simp only [gammaRReciprocalTerm, div_eq_mul_inv]
  ring

/-- The full-line integral of one reciprocal-series summand, read back to the
same center-`2` resolvent owner. -/
theorem integral_gammaRReciprocalTerm
    (F : CompactLogTest) (n : Nat) :
    (∫ t : Real, gammaRReciprocalTerm F n t) =
      (((n : Complex) + (1 / 2 : Complex))⁻¹) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t)) * Complex.I -
        (2 : Complex) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I))) * Complex.I := by
  have hweight :=
    C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F
  have hdiv :=
    C1XiCenterTwoPole.integrable_symmetrizedLaplaceWeight_centerTwo_div_vertical
      F (a := 2 * ((n : Real) + 1)) (by positivity)
  have hhalf : Integrable (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t) /
        ((n : Complex) + (verticalPoint 2 t / 2))) := by
    have heq : (fun t : Real =>
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          ((n : Complex) + (verticalPoint 2 t / 2))) =
        (fun t : Real =>
          (2 : Complex) *
            (symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I)))) := by
      funext t
      rw [div_eq_mul_inv, centerTwo_halfResolvent_inv_eq]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact hdiv.const_mul (2 : Complex)
  have hhalfIntegral :
      (∫ t : Real,
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          ((n : Complex) + (verticalPoint 2 t / 2))) =
        (2 : Complex) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I))) := by
    have heq : (fun t : Real =>
        symmetrizedLaplaceWeight F (verticalPoint 2 t) /
          ((n : Complex) + (verticalPoint 2 t / 2))) =
        (fun t : Real =>
          (2 : Complex) *
            (symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I)))) := by
      funext t
      rw [div_eq_mul_inv, centerTwo_halfResolvent_inv_eq]
      simp only [div_eq_mul_inv]
      ring
    rw [heq, integral_const_mul]
  have hleft : Integrable (fun t : Real =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ *
        symmetrizedLaplaceWeight F (verticalPoint 2 t)) :=
    hweight.const_mul (((n : Complex) + (1 / 2 : Complex))⁻¹)
  calc
    (∫ t : Real, gammaRReciprocalTerm F n t) =
        (∫ t : Real,
          ((n : Complex) + (1 / 2 : Complex))⁻¹ *
              symmetrizedLaplaceWeight F (verticalPoint 2 t) -
            symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((n : Complex) + (verticalPoint 2 t / 2))) * Complex.I := by
      rw [show (fun t : Real => gammaRReciprocalTerm F n t) =
          (fun t : Real =>
            (((n : Complex) + (1 / 2 : Complex))⁻¹ *
                symmetrizedLaplaceWeight F (verticalPoint 2 t) -
              symmetrizedLaplaceWeight F (verticalPoint 2 t) /
                ((n : Complex) + (verticalPoint 2 t / 2))) * Complex.I) by
        funext t
        simp only [gammaRReciprocalTerm, div_eq_mul_inv]
        ring]
      rw [integral_mul_const]
    _ = (((n : Complex) + (1 / 2 : Complex))⁻¹) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t)) * Complex.I -
        (∫ t : Real,
          symmetrizedLaplaceWeight F (verticalPoint 2 t) /
            ((n : Complex) + (verticalPoint 2 t / 2))) * Complex.I := by
      rw [integral_sub hleft hhalf, integral_const_mul]
      ring
    _ = (((n : Complex) + (1 / 2 : Complex))⁻¹) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t)) * Complex.I -
        (2 : Complex) *
          (∫ t : Real,
            symmetrizedLaplaceWeight F (verticalPoint 2 t) /
              ((((2 * ((n : Real) + 1) : Real) : Complex) +
                (t : Complex) * Complex.I))) * Complex.I := by
      rw [hhalfIntegral]

/-- Any finite reciprocal-series partial sum can be integrated term by term;
the infinite exchange remains a separate convergence obligation. -/
theorem integral_gammaRReciprocalPartialSum
    (F : CompactLogTest) (N : Nat) :
    (∫ t : Real, ∑ n ∈ Finset.range N, gammaRReciprocalTerm F n t) =
      ∑ n ∈ Finset.range N, ∫ t : Real, gammaRReciprocalTerm F n t := by
  rw [integral_finsetSum]
  intro n hn
  exact integrable_gammaRReciprocalTerm F n

private lemma moment_fourier_centerTwo (f : TestFunction) :
    Integrable (fun t : Real =>
      ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t‖) := by
  have hbase := (𝓕 f).integrable_pow_mul (volume : Measure Real) 1
  have hcomp := hbase.comp_mul_left'
    (R := -(1 / (2 * Real.pi) : Real)) (by
      exact neg_ne_zero.mpr (one_div_ne_zero (by positivity)))
  have hscaled := hcomp.const_mul (2 * Real.pi)
  apply hscaled.congr
  filter_upwards with t
  rw [C1XiArithmeticPrimePowerReadback.fourierLaplace_eq_fourier]
  simp only [Nat.cast_one, Real.norm_eq_abs, norm_neg, abs_mul]
  rw [abs_neg, abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : Real))]
  have harg : -(1 / (2 * Real.pi) : Real) * t = -(t / (2 * Real.pi)) := by
    field_simp [Real.pi_ne_zero]
  rw [harg]
  norm_num [pow_one]
  field_simp [Real.pi_ne_zero]

private lemma moment_fourier_sum_centerTwo (f g : TestFunction) :
    Integrable (fun t : Real => ‖t‖ *
      ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
        C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖) := by
  have hplus := moment_fourier_centerTwo f
  have hminus := (moment_fourier_centerTwo g).comp_mul_left'
    (R := (-1 : Real)) (by norm_num)
  have hminus' : Integrable (fun t : Real => ‖t‖ *
      ‖C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖) := by
    apply hminus.congr
    filter_upwards with t
    simp only [neg_one_mul, norm_neg]
  have hbound := hplus.add hminus'
  have hplusMeas :=
    (C1XiArithmeticPrimePowerReadback.integrable_fourierLaplace f).aestronglyMeasurable
  have hminusMeas :=
    ((C1XiArithmeticPrimePowerReadback.integrable_fourierLaplace g).aestronglyMeasurable).comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure Real))
  have hsumMeas : AEStronglyMeasurable (fun t : Real =>
      C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
        C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)) := by
    simpa only [Function.comp_def] using hplusMeas.add hminusMeas
  have htMeas : AEStronglyMeasurable (fun t : Real => (t : Complex)) := by
    exact Complex.continuous_ofReal.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun t : Real => (t : Complex) *
        (C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
          C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t))) := by
    simpa only [Pi.mul_apply] using htMeas.mul hsumMeas
  have hvec := hbound.mono' hmeas
    (by
      filter_upwards with t
      change ‖(t : Complex) *
          (C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
            C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t))‖ ≤
        ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t‖ +
          ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖
      rw [norm_mul, norm_real]
      calc
        ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
            C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖ ≤
            ‖t‖ * (‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t‖ +
              ‖C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ = ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t‖ +
              ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖ := by
          ring)
  have hnorm := hvec.norm
  apply hnorm.congr
  filter_upwards with t
  rw [norm_mul, norm_real]

private theorem moment_symmetrizedLaplaceWeight_centerTwo (F : CompactLogTest) :
    Integrable (fun t : Real => ‖t‖ *
      ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖) := by
  let fPlus : TestFunction :=
    (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
      (((3 / 2 : Real) : Complex))).test
  let fMinus : TestFunction :=
    (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
      (((-3 / 2 : Real) : Complex))).test
  have hweight : (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t)) =
      (fun t : Real =>
        C1XiArithmeticPrimePowerReadback.fourierLaplace fPlus t +
          C1XiArithmeticPrimePowerReadback.fourierLaplace fMinus (-t)) := by
    funext t
    unfold symmetrizedLaplaceWeight
    rw [C1XiArithmeticPrimePowerReadback.centeredLaplaceWeight_vertical_eq_fourierLaplace
      F 2 t]
    have hreflect : (1 : Complex) - verticalPoint 2 t =
        verticalPoint (-1) (-t) := by
      apply Complex.ext <;> simp [verticalPoint] <;> ring
    rw [hreflect,
      C1XiArithmeticPrimePowerReadback.centeredLaplaceWeight_vertical_eq_fourierLaplace
        F (-1) (-t)]
    norm_num [fPlus, fMinus]
  have hmoment := moment_fourier_sum_centerTwo fPlus fMinus
  apply hmoment.congr
  filter_upwards with t
  rw [congrFun hweight t]

private theorem integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo
    (F : CompactLogTest) :
    Integrable (fun t : Real => (1 + ‖t‖) *
      ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖) := by
  have hweight :=
    (C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F).norm
  have hmoment := moment_symmetrizedLaplaceWeight_centerTwo F
  have hsum := hweight.add hmoment
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

private theorem norm_centerTwoReciprocalDifference_le
    {n : Nat} (hn : 0 < n) (t : Real) :
    ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (verticalPoint 2 t / 2))⁻¹‖ ≤
      (1 + ‖t‖) * (((n : Real) ^ 2)⁻¹) := by
  let a : Complex := (n : Complex) + (1 / 2 : Complex)
  let b : Complex := (n : Complex) + (verticalPoint 2 t / 2)
  have ha : a ≠ 0 := by
    dsimp [a]
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, Complex.natCast_re] at hre
    norm_num at hre
    exact (by positivity : 0 < (n : Real) + 1 / 2).ne' hre
  have hb : b ≠ 0 := by
    dsimp [b]
    intro h
    have hre := congrArg Complex.re h
    simp [verticalPoint] at hre
    exact (by positivity : 0 < (n : Real) + 1).ne' hre
  have hdiff : b - a =
      ((1 / 2 : Real) : Complex) + ((t / 2 : Real) : Complex) * Complex.I := by
    dsimp [a, b]
    simp [verticalPoint]
    push_cast
    ring
  have hdiffNorm : ‖b - a‖ ≤ 1 + ‖t‖ := by
    rw [hdiff]
    calc
      ‖((1 / 2 : Real) : Complex) + ((t / 2 : Real) : Complex) * Complex.I‖ ≤
          ‖((1 / 2 : Real) : Complex)‖ + ‖((t / 2 : Real) : Complex) * Complex.I‖ :=
        norm_add_le _ _
      _ = (1 / 2 : Real) + ‖t‖ / 2 := by
        rw [norm_real, Real.norm_of_nonneg (by norm_num), norm_mul, norm_real,
          Real.norm_eq_abs, norm_I, abs_div,
          abs_of_pos (by norm_num : (0 : Real) < 2)]
        simp only [Real.norm_eq_abs]
        ring
      _ ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have haLower : (n : Real) ≤ ‖a‖ := by
    dsimp [a]
    rw [show ((n : Complex) + (1 / 2 : Complex)) =
        (((n : Real) + 1 / 2 : Real) : Complex) by push_cast; ring]
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hbLower : (n : Real) ≤ ‖b‖ := by
    have hre : (n : Real) ≤ b.re := by
      dsimp [b]
      simp [verticalPoint]
    exact hre.trans (Complex.re_le_norm b)
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  rw [inv_sub_inv' ha hb, norm_mul, norm_mul, norm_inv, norm_inv]
  have hprod : (1 / ‖a‖) * ‖b - a‖ * (1 / ‖b‖) ≤
      (1 / (n : Real)) * (1 + ‖t‖) * (1 / (n : Real)) := by
    gcongr
  calc
    (‖a‖⁻¹ * ‖b - a‖ * ‖b‖⁻¹) =
        (1 / ‖a‖) * ‖b - a‖ * (1 / ‖b‖) := by simp [one_div]
    _ ≤ (1 / (n : Real)) * (1 + ‖t‖) * (1 / (n : Real)) := hprod
    _ = (1 + ‖t‖) * (((n : Real) ^ 2)⁻¹) := by
      field_simp

private theorem integrable_norm_gammaRReciprocalTerm_bound
    (F : CompactLogTest) {n : Nat} (hn : 0 < n) :
    Integrable (fun t : Real => ‖gammaRReciprocalTerm F n t‖) := by
  have hterm := integrable_gammaRReciprocalTerm F n
  have hmoment := integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo F
  let c : Real := (((n : Real) ^ 2)⁻¹)
  have hmajorant : Integrable (fun t : Real =>
      c * ((1 + ‖t‖) * ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖)) := by
    simpa only [c] using hmoment.const_mul c
  have hcomplex : Integrable (fun t : Real => gammaRReciprocalTerm F n t) := by
    apply hmajorant.mono' hterm.aestronglyMeasurable
    filter_upwards with t
    calc
      ‖gammaRReciprocalTerm F n t‖ =
          ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) + (verticalPoint 2 t / 2))⁻¹‖ *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖ := by
        simp only [gammaRReciprocalTerm, norm_mul, norm_I, mul_one]
      _ ≤ ((1 + ‖t‖) * c) *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖ := by
        gcongr
        exact norm_centerTwoReciprocalDifference_le hn t
      _ = c * ((1 + ‖t‖) *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖) := by
        ring
  exact hcomplex.norm

private theorem integral_norm_gammaRReciprocalTerm_le
    (F : CompactLogTest) {n : Nat} (hn : 0 < n) :
    (∫ t : Real, ‖gammaRReciprocalTerm F n t‖) ≤
      (((n : Real) ^ 2)⁻¹) *
        (∫ t : Real, (1 + ‖t‖) *
          ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖) := by
  have hterm := integrable_norm_gammaRReciprocalTerm_bound F hn
  have hmoment := integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo F
  let c : Real := (((n : Real) ^ 2)⁻¹)
  have hmajorant : Integrable (fun t : Real =>
      c * ((1 + ‖t‖) * ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖)) := by
    simpa only [c] using hmoment.const_mul c
  have hle := integral_mono_ae hterm hmajorant (by
    filter_upwards with t
    calc
      ‖gammaRReciprocalTerm F n t‖ =
          ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) + (verticalPoint 2 t / 2))⁻¹‖ *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖ := by
        simp only [gammaRReciprocalTerm, norm_mul, norm_I, mul_one]
      _ ≤ ((1 + ‖t‖) * c) *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖ := by
        gcongr
        exact norm_centerTwoReciprocalDifference_le hn t
      _ = c * ((1 + ‖t‖) *
            ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖) := by
        ring)
  rw [integral_const_mul] at hle
  simpa only [c, mul_comm] using hle

theorem summable_integral_norm_gammaRReciprocalTerm (F : CompactLogTest) :
    Summable (fun n : Nat => ∫ t : Real, ‖gammaRReciprocalTerm F n t‖) := by
  let C : Real :=
    ∫ t : Real, (1 + ‖t‖) * ‖symmetrizedLaplaceWeight F (verticalPoint 2 t)‖
  have hbase : Summable (fun n : Nat => C * (((n : Real) ^ 2)⁻¹)) := by
    have hpow : Summable (fun n : Nat => (((n : Real) ^ 2)⁻¹)) := by
      exact (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    exact hpow.mul_left C
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hle := integral_norm_gammaRReciprocalTerm_le F hnpos
  have hnonneg : 0 ≤ ∫ t : Real, ‖gammaRReciprocalTerm F n t‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [C, mul_comm] using hle

theorem integral_tsum_gammaRReciprocalTerm (F : CompactLogTest) :
    (∫ t : Real, ∑' n : Nat, gammaRReciprocalTerm F n t) =
      ∑' n : Nat, ∫ t : Real, gammaRReciprocalTerm F n t := by
  symm
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrable_gammaRReciprocalTerm F n)
    (summable_integral_norm_gammaRReciprocalTerm F)

/-! The norm-summable reciprocal series is itself an integrable full-line
function.  This is the missing measurability/finite-integral half behind the
pointwise Gamma_R series identity. -/

private theorem integrable_tsum_gammaRReciprocalTerm (F : CompactLogTest) :
    Integrable (fun t : Real => ∑' n : Nat, gammaRReciprocalTerm F n t) := by
  let g : Nat → Real → Complex := fun n t => gammaRReciprocalTerm F n t
  have hg : ∀ n, Integrable (g n) := fun n =>
    integrable_gammaRReciprocalTerm F n
  have hsumNorm : Summable (fun n : Nat =>
      ∫ t : Real, norm (g n t)) :=
    summable_integral_norm_gammaRReciprocalTerm F
  have hsumAE : AEStronglyMeasurable
      (fun t : Real => tsum fun n : Nat => g n t) :=
    AEStronglyMeasurable.tsum (fun n => (hg n).aestronglyMeasurable)
  have hfinite : HasFiniteIntegral
      (fun t : Real => tsum fun n : Nat => g n t) := by
    rw [HasFiniteIntegral]
    have hmeasNorm (n : Nat) : AEMeasurable (fun t : Real =>
        enorm (g n t)) := (hg n).aestronglyMeasurable.enorm
    have hlin :
        (∫⁻ t : Real, enorm (∑' n : Nat, g n t)) <=
          tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) := by
      calc
        _ <= ∫⁻ t : Real, ∑' n : Nat, enorm (g n t) := by
          apply lintegral_mono_ae
          filter_upwards with t
          exact enorm_tsum_le_tsum_enorm
        _ = tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) := by
          rw [lintegral_tsum hmeasNorm]
    have hlinFinite :
        tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) ≠ ⊤ := by
      have hterm (n : Nat) :
          (∫⁻ t : Real, enorm (g n t)) =
            ENNReal.ofReal (∫ t : Real, norm (g n t)) := by
        exact (ofReal_integral_norm_eq_lintegral_enorm (hg n)).symm
      rw [tsum_congr hterm]
      exact hsumNorm.tsum_ofReal_ne_top
    exact hlin.trans_lt (lt_top_iff_ne_top.mpr hlinFinite)
  exact ⟨hsumAE, hfinite⟩

private theorem gammaRReciprocalTerm_tsum_eq
    (F : CompactLogTest) (t : Real) :
    (∑' n : Nat, gammaRReciprocalTerm F n t) =
      (∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + (verticalPoint 2 t / 2))⁻¹)) *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I := by
  simp only [gammaRReciprocalTerm]
  rw [tsum_mul_right, tsum_mul_right]

private theorem gammaRIntegrand_centerTwo_eq_constant_sub_tsum
    (F : CompactLogTest) (t : Real) :
    gammaRIntegrand F 2 t =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
          symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I -
        (1 / 2 : Complex) *
          (∑' n : Nat, gammaRReciprocalTerm F n t) := by
  unfold gammaRIntegrand
  rw [logDeriv_GammaR_centerTwo_eq_reciprocalSeries t,
    gammaRReciprocalTerm_tsum_eq F t]
  ring

/-! The Gamma_R integrability obligation in the center-`2` contract is now
proved from the reciprocal-series majorant and the already-integrable constant
term. -/

theorem integrable_gammaRIntegrand_centerTwo
    (F : CompactLogTest) :
    Integrable (fun t : Real => gammaRIntegrand F 2 t) := by
  have hweight :=
    C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F
  have hconstant : Integrable (fun t : Real =>
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I) :=
    (hweight.const_mul
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2)).mul_const
      Complex.I
  have hseries := integrable_tsum_gammaRReciprocalTerm F
  have hsub := hconstant.sub
    (hseries.const_mul (1 / 2 : Complex))
  apply hsub.congr
  filter_upwards with t
  exact (gammaRIntegrand_centerTwo_eq_constant_sub_tsum F t).symm

/-- The paired positive-variable term obtained after the center-`2` resolvent
readback.  The two pieces are kept in one term because their separate series
are divergent at the origin, while this difference is the archimedean density
term that has a finite `n⁻²` readback. -/
noncomputable def gammaRArchProfileTerm
    (F : CompactLogTest) (n : Nat) (y : Real) : Complex :=
  Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) * (y : Complex))) *
      (F.test y + F.test (-y)) -
    2 * Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) * (y : Complex))) *
      F.test 0

private theorem gammaRArchProfileTerm_factor
    (F : CompactLogTest) (n : Nat) {y : Real} (hy : 0 < y) :
    gammaRArchProfileTerm F n y =
      (Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
          (F.test y + F.test (-y)) -
        2 * Complex.exp (-((y : Complex))) * F.test 0) *
        (Complex.exp (-(((2 : Real) : Complex) * (y : Complex)))) ^ n := by
  unfold gammaRArchProfileTerm
  have hfirst :
      Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) * (y : Complex))) =
        Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
          (Complex.exp (-(((2 : Real) : Complex) * (y : Complex)))) ^ n := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsecond :
      Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) * (y : Complex))) =
        Complex.exp (-((y : Complex))) *
          (Complex.exp (-(((2 : Real) : Complex) * (y : Complex)))) ^ n := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfirst, hsecond]
  ring

/-- The paired-fraction normalization underlying the archimedean readback:
clearing negative powers turns the geometric-sum normal form into the
`r = exp (y / 2)` numerator/denominator shape of the archimedean density. -/
private theorem pairFraction_normalize
    (r A B : Complex) (hr : r ≠ 0) (hden : r ^ 4 - 1 ≠ 0) :
    (r⁻¹ * A - 2 * (r⁻¹ ^ 2) * B) / (1 - (r⁻¹ ^ 4)) =
      (r * A - 2 * B) / (r ^ 2 - r⁻¹ ^ 2) := by
  have hleft : 1 - (r⁻¹ ^ 4) ≠ 0 := by
    intro h
    apply hden
    field_simp [hr] at h
    simpa using h
  have hright : r ^ 2 - r⁻¹ ^ 2 ≠ 0 := by
    intro h
    apply hden
    field_simp [hr] at h
    simpa using h
  field_simp [hleft, hright, hr]

theorem tsum_gammaRArchProfileTerm_eq_archimedeanIntegrand
    (F : CompactLogTest) {y : Real} (hy : 0 < y) :
    (∑' n : Nat, gammaRArchProfileTerm F n y) =
      C1SameOwnerWeil.archimedeanIntegrand F y := by
  let q : Complex :=
    Complex.exp (-(((2 : Real) : Complex) * (y : Complex)))
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    rw [Complex.norm_exp]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      add_re, zero_mul, add_zero]
    apply Real.exp_lt_one_iff.mpr
    norm_num
    linarith
  have hterm : (fun n : Nat => gammaRArchProfileTerm F n y) =
      (fun n : Nat =>
        (Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
            (F.test y + F.test (-y)) -
          2 * Complex.exp (-((y : Complex))) * F.test 0) * q ^ n) := by
    funext n
    simpa only [q] using gammaRArchProfileTerm_factor F n hy
  rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
  unfold C1SameOwnerWeil.archimedeanIntegrand
  unfold C1SameOwnerWeil.archimedeanNumerator
  unfold CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator
  simp only [Complex.ofRealCLM_apply]
  set r : Complex := ((Real.exp (y / 2) : Real) : Complex) with hr_def
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hexpHalf : Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) =
      r⁻¹ := by
    rw [show -(((1 / 2 : Real) : Complex) * (y : Complex)) =
        ((-(y / 2) : Real) : Complex) by push_cast; ring,
      ← Complex.ofReal_exp, hr_def, Real.exp_neg, Complex.ofReal_inv]
  have hexpY : Complex.exp (-((y : Complex))) = r⁻¹ ^ 2 := by
    rw [show -(y : Complex) = ((-y : Real) : Complex) by push_cast; ring,
      ← Complex.ofReal_exp, hr_def]
    have hreal : Real.exp (-y) = (Real.exp (y / 2))⁻¹ ^ 2 := by
      calc
        Real.exp (-y) = Real.exp (-(y / 2) + -(y / 2)) := by congr 1 <;> ring
        _ = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by rw [Real.exp_add]
        _ = (Real.exp (y / 2))⁻¹ * (Real.exp (y / 2))⁻¹ := by
          simp only [Real.exp_neg]
        _ = (Real.exp (y / 2))⁻¹ ^ 2 := by rw [pow_two]
    rw [hreal, Complex.ofReal_pow, Complex.ofReal_inv]
  have hq_r : q = r⁻¹ ^ 4 := by
    have hneg2 : Real.exp (-y) = (Real.exp (y / 2))⁻¹ ^ 2 := by
      calc
        Real.exp (-y) = Real.exp (-(y / 2) + -(y / 2)) := by congr 1 <;> ring
        _ = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by rw [Real.exp_add]
        _ = (Real.exp (y / 2))⁻¹ * (Real.exp (y / 2))⁻¹ := by
          simp only [Real.exp_neg]
        _ = (Real.exp (y / 2))⁻¹ ^ 2 := by rw [pow_two]
    have hreal : Real.exp (-(2 * y)) = (Real.exp (y / 2))⁻¹ ^ 4 := by
      calc
        Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
          rw [show -(2 * y) = -y + -y by ring, Real.exp_add]
        _ = ((Real.exp (y / 2))⁻¹ ^ 2) ^ 2 := by rw [hneg2, ← pow_two]
        _ = (Real.exp (y / 2))⁻¹ ^ 4 := by rw [← pow_mul]
    show Complex.exp (-(((2 : Real) : Complex) * (y : Complex))) = r⁻¹ ^ 4
    rw [show -(((2 : Real) : Complex) * (y : Complex)) =
        ((-(2 * y) : Real) : Complex) by push_cast; ring,
      ← Complex.ofReal_exp, hreal, hr_def, Complex.ofReal_pow,
      Complex.ofReal_inv]
  have hdenC : ((Real.exp y - Real.exp (-y) : Real) : Complex) =
      r ^ 2 - r⁻¹ ^ 2 := by
    have hpos : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
      calc
        Real.exp y = Real.exp (y / 2 + y / 2) := by congr 1 <;> ring
        _ = Real.exp (y / 2) * Real.exp (y / 2) := by rw [Real.exp_add]
        _ = (Real.exp (y / 2)) ^ 2 := by rw [pow_two]
    have hneg : Real.exp (-y) = (Real.exp (y / 2))⁻¹ ^ 2 := by
      calc
        Real.exp (-y) = Real.exp (-(y / 2) + -(y / 2)) := by congr 1 <;> ring
        _ = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by rw [Real.exp_add]
        _ = (Real.exp (y / 2))⁻¹ * (Real.exp (y / 2))⁻¹ := by
          simp only [Real.exp_neg]
        _ = (Real.exp (y / 2))⁻¹ ^ 2 := by rw [pow_two]
    rw [Complex.ofReal_sub, hr_def, hpos, hneg]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
  have hden : r ^ 4 - 1 ≠ 0 := by
    intro hzero
    have hr4 : r ^ 4 = 1 := sub_eq_zero.mp hzero
    have hq1 : q = 1 := by rw [hq_r, inv_pow, hr4, inv_one]
    have hnorm : ‖(1 : Complex)‖ < 1 := by rw [← hq1]; exact hq
    simp at hnorm
  rw [hexpHalf, hexpY, hq_r, hdenC]
  have hpair := pairFraction_normalize r (F.test y + F.test (-y)) (F.test 0)
    hr hden
  rw [← div_eq_mul_inv]
  exact hpair

/-! ### The y-side sum-integral exchange for the arch profile family

The two pieces of `gammaRArchProfileTerm` diverge separately, so the domination
below keeps them paired.  After the geometric factoring of
`gammaRArchProfileTerm_factor`, the remaining bracket vanishes linearly at the
origin because a Schwartz test is smooth on its compact support; beyond the
support radius only the exponentially decaying `F(0)` piece survives.  The
resulting bound is an `n⁻²` head plus a geometric tail, which is summable in
`n` and licenses the sum-integral exchange on `(0, ∞)`. -/

/-- The split radius: one past the support radius, hence positive while still
containing the test support. -/
private def archProfileSplit (F : CompactLogTest) : Real :=
  supportRadius F + 1

private theorem archProfileSplit_pos (F : CompactLogTest) :
    0 < archProfileSplit F := by
  have hR := supportRadius_nonnegative F
  unfold archProfileSplit
  linarith

private theorem test_apply_eq_zero_of_split_lt
    (F : CompactLogTest) {y : Real} (hy : archProfileSplit F < y) :
    F.test y = 0 ∧ F.test (-y) = 0 := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hmem : y ∈ Function.support F.test := Function.mem_support.mpr hne
    have hyR := (support_subset_Icc F hmem).2
    unfold archProfileSplit at hy
    linarith
  · by_contra hne
    have hmem : -y ∈ Function.support F.test := Function.mem_support.mpr hne
    have hyR := neg_le_neg_iff.mp (support_subset_Icc F hmem).1
    unfold archProfileSplit at hy
    linarith

private theorem exists_archProfile_deriv_bound (F : CompactLogTest) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ x ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
        ‖(deriv F.test) x‖ ≤ B := by
  have hsmooth : ContDiff ℝ 1 F.test := F.test.smooth 1
  have hderiv : Continuous (deriv F.test) :=
    hsmooth.continuous_deriv le_rfl
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hderiv.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x hx =>
    (hB x hx).trans (le_max_left _ _)⟩

private theorem exists_archProfile_lipschitz (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ x ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
        ∀ y ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
          ‖F.test x - F.test y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨B, hB0, hB⟩ := exists_archProfile_deriv_bound F
  refine ⟨B, hB0, fun x hx y hy => ?_⟩
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
  · intro z _
    exact ((F.test.smooth 1).differentiable (by norm_num)).differentiableAt
  · intro z hz
    exact hB z hz
  · exact convex_Icc (-(archProfileSplit F)) (archProfileSplit F)
  · exact hy
  · exact hx

private lemma real_exp_pow_nat (x : Real) (n : Nat) :
    Real.exp x ^ n = Real.exp (((n : Real)) * x) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      push_cast
      ring

private lemma complex_exp_half_real (y : Real) :
    Complex.exp (-((((1 / 2 : Real) : Complex) * (y : Complex)))) =
      ((Real.exp (-(y / 2)) : Real) : Complex) := by
  have harg : -((((1 / 2 : Real) : Complex) * (y : Complex))) =
      ((-(y / 2) : Real) : Complex) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]

private lemma complex_exp_one_real (y : Real) :
    Complex.exp (-((y : Complex))) =
      ((Real.exp (-y) : Real) : Complex) := by
  rw [show -((y : Complex)) = ((-y : Real) : Complex) by push_cast; ring,
    ← Complex.ofReal_exp]

private lemma complex_exp_two_real (y : Real) :
    Complex.exp (-((((2 : Real) : Complex) * (y : Complex)))) =
      ((Real.exp (-(2 * y)) : Real) : Complex) := by
  have harg : -((((2 : Real) : Complex) * (y : Complex))) =
      ((-(2 * y) : Real) : Complex) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]

private lemma norm_complex_exp_two_pow (y : Real) (n : Nat) :
    ‖(((Real.exp (-(2 * y)) : Real) : Complex) ^ n)‖ =
      Real.exp (((n : Real)) * (-(2 * y))) := by
  rw [norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), real_exp_pow_nat]

private lemma norm_complex_exp_two_mul_test (y : Real) (F : CompactLogTest) :
    ‖-(2 * ((Real.exp (-y) : Real) : Complex) * F.test 0)‖ =
      2 * Real.exp (-y) * ‖F.test 0‖ := by
  calc
    ‖-(2 * ((Real.exp (-y) : Real) : Complex) * F.test 0)‖ =
        ‖(2 : Complex)‖ * ‖((Real.exp (-y) : Real) : Complex)‖ * ‖F.test 0‖ := by
          rw [norm_neg, norm_mul, norm_mul]
    _ = 2 * Real.exp (-y) * ‖F.test 0‖ := by
      rw [show ‖(2 : Complex)‖ = 2 by norm_num]
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The paired bracket at a point below the split radius, bounded linearly in
`y`.  This is where the two separately divergent pieces are kept together. -/
private theorem archProfile_bracket_norm_le (F : CompactLogTest)
    {y : Real} (hy0 : 0 ≤ y) (hyS : y ≤ archProfileSplit F)
    {Lip : Real}
    (hLip : ∀ x ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
        ∀ z ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
          ‖F.test x - F.test z‖ ≤ Lip * ‖x - z‖) :
    ‖(Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
        (F.test y + F.test (-y)) -
      2 * Complex.exp (-((y : Complex))) * F.test 0)‖ ≤
      (2 * Lip + ‖F.test 0‖) * y := by
  rw [complex_exp_half_real, complex_exp_one_real]
  have hS := archProfileSplit_pos F
  have hzero : (0 : Real) ∈
      Set.Icc (-(archProfileSplit F)) (archProfileSplit F) := by
    constructor
    · exact neg_nonpos.mpr hS.le
    · exact hS.le
  have hymem : y ∈
      Set.Icc (-(archProfileSplit F)) (archProfileSplit F) := by
    constructor <;> linarith
  have hnymem : -y ∈
      Set.Icc (-(archProfileSplit F)) (archProfileSplit F) := by
    constructor <;> linarith
  have hL1 : ‖F.test y - F.test 0‖ ≤ Lip * y := by
    have hmem := hLip y hymem 0 hzero
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy0] at hmem
  have hL2 : ‖F.test (-y) - F.test 0‖ ≤ Lip * y := by
    have hmem := hLip (-y) hnymem 0 hzero
    simpa [Real.norm_eq_abs, sub_zero, abs_neg, abs_of_nonneg hy0] using hmem
  have hsum : ‖(F.test y + F.test (-y)) - 2 * F.test 0‖ ≤ 2 * Lip * y := by
    have hsplit : (F.test y + F.test (-y)) - 2 * F.test 0 =
        (F.test y - F.test 0) + (F.test (-y) - F.test 0) := by
      ring
    rw [hsplit]
    calc ‖(F.test y - F.test 0) + (F.test (-y) - F.test 0)‖ ≤
        ‖F.test y - F.test 0‖ + ‖F.test (-y) - F.test 0‖ :=
          norm_add_le _ _
      _ ≤ Lip * y + Lip * y := add_le_add hL1 hL2
      _ = 2 * Lip * y := by ring
  have hc1le : Real.exp (-(y / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hdiff : Real.exp (-(y / 2)) - Real.exp (-y) ≤ y / 2 := by
    have hone : 1 - y / 2 ≤ Real.exp (-(y / 2)) := by
      have hexp := Real.add_one_le_exp (-(y / 2))
      linarith
    have hone' : 1 - Real.exp (-(y / 2)) ≤ y / 2 := by
      linarith
    have hsplitexp : Real.exp (-(y / 2)) - Real.exp (-y) =
        Real.exp (-(y / 2)) * (1 - Real.exp (-(y / 2))) := by
      have hsq : Real.exp (-y) =
          Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsq]
      ring
    rw [hsplitexp]
    calc Real.exp (-(y / 2)) * (1 - Real.exp (-(y / 2))) ≤
        Real.exp (-(y / 2)) * (y / 2) :=
          mul_le_mul_of_nonneg_left hone' (Real.exp_pos _).le
      _ ≤ 1 * (y / 2) :=
          mul_le_mul hc1le le_rfl (by positivity) (by linarith)
      _ = y / 2 := by ring
  have hdecomp : (((Real.exp (-(y / 2)) : Real) : Complex) *
      (F.test y + F.test (-y)) -
      2 * ((Real.exp (-y) : Real) : Complex) * F.test 0) =
      ((Real.exp (-(y / 2)) : Real) : Complex) *
          ((F.test y + F.test (-y)) - 2 * F.test 0) +
        (((Real.exp (-(y / 2)) - Real.exp (-y) : Real) : Complex) *
          (2 * F.test 0)) := by
    rw [Complex.ofReal_sub]
    ring
  rw [hdecomp]
  have hn1 : ‖(((Real.exp (-(y / 2)) : Real) : Complex) *
      ((F.test y + F.test (-y)) - 2 * F.test 0))‖ ≤
      1 * (2 * Lip * y) := by
    have hnorm1 : ‖((Real.exp (-(y / 2)) : Real) : Complex)‖ = Real.exp (-(y / 2)) := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [norm_mul, hnorm1]
    exact mul_le_mul hc1le hsum (by positivity) (by linarith)
  have hn2 : ‖(((Real.exp (-(y / 2)) - Real.exp (-y) : Real) : Complex) *
      (2 * F.test 0))‖ ≤ (y / 2) * (2 * ‖F.test 0‖) := by
    have hnorm2 : ‖((Real.exp (-(y / 2)) - Real.exp (-y) : Real) : Complex)‖ =
        Real.exp (-(y / 2)) - Real.exp (-y) := by
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by
          have h1 := Real.exp_pos (-(y / 2))
          have h2 := Real.exp_pos (-y)
          have h3 := Real.exp_le_exp.mpr (by linarith : (-(y : Real)) ≤ -(y / 2))
          linarith)]
    rw [norm_mul, hnorm2, norm_mul,
      show ‖(2 : Complex)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_right hdiff (by positivity)
  calc ‖(((Real.exp (-(y / 2)) : Real) : Complex) *
        ((F.test y + F.test (-y)) - 2 * F.test 0) +
        (((Real.exp (-(y / 2)) - Real.exp (-y) : Real) : Complex) *
          (2 * F.test 0)))‖ ≤
      ‖(((Real.exp (-(y / 2)) : Real) : Complex) *
        ((F.test y + F.test (-y)) - 2 * F.test 0))‖ +
      ‖(((Real.exp (-(y / 2)) - Real.exp (-y) : Real) : Complex) *
        (2 * F.test 0))‖ :=
        norm_add_le _ _
    _ ≤ 1 * (2 * Lip * y) + (y / 2) * (2 * ‖F.test 0‖) :=
        add_le_add hn1 hn2
    _ = (2 * Lip + ‖F.test 0‖) * y := by
        ring

/-- The paired pointwise domination.  Below the split radius the paired
bracket is linearly small at the origin; above it only the exponentially
decaying `F(0)` piece remains. -/
private theorem exists_archProfile_majorant (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      (∀ (n : Nat) {y : Real}, 0 < y → y ≤ archProfileSplit F →
        ‖gammaRArchProfileTerm F n y‖ ≤
          L * y * Real.exp (-(2 * (n : Real) * y))) ∧
      (∀ (n : Nat) {y : Real}, archProfileSplit F < y →
        ‖gammaRArchProfileTerm F n y‖ ≤
          2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) := by
  obtain ⟨Lip, hLip0, hLip⟩ := exists_archProfile_lipschitz F
  have hS := archProfileSplit_pos F
  refine ⟨2 * Lip + ‖F.test 0‖, by positivity, ?_, ?_⟩
  · intro n y hy0 hyS
    have hfactor := gammaRArchProfileTerm_factor F n hy0
    have hbracket := archProfile_bracket_norm_le F hy0.le hyS hLip
    rw [hfactor, complex_exp_two_real, norm_mul, norm_complex_exp_two_pow]
    calc ‖(Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
          (F.test y + F.test (-y)) -
        2 * Complex.exp (-((y : Complex))) * F.test 0)‖ *
        Real.exp (((n : Real)) * (-(2 * y))) ≤
        ((2 * Lip + ‖F.test 0‖) * y) *
          Real.exp (((n : Real)) * (-(2 * y))) := by
          exact mul_le_mul hbracket le_rfl (by positivity) (by positivity)
      _ ≤ ((2 * Lip + ‖F.test 0‖) * y) *
          Real.exp (-(2 * (n : Real) * y)) := by
          have hexpEq :
              Real.exp ((n : Real) * (-(2 * y))) =
                Real.exp (-(2 * (n : Real) * y)) := by
            congr 1
            ring
          rw [hexpEq]
  · intro n y hy
    obtain ⟨hy1, hy2⟩ := test_apply_eq_zero_of_split_lt F hy
    have hy0 : 0 < y := lt_trans (archProfileSplit_pos F) hy
    have hfactor := gammaRArchProfileTerm_factor F n hy0
    rw [hfactor, hy1, hy2, complex_exp_half_real, complex_exp_one_real,
      complex_exp_two_real]
    have hsimp0 : (((Real.exp (-(y / 2)) : Real) : Complex) * (0 + 0) -
        2 * ((Real.exp (-y) : Real) : Complex) * F.test 0) =
        -(2 * ((Real.exp (-y) : Real) : Complex) * F.test 0) := by
      simp
    rw [hsimp0, norm_mul, norm_complex_exp_two_pow,
      norm_complex_exp_two_mul_test]
    have hexpsum : Real.exp (-y) * Real.exp (((n : Real)) * (-(2 * y))) =
        Real.exp (-((2 * (n : Real) + 1) * y)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc 2 * Real.exp (-y) * ‖F.test 0‖ *
        Real.exp (((n : Real)) * (-(2 * y))) =
        2 * ‖F.test 0‖ *
          (Real.exp (-y) * Real.exp (((n : Real)) * (-(2 * y)))) := by
            ring
      _ = 2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * y)) := by
            rw [hexpsum]
      _ ≤ 2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * y)) :=
            le_rfl

/-- A supplied support-local Lipschitz certificate gives the explicit paired
profile head bound.  This is the producer-facing form of the compact-support
argument used by `exists_gammaRArchProfile_pointwise_majorant`; it leaves the
Lipschitz constant visible for later finite-band or energy estimates. -/
theorem gammaRArchProfileTerm_norm_le_of_support_lipschitz
    (F : CompactLogTest) (Lip : Real) (hLip0 : 0 ≤ Lip)
    (hLip :
      ∀ x ∈ Set.Icc (-(supportRadius F + 1)) (supportRadius F + 1),
        ∀ z ∈ Set.Icc (-(supportRadius F + 1)) (supportRadius F + 1),
          ‖F.test x - F.test z‖ ≤ Lip * ‖x - z‖)
    (n : Nat) {y : Real} (hy0 : 0 < y)
    (hyS : y ≤ supportRadius F + 1) :
    ‖gammaRArchProfileTerm F n y‖ ≤
      (2 * Lip + ‖F.test 0‖) * y *
        Real.exp (-(2 * (n : Real) * y)) := by
  have hLip' :
      ∀ x ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
        ∀ z ∈ Set.Icc (-(archProfileSplit F)) (archProfileSplit F),
          ‖F.test x - F.test z‖ ≤ Lip * ‖x - z‖ := by
    intro x hx z hz
    exact hLip x (by simpa [archProfileSplit] using hx) z
      (by simpa [archProfileSplit] using hz)
  have hyS' : y ≤ archProfileSplit F := by
    simpa [archProfileSplit] using hyS
  have hbracket := archProfile_bracket_norm_le F hy0.le hyS' hLip'
  have hfactor := gammaRArchProfileTerm_factor F n hy0
  have hcoef : 0 ≤ (2 * Lip + ‖F.test 0‖) * y := by
    positivity
  rw [hfactor, complex_exp_two_real, norm_mul, norm_complex_exp_two_pow]
  calc
    ‖(Complex.exp (-(((1 / 2 : Real) : Complex) * (y : Complex))) *
          (F.test y + F.test (-y)) -
        2 * Complex.exp (-((y : Complex))) * F.test 0)‖ *
        Real.exp (((n : Real)) * (-(2 * y))) ≤
        ((2 * Lip + ‖F.test 0‖) * y) *
          Real.exp (((n : Real)) * (-(2 * y))) := by
      exact mul_le_mul hbracket le_rfl (by positivity) hcoef
    _ ≤ ((2 * Lip + ‖F.test 0‖) * y) *
        Real.exp (-(2 * (n : Real) * y)) := by
      have hexpEq :
          Real.exp ((n : Real) * (-(2 * y))) =
            Real.exp (-(2 * (n : Real) * y)) := by
        congr 1
        ring
      rw [hexpEq]

/-- Every paired arch profile term is integrable on the positive half-line. -/
private theorem integrableOn_gammaRArchProfileTerm
    (F : CompactLogTest) (n : Nat) :
    IntegrableOn (gammaRArchProfileTerm F n) (Ioi (0 : Real)) := by
  obtain ⟨-, -, hle1, hle2⟩ := exists_archProfile_majorant F
  have hS := archProfileSplit_pos F
  have hcont : Continuous (gammaRArchProfileTerm F n) := by
    unfold gammaRArchProfileTerm
    fun_prop
  have hIcc : IntegrableOn (gammaRArchProfileTerm F n)
      (Set.Icc 0 (archProfileSplit F)) := hcont.integrableOn_Icc
  have hIoc : IntegrableOn (gammaRArchProfileTerm F n)
      (Set.Ioc 0 (archProfileSplit F)) := hIcc.mono_set Ioc_subset_Icc_self
  have hexp : IntegrableOn
      (fun y : Real => Real.exp (-((2 * (n : Real) + 1) * y)))
      (Ioi (archProfileSplit F)) :=
    by
      simpa only [neg_mul] using
        (integrableOn_exp_mul_Ioi (a := -(2 * (n : Real) + 1))
          (neg_lt_zero.mpr (by positivity)) (archProfileSplit F))
  have hIoi : IntegrableOn (gammaRArchProfileTerm F n)
      (Ioi (archProfileSplit F)) := by
    refine (hexp.const_mul (2 * ‖F.test 0‖)).mono'
      (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hle2 n (Set.mem_Ioi.mp hy)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  exact hIoc.union hIoi

/-- Public form of the paired profile majorant.  The private split-radius
proof above is retained as the implementation owner; this theorem exposes
only the support-radius interface needed by later tail estimates. -/
theorem exists_gammaRArchProfile_pointwise_majorant
    (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      (∀ (n : Nat) {y : Real}, 0 < y → y ≤ supportRadius F + 1 →
        ‖gammaRArchProfileTerm F n y‖ ≤
          L * y * Real.exp (-(2 * (n : Real) * y))) ∧
      (∀ (n : Nat) {y : Real}, supportRadius F + 1 < y →
        ‖gammaRArchProfileTerm F n y‖ ≤
          2 * ‖F.test 0‖ *
            Real.exp (-((2 * (n : Real) + 1) * y))) := by
  simpa [archProfileSplit] using exists_archProfile_majorant F

/-- Public integrability view for consumers that keep the profile term as
an owner rather than reopening the source file's private split proof. -/
theorem integrableOn_gammaRArchProfileTerm_public
    (F : CompactLogTest) (n : Nat) :
    IntegrableOn (gammaRArchProfileTerm F n) (Ioi (0 : Real)) :=
  integrableOn_gammaRArchProfileTerm F n

/-- The summable majorant series for the norm integrals: an `n⁻²` head plus a
geometric tail beyond the split radius. -/
theorem summable_integralOn_norm_gammaRArchProfileTerm
    (F : CompactLogTest) :
    Summable (fun n : Nat =>
      ∫ y : Real in Ioi (0 : Real), ‖gammaRArchProfileTerm F n y‖) := by
  obtain ⟨L, hL0, hle1, hle2⟩ := exists_archProfile_majorant F
  have hS := archProfileSplit_pos F
  -- the model integral value for 0 < n
  have hintval : ∀ n : Nat, 0 < n →
      (∫ y : Real in Ioi (0 : Real),
        y * Real.exp (-(2 * (n : Real) * y))) =
        (((2 * (n : Real)) ^ 2)⁻¹) := by
    intro n hn
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : Real)) (r := 2 * (n : Real)) (by norm_num) (by positivity)
    have hgamma' :
        (∫ y : Real in Ioi (0 : Real),
          y * Real.exp (-(2 * (n : Real) * y))) =
          (1 / (2 * (n : Real))) ^ 2 * Real.Gamma 2 := by
      simpa [show (2 : Real) - 1 = 1 by norm_num] using hgamma
    rw [hgamma']
    norm_num [Real.Gamma_nat_eq_factorial, div_eq_mul_inv]
    ring
  have hint : ∀ n : Nat, 0 < n →
      IntegrableOn (fun y : Real => y * Real.exp (-(2 * (n : Real) * y)))
        (Ioi (0 : Real)) := by
    intro n hn
    refine Integrable.of_integral_ne_zero ?_
    rw [hintval n hn]
    positivity
  -- the tail integral value
  have htailval : ∀ n : Nat,
      (∫ y : Real in Ioi (archProfileSplit F),
        Real.exp (-((2 * (n : Real) + 1) * y))) =
        Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) /
          ((2 * (n : Real) + 1)) := by
    intro n
    have hval := integral_exp_mul_Ioi
      (a := -(2 * (n : Real) + 1))
      (neg_lt_zero.mpr (by positivity)) (archProfileSplit F)
    calc
      (∫ y : Real in Ioi (archProfileSplit F),
          Real.exp (-((2 * (n : Real) + 1) * y))) =
          -Real.exp (-(2 * (n : Real) + 1) * archProfileSplit F) /
            -(2 * (n : Real) + 1) := by
              convert hval using 1 <;> ring
      _ = Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) /
            (2 * (n : Real) + 1) := by
              rw [neg_div_neg_eq]
              congr 2
              ring
  -- the per-term bound for 0 < n
  have hbound : ∀ n : Nat, 0 < n →
      (∫ y : Real in Ioi (0 : Real), ‖gammaRArchProfileTerm F n y‖) ≤
        L * (((2 * (n : Real)) ^ 2)⁻¹) +
          2 * ‖F.test 0‖ *
            Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) := by
    intro n hn
    have hintTerm : IntegrableOn (fun y : Real => ‖gammaRArchProfileTerm F n y‖)
        (Ioi (0 : Real)) := (integrableOn_gammaRArchProfileTerm F n).norm
    have hdisj : Disjoint (Set.Ioc 0 (archProfileSplit F))
        (Ioi (archProfileSplit F)) := by
      rw [Set.disjoint_right]
      intro x hx1 hx2
      exact (not_lt_of_ge hx2.2) hx1
    have hsubIoc : Set.Ioc 0 (archProfileSplit F) ⊆ Ioi (0 : Real) :=
      fun y hy => Set.mem_Ioi.mpr (Set.mem_Ioc.mp hy).1
    have hsubTail : Ioi (archProfileSplit F) ⊆ Ioi (0 : Real) :=
      fun y hy => lt_trans hS (Set.mem_Ioi.mp hy)
    have hintg : IntegrableOn
        (fun y : Real => L * (y * Real.exp (-(2 * (n : Real) * y))))
        (Ioi (0 : Real)) := (hint n hn).const_mul L
    have hexp : IntegrableOn
        (fun y : Real => Real.exp (-((2 * (n : Real) + 1) * y)))
        (Ioi (archProfileSplit F)) :=
      by
        simpa only [neg_mul] using
          (integrableOn_exp_mul_Ioi (a := -(2 * (n : Real) + 1))
            (neg_lt_zero.mpr (by positivity)) (archProfileSplit F))
    have hexpScaled : IntegrableOn
        (fun y : Real =>
          2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y)))
        (Ioi (archProfileSplit F)) := hexp.const_mul _
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    rw [setIntegral_union hdisj measurableSet_Ioi
      (hintTerm.mono_set hsubIoc) (hintTerm.mono_set hsubTail)]
    -- head: mono on the compact piece, then extend to the half-line
    have hheadIoc : (∫ y : Real in Set.Ioc 0 (archProfileSplit F),
        ‖gammaRArchProfileTerm F n y‖) ≤
        (∫ y : Real in Set.Ioc 0 (archProfileSplit F),
          L * (y * Real.exp (-(2 * (n : Real) * y)))) := by
      refine integral_mono_ae (hintTerm.mono_set hsubIoc)
        (hintg.mono_set hsubIoc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      simpa [mul_assoc] using
        hle1 n (Set.mem_Ioc.mp hy).1 (Set.mem_Ioc.mp hy).2
    have hheadExt : (∫ y : Real in Set.Ioc 0 (archProfileSplit F),
        L * (y * Real.exp (-(2 * (n : Real) * y)))) ≤
        (∫ y : Real in Ioi (0 : Real),
          L * (y * Real.exp (-(2 * (n : Real) * y)))) := by
      refine setIntegral_mono_set hintg ?_ (Filter.Eventually.of_forall hsubIoc)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg hL0
        (mul_nonneg (le_of_lt (Set.mem_Ioi.mp hy)) (Real.exp_nonneg _))
    have hheadVal : (∫ y : Real in Ioi (0 : Real),
        L * (y * Real.exp (-(2 * (n : Real) * y)))) =
        L * (((2 * (n : Real)) ^ 2)⁻¹) := by
      rw [integral_const_mul, hintval n hn]
    have hheadFinal : (∫ y : Real in Set.Ioc 0 (archProfileSplit F),
        ‖gammaRArchProfileTerm F n y‖) ≤
        L * (((2 * (n : Real)) ^ 2)⁻¹) :=
      hheadIoc.trans (hheadExt.trans (le_of_eq hheadVal))
    -- tail: mono then the exact exponential value
    have htailMono : (∫ y : Real in Ioi (archProfileSplit F),
        ‖gammaRArchProfileTerm F n y‖) ≤
        (∫ y : Real in Ioi (archProfileSplit F),
          2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) := by
      refine integral_mono_ae (hintTerm.mono_set hsubTail) hexpScaled ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hle2 n (Set.mem_Ioi.mp hy)
    have htailFinal : (∫ y : Real in Ioi (archProfileSplit F),
        ‖gammaRArchProfileTerm F n y‖) ≤
        2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) := by
      calc (∫ y : Real in Ioi (archProfileSplit F),
          ‖gammaRArchProfileTerm F n y‖) ≤
          (∫ y : Real in Ioi (archProfileSplit F),
            2 * ‖F.test 0‖ * Real.exp (-((2 * (n : Real) + 1) * y))) :=
              htailMono
        _ = 2 * ‖F.test 0‖ *
            (∫ y : Real in Ioi (archProfileSplit F),
              Real.exp (-((2 * (n : Real) + 1) * y))) := by
              rw [integral_const_mul]
        _ = 2 * ‖F.test 0‖ *
            (Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) /
              ((2 * (n : Real) + 1))) := by
              rw [htailval n]
        _ ≤ 2 * ‖F.test 0‖ *
            Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) :=
              by
                apply mul_le_mul_of_nonneg_left
                · have hkpos : 0 < 2 * (n : Real) + 1 := by positivity
                  apply (div_le_iff₀ hkpos).2
                  have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg n
                  have hk : (1 : Real) ≤ 2 * (n : Real) + 1 := by nlinarith
                  nlinarith [Real.exp_nonneg
                    (-((2 * (n : Real) + 1) * archProfileSplit F))]
                · positivity
    exact add_le_add hheadFinal htailFinal
  -- summability of the majorant series
  have hbase : Summable (fun n : Nat =>
      L * (((2 * (n : Real)) ^ 2)⁻¹) +
        2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F))) := by
    have h1 : Summable (fun n : Nat => L * (4⁻¹ * (((n : Real) ^ 2)⁻¹))) := by
      have hpow : Summable (fun n : Nat => (((n : Real) ^ 2)⁻¹)) :=
        (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
      exact (hpow.mul_left _).mul_left _
    have h1' : Summable (fun n : Nat =>
        L * (((2 * (n : Real)) ^ 2)⁻¹)) :=
      h1.congr (fun n => by
        have : (((2 * (n : Real)) ^ 2)⁻¹) = 4⁻¹ * (((n : Real) ^ 2)⁻¹) := by
          field_simp
          ring
        rw [this])
    have h2 : Summable (fun n : Nat => 2 * ‖F.test 0‖ *
        (Real.exp (-(archProfileSplit F))) *
        ((Real.exp (-(2 * archProfileSplit F))) ^ n)) := by
      have hgeom : Summable (fun n : Nat =>
          ((Real.exp (-(2 * archProfileSplit F))) ^ n)) :=
        summable_geometric_of_lt_one (by positivity)
          (Real.exp_lt_one_iff.mpr (by
            have := archProfileSplit_pos F
            linarith))
      exact hgeom.mul_left _
    have h2' : Summable (fun n : Nat =>
        2 * ‖F.test 0‖ *
          Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F))) :=
      h2.congr (fun n => by
        have hpoweq : ((Real.exp (-(2 * archProfileSplit F))) ^ n) =
            Real.exp (((n : Real)) * (-(2 * archProfileSplit F))) :=
          real_exp_pow_nat _ n
        rw [hpoweq]
        calc
          2 * ‖F.test 0‖ * Real.exp (-(archProfileSplit F)) *
              Real.exp (((n : Real)) * (-(2 * archProfileSplit F))) =
            2 * ‖F.test 0‖ *
              (Real.exp (-(archProfileSplit F)) *
                Real.exp (((n : Real)) * (-(2 * archProfileSplit F)))) := by
                ring
          _ = 2 * ‖F.test 0‖ *
              Real.exp (-(archProfileSplit F) +
                ((n : Real) * (-(2 * archProfileSplit F)))) := by
                rw [← Real.exp_add]
          _ = 2 * ‖F.test 0‖ *
              Real.exp (-((2 * (n : Real) + 1) * archProfileSplit F)) := by
                congr 2
                ring)
    exact h1'.add h2'
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hle := hbound n hnpos
  have hnn : 0 ≤
      (∫ y : Real in Ioi (0 : Real), ‖gammaRArchProfileTerm F n y‖) :=
    integral_nonneg (fun y => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- The genuine infinite sum-integral exchange for the arch profile family on
the positive half-line. -/
theorem integralOn_tsum_gammaRArchProfileTerm (F : CompactLogTest) :
    (∫ y : Real in Ioi (0 : Real),
      ∑' n : Nat, gammaRArchProfileTerm F n y) =
      ∑' n : Nat,
        (∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y) := by
  exact (integral_tsum_of_summable_integral_norm
    (fun n => integrableOn_gammaRArchProfileTerm F n)
    (summable_integralOn_norm_gammaRArchProfileTerm F)).symm

/-- The archimedean density integral equals the paired arch profile series.
This is the y-side half of the Gamma_R archimedean readback. -/
theorem integralOn_archimedeanIntegrand_eq_tsum (F : CompactLogTest) :
    (∫ y : Real in Ioi (0 : Real),
      C1SameOwnerWeil.archimedeanIntegrand F y) =
      ∑' n : Nat,
        (∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y) := by
  have hpt : ∀ y ∈ Ioi (0 : Real),
      C1SameOwnerWeil.archimedeanIntegrand F y =
        ∑' n : Nat, gammaRArchProfileTerm F n y :=
    fun y hy => (tsum_gammaRArchProfileTerm_eq_archimedeanIntegrand F hy).symm
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  exact integralOn_tsum_gammaRArchProfileTerm F

/-! ### Per-term Fourier/resolvent readback

The paired profile has one elementary exponential tail involving `F.test 0`.
Its integral is exactly the static reciprocal in `gammaRReciprocalTerm`; after
that cancellation, the public center-`2` resolvent readback supplies the other
profile.  This proves the single-index bridge without splitting the divergent
infinite series. -/

private theorem integrableOn_gammaRArchProfileTail
    (F : CompactLogTest) (n : Nat) :
    IntegrableOn (fun y : Real =>
      (2 : Complex) *
        Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
          (y : Complex))) * F.test 0)
      (Ioi (0 : Real)) := by
  have ha : 0 < (((2 * (n : Real) + 1 : Real) : Complex).re) := by
    simp only [ofReal_re]
    positivity
  exact ((integrableOn_exp_neg_mul_complex_Ioi ha).const_mul (2 : Complex)).mul_const
    (F.test 0)

private theorem integralOn_gammaRArchProfileTail
    (F : CompactLogTest) (n : Nat) :
    (∫ y : Real in Ioi (0 : Real),
      (2 : Complex) *
        Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
          (y : Complex))) * F.test 0) =
      ((n : Complex) + (1 / 2 : Complex))⁻¹ * F.test 0 := by
  have ha : 0 < (((2 * (n : Real) + 1 : Real) : Complex).re) := by
    simp only [ofReal_re]
    positivity
  have hn : (n : Complex) + (1 / 2 : Complex) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [add_re, Complex.natCast_re] at hre
    norm_num at hre
    have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  rw [integral_mul_const, integral_const_mul,
    integral_exp_neg_mul_complex_Ioi ha]
  have hcoeff : ((2 * (n : Real) + 1 : Real) : Complex) =
      (2 : Complex) * ((n : Complex) + (1 / 2 : Complex)) := by
    push_cast
    ring
  rw [hcoeff]
  field_simp [hn]

private theorem integralOn_gammaRArchProfileTerm_eq_profile_sub_tail
    (F : CompactLogTest) (n : Nat) :
    (∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y) =
      (∫ y : Real in Ioi (0 : Real),
        Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
          (y : Complex))) * (F.test y + F.test (-y))) -
        ((n : Complex) + (1 / 2 : Complex))⁻¹ * F.test 0 := by
  have htail := integrableOn_gammaRArchProfileTail F n
  have hpaired := integrableOn_gammaRArchProfileTerm F n
  have hpoint : (fun y : Real => gammaRArchProfileTerm F n y) =
      (fun y : Real =>
        Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
          (y : Complex))) * (F.test y + F.test (-y)) -
          (2 : Complex) *
            Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
              (y : Complex))) * F.test 0) := by
    funext y
    unfold gammaRArchProfileTerm
    ring
  have hprofile : IntegrableOn (fun y : Real =>
      Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
        (y : Complex))) * (F.test y + F.test (-y))) (Ioi (0 : Real)) := by
    apply (hpaired.add htail).congr_fun _ measurableSet_Ioi
    intro y hy
    change gammaRArchProfileTerm F n y +
      (2 : Complex) *
        Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
          (y : Complex))) * F.test 0 =
      Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
        (y : Complex))) * (F.test y + F.test (-y))
    rw [congrFun hpoint y]
    ring
  rw [hpoint, integral_sub hprofile htail,
    integralOn_gammaRArchProfileTail F n]

/-- The full-line integral of one reciprocal Gamma_R summand is the negative
`4 * pi * I` multiple of its paired positive-variable profile integral. -/
theorem integral_gammaRReciprocalTerm_eq_neg_four_pi_I_mul_archProfile
    (F : CompactLogTest) (n : Nat) :
    (∫ t : Real, gammaRReciprocalTerm F n t) =
      -(4 * (Real.pi : Complex) * Complex.I) *
        (∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y) := by
  have hweight :=
    C1XiCenterTwoPole.integral_symmetrizedLaplaceWeight_centerTwo F
  have hresolvent :=
    C1XiCenterTwoPole.integral_symmetrizedLaplaceWeight_centerTwo_div_vertical_eq_archProfile
      F (a := 2 * ((n : Real) + 1)) (by positivity)
  have hprofile := integralOn_gammaRArchProfileTerm_eq_profile_sub_tail F n
  have hresolventProfile :
      (∫ y : Real in Ioi (0 : Real),
        Complex.exp (-(((2 * ((n : Real) + 1) - 3 / 2 : Real) : Complex) *
          (y : Complex))) * (F.test y + F.test (-y))) =
        ∫ y : Real in Ioi (0 : Real),
          Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
            (y : Complex))) * (F.test y + F.test (-y)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    push_cast
    ring
  rw [integral_gammaRReciprocalTerm F n, hweight, hresolvent,
    hresolventProfile, hprofile]
  ring

/-- The normalized reciprocal series is the negative direct archimedean
density integral.  This is the series-level combination of the per-term
resolvent readback with the paired-profile Fubini theorem. -/
theorem normalized_tsum_integral_gammaRReciprocalTerm_eq_neg_archimedeanIntegral
    (F : CompactLogTest) :
    (1 / 2 : Complex) * (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
        (∑' n : Nat, ∫ t : Real, gammaRReciprocalTerm F n t) =
      -(∫ y : Real in Ioi (0 : Real),
        C1SameOwnerWeil.archimedeanIntegrand F y) := by
  have hterms :
      (fun n : Nat => ∫ t : Real, gammaRReciprocalTerm F n t) =
        (fun n : Nat => -(4 * (Real.pi : Complex) * Complex.I) *
          (∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y)) := by
    funext n
    exact integral_gammaRReciprocalTerm_eq_neg_four_pi_I_mul_archProfile F n
  rw [hterms, tsum_mul_left,
    ← integralOn_archimedeanIntegrand_eq_tsum F]
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi, Complex.I_ne_zero]
  ring

/-! The full-line Gamma_R integral now has a scalar-series normal form.  The
remaining archimedean readback is precisely the conversion of this convergent
series into the direct positive-variable density. -/

theorem integral_gammaRIntegrand_centerTwo_eq_constant_sub_tsum_integrals
    (F : CompactLogTest) :
    (∫ t : Real, gammaRIntegrand F 2 t) =
      (∫ t : Real,
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
          symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I) -
        (1 / 2 : Complex) *
          (∑' n : Nat, ∫ t : Real, gammaRReciprocalTerm F n t) := by
  have hweight :=
    C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F
  have hconstant : Integrable (fun t : Real =>
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I) :=
    (hweight.const_mul
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2)).mul_const
      Complex.I
  have hseries := integrable_tsum_gammaRReciprocalTerm F
  have hsum : Integrable (fun t : Real =>
      (1 / 2 : Complex) * ∑' n : Nat, gammaRReciprocalTerm F n t) :=
    hseries.const_mul (1 / 2 : Complex)
  have hdecomp := integral_sub hconstant hsum
  have hpoint : (fun t : Real => gammaRIntegrand F 2 t) =
      (fun t : Real =>
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
            symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I -
          (1 / 2 : Complex) * ∑' n : Nat, gammaRReciprocalTerm F n t) := by
    funext t
    exact gammaRIntegrand_centerTwo_eq_constant_sub_tsum F t
  rw [hpoint, hdecomp, integral_const_mul, integral_tsum_gammaRReciprocalTerm]

theorem normalized_gammaR_centerTwo_eq_constant_sub_tsum_integrals
    (F : CompactLogTest) :
    (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
        (∫ t : Real, gammaRIntegrand F 2 t) =
      (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
          (∫ t : Real,
            (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
              symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I) -
        (1 / 2 : Complex) *
          (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
            (∑' n : Nat, ∫ t : Real, gammaRReciprocalTerm F n t) := by
  rw [integral_gammaRIntegrand_centerTwo_eq_constant_sub_tsum_integrals]
  ring

/-! The constant term in the center-`2` Gamma_R logarithmic derivative has an
explicit same-owner readback.  This is only the constant piece; the reciprocal
series piece still needs its own sum-integral argument. -/

theorem normalized_gammaR_centerTwo_constant_part_eq
    (F : CompactLogTest) :
    (((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
      (∫ t : Real,
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
          symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I))).re =
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
        F.test 0).re) := by
  have hweight :=
    ConnesWeilRH.Source.C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F
  have hconstant : Integrable (fun t : Real =>
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I) := by
    exact (hweight.const_mul
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2)).mul_const
      Complex.I
  have hbase :=
    ConnesWeilRH.Source.C1XiCenterTwoPole.integral_symmetrizedLaplaceWeight_centerTwo F
  rw [integral_mul_const, integral_const_mul, hbase]
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinner :
      (2 * (Real.pi : Complex) * Complex.I)⁻¹ *
          ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) / 2) *
            (4 * (Real.pi : Complex) * (F.test 0 : Complex)) * Complex.I) =
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0) := by
    field_simp [hpi, Complex.I_ne_zero]
    push_cast
    ring
  rw [hinner]

/-- The normalized center-`2` Gamma_R integral reads back to the complete
same-owner archimedean term. -/
theorem normalized_gammaR_centerTwo_re_eq_archimedeanTerm
    (F : CompactLogTest) :
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
      (∫ t : Real, gammaRIntegrand F 2 t)).re =
        archimedeanTerm F := by
  rw [normalized_gammaR_centerTwo_eq_constant_sub_tsum_integrals,
    Complex.sub_re, normalized_gammaR_centerTwo_constant_part_eq F,
    normalized_tsum_integral_gammaRReciprocalTerm_eq_neg_archimedeanIntegral F]
  simp only [Complex.neg_re]
  unfold archimedeanTerm
  rw [Complex.add_re]
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

/-- The center-`2` Gamma_R readback contract is supplied by the proved
half-anchor Gauss formula, full-line integrability, and the paired-profile
Fourier readback. -/
theorem centerTwoGammaReadbackContract_of_halfAnchorGauss
    (F : CompactLogTest) : CenterTwoGammaReadbackContract F :=
  ⟨halfAnchorGaussContract_of_pos,
    integrable_gammaRIntegrand_centerTwo F,
    normalized_gammaR_centerTwo_re_eq_archimedeanTerm F⟩

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
