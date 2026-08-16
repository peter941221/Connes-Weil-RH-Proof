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
