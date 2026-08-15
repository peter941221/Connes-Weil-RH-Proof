import ConnesWeilRH.Dev.C1XiArithmeticIntervalReadback
import ConnesWeilRH.Dev.C1SpectralWeil
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# C1XiArithmeticPrimePowerReadback - prime-power Fourier readback

The right-line von Mangoldt term is a Fourier transform of an exponentially
weighted compact-log test.  Fourier inversion therefore reads one complete
vertical-line integral back to the corresponding finite prime-power value.
This module proves that bridge for one index before assembling the finite
visible-prime sum.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticPrimePowerReadback

open MeasureTheory
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiArithmeticIntervalReadback
open C1XiVerticalFunctional
open scoped FourierTransform LSeries.notation Topology

noncomputable section

/-- The unweighted Fourier profile used by a vertical-line Laplace value. -/
noncomputable def fourierLaplace
    (f : TestFunction) (t : Real) : Complex :=
  ∫ u : Real,
    Complex.exp ((t : Complex) * (u : Complex) * Complex.I) * f u

theorem fourierLaplace_eq_fourier
    (f : TestFunction) (t : Real) :
    fourierLaplace f t =
      (𝓕 f) (-(t / (2 * Real.pi))) := by
  unfold fourierLaplace
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul, Real.inner_apply]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

theorem fourierLaplace_compactLogTest_test_eq_laplaceAt
    (F : CompactLogTest) (t : Real) :
    fourierLaplace F.test t =
      CompactLogTest.laplaceAt F ((t : Complex) * Complex.I) := by
  unfold fourierLaplace CompactLogTest.laplaceAt
  apply integral_congr_ae
  filter_upwards with u
  simp only [CompactLogTest.exponentialWeight_apply]
  congr 2
  ring

theorem centeredLaplaceWeight_vertical_eq_fourierLaplace
    (F : CompactLogTest) (c t : Real) :
    centeredLaplaceWeight F (verticalPoint c t) =
      fourierLaplace
        (CompactLogTest.exponentialWeight F
          ((c - (1 / 2 : Real)) : Complex)).test t := by
  rw [fourierLaplace_compactLogTest_test_eq_laplaceAt]
  rw [C1SpectralWeil.laplaceAt_exponentialWeight_eq]
  unfold centeredLaplaceWeight verticalPoint
  congr 1
  push_cast
  ring

theorem lSeriesTerm_vonMangoldt_vertical_eq_exp
    {c t : Real} {n : Nat} (hn : n ≠ 0) :
    LSeries.term (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (verticalPoint c t) n =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp (-((c : Complex) * (Real.log n : Complex))) *
        Complex.exp (-((t : Complex) * (Real.log n : Complex) * Complex.I)) := by
  rw [LSeries.term_of_ne_zero hn]
  have hnC : (n : Complex) ≠ 0 := by
    exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  simp only [verticalPoint]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  have hsplit :
      -((Real.log n : Complex) *
        ((c : Complex) + (t : Complex) * Complex.I)) =
        -((c : Complex) * (Real.log n : Complex)) +
          -((t : Complex) * (Real.log n : Complex) * Complex.I) := by
    ring
  rw [hsplit, Complex.exp_add]
  ring

@[simp] theorem arithmeticPrimePowerIntegrand_zero
    (F : CompactLogTest) (c t : Real) :
    arithmeticPrimePowerIntegrand F c t 0 = 0 := by
  simp [arithmeticPrimePowerIntegrand]

theorem arithmeticPrimePowerIntegrand_eq_exp_of_ne_zero
    (F : CompactLogTest) {c t : Real} {n : Nat} (hn : n ≠ 0) :
    arithmeticPrimePowerIntegrand F c t n =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp (-((c : Complex) * (Real.log n : Complex))) *
      Complex.exp (-((t : Complex) * (Real.log n : Complex) * Complex.I)) *
        symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I := by
  unfold arithmeticPrimePowerIntegrand
  change
    LSeries.term (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (verticalPoint c t) n *
        symmetrizedLaplaceWeight F (verticalPoint c t) * Complex.I = _
  rw [lSeriesTerm_vonMangoldt_vertical_eq_exp hn]

set_option maxHeartbeats 800000 in
-- The Fourier inversion proof expands several coercion and change-of-variable
-- identities before the final algebraic normalization.
theorem integral_fourierLaplace_mul_character
    (f : TestFunction) (x : Real) :
    ∫ t : Real,
        fourierLaplace f t *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) * f x := by
  let h : Real → Complex := fun t =>
    fourierLaplace f t *
      Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))
  have hinv : 𝓕⁻ (𝓕 f) x = f x := by
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
      (f.integrable.fourierInv_fourier_eq (𝓕 f).integrable
        f.continuous.continuousAt)
  have hchange := Measure.integral_comp_mul_left h (-2 * Real.pi)
  have hscale : |((-2 * Real.pi)⁻¹ : Real)| = (2 * Real.pi)⁻¹ := by
    have harg : (-2 * Real.pi : Real) = -(2 * Real.pi) := by ring
    have harg_neg : (-2 * Real.pi : Real) < 0 := by nlinarith [Real.pi_pos]
    rw [abs_of_neg (inv_lt_zero.mpr harg_neg), harg, inv_neg]
    simp
  have hchange' :
      ∫ ξ : Real, h ((-2 * Real.pi) * ξ) =
        ((2 * Real.pi : Real)⁻¹ : Complex) * ∫ t : Real, h t := by
    simpa only [hscale, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul] using hchange
  have hinv' := Real.fourierInv_eq' ((𝓕 f : TestFunction) : Real → Complex) x
  have hscaled :
      ∫ ξ : Real, h ((-2 * Real.pi) * ξ) = 𝓕⁻ (𝓕 f) x := by
    rw [SchwartzMap.fourierInv_coe, hinv']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [h]
    rw [fourierLaplace_eq_fourier]
    simp only [smul_eq_mul]
    have harg : -((-2 * Real.pi * ξ) / (2 * Real.pi)) = ξ := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    have hexp :
        Complex.exp (-(((-2 * Real.pi * ξ : Real) : Complex) *
          (x : Complex) * Complex.I)) =
          Complex.exp ((↑(2 * Real.pi * (inner ℝ ξ x)) : Complex) * Complex.I) := by
      congr 1
      simp only [Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg]
      push_cast
      ring
    rw [hexp]
    ring
  rw [hscaled, hinv] at hchange'
  have hpi_ne : (2 * (Real.pi : Complex)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hchange'' :
      f x = (2 * (Real.pi : Complex))⁻¹ * ∫ t : Real, h t := by
    simpa only [Complex.ofReal_mul] using hchange'
  calc
    ∫ t : Real, h t =
        (2 * (Real.pi : Complex)) *
          ((2 * (Real.pi : Complex))⁻¹ * ∫ t : Real, h t) := by
      field_simp
    _ = (2 * (Real.pi : Complex)) * f x := by rw [← hchange'']

theorem integrable_fourierLaplace (f : TestFunction) :
    Integrable (fun t : Real => fourierLaplace f t) := by
  have hscale :
      Integrable (fun t : Real =>
        (𝓕 f : TestFunction) (-(1 / (2 * Real.pi)) * t)) := by
    apply (𝓕 f).integrable.comp_mul_left'
    exact neg_ne_zero.mpr (one_div_ne_zero (by positivity))
  have heq :
      (fun t : Real => fourierLaplace f t) =
        (fun t : Real => (𝓕 f : TestFunction)
          (-(1 / (2 * Real.pi)) * t)) := by
    funext t
    rw [fourierLaplace_eq_fourier]
    congr 1
    field_simp [Real.pi_ne_zero]
  rw [heq]
  exact hscale

theorem integrable_fourierLaplace_mul_character
    (f : TestFunction) (x : Real) :
    Integrable (fun t : Real =>
      fourierLaplace f t *
        Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) := by
  apply (integrable_fourierLaplace f).mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with t
    rw [Complex.norm_exp]
    simp

theorem integrable_fourierLaplace_neg_mul_character
    (f : TestFunction) (x : Real) :
    Integrable (fun t : Real =>
      fourierLaplace f (-t) *
        Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) := by
  have hbase := integrable_fourierLaplace_mul_character f (-x)
  have hcomp := hbase.comp_mul_left' (R := (-1 : Real)) (by norm_num)
  have heq :
      (fun t : Real =>
        fourierLaplace f (-t) *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) =
        (fun t : Real =>
          fourierLaplace f ((-1 : Real) * t) *
            Complex.exp (-((((-1 : Real) * t : Real) : Complex) *
              ((-x : Real) : Complex) * Complex.I))) := by
    funext t
    congr 2
    · ring
    · congr 1
      push_cast
      ring
  rw [heq]
  exact hcomp

theorem integral_fourierLaplace_neg_mul_character
    (f : TestFunction) (x : Real) :
    ∫ t : Real,
        fourierLaplace f (-t) *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) * f (-x) := by
  let h : Real → Complex := fun t =>
    fourierLaplace f t *
      Complex.exp (-((t : Complex) * ((-x : Real) : Complex) * Complex.I))
  have hchange := Measure.integral_comp_mul_left h (-1)
  have hchange' :
      (∫ t : Real, h (-t)) = ∫ t : Real, h t := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using hchange
  have heq :
      (fun t : Real =>
        fourierLaplace f (-t) *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))) =
        (fun t : Real => h (-t)) := by
    funext t
    dsimp [h]
    congr 2
    congr 1
    push_cast
    ring
  rw [heq, hchange']
  exact integral_fourierLaplace_mul_character f (-x)

theorem integral_arithmeticPrimePowerIntegrand_one_eq_finitePrimeTermComplex
    (F : CompactLogTest) (n : Nat) :
    ∫ t : Real, arithmeticPrimePowerIntegrand F 1 t n =
      (2 * (Real.pi : Complex) * Complex.I) *
        C1SameOwnerWeil.finitePrimeTermComplex F n := by
  by_cases hn : n = 0
  · subst n
    simp [arithmeticPrimePowerIntegrand,
      C1SameOwnerWeil.finitePrimeTermComplex]
  let fPlus : TestFunction :=
    (CompactLogTest.exponentialWeight F
      (((1 / 2 : Real) : Complex))).test
  let fMinus : TestFunction :=
    (CompactLogTest.exponentialWeight F
      (((-1 / 2 : Real) : Complex))).test
  have hweight :
      (fun t : Real =>
        symmetrizedLaplaceWeight F (verticalPoint 1 t)) =
      (fun t : Real => fourierLaplace fPlus t +
        fourierLaplace fMinus (-t)) := by
    funext t
    unfold symmetrizedLaplaceWeight
    rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 1 t]
    have hreflect :
        (1 : Complex) - verticalPoint 1 t = verticalPoint 0 (-t) := by
      simpa using (verticalPoint_reflection 1 t).symm
    rw [hreflect]
    rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 0 (-t)]
    simp only [fPlus, fMinus]
    norm_num
  have hrepr :
      (fun t : Real => arithmeticPrimePowerIntegrand F 1 t n) =
      (fun t : Real =>
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace fPlus t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace fMinus (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) := by
    funext t
    rw [arithmeticPrimePowerIntegrand_eq_exp_of_ne_zero F hn]
    rw [congrFun hweight t]
    norm_num [one_mul]
    ring
  have hplusInt :=
    integrable_fourierLaplace_mul_character fPlus (Real.log n)
  have hminusInt :=
    integrable_fourierLaplace_neg_mul_character fMinus (Real.log n)
  have hsumInt :
      Integrable (fun t : Real =>
        fourierLaplace fPlus t *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I)) +
          fourierLaplace fMinus (-t) *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I))) :=
    hplusInt.add hminusInt
  have hwholeInt :
      Integrable (fun t : Real =>
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace fPlus t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace fMinus (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) := by
    exact (hsumInt.const_mul
      ((ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp (-((1 : Complex) * (Real.log n : Complex))))).mul_const
          Complex.I
  rw [hrepr]
  calc
    (∫ t : Real,
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace fPlus t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace fMinus (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) =
        ((ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (∫ t : Real,
            fourierLaplace fPlus t *
                Complex.exp (-((t : Complex) *
                  (Real.log n : Complex) * Complex.I)) +
              fourierLaplace fMinus (-t) *
                Complex.exp (-((t : Complex) *
                  (Real.log n : Complex) * Complex.I)))) * Complex.I := by
      rw [integral_mul_const, integral_const_mul]
    _ = ((ArithmeticFunction.vonMangoldt n : Complex) *
          Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
        ((2 * (Real.pi : Complex)) * fPlus (Real.log n) +
          (2 * (Real.pi : Complex)) * fMinus (-Real.log n))) * Complex.I := by
      rw [integral_add hplusInt hminusInt,
        integral_fourierLaplace_mul_character,
        integral_fourierLaplace_neg_mul_character]
    _ = (2 * (Real.pi : Complex) * Complex.I) *
        C1SameOwnerWeil.finitePrimeTermComplex F n := by
      have hnpos : 0 < (n : Real) := by
        exact_mod_cast Nat.zero_lt_of_ne_zero hn
      have hreal :
          Real.exp (-(Real.log (n : Real)) / 2) =
            1 / Real.sqrt (n : Real) := by
        calc
          Real.exp (-(Real.log (n : Real)) / 2) =
              Real.exp (-Real.log (Real.sqrt (n : Real))) := by
                congr 1
                rw [Real.log_sqrt hnpos.le]
                ring
          _ = (Real.exp (Real.log (Real.sqrt (n : Real))))⁻¹ := by
                rw [Real.exp_neg]
          _ = (Real.sqrt (n : Real))⁻¹ := by
                rw [Real.exp_log (Real.sqrt_pos.2 hnpos)]
          _ = 1 / Real.sqrt (n : Real) := by rw [one_div]
      have hhalfPlus :
          Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
              Complex.exp (((1 / 2 : Real) : Complex) *
                (Real.log n : Complex)) =
            ((1 / Real.sqrt (n : Real) : Real) : Complex) := by
        rw [← Complex.exp_add]
        have harg :
            -((1 : Complex) * (Real.log n : Complex)) +
                (((1 / 2 : Real) : Complex) * (Real.log n : Complex)) =
              ((-(Real.log (n : Real)) / 2 : Real) : Complex) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_exp, hreal]
      have hhalfMinus :
          Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
              Complex.exp (((-1 / 2 : Real) : Complex) *
                ((-Real.log n : Real) : Complex)) =
            ((1 / Real.sqrt (n : Real) : Real) : Complex) := by
        rw [← Complex.exp_add]
        have harg :
            -((1 : Complex) * (Real.log n : Complex)) +
                (((-1 / 2 : Real) : Complex) *
                  ((-Real.log n : Real) : Complex)) =
              ((-(Real.log (n : Real)) / 2 : Real) : Complex) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_exp, hreal]
      have hfPlus :
          fPlus (Real.log n) =
            Complex.exp (((1 / 2 : Real) : Complex) *
              (Real.log n : Complex)) * F.test (Real.log n) := by
        simp [fPlus, CompactLogTest.exponentialWeight_apply]
      have hfMinus :
          fMinus (-Real.log n) =
            Complex.exp (((-1 / 2 : Real) : Complex) *
              ((-Real.log n : Real) : Complex)) *
                F.test (-Real.log n) := by
        simp [fMinus, CompactLogTest.exponentialWeight_apply]
      rw [hfPlus, hfMinus]
      have hsum :
          Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
              ((2 * (Real.pi : Complex)) *
                  (Complex.exp (((1 / 2 : Real) : Complex) *
                    (Real.log n : Complex)) * F.test (Real.log n)) +
                (2 * (Real.pi : Complex)) *
                  (Complex.exp (((-1 / 2 : Real) : Complex) *
                    ((-Real.log n : Real) : Complex)) *
                    F.test (-Real.log n))) =
            (2 * (Real.pi : Complex)) *
              (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                (F.test (Real.log n) + F.test (-Real.log n))) := by
        calc
          _ = (2 * (Real.pi : Complex)) *
                ((Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
                    Complex.exp (((1 / 2 : Real) : Complex) *
                      (Real.log n : Complex))) * F.test (Real.log n) +
                  (Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
                    Complex.exp (((-1 / 2 : Real) : Complex) *
                      ((-Real.log n : Real) : Complex))) *
                    F.test (-Real.log n)) := by ring
          _ = (2 * (Real.pi : Complex)) *
                (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  F.test (Real.log n) +
                ((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  F.test (-Real.log n)) := by
                rw [hhalfPlus, hhalfMinus]
          _ = (2 * (Real.pi : Complex)) *
                (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  (F.test (Real.log n) + F.test (-Real.log n))) := by ring
      calc
        _ = (ArithmeticFunction.vonMangoldt n : Complex) *
              (Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
                ((2 * (Real.pi : Complex)) *
                    (Complex.exp (((1 / 2 : Real) : Complex) *
                      (Real.log n : Complex)) * F.test (Real.log n)) +
                  (2 * (Real.pi : Complex)) *
                    (Complex.exp (((-1 / 2 : Real) : Complex) *
                      ((-Real.log n : Real) : Complex)) *
                      F.test (-Real.log n)))) * Complex.I := by ring
        _ = (ArithmeticFunction.vonMangoldt n : Complex) *
              ((2 * (Real.pi : Complex)) *
                (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  (F.test (Real.log n) + F.test (-Real.log n)))) *
              Complex.I := by rw [hsum]
        _ = (2 * (Real.pi : Complex) * Complex.I) *
              C1SameOwnerWeil.finitePrimeTermComplex F n := by
          simp only [C1SameOwnerWeil.finitePrimeTermComplex]
          ring

end
end C1XiArithmeticPrimePowerReadback
end Source
end ConnesWeilRH
