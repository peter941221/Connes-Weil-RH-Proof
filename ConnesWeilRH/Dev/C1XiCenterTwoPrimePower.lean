import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerAssembly
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# C1XiCenterTwoPrimePower - full-line prime-power readback at `Re(s)=2`

On the fixed line `Re(s)=2`, the von Mangoldt series is absolutely
convergent.  The two halves of the symmetrized compact-log weight have
exponential twists `3/2` and `-3/2`; Fourier inversion cancels the factor
`n^(-2)` against `n^(3/2)` and leaves the canonical `n^(-1/2)` coefficient.

This module performs the full-line sum/integral exchange.  It does not use a
boundary value at `Re(s)=1`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoPrimePower

open MeasureTheory
open Complex
open Filter
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1XiArithmeticIntervalReadback
open C1XiArithmeticPrimePowerAssembly
open C1XiArithmeticPrimePowerReadback
open C1XiArithmeticRightLine
open C1XiVerticalFunctional
open scoped BigOperators LSeries.notation Topology

noncomputable section

private def centerTwoPlusProfile (F : CompactLogTest) : TestFunction :=
  (CompactLogTest.exponentialWeight F
    (((3 / 2 : Real) : Complex))).test

private def centerTwoMinusProfile (F : CompactLogTest) : TestFunction :=
  (CompactLogTest.exponentialWeight F
    (((-3 / 2 : Real) : Complex))).test

/-- On `Re(s)=2`, the symmetrized weight is the sum of two Fourier profiles
with twists `3/2` and `-3/2`. -/
theorem symmetrizedLaplaceWeight_centerTwo_eq
    (F : CompactLogTest) (t : Real) :
    symmetrizedLaplaceWeight F (verticalPoint 2 t) =
      fourierLaplace (centerTwoPlusProfile F) t +
        fourierLaplace (centerTwoMinusProfile F) (-t) := by
  unfold symmetrizedLaplaceWeight
  rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 2 t]
  have hreflect :
      (1 : Complex) - verticalPoint 2 t = verticalPoint (-1) (-t) := by
    apply Complex.ext
    · simp [verticalPoint]
      ring
    · simp [verticalPoint]
  rw [hreflect]
  rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F (-1) (-t)]
  simp only [centerTwoPlusProfile, centerTwoMinusProfile]
  norm_num

/-- The center-`2` symmetrized weight is integrable on the full real line. -/
theorem integrable_symmetrizedLaplaceWeight_centerTwo
    (F : CompactLogTest) :
    Integrable (fun t : Real =>
      symmetrizedLaplaceWeight F (verticalPoint 2 t)) := by
  have hplus := integrable_fourierLaplace (centerTwoPlusProfile F)
  have hminus := (integrable_fourierLaplace
    (centerTwoMinusProfile F)).comp_mul_left'
      (R := (-1 : Real)) (by norm_num)
  have hsum : Integrable (fun t : Real =>
      fourierLaplace (centerTwoPlusProfile F) t +
        fourierLaplace (centerTwoMinusProfile F) (-t)) := by
    simpa only [neg_one_mul] using hplus.add hminus
  simpa only [symmetrizedLaplaceWeight_centerTwo_eq] using hsum

private theorem centerTwo_primePower_repr
    (F : CompactLogTest) {n : Nat} (hn : n ≠ 0) :
    (fun t : Real => arithmeticPrimePowerIntegrand F 2 t n) =
      (fun t : Real =>
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace (centerTwoPlusProfile F) t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace (centerTwoMinusProfile F) (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) := by
  funext t
  rw [arithmeticPrimePowerIntegrand_eq_exp_of_ne_zero F hn]
  rw [symmetrizedLaplaceWeight_centerTwo_eq]
  norm_num
  ring

/-- Every single center-`2` prime-power term is integrable on the full line. -/
theorem integrable_arithmeticPrimePowerIntegrand_centerTwo
    (F : CompactLogTest) (n : Nat) :
    Integrable (fun t : Real =>
      arithmeticPrimePowerIntegrand F 2 t n) := by
  by_cases hn : n = 0
  · subst n
    simp [arithmeticPrimePowerIntegrand]
  have hplus := integrable_fourierLaplace_mul_character
    (centerTwoPlusProfile F) (Real.log n)
  have hminus := integrable_fourierLaplace_neg_mul_character
    (centerTwoMinusProfile F) (Real.log n)
  have hsum : Integrable (fun t : Real =>
      fourierLaplace (centerTwoPlusProfile F) t *
          Complex.exp (-((t : Complex) *
            (Real.log n : Complex) * Complex.I)) +
        fourierLaplace (centerTwoMinusProfile F) (-t) *
          Complex.exp (-((t : Complex) *
            (Real.log n : Complex) * Complex.I))) :=
    hplus.add hminus
  have hwhole : Integrable (fun t : Real =>
      (ArithmeticFunction.vonMangoldt n : Complex) *
          Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
        (fourierLaplace (centerTwoPlusProfile F) t *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I)) +
          fourierLaplace (centerTwoMinusProfile F) (-t) *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I))) * Complex.I) := by
    exact (hsum.const_mul
      ((ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp (-((2 : Complex) *
          (Real.log n : Complex))))).mul_const Complex.I
  rw [centerTwo_primePower_repr F hn]
  exact hwhole

/-- Fourier inversion on the center-`2` line reads one von Mangoldt term
back to the same compact-log prime-power owner used by `C1SameOwnerWeil`. -/
theorem integral_arithmeticPrimePowerIntegrand_centerTwo_eq
    (F : CompactLogTest) (n : Nat) :
    (∫ t : Real, arithmeticPrimePowerIntegrand F 2 t n) =
      (2 * (Real.pi : Complex) * Complex.I) *
        finitePrimeTermComplex F n := by
  by_cases hn : n = 0
  · subst n
    simp [arithmeticPrimePowerIntegrand, finitePrimeTermComplex]
  have hplus := integrable_fourierLaplace_mul_character
    (centerTwoPlusProfile F) (Real.log n)
  have hminus := integrable_fourierLaplace_neg_mul_character
    (centerTwoMinusProfile F) (Real.log n)
  have hsum : Integrable (fun t : Real =>
      fourierLaplace (centerTwoPlusProfile F) t *
          Complex.exp (-((t : Complex) *
            (Real.log n : Complex) * Complex.I)) +
        fourierLaplace (centerTwoMinusProfile F) (-t) *
          Complex.exp (-((t : Complex) *
            (Real.log n : Complex) * Complex.I))) :=
    hplus.add hminus
  rw [centerTwo_primePower_repr F hn]
  calc
    (∫ t : Real,
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace (centerTwoPlusProfile F) t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace (centerTwoMinusProfile F) (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) =
        ((ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
          (∫ t : Real,
            fourierLaplace (centerTwoPlusProfile F) t *
                Complex.exp (-((t : Complex) *
                  (Real.log n : Complex) * Complex.I)) +
              fourierLaplace (centerTwoMinusProfile F) (-t) *
                Complex.exp (-((t : Complex) *
                  (Real.log n : Complex) * Complex.I)))) * Complex.I := by
      rw [integral_mul_const, integral_const_mul]
    _ = ((ArithmeticFunction.vonMangoldt n : Complex) *
          Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
        ((2 * (Real.pi : Complex)) *
            centerTwoPlusProfile F (Real.log n) +
          (2 * (Real.pi : Complex)) *
            centerTwoMinusProfile F (-Real.log n))) * Complex.I := by
      rw [integral_add hplus hminus,
        integral_fourierLaplace_mul_character,
        integral_fourierLaplace_neg_mul_character]
    _ = (2 * (Real.pi : Complex) * Complex.I) *
        finitePrimeTermComplex F n := by
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
          Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
              Complex.exp (((3 / 2 : Real) : Complex) *
                (Real.log n : Complex)) =
            ((1 / Real.sqrt (n : Real) : Real) : Complex) := by
        rw [← Complex.exp_add]
        have harg :
            -((2 : Complex) * (Real.log n : Complex)) +
                (((3 / 2 : Real) : Complex) *
                  (Real.log n : Complex)) =
              ((-(Real.log (n : Real)) / 2 : Real) : Complex) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_exp, hreal]
      have hhalfMinus :
          Complex.exp (-((2 : Complex) * (Real.log n : Complex))) *
              Complex.exp (((-3 / 2 : Real) : Complex) *
                ((-Real.log n : Real) : Complex)) =
            ((1 / Real.sqrt (n : Real) : Real) : Complex) := by
        rw [← Complex.exp_add]
        have harg :
            -((2 : Complex) * (Real.log n : Complex)) +
                (((-3 / 2 : Real) : Complex) *
                  ((-Real.log n : Real) : Complex)) =
              ((-(Real.log (n : Real)) / 2 : Real) : Complex) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_exp, hreal]
      have hfPlus :
          centerTwoPlusProfile F (Real.log n) =
            Complex.exp (((3 / 2 : Real) : Complex) *
              (Real.log n : Complex)) * F.test (Real.log n) := by
        simp [centerTwoPlusProfile,
          CompactLogTest.exponentialWeight_apply]
      have hfMinus :
          centerTwoMinusProfile F (-Real.log n) =
            Complex.exp (((-3 / 2 : Real) : Complex) *
              ((-Real.log n : Real) : Complex)) *
                F.test (-Real.log n) := by
        simp [centerTwoMinusProfile,
          CompactLogTest.exponentialWeight_apply]
      rw [hfPlus, hfMinus]
      rw [finitePrimeTermComplex]
      calc
        _ = (ArithmeticFunction.vonMangoldt n : Complex) *
              (2 * (Real.pi : Complex)) *
              ((Complex.exp (-((2 : Complex) *
                    (Real.log n : Complex))) *
                  Complex.exp (((3 / 2 : Real) : Complex) *
                    (Real.log n : Complex))) * F.test (Real.log n) +
                (Complex.exp (-((2 : Complex) *
                    (Real.log n : Complex))) *
                  Complex.exp (((-3 / 2 : Real) : Complex) *
                    ((-Real.log n : Real) : Complex))) *
                      F.test (-Real.log n)) * Complex.I := by ring
        _ = (ArithmeticFunction.vonMangoldt n : Complex) *
              (2 * (Real.pi : Complex)) *
              (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  F.test (Real.log n) +
                ((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  F.test (-Real.log n)) * Complex.I := by
            rw [hhalfPlus, hhalfMinus]
        _ = (2 * (Real.pi : Complex) * Complex.I) *
              ((ArithmeticFunction.vonMangoldt n : Complex) *
                (((1 / Real.sqrt (n : Real) : Real) : Complex) *
                  (F.test (Real.log n) + F.test (-Real.log n)))) := by ring

private theorem norm_lSeriesTerm_centerTwo_vertical
    {f : Nat → Complex} (t : Real) (n : Nat) :
    norm (LSeries.term f (verticalPoint 2 t) n) =
      norm (LSeries.term f (2 : Complex) n) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.norm_term_eq, verticalPoint, hn, ↓reduceIte]
    congr 2
    simp

private theorem hasSum_centerTwo_primePower
    (F : CompactLogTest) (t : Real) :
    HasSum (fun n : Nat => arithmeticPrimePowerIntegrand F 2 t n)
      (arithmeticLSeriesIntegrand F 2 t) := by
  have hseries : HasSum
      (fun n : Nat => LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (verticalPoint 2 t) n)
      (vonMangoldtLSeries (verticalPoint 2 t)) := by
    unfold vonMangoldtLSeries
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      simp [verticalPoint])).hasSum
  simpa only [arithmeticPrimePowerIntegrand,
    arithmeticLSeriesIntegrand] using
      (hseries.mul_right
        (symmetrizedLaplaceWeight F (verticalPoint 2 t))).mul_right
          Complex.I

private theorem integral_norm_centerTwo_primePower_eq
    (F : CompactLogTest) (n : Nat) :
    (∫ t : Real, norm (arithmeticPrimePowerIntegrand F 2 t n)) =
      norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (2 : Complex) n) *
        (∫ t : Real,
          norm (symmetrizedLaplaceWeight F (verticalPoint 2 t))) := by
  have heq : (fun t : Real =>
      norm (arithmeticPrimePowerIntegrand F 2 t n)) =
    (fun t : Real =>
      norm (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (2 : Complex) n) *
      norm (symmetrizedLaplaceWeight F (verticalPoint 2 t))) := by
    funext t
    unfold arithmeticPrimePowerIntegrand
    change
      ‖LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (verticalPoint 2 t) n *
        symmetrizedLaplaceWeight F (verticalPoint 2 t) * Complex.I‖ = _
    rw [norm_mul, norm_mul, norm_I,
      mul_one, norm_lSeriesTerm_centerTwo_vertical]
  rw [heq, integral_const_mul]

private theorem summable_integral_norm_centerTwo_primePower
    (F : CompactLogTest) :
    Summable (fun n : Nat =>
      ∫ t : Real, norm (arithmeticPrimePowerIntegrand F 2 t n)) := by
  have hseries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (2 : Complex)) (by norm_num)
  have hnorm := hseries.norm.mul_right
    (∫ t : Real,
      norm (symmetrizedLaplaceWeight F (verticalPoint 2 t)))
  simpa only [integral_norm_centerTwo_primePower_eq, mul_comm] using hnorm

/-- The complete center-`2` von Mangoldt integrand is integrable on the full
line. -/
theorem integrable_arithmeticLSeriesIntegrand_centerTwo
    (F : CompactLogTest) :
    Integrable (fun t : Real => arithmeticLSeriesIntegrand F 2 t) := by
  let g : Nat → Real → Complex := fun n t =>
    arithmeticPrimePowerIntegrand F 2 t n
  have hg : ∀ n, Integrable (g n) := fun n =>
    integrable_arithmeticPrimePowerIntegrand_centerTwo F n
  have hsumNorm : Summable (fun n : Nat =>
      ∫ t : Real, norm (g n t)) :=
    summable_integral_norm_centerTwo_primePower F
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
          tsum (fun n : Nat =>
            ∫⁻ t : Real, enorm (g n t)) := by
      calc
        _ <= ∫⁻ t : Real, ∑' n : Nat, enorm (g n t) := by
          apply lintegral_mono_ae
          filter_upwards with t
          exact enorm_tsum_le_tsum_enorm
        _ = tsum (fun n : Nat =>
              ∫⁻ t : Real, enorm (g n t)) := by
          rw [lintegral_tsum hmeasNorm]
    have hlinFinite :
        tsum (fun n : Nat =>
          ∫⁻ t : Real, enorm (g n t)) ≠ ⊤ := by
      have hterm (n : Nat) :
          (∫⁻ t : Real, enorm (g n t)) =
            ENNReal.ofReal (∫ t : Real, norm (g n t)) := by
        exact (ofReal_integral_norm_eq_lintegral_enorm (hg n)).symm
      rw [tsum_congr hterm]
      exact hsumNorm.tsum_ofReal_ne_top
    exact hlin.trans_lt (lt_top_iff_ne_top.mpr hlinFinite)
  have htsum : Integrable (fun t : Real => tsum fun n : Nat => g n t) :=
    ⟨hsumAE, hfinite⟩
  apply htsum.congr
  filter_upwards with t
  exact (hasSum_centerTwo_primePower F t).tsum_eq

/-- The full-line center-`2` von Mangoldt integral is the exact finite
prime-power owner after Fourier inversion. -/
theorem integral_arithmeticLSeriesIntegrand_centerTwo_eq
    (F : CompactLogTest) :
    (∫ t : Real, arithmeticLSeriesIntegrand F 2 t) =
      (2 * (Real.pi : Complex) * Complex.I) *
        (∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n) := by
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun n : Nat => integrable_arithmeticPrimePowerIntegrand_centerTwo F n)
    (summable_integral_norm_centerTwo_primePower F)
  have hsum' : HasSum
      (fun n : Nat =>
        (2 * (Real.pi : Complex) * Complex.I) *
          finitePrimeTermComplex F n)
      (∫ t : Real,
        ∑' n : Nat, arithmeticPrimePowerIntegrand F 2 t n) := by
    simpa only [integral_arithmeticPrimePowerIntegrand_centerTwo_eq] using hsum
  have htarget :
      tsum (fun n : Nat => finitePrimeTermComplex F n) =
        ∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n := by
    exact tsum_eq_sum (s := globalPrimeIndexSet F)
      (fun n hn => finitePrimeTermComplex_eq_zero_of_not_mem_globalPrimeIndexSet
        F hn)
  have hintegral :
      (∫ t : Real,
        ∑' n : Nat, arithmeticPrimePowerIntegrand F 2 t n) =
      ∫ t : Real, arithmeticLSeriesIntegrand F 2 t := by
    apply integral_congr_ae
    filter_upwards with t
    exact (hasSum_centerTwo_primePower F t).tsum_eq
  rw [hintegral] at hsum'
  rw [← hsum'.tsum_eq, tsum_mul_left, htarget]

/-- Normalization and real readback give the same `finitePrimeSum` owner. -/
theorem normalized_integral_arithmeticLSeries_centerTwo_re_eq
    (F : CompactLogTest) :
    (((2 * (Real.pi : Complex) * Complex.I)⁻¹) *
      (∫ t : Real, arithmeticLSeriesIntegrand F 2 t)).re =
        finitePrimeSum F := by
  have hK : (2 * (Real.pi : Complex) * Complex.I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [integral_arithmeticLSeriesIntegrand_centerTwo_eq]
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  exact re_sum_globalPrimeTermComplex_eq_finitePrimeSum F

/-- Symmetric selected-height intervals converge to the full center-`2`
von Mangoldt integral. -/
theorem tendsto_selected_intervalIntegral_arithmeticLSeries_centerTwo
    (F : CompactLogTest) {height : Nat → Real}
    (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun n : Nat => ∫ t : Real in (-height n)..height n,
        arithmeticLSeriesIntegrand F 2 t)
      atTop
      (nhds (∫ t : Real, arithmeticLSeriesIntegrand F 2 t)) := by
  have hneg : Tendsto (fun n : Nat => -height n) atTop atBot :=
    by simpa only [mul_neg, mul_one] using
      hheight.atTop_mul_const_of_neg' (by norm_num : (-1 : Real) < 0)
  exact intervalIntegral_tendsto_integral
    (integrable_arithmeticLSeriesIntegrand_centerTwo F) hneg hheight

end
end C1XiCenterTwoPrimePower
end Source
end ConnesWeilRH
