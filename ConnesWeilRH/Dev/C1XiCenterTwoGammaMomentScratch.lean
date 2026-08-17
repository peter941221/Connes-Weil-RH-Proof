import ConnesWeilRH.Dev.C1XiCenterTwoGamma

open MeasureTheory Set Complex Filter
open ConnesWeilRH Source
open ConnesWeilRH.Source.CC20YoshidaConvolution
open ConnesWeilRH.Source.C1XiCenterTwoGamma
open ConnesWeilRH.Source.C1XiVerticalFunctional
open scoped Topology

abbrev CLogTest :=
  ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest

#check Integrable.comp_mul_left'
#check Integrable.const_mul
#check SchwartzMap.integrable_pow_mul
#check C1XiArithmeticPrimePowerReadback.fourierLaplace_eq_fourier
#check C1XiCenterTwoPrimePower.symmetrizedLaplaceWeight_centerTwo_eq
#check norm_mul
#check Real.norm_eq_abs

open scoped FourierTransform

lemma moment_fourier (f : TestFunction) :
    Integrable (fun t : Real => ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t‖) := by
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

#check Integrable.mono'
#check integrable_norm_iff
#check Integrable.norm
#check AEStronglyMeasurable.comp_quasiMeasurePreserving
#check AEStronglyMeasurable.comp_measurePreserving
#check AEStronglyMeasurable.mul
#check Continuous.aestronglyMeasurable

lemma moment_fourier_sum (f g : TestFunction) :
    Integrable (fun t : Real => ‖t‖ *
      ‖C1XiArithmeticPrimePowerReadback.fourierLaplace f t +
        C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖) := by
  have hplus := moment_fourier f
  have hminus := (moment_fourier g).comp_mul_left'
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
              ‖t‖ * ‖C1XiArithmeticPrimePowerReadback.fourierLaplace g (-t)‖ := by ring)
  have hnorm := hvec.norm
  apply hnorm.congr
  filter_upwards with t
  rw [norm_mul, norm_real]

private theorem moment_symmetrizedLaplaceWeight_centerTwo (F : CLogTest) :
    Integrable (fun t : Real => ‖t‖ *
      ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
          (C1XiVerticalFunctional.verticalPoint 2 t)‖) := by
  let fPlus : TestFunction :=
    (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
      (((3 / 2 : Real) : Complex))).test
  let fMinus : TestFunction :=
    (CC20YoshidaConvolution.CompactLogTest.exponentialWeight F
      (((-3 / 2 : Real) : Complex))).test
  have hweight : (fun t : Real =>
      C1XiVerticalFunctional.symmetrizedLaplaceWeight F
        (C1XiVerticalFunctional.verticalPoint 2 t)) =
      (fun t : Real =>
        C1XiArithmeticPrimePowerReadback.fourierLaplace fPlus t +
          C1XiArithmeticPrimePowerReadback.fourierLaplace fMinus (-t)) := by
    funext t
    unfold C1XiVerticalFunctional.symmetrizedLaplaceWeight
    rw [C1XiArithmeticPrimePowerReadback.centeredLaplaceWeight_vertical_eq_fourierLaplace
      F 2 t]
    have hreflect : (1 : Complex) - C1XiVerticalFunctional.verticalPoint 2 t =
        C1XiVerticalFunctional.verticalPoint (-1) (-t) := by
      apply Complex.ext <;> simp [C1XiVerticalFunctional.verticalPoint] <;> ring
    rw [hreflect,
      C1XiArithmeticPrimePowerReadback.centeredLaplaceWeight_vertical_eq_fourierLaplace
        F (-1) (-t)]
    norm_num [fPlus, fMinus]
  have hmoment := moment_fourier_sum fPlus fMinus
  apply hmoment.congr
  filter_upwards with t
  rw [congrFun hweight t]

private theorem reciprocal_difference_norm_bound
    {n : Nat} (hn : 0 < n) (t : Real) :
    ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (C1XiVerticalFunctional.verticalPoint 2 t / 2))⁻¹‖ ≤
      (1 + ‖t‖) * (((n : Real) ^ 2)⁻¹) := by
  let a : Complex := (n : Complex) + (1 / 2 : Complex)
  let b : Complex := (n : Complex) +
    (C1XiVerticalFunctional.verticalPoint 2 t / 2)
  have ha : a ≠ 0 := by
    dsimp [a]
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, Complex.natCast_re, ofReal_re] at hre
    norm_num at hre
    exact (by positivity : 0 < (n : Real) + 1 / 2).ne' hre
  have hb : b ≠ 0 := by
    dsimp [b]
    intro h
    have hre := congrArg Complex.re h
    simp [C1XiVerticalFunctional.verticalPoint] at hre
    exact (by positivity : 0 < (n : Real) + 1).ne' hre
  have hdiff : b - a =
      ((1 / 2 : Real) : Complex) + ((t / 2 : Real) : Complex) * Complex.I := by
    dsimp [a, b]
    simp [C1XiVerticalFunctional.verticalPoint]
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
      simp [C1XiVerticalFunctional.verticalPoint]
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

private theorem integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo
    (F : CLogTest) :
    Integrable (fun t : Real =>
      (1 + ‖t‖) *
        ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
          (C1XiVerticalFunctional.verticalPoint 2 t)‖) := by
  have hweight :=
    (C1XiCenterTwoPrimePower.integrable_symmetrizedLaplaceWeight_centerTwo F).norm
  have hmoment' := moment_symmetrizedLaplaceWeight_centerTwo F
  have hsum := hweight.add hmoment'
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

private theorem integrable_norm_gammaRReciprocalTerm_bound
    (F : CLogTest) {n : Nat} (hn : 0 < n) :
    Integrable (fun t : Real =>
      ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖) := by
  have hterm :=
    ConnesWeilRH.Source.C1XiCenterTwoGamma.integrable_gammaRReciprocalTerm F n
  have hmoment := integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo F
  let c : Real := (((n : Real) ^ 2)⁻¹)
  have hmajorant : Integrable (fun t : Real =>
      c * ((1 + ‖t‖) *
        ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
          (C1XiVerticalFunctional.verticalPoint 2 t)‖)) := by
    simpa only [c] using hmoment.const_mul c
  have hcomplex : Integrable (fun t : Real =>
      ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t) := by
    apply hmajorant.mono' hterm.aestronglyMeasurable
    filter_upwards with t
    calc
      ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖ =
          ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) +
              (C1XiVerticalFunctional.verticalPoint 2 t / 2))⁻¹‖ *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖ := by
        simp only [ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm,
          norm_mul, norm_I,
          mul_one]
      _ ≤ ((1 + ‖t‖) * c) *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖ := by
        gcongr
        exact reciprocal_difference_norm_bound hn t
      _ = c * ((1 + ‖t‖) *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖) := by
        ring
  exact hcomplex.norm

private theorem integral_norm_gammaRReciprocalTerm_le
    (F : CLogTest) {n : Nat} (hn : 0 < n) :
    (∫ t : Real,
      ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖) ≤
      (((n : Real) ^ 2)⁻¹) *
        (∫ t : Real,
          (1 + ‖t‖) *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖) := by
  have hterm := integrable_norm_gammaRReciprocalTerm_bound F hn
  have hmoment := integrable_one_add_norm_symmetrizedLaplaceWeight_centerTwo F
  let c : Real := (((n : Real) ^ 2)⁻¹)
  have hmajorant : Integrable (fun t : Real =>
      c * ((1 + ‖t‖) *
        ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
          (C1XiVerticalFunctional.verticalPoint 2 t)‖)) := by
    simpa only [c] using hmoment.const_mul c
  have hle := integral_mono_ae hterm hmajorant (by
    filter_upwards with t
    calc
      ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖ =
          ‖((n : Complex) + (1 / 2 : Complex))⁻¹ -
            ((n : Complex) +
              (C1XiVerticalFunctional.verticalPoint 2 t / 2))⁻¹‖ *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖ := by
        simp only [ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm,
          norm_mul, norm_I,
          mul_one]
      _ ≤ ((1 + ‖t‖) * c) *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖ := by
        gcongr
        exact reciprocal_difference_norm_bound hn t
      _ = c * ((1 + ‖t‖) *
            ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
              (C1XiVerticalFunctional.verticalPoint 2 t)‖) := by
        ring)
  rw [integral_const_mul] at hle
  simpa only [c, mul_comm] using hle

theorem summable_integral_norm_gammaRReciprocalTerm (F : CLogTest) :
    Summable (fun n : Nat =>
      ∫ t : Real,
        ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖) := by
  let C : Real :=
    ∫ t : Real,
      (1 + ‖t‖) *
        ‖C1XiVerticalFunctional.symmetrizedLaplaceWeight F
          (C1XiVerticalFunctional.verticalPoint 2 t)‖
  have hbase : Summable (fun n : Nat => C * (((n : Real) ^ 2)⁻¹)) := by
    have hpow : Summable (fun n : Nat => (((n : Real) ^ 2)⁻¹)) := by
      exact (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    exact hpow.mul_left C
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hle := integral_norm_gammaRReciprocalTerm_le F hnpos
  have hnonneg : 0 ≤
      ∫ t : Real,
        ‖ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [C, mul_comm] using hle

theorem integral_tsum_gammaRReciprocalTerm (F : CLogTest) :
    (∫ t : Real,
        ∑' n : Nat,
          ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t) =
      ∑' n : Nat, ∫ t : Real,
        ConnesWeilRH.Source.C1XiCenterTwoGamma.gammaRReciprocalTerm F n t := by
  symm
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n =>
      ConnesWeilRH.Source.C1XiCenterTwoGamma.integrable_gammaRReciprocalTerm F n)
    (summable_integral_norm_gammaRReciprocalTerm F)
