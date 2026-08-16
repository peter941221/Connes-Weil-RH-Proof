import ConnesWeilRH.Dev.C1XiCenterTwoGamma
import ConnesWeilRH.Dev.C1XiCenterTwoPrimePower
import ConnesWeilRH.Dev.C1XiCenterTwoPole
import ConnesWeilRH.Dev.C1XiCenterTwoSpectralLimit

/-!
# C1XiCenterTwoArithmeticAssembly - conditional Gate 2 consumer

The center-`2` contour has four separately owned pieces: the pole, the
`Gamma_R` term, the visible prime-power series, and the zero spectrum.  The
pole, prime, and spectral limits are proved in their owning modules.  This
file only assembles those limits with the explicit `Gamma_R` readback
contract; it does not manufacture the missing Gauss integral or its Fubini
evaluation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoArithmeticAssembly

open MeasureTheory
open Filter
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralSummability
open C1SpectralWeil
open C1XiArithmeticIntervalReadback
open C1XiCenterTwoGamma
open C1XiCenterTwoHorizontal
open C1XiCenterTwoHorizontalDecay
open C1XiCenterTwoPole
open C1XiCenterTwoPrimePower
open C1XiCenterTwoRectangleAssembly
open C1XiCenterTwoSpectralLimit
open C1XiVerticalFunctional
open scoped Interval Topology

noncomputable section

/-- The same-owner arithmetic/spectral identity follows once the center-`2`
`Gamma_R` full-line readback is supplied.  The theorem is conditional because
the half-anchor Gauss representation and its Fubini evaluation remain an
explicit analytic input in `CenterTwoGammaReadbackContract`. -/
theorem centerTwo_arithmetic_eq_spectral_of_gamma_contract
    (F : CompactLogTest)
    (hgamma : CenterTwoGammaReadbackContract F) :
    C1SameOwnerWeil.psi F = spectralWeilValue F := by
  let K : Complex := 2 * (Real.pi : Complex) * Complex.I
  have hK : K ≠ 0 := by
    dsimp only [K]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hheight : Tendsto selectedDyadicCenterTwoHeight atTop atTop :=
    tendsto_selectedDyadicCenterTwoHeight_atTop
  have hneg : Tendsto
      (fun n : Nat => -selectedDyadicCenterTwoHeight n) atTop atBot := by
    simpa only [mul_neg, mul_one] using
      hheight.atTop_mul_const_of_neg' (by norm_num : (-1 : Real) < 0)

  have hpoleIntervals : Tendsto
      (fun n : Nat =>
        ∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
          selectedDyadicCenterTwoHeight n,
          elementaryPoleIntegrand F 2 t)
      atTop (nhds (∫ t : Real, elementaryPoleIntegrand F 2 t)) :=
    tendsto_selected_intervalIntegral_elementaryPole_centerTwo F hheight

  have hgammaIntervals : Tendsto
      (fun n : Nat =>
        ∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
          selectedDyadicCenterTwoHeight n,
          gammaRIntegrand F 2 t)
      atTop (nhds (∫ t : Real, gammaRIntegrand F 2 t)) :=
    intervalIntegral_tendsto_integral hgamma.integrable hneg hheight

  have hprimeIntervals : Tendsto
      (fun n : Nat =>
        ∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
          selectedDyadicCenterTwoHeight n,
          arithmeticLSeriesIntegrand F 2 t)
      atTop (nhds (∫ t : Real, arithmeticLSeriesIntegrand F 2 t)) :=
    tendsto_selected_intervalIntegral_arithmeticLSeries_centerTwo F hheight

  have hpoleNorm : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            elementaryPoleIntegrand F 2 t)).re)
      atTop (nhds (-poleTerm F)) := by
    have hmul : Tendsto
        (fun n : Nat => K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            elementaryPoleIntegrand F 2 t))
        atTop (nhds (K⁻¹ * (∫ t : Real, elementaryPoleIntegrand F 2 t))) :=
      (tendsto_const_nhds : Tendsto (fun _ : Nat => K⁻¹) atTop (nhds K⁻¹)).mul
        hpoleIntervals
    have hre := (Complex.continuous_re.tendsto _).comp hmul
    have hread := normalized_integral_elementaryPole_centerTwo_re_eq F
    simpa only [Function.comp_apply, K, hread] using hre

  have hgammaNorm : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            gammaRIntegrand F 2 t)).re)
      atTop (nhds (archimedeanTerm F)) := by
    have hmul : Tendsto
        (fun n : Nat => K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            gammaRIntegrand F 2 t))
        atTop (nhds (K⁻¹ * (∫ t : Real, gammaRIntegrand F 2 t))) :=
      (tendsto_const_nhds : Tendsto (fun _ : Nat => K⁻¹) atTop (nhds K⁻¹)).mul
        hgammaIntervals
    have hre := (Complex.continuous_re.tendsto _).comp hmul
    have hread := hgamma.normalized_readback
    simpa only [Function.comp_apply, K, hread] using hre

  have hprimeNorm : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            arithmeticLSeriesIntegrand F 2 t)).re)
      atTop (nhds (finitePrimeSum F)) := by
    have hmul : Tendsto
        (fun n : Nat => K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            arithmeticLSeriesIntegrand F 2 t))
        atTop (nhds (K⁻¹ * (∫ t : Real, arithmeticLSeriesIntegrand F 2 t))) :=
      (tendsto_const_nhds : Tendsto (fun _ : Nat => K⁻¹) atTop (nhds K⁻¹)).mul
        hprimeIntervals
    have hre := (Complex.continuous_re.tendsto _).comp hmul
    have hread := normalized_integral_arithmeticLSeries_centerTwo_re_eq F
    simpa only [Function.comp_apply, K, hread] using hre

  have hcomponents : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            elementaryPoleIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            gammaRIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            arithmeticLSeriesIntegrand F 2 t)).re)
      atTop
      (nhds (-poleTerm F + archimedeanTerm F + finitePrimeSum F)) := by
    simpa only [add_assoc] using
      (hpoleNorm.add hgammaNorm).add hprimeNorm

  have htotal : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            verticalIntegrand F 2 t)).re)
      atTop (nhds (-spectralWeilValue F)) := by
    simpa only [K, centerTwoFoldedRightLineIntegral] using
      tendsto_selected_normalized_centerTwoRightLine_re F

  have hpoint : ∀ n : Nat,
      (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            verticalIntegrand F 2 t)).re =
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            elementaryPoleIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            gammaRIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            arithmeticLSeriesIntegrand F 2 t)).re := by
    intro n
    have hdecomp := intervalIntegral_verticalIntegrand_eq_arithmetic_components
      F (c := (2 : Real))
        (T := selectedDyadicCenterTwoHeight n) (by norm_num)
    rw [hdecomp]
    simp only [mul_add, Complex.add_re]

  have htotal' : Tendsto
      (fun n : Nat =>
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            elementaryPoleIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            gammaRIntegrand F 2 t)).re +
        (K⁻¹ *
          (∫ t : Real in (-selectedDyadicCenterTwoHeight n)..
            selectedDyadicCenterTwoHeight n,
            arithmeticLSeriesIntegrand F 2 t)).re)
      atTop (nhds (-spectralWeilValue F)) := by
    apply htotal.congr'
    filter_upwards [] with n
    exact hpoint n

  have hbalance : -spectralWeilValue F =
      -poleTerm F + archimedeanTerm F + finitePrimeSum F :=
    tendsto_nhds_unique htotal' hcomponents
  rw [C1SameOwnerWeil.psi_eq_components]
  linarith

/-- The reduced Gate 2 proposition is obtained from the same contract by
adding the already unconditional spectral summability theorem. -/
theorem gate2ExplicitFormula_of_centerTwo_gamma_contract
    (F : CompactLogTest)
    (hgamma : CenterTwoGammaReadbackContract F) :
    gate2ExplicitFormula F := by
  refine ⟨spectralSummableProp F, ?_⟩
  exact centerTwo_arithmetic_eq_spectral_of_gamma_contract F hgamma

end
end C1XiCenterTwoArithmeticAssembly
end Source
end ConnesWeilRH
