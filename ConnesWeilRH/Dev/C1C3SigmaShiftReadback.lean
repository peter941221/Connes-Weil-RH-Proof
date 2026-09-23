/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3CarrierFourierShift
import ConnesWeilRH.Dev.C1XiCenterTwoGamma

/-!
# C3' carrier shift through the complete Gamma_R readback

The carrier frequency shift is now transported through the full center-two
Gamma_R integral to the actual archimedean term of a carrier square.  The
identity is exact on one `CompactLogTest` owner.  It is an integral-level
readback only: it does not assert the paper's Fourier-multiplier sigma formula,
any sigma sign, or the detector-specific prime budget.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3SigmaShiftReadback

open MeasureTheory
open ConnesWeilRH.Source.C1SameOwnerWeil
open ConnesWeilRH.Source.C1XiArithmeticIntervalReadback
open ConnesWeilRH.Source.C1XiCenterTwoGamma
open ConnesWeilRH.Source.C1XiVerticalFunctional
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-- The center-two Gamma_R integrand with the carrier frequency shift
explicitly applied to both centered Laplace weights. -/
noncomputable def carrierShiftedGammaRIntegrand
    (γ : Real) (F : CompactLogTest) (t : Real) : Complex :=
  -logDeriv Complex.Gammaℝ (verticalPoint 2 t) *
    (centeredLaplaceWeight F
        (verticalPoint 2 t - (γ : Complex) * Complex.I) +
      centeredLaplaceWeight F
        ((1 : Complex) - verticalPoint 2 t - (γ : Complex) * Complex.I)) *
    Complex.I

/-- Pointwise, the shifted-weight integrand is exactly the ordinary Gamma_R
integrand of the carrier-modulated test. -/
theorem gammaRIntegrand_carrierModulate_eq_carrierShifted
    (γ t : Real) (F : CompactLogTest) :
    gammaRIntegrand (C1C3CarrierTransport.carrierModulate γ F) 2 t =
      carrierShiftedGammaRIntegrand γ F t := by
  simpa only [carrierShiftedGammaRIntegrand] using
    C1C3CarrierTransport.gammaRIntegrand_carrierModulate_eq_shiftedWeight
      γ 2 t F

/-- The exact shifted integrand inherits full-line integrability from the
same-owner center-two Gamma_R integrability theorem. -/
theorem integrable_carrierShiftedGammaRIntegrand
    (γ : Real) (F : CompactLogTest) :
    Integrable (fun t : Real => carrierShiftedGammaRIntegrand γ F t) := by
  have h := integrable_gammaRIntegrand_centerTwo
    (C1C3CarrierTransport.carrierModulate γ F)
  exact h.congr (Filter.Eventually.of_forall fun t =>
    gammaRIntegrand_carrierModulate_eq_carrierShifted γ t F)

/-- The normalized center-two Gamma_R integral of the shifted weights is the
complete archimedean term of the carrier-modulated test. -/
theorem normalized_gammaR_carrierModulate_re_eq_archimedeanTerm
    (γ : Real) (F : CompactLogTest) :
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
      (∫ t : Real, carrierShiftedGammaRIntegrand γ F t)).re =
        archimedeanTerm (C1C3CarrierTransport.carrierModulate γ F) := by
  rw [← normalized_gammaR_centerTwo_re_eq_archimedeanTerm
    (C1C3CarrierTransport.carrierModulate γ F)]
  apply congrArg (fun z : Complex =>
    ((2 * (Real.pi : Complex) * Complex.I)⁻¹ * z).re)
  apply integral_congr_ae
  filter_upwards with t
  exact (gammaRIntegrand_carrierModulate_eq_carrierShifted γ t F).symm

/-- The square of a carrier-modulated test is the carrier modulation of its
unmodulated convolution square. This identifies the archimedean owner without
forming or transporting a second square. -/
theorem convolutionSquare_carrier_eq
    (γ : Real) (u : CompactLogTest) :
    (C1C3CarrierTransport.carrierModulate γ u).convolutionSquare =
      C1C3CarrierTransport.carrierModulate γ u.convolutionSquare := by
  apply CompactLogTest.ext
  ext x
  rw [C1C3CarrierTransport.convolutionSquare_carrier_apply,
    C1C3CarrierTransport.carrierModulate_apply]

/-- Exact same-owner Gamma_R readback for the actual carrier square consumed
by the C3' archimedean determinant face. -/
theorem archimedeanTerm_carrierSquare_eq_shiftedGammaR
    (γ : Real) (u : CompactLogTest) :
    archimedeanTerm
        (C1C3CarrierTransport.carrierModulate γ u).convolutionSquare =
      ((2 * (Real.pi : Complex) * Complex.I)⁻¹ *
        (∫ t : Real,
          carrierShiftedGammaRIntegrand γ u.convolutionSquare t)).re := by
  rw [convolutionSquare_carrier_eq]
  exact (normalized_gammaR_carrierModulate_re_eq_archimedeanTerm
    γ u.convolutionSquare).symm

end C1C3SigmaShiftReadback
end Dev
end ConnesWeilRH
