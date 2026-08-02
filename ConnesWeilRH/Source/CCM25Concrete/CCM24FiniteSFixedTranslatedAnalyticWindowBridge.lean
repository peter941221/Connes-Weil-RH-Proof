/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedAnalyticWindowUniquenessBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryOriginalRootMultiplierBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedOwnerFourierAeNonzeroBridge

/-!
# Translated analytic-window bridge

This module attaches the analytic finite-window uniqueness theorem to the
actual translated `sourceSoninCarrier` premise consumed by the full-boundary
chain.  It keeps the analytic representative as an explicit per-vector source
contract; no theorem here constructs such a representative for the current
root convolution.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedTranslatedAnalyticWindowBridge

open MeasureTheory
open scoped FourierTransform

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSGramResponse
open CCM24FiniteSFixedAnalyticWindowUniquenessBridge
open CCM24FiniteSFixedFullBoundaryOriginalRootMultiplierBridge
open CCM24FiniteSFixedOwnerFourierAeNonzeroBridge
open CCM24FiniteSProjectionTrace
open SelectedCrossingOperatorBridge

/-! ## Translated finite-window uniqueness from analytic representatives -/

/-- Per-vector analytic representatives of the translated root convolution
instantiate the finite-window uniqueness premise used by Proof 704. -/
theorem translated_window_unique_of_analytic_representatives
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hwidth : a < c)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∀ y : sourceSoninCarrier lambda,
      globalL2ToKernelInterval (-c) (-a) 0
          (cc20GlobalLogConvolution owner.sourceTest.involution.test
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
              (sourceInclusion lambda y))) = 0 →
        cc20GlobalLogConvolution owner.sourceTest.involution.test
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 := by
  intro y hwindow
  obtain ⟨f, hanalytic, hrep⟩ := hanalyticRep y
  exact
    cc20GlobalLogConvolution_eq_zero_of_analytic_representative_of_kernelInterval_zero
      owner.sourceTest.involution.test
      ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
        (sourceInclusion lambda y))
      (-c) (-a) 0 (by linarith) f hanalytic hrep hwindow

/-! ## Full-boundary injectivity consumers -/

theorem fullBoundaryRootFactor_injective_of_translated_analytic_window_of_original_fourierMultiplier
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c)
    (hfourier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0 := by
  apply
    fullBoundaryRootFactor_injective_of_translated_window_unique_of_original_fourierMultiplier
      owner lambda a c hsupp hfourier
  exact translated_window_unique_of_analytic_representatives
    owner lambda a c hwidth hanalyticRep

theorem fullBoundaryRootFactor_injective_of_translated_analytic_window_of_finitePrimeTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0)
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0 := by
  apply
    fullBoundaryRootFactor_injective_of_translated_analytic_window_of_original_fourierMultiplier
      owner lambda a c hsupp hwidth
  · exact sourceTest_fourier_ae_ne_zero_of_analytic_of_finitePrimeTerm_ne_zero
      owner hterm hfourierAnalytic
  · exact hanalyticRep

theorem fullBoundaryRootFactor_injective_of_translated_analytic_window_of_selectedVisiblePrime
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {p : CCM24VisiblePrime}
    (hp : p ∈
      FinitePrimePowerFamily.visiblePrimes
        (FinitePrimePowerFamily.ofSelectedOwner owner))
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0 := by
  apply
    fullBoundaryRootFactor_injective_of_translated_analytic_window_of_original_fourierMultiplier
      owner lambda a c hsupp hwidth
  · exact sourceTest_fourier_ae_ne_zero_of_analytic_of_selectedVisiblePrime
      owner hp hfourierAnalytic
  · exact hanalyticRep

end CCM24FiniteSFixedTranslatedAnalyticWindowBridge
end CCM25Concrete
end Source
end ConnesWeilRH
