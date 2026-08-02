/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedReflectedRootFourierMultiplierBridge

/-!
# Full-boundary injectivity with the original root multiplier premise

Proof 705 transfers Fourier nonvanishing from the original compact root to
the involuted root used by the full-boundary convolution.  This module wires
that exact transfer into the existing full-boundary injectivity consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedFullBoundaryOriginalRootMultiplierBridge

open MeasureTheory
open scoped ENNReal FourierTransform

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedFullBoundaryInjectivityBridge
open CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
open CCM24FiniteSFixedReflectedRootFourierMultiplierBridge
open SelectedCrossingOperatorBridge

theorem fullBoundaryRootFactor_injective_of_translated_window_unique_of_original_fourierMultiplier
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hfourier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    (hwindow : ∀ y : sourceSoninCarrier lambda,
      globalL2ToKernelInterval (-c) (-a) 0
          (cc20GlobalLogConvolution owner.sourceTest.involution.test
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
              (sourceInclusion lambda y))) = 0 →
        cc20GlobalLogConvolution owner.sourceTest.involution.test
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
              (sourceInclusion lambda y)) = 0) :
    ∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0 := by
  apply fullBoundaryRootFactor_injective_of_translated_window_unique
    owner lambda a c hsupp
  · exact fourier_involution_test_ae_ne_zero_of_fourier_test_ae_ne_zero
      owner.sourceTest hfourier
  · exact hwindow

end CCM24FiniteSFixedFullBoundaryOriginalRootMultiplierBridge
end CCM25Concrete
end Source
end ConnesWeilRH
