/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryInjectivityBridge

/-!
# Fixed full-boundary window-uniqueness bridge

The full-boundary factor is the reflected-window readout of a genuine global
root convolution.  This module separates the two analytic inputs that are
needed to turn that readout into injectivity:

* the root Fourier multiplier is nonzero almost everywhere, which makes the
  global convolution injective; and
* the finite-window readout is unique on the translated source Sonin carrier,
  which upgrades a zero window to a zero global convolution.

The first implication is proved here on the actual `Lp` carrier.  The second
one remains an explicit finite-window uniqueness premise; it is not inferred
from compactness or from the nonzero root alone.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge

open MeasureTheory
open scoped ENNReal FourierTransform

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedFullBoundaryInjectivityBridge
open SelectedCrossingOperatorBridge

/-! ## Global convolution injectivity from a nonvanishing multiplier -/

theorem cc20GlobalLogConvolution_injective_of_fourierMultiplier_ae_ne_zero
    (h : SchwartzMap ℝ ℂ)
    (hmultiplier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier h).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    {u : cc20GlobalLogCrossingL2}
    (hu : cc20GlobalLogConvolution h u = 0) :
    u = 0 := by
  have hmul :
      cc20FourierMultiplier h
          ((Lp.fourierTransformₗᵢ ℝ ℂ) u) = 0 := by
    rw [← fourier_globalLogConvolution h u, hu, map_zero]
  rw [cc20FourierMultiplier_apply] at hmul
  rw [Lp.ext_iff] at hmul
  have hfourier :
      (Lp.fourierTransformₗᵢ ℝ ℂ) u = 0 := by
    rw [Lp.ext_iff]
    filter_upwards
      [hmul,
       Lp.coeFn_lpSMul (r := 2)
         ((FourierTransform.fourier h).toLp ⊤)
         ((Lp.fourierTransformₗᵢ ℝ ℂ) u),
       Lp.coeFn_zero ℂ 2 (volume : Measure ℝ),
       hmultiplier] with ξ hmulAt hsmul hzero hnonzero
    rw [hsmul, hzero] at hmulAt
    simpa using (mul_eq_zero.mp hmulAt).resolve_left hnonzero
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simpa using hfourier

/-! ## The finite-window uniqueness consumer -/

set_option maxHeartbeats 4000000 in
-- The translated source-carrier conclusion unfolds several dependent Lp
-- carriers and needs the same elaboration budget as the fixed-source bridge.
theorem fullBoundaryRootFactor_injective_of_translated_window_unique
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hmultiplier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.involution.test).toLp ⊤ :
        ℝ → ℂ) ξ ≠ 0)
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
  intro y hfactor
  have hwindowZero :
      globalL2ToKernelInterval (-c) (-a) 0
          (cc20GlobalLogConvolution owner.sourceTest.involution.test
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
              (sourceInclusion lambda y))) = 0 := by
    have hfactorEq := congrArg
      (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) =>
        T ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
          (sourceInclusion lambda y)))
      (fullBoundaryRootFactor_eq_globalConvolution
        owner.sourceTest a c hsupp)
    have hfactorEq' :
        fullBoundaryRootFactor owner.sourceTest a c
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
              (sourceInclusion lambda y)) =
          globalL2ToKernelInterval (-c) (-a) 0
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y))) := by
      simpa only [ContinuousLinearMap.comp_apply] using hfactorEq
    calc
      _ = fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) := hfactorEq'.symm
      _ = 0 := hfactor
  have hconvolutionZero := hwindow y hwindowZero
  have htranslated :
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
          (sourceInclusion lambda y) = 0 :=
    cc20GlobalLogConvolution_injective_of_fourierMultiplier_ae_ne_zero
      owner.sourceTest.involution.test hmultiplier hconvolutionZero
  have hinclusion : sourceInclusion lambda y = 0 := by
    apply (cc20GlobalLogTranslation (Real.log lambda)).injective
    exact htranslated
  have hyvalue : (y : finiteSCarrier) = 0 := by
    simpa only [sourceInclusion] using hinclusion
  exact Subtype.ext hyvalue

end CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
end CCM25Concrete
end Source
end ConnesWeilRH
