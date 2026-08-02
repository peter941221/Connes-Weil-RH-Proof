/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryInjectivityBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedTranslatedAnalyticWindowBridge

/-!
# Fixed physical source dense range from translated analytic windows

This module composes the Proof 710 translated analytic-window injectivity
bridge with the Proof 702 fixed physical source dense-range consumer.  It
does not construct analytic representatives or Fourier analyticity; those
remain explicit source inputs.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridge

open MeasureTheory
open scoped FourierTransform InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedFullBoundaryInjectivityBridge
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSFixedTranslatedAnalyticWindowBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

/-! ## Dense range from translated analytic-window uniqueness -/

set_option maxHeartbeats 4000000 in
-- The dependent fixed-source dense-range consumer elaborates the same long
-- basis-indexed physical source input as Proof 702.
theorem fixedPhysicalSourceInput_denseRange_of_analytic_window_originalMultiplier
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c)
    {ι κ τ ιr κr τr ν mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hfourier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    DenseRange (fixedPhysicalSourceInput owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor) := by
  apply
    fixedPhysicalSourceInput_denseRange_of_translated_fullBoundaryRootFactor_injective
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  exact
    fullBoundaryRootFactor_injective_of_translated_analytic_window_of_original_fourierMultiplier
      owner lambda a c hsupp hwidth hfourier hanalyticRep

set_option maxHeartbeats 4000000 in
-- The dependent fixed-source dense-range consumer elaborates the same long
-- basis-indexed physical source input as Proof 702.
theorem fixedPhysicalSourceInput_denseRange_of_analytic_window_finitePrimeTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0)
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
    {ι κ τ ιr κr τr ν mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    DenseRange (fixedPhysicalSourceInput owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor) := by
  apply
    fixedPhysicalSourceInput_denseRange_of_translated_fullBoundaryRootFactor_injective
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  exact
    fullBoundaryRootFactor_injective_of_translated_analytic_window_of_finitePrimeTerm
      owner lambda a c hsupp hwidth hterm hfourierAnalytic hanalyticRep

set_option maxHeartbeats 4000000 in
-- The dependent fixed-source dense-range consumer elaborates the same long
-- basis-indexed physical source input as Proof 702.
theorem fixedPhysicalSourceInput_denseRange_of_analytic_window_selectedVisiblePrime
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {p : CCM24VisiblePrime}
    (hp : p ∈
      FinitePrimePowerFamily.visiblePrimes
        (FinitePrimePowerFamily.ofSelectedOwner owner))
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
    {ι κ τ ιr κr τr ν mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    DenseRange (fixedPhysicalSourceInput owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor) := by
  apply
    fixedPhysicalSourceInput_denseRange_of_translated_fullBoundaryRootFactor_injective
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  exact
    fullBoundaryRootFactor_injective_of_translated_analytic_window_of_selectedVisiblePrime
      owner lambda a c hsupp hwidth hp hfourierAnalytic hanalyticRep

end CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridge
end CCM25Concrete
end Source
end ConnesWeilRH
