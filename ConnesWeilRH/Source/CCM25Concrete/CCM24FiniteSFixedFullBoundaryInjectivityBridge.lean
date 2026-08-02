/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedBoundaryKernelReduction

/-!
# Fixed full-boundary injectivity bridge

Proof 701 reduces the common kernel of the translated compact pair to a zero
of the full boundary factor.  This module feeds that exact reduction into the
Proof 700 dense-range consumer.  Injectivity of the full factor remains an
explicit analytic source hypothesis.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedFullBoundaryInjectivityBridge

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSGramResponse
open CCM24SourceProlateTrace
open CCM24FiniteSFixedPhysicalKernelBridge
open CCM24FiniteSFixedBoundaryKernelReduction

set_option maxHeartbeats 4000000 in
-- The dependent fixed-source carrier application needs the same elaboration
-- budget as the Proof 700 dense-range consumer.
theorem fixedPhysicalSourceInput_denseRange_of_translated_fullBoundaryRootFactor_injective
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    (hinjective : ∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0) :
    DenseRange (fixedPhysicalSourceInput owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor) := by
  apply fixedPhysicalSourceInput_denseRange_of_translated_boundary_pair_injective
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    boundaryBasis sourceBasis hfactor
  intro y hleft hright
  apply hinjective y
  exact translatedBoundaryPair_zero_imp_fullBoundaryRootFactor_zero
    owner lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
    (sourceInclusion lambda y) hleft hright

end CCM24FiniteSFixedFullBoundaryInjectivityBridge
end CCM25Concrete
end Source
end ConnesWeilRH
