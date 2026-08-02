/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalKernelBridge

/-!
# Fixed boundary-kernel reduction

The translated negative and positive boundary legs use inverse translation
dressings.  Their common source input is therefore the same translated vector.
This module combines the two zero-leg conclusions through the full compact
input window.  It does not assert injectivity of the resulting full factor.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedBoundaryKernelReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open SelectedCrossingOperatorBridge

theorem translatedBoundaryPair_zero_imp_fullBoundaryRootFactor_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (x : finiteSCarrier)
    (hleft :
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left x = 0)
    (hright :
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right x = 0) :
    fullBoundaryRootFactor owner.sourceTest a c
        ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
      0 := by
  have hleft' :
      (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
        globalBasis).left
          ((cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap.adjoint
            x) = 0 := by
    simpa only [translatedCompactRootPairData,
      BasisHilbertSchmidtPairData.boundedSandwich,
      ContinuousLinearMap.comp_apply] using hleft
  have hright' :
      (pairData owner.sourceTest a c negativeBasis positiveBasis outputBasis
        globalBasis).right
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
        0 := by
    simpa only [translatedCompactRootPairData,
      BasisHilbertSchmidtPairData.boundedSandwich,
      ContinuousLinearMap.comp_apply] using hright
  rw [cc20GlobalLogTranslation_neg_adjoint] at hleft'
  have hnegative :
      negativeBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
        0 := by
    simpa only [pairData] using hleft'
  have hpositive :
      positiveBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
        0 := by
    simpa only [pairData] using hright'
  have hnegativeFull :
      fullBoundaryRootFactor owner.sourceTest a c
          (cc20NegativeHalfLineProjection
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x)) =
        0 := by
    change (fullBoundaryRootFactor owner.sourceTest a c ∘L
        cc20NegativeHalfLineProjection)
        ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) = 0
    rw [fullBoundaryRootFactor_comp_negativeHalfLineProjection
      owner.sourceTest a c hac]
    exact hnegative
  have hpositiveFull :
      fullBoundaryRootFactor owner.sourceTest a c
          (cc20PositiveHalfLineProjection
            ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x)) =
        0 := by
    change (fullBoundaryRootFactor owner.sourceTest a c ∘L
        cc20PositiveHalfLineProjection)
        ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) = 0
    rw [fullBoundaryRootFactor_comp_positiveHalfLineProjection
      owner.sourceTest a c hac]
    exact hpositive
  have hsplit :
      cc20NegativeHalfLineProjection + cc20PositiveHalfLineProjection =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [cc20NegativeHalfLineProjection,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hsum :
      cc20NegativeHalfLineProjection
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) +
        cc20PositiveHalfLineProjection
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x := by
    have h := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
        T ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x))
      hsplit
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h
  calc
    fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) =
        fullBoundaryRootFactor owner.sourceTest a c
          (cc20NegativeHalfLineProjection
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x) +
            cc20PositiveHalfLineProjection
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x)) := by
      rw [hsum]
    _ = fullBoundaryRootFactor owner.sourceTest a c
          (cc20NegativeHalfLineProjection
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x)) +
        fullBoundaryRootFactor owner.sourceTest a c
          (cc20PositiveHalfLineProjection
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap x)) := by
      rw [map_add]
    _ = 0 := by rw [hnegativeFull, hpositiveFull, add_zero]

end CCM24FiniteSFixedBoundaryKernelReduction
end CCM25Concrete
end Source
end ConnesWeilRH
