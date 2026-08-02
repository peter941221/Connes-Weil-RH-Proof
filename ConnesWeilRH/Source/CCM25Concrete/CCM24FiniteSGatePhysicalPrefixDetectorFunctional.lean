/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixCompression

/-!
# Finite detector functional for the physical Gate prefix

Proof 735 owns each ordered Gate prefix as a finite matrix trace.  This file
separates the genuine detector operator from the family-dependent physical
boundary data before any estimate: the prefix is the value of one finite
continuous linear functional on the ambient operator space at that detector.

The functional keeps the endpoint residual and reverse-forward coordinate in
one sum.  Its operator norm is deliberately not used, because that would
replace the signed target by a total-variation estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixDetectorFunctional

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalDetectorNormalForm
open CCM24FiniteSGatePhysicalPrefixCompression
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "AmbientOp" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- Evaluation of an ambient operator in one oriented matrix coefficient. -/
noncomputable def ambientOperatorCoefficient
    (left right : finiteSCarrier) : AmbientOp →L[ℂ] ℂ :=
  (innerSL ℂ left).comp
    (ContinuousLinearMap.apply ℂ finiteSCarrier right)

@[simp] theorem ambientOperatorCoefficient_apply
    (left right : finiteSCarrier) (operator : AmbientOp) :
    ambientOperatorCoefficient left right operator =
      ⟪left, operator right⟫_ℂ := by
  rfl

/-- The finite physical boundary data as one continuous linear functional of
the detector operator. -/
noncomputable def sourceGatePhysicalPrefixDetectorFunctional
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : AmbientOp →L[ℂ] ℂ :=
  ∑ i ∈ Finset.range N,
    (ambientOperatorCoefficient
        (sourceInclusion lambda (basis i))
        (sourceEndpointCancellationResidual lambda family (basis i)) +
      ambientOperatorCoefficient
        (sourceActualBandForwardCoframe lambda family (basis i))
        (sourceInclusion lambda (basis i)))

/-- Evaluation keeps both physical coordinates inside each finite summand. -/
theorem sourceGatePhysicalPrefixDetectorFunctional_apply
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (operator : AmbientOp) :
    sourceGatePhysicalPrefixDetectorFunctional
        lambda family basis N operator =
      ∑ i ∈ Finset.range N,
        (⟪sourceInclusion lambda (basis i),
            operator
              (sourceEndpointCancellationResidual
                lambda family (basis i))⟫_ℂ +
          ⟪sourceActualBandForwardCoframe lambda family (basis i),
            operator (sourceInclusion lambda (basis i))⟫_ℂ) := by
  simp only [sourceGatePhysicalPrefixDetectorFunctional,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ambientOperatorCoefficient_apply]

/-- One Gate diagonal coefficient is the complete two-coordinate detector
pairing before the forward/leakage expansion of Proof 733. -/
theorem inner_lowerFactorGaugedResponse_eq_detectorPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, lowerFactorGaugedActualBandCompletedRelativeResponse
      owner lambda family x⟫_ℂ =
      ⟪sourceInclusion lambda x,
        detectorOperator owner
          (sourceEndpointCancellationResidual lambda family x)⟫_ℂ +
      ⟪sourceActualBandForwardCoframe lambda family x,
        detectorOperator owner (sourceInclusion lambda x)⟫_ℂ := by
  rw [lowerFactorGaugedResponse_eq_detectorOffDiagonal,
    sourceGatePhysicalDetectorOffDiagonalResponse]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

/-- The finite Gate compression trace is exactly the finite physical
functional evaluated at the genuine compact-root detector. -/
theorem sourceGatePhysicalPrefixCompressionTrace_eq_detectorFunctional
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceGatePhysicalPrefixCompressionTrace owner lambda family basis N =
      sourceGatePhysicalPrefixDetectorFunctional lambda family basis N
        (detectorOperator owner) := by
  rw [sourceGatePhysicalPrefixCompressionTrace,
    CCM24FiniteSMovingBandPrefixCompression.trace_basisPrefixMatrix_eq_rangeDiagonal,
    sourceGatePhysicalPrefixDetectorFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_lowerFactorGaugedResponse_eq_detectorPairing
    owner lambda family (basis i)

/-- A uniform bound on the detector functional along the ordered exhaustion
feeds Proof 735 directly. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixDetectorFunctionalBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda)) (bound : ℝ)
    (htrace : IsTraceClassAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixDetectorFunctional lambda family basis N
        (detectorOperator owner)‖ ≤ bound) :
    ‖ordinaryTraceAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_prefixCompressionBound
    owner lambda family basis bound htrace
  intro N
  rw [sourceGatePhysicalPrefixCompressionTrace_eq_detectorFunctional]
  exact hbound N

/-- Fixed-family Hilbert--Schmidt pair data discharges trace legality, leaving
only the finite detector-functional bound. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixDetectorBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ : Type*}
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
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixDetectorFunctional
        lambda family sourceBasis N (detectorOperator owner)‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixCompressionBound
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro N
  rw [sourceGatePhysicalPrefixCompressionTrace_eq_detectorFunctional]
  exact hbound N

end CCM24FiniteSGatePhysicalPrefixDetectorFunctional
end CCM25Concrete
end Source
end ConnesWeilRH
