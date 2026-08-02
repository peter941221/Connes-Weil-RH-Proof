/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixDetectorFunctional

/-!
# Compact-root pairing for the physical Gate prefix

The selected detector is the positive square `C_h^dagger C_h` of the genuine
compact convolution root.  This file evaluates Proof 736's finite detector
functional through that exact factorization.  Both physical coordinates stay
inside one finite root pairing; no Cauchy--Schwarz or termwise norm is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixRootPairing

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalPrefixDetectorFunctional
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- One detector coefficient is the inner product of the two genuine compact
convolution-root images. -/
theorem inner_detectorOperator_eq_rootConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (left right : finiteSCarrier) :
    ⟪left, detectorOperator owner right⟫_ℂ =
      ⟪rootConvolution owner left, rootConvolution owner right⟫_ℂ := by
  unfold detectorOperator cc20GlobalConvolutionPositive rootConvolution
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The complete ordered prefix after the detector square is opened but before
any estimate is taken. -/
noncomputable def sourceGatePhysicalPrefixRootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (⟪rootConvolution owner (sourceInclusion lambda (basis i)),
        rootConvolution owner
          (sourceEndpointCancellationResidual lambda family (basis i))⟫_ℂ +
      ⟪rootConvolution owner
          (sourceActualBandForwardCoframe lambda family (basis i)),
        rootConvolution owner (sourceInclusion lambda (basis i))⟫_ℂ)

/-- Proof 736's detector functional at the selected detector is exactly the
complete compact-root pairing. -/
theorem sourceGatePhysicalPrefixDetectorFunctional_eq_rootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceGatePhysicalPrefixDetectorFunctional lambda family basis N
        (detectorOperator owner) =
      sourceGatePhysicalPrefixRootPairing owner lambda family basis N := by
  rw [sourceGatePhysicalPrefixDetectorFunctional_apply,
    sourceGatePhysicalPrefixRootPairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_detectorOperator_eq_rootConvolution,
    inner_detectorOperator_eq_rootConvolution]

/-- The finite Gate compression trace is the same compact-root pairing. -/
theorem sourceGatePhysicalPrefixCompressionTrace_eq_rootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    CCM24FiniteSGatePhysicalPrefixCompression.sourceGatePhysicalPrefixCompressionTrace
        owner lambda family basis N =
      sourceGatePhysicalPrefixRootPairing owner lambda family basis N := by
  rw [sourceGatePhysicalPrefixCompressionTrace_eq_detectorFunctional,
    sourceGatePhysicalPrefixDetectorFunctional_eq_rootPairing]

/-- A uniform bound on the complete compact-root prefixes controls the
ordinary Gate trace once fixed-family trace legality is supplied. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixRootPairingBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda)) (bound : ℝ)
    (htrace : IsTraceClassAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixRootPairing
        owner lambda family basis N‖ ≤ bound) :
    ‖ordinaryTraceAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_prefixDetectorFunctionalBound
    owner lambda family basis bound htrace
  intro N
  rw [sourceGatePhysicalPrefixDetectorFunctional_eq_rootPairing]
  exact hbound N

/-- Existing Hilbert--Schmidt pair data discharges trace legality, so the
remaining premise is only the complete finite compact-root pairing bound. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixRootPairingBound
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
      ‖sourceGatePhysicalPrefixRootPairing
        owner lambda family sourceBasis N‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixDetectorBound
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro N
  rw [sourceGatePhysicalPrefixDetectorFunctional_eq_rootPairing]
  exact hbound N

end CCM24FiniteSGatePhysicalPrefixRootPairing
end CCM25Concrete
end Source
end ConnesWeilRH
