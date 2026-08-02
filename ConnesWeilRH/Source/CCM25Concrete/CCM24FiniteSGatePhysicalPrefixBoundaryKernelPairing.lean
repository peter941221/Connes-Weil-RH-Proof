/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixBoundaryCenteredCycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorSignedKernelResponse

/-!
# Concrete kernel pairing for the centered physical Gate prefix

Proof 739 leaves one finite signed boundary trace.  This file reads that trace
as a finite sum of the genuine complete physical pair and then opens only the
outer/reflected coordinate to its common compact-root signed kernel.  The
second-support/prolate coordinate remains coupled in the same scalar bracket.

No branchwise absolute value, cutoff commutation, uniform estimate, finite-S
sign, Burnol identity, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSGatePhysicalBoundaryCenteredCycle
open CCM24FiniteSGatePhysicalBoundaryDifference
open CCM24FiniteSGatePhysicalPrefixBoundaryCenteredCycle
open CCM24FiniteSGatePhysicalPrefixCompression
open CCM24FiniteSGatePhysicalPrefixRootPairing
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRectangularTailFactorization
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorSignedKernelResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

section BoundaryData

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {ι κ τ ιr κr τr ν μ σ : Type*}
variable (negativeBasis : HilbertBasis ι ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis κ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis τ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis ιr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis κr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis τr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
variable (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
variable (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

/-- One complete physical pair coefficient is the matrix coefficient of the
genuine three-branch Sonin detector commutator. -/
theorem sourceThreeBranchPhysicalPairing_eq_inner_threeBranchCommutator
    (x y : finiteSCarrier) :
    sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor x y =
      inner ℂ x
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) y) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hinner := sourceThreeBranchPairData_inner_eq_physicalPairing owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor x y
  have htrace := sourceThreeBranchPairData_traceProduct_eq owner lambda a c
    hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  calc
    sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor x y =
      inner ℂ (base.left x) (base.right y) := by
        simpa only [base] using hinner.symm
    _ = inner ℂ x (base.traceProduct y) := by
      rw [BasisHilbertSchmidtPairData.traceProduct,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ x
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) y) := by
      rw [htrace]

/-- Pointwise, the Gate diagonal is the centered difference of two complete
physical-pair coefficients.  The fixed `J` block vanishes before summation. -/
theorem inner_lowerFactorGaugedResponse_eq_centeredPhysicalPairing
    (x : sourceSoninCarrier lambda) :
    inner ℂ x
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family x) =
      sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
          (sourceInclusion lambda x)
          (sourceEndpointCancellationResidual lambda family x) -
        sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
          (sourceActualBandForwardCoframe lambda family x)
          (sourceInclusion lambda x) := by
  let branch := cc20ThreeBranchCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
    (detectorOperator owner)
  let J := sourceInclusion lambda
  let D := sourceActualBandForwardEndpointCoframe lambda family
  let U := sourceEndpointCancellationResidual lambda family
  let F := sourceActualBandForwardCoframe lambda family
  have hendpoint : D = J + U := by
    dsimp only [D, J, U]
    rw [sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage,
      sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  have hcompressed : J† ∘L branch ∘L J = 0 := by
    dsimp only [J, branch]
    exact sourceInclusionAdjoint_comp_threeBranch_comp_sourceInclusion_eq_zero
      owner lambda
  have hfixed : inner ℂ (J x) (branch (J x)) = 0 := by
    calc
      inner ℂ (J x) (branch (J x)) =
          inner ℂ x ((J† ∘L branch ∘L J) x) := by
        simp only [ContinuousLinearMap.comp_apply]
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hcompressed]; simp
  rw [lowerFactorGaugedResponse_eq_completePhysicalBoundaryDifference]
  rw [sourceThreeBranchPhysicalPairing_eq_inner_threeBranchCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceThreeBranchPhysicalPairing_eq_inner_threeBranchCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  change inner ℂ x
      (((J† ∘L branch ∘L D) - (F† ∘L branch ∘L J)) x) = _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right]
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, hendpoint]
  simp only [ContinuousLinearMap.add_apply, map_add, inner_add_right]
  rw [hfixed, zero_add]

/-- The ordered centered prefix written as one finite sum of complete physical
pair coefficients. -/
noncomputable def sourceGatePhysicalPrefixCenteredPhysicalPairing
    (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceInclusion lambda (sourceBasis i))
        (sourceEndpointCancellationResidual lambda family (sourceBasis i)) -
      sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceActualBandForwardCoframe lambda family (sourceBasis i))
        (sourceInclusion lambda (sourceBasis i)))

/-- Proof 737's compact-root prefix is exactly the centered complete physical
pairing, before any physical coordinate is estimated. -/
theorem sourceGatePhysicalPrefixRootPairing_eq_centeredPhysicalPairing
    (N : ℕ) :
    sourceGatePhysicalPrefixRootPairing owner lambda family sourceBasis N =
      sourceGatePhysicalPrefixCenteredPhysicalPairing owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor N := by
  rw [← sourceGatePhysicalPrefixCompressionTrace_eq_rootPairing]
  rw [sourceGatePhysicalPrefixCompressionTrace,
    trace_basisPrefixMatrix_eq_rangeDiagonal]
  rw [sourceGatePhysicalPrefixCenteredPhysicalPairing]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_lowerFactorGaugedResponse_eq_centeredPhysicalPairing owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor (sourceBasis i)

/-- The analytic scalar for one source vector.  The compact-root signed kernel
and the coupled second-support/prolate remainder stay inside each difference. -/
noncomputable def sourceGatePhysicalCenteredKernelScalar
    (x : sourceSoninCarrier lambda) : ℂ :=
  let remainder := secondSupportProlateRemainderPairData owner lambda a c hac
    hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  let Jx := sourceInclusion lambda x
  let Ux := sourceEndpointCancellationResidual lambda family x
  let Fx := sourceActualBandForwardCoframe lambda family x
  (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Jx Ux +
      inner ℂ (remainder.left Jx) (remainder.right Ux)) -
    (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Fx Jx +
      inner ℂ (remainder.left Fx) (remainder.right Jx))

/-- The complete physical-pair difference opens to the concrete signed kernel
without splitting off the second-support/prolate remainder. -/
theorem centeredPhysicalPairing_eq_centeredKernelScalar
    (x : sourceSoninCarrier lambda) :
    sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceInclusion lambda x)
        (sourceEndpointCancellationResidual lambda family x) -
      sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceActualBandForwardCoframe lambda family x)
        (sourceInclusion lambda x) =
      sourceGatePhysicalCenteredKernelScalar owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor x := by
  rw [sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rfl

/-- The one finite Gate 3U analytic target after the genuine compact-root
kernel has been exposed. -/
noncomputable def sourceGatePhysicalPrefixCenteredKernelPairing
    (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    sourceGatePhysicalCenteredKernelScalar owner lambda family a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor (sourceBasis i)

/-- The complete physical prefix and the concrete centered kernel prefix are
identical finite scalars. -/
theorem sourceGatePhysicalPrefixCenteredPhysicalPairing_eq_kernelPairing
    (N : ℕ) :
    sourceGatePhysicalPrefixCenteredPhysicalPairing owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor N =
      sourceGatePhysicalPrefixCenteredKernelPairing owner lambda family a c
        hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor N := by
  rw [sourceGatePhysicalPrefixCenteredPhysicalPairing,
    sourceGatePhysicalPrefixCenteredKernelPairing]
  apply Finset.sum_congr rfl
  intro i _
  exact centeredPhysicalPairing_eq_centeredKernelScalar owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor (sourceBasis i)

/-- Proof 739's centered common-boundary trace is the same concrete finite
kernel bracket. -/
theorem ordinaryTraceAlong_prefixBoundaryCenteredResponse_eq_kernelPairing
    (N : ℕ) :
    ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCenteredResponse owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis N hfactor) =
      sourceGatePhysicalPrefixCenteredKernelPairing owner lambda family a c
        hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor N := by
  rw [← sourceGatePhysicalPrefixRootPairing_eq_centeredBoundaryCycle owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis N hfactor]
  rw [sourceGatePhysicalPrefixRootPairing_eq_centeredPhysicalPairing owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor N]
  exact sourceGatePhysicalPrefixCenteredPhysicalPairing_eq_kernelPairing owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor N

include negativeBasis positiveBasis outputBasis boundaryBasis
include pairedBoundaryBasis

/-- A bound on the complete concrete kernel brackets feeds the ordered Gate
consumer directly.  The hypothesis is still the open uniform estimate. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixCenteredKernelBound
    (bound : ℝ)
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixCenteredKernelPairing owner lambda family a c
        hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor N‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_prefixCenteredBoundaryBound
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro N
  rw [ordinaryTraceAlong_prefixBoundaryCenteredResponse_eq_kernelPairing owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor N]
  exact hbound N

end BoundaryData

end CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing
end CCM25Concrete
end Source
end ConnesWeilRH
