/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTransitionOrientation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurEndpointAlignmentResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction

/-!
# Canonical skew part of the actual Schur boundary moment

The boundary moment from the actual Schur row is not self-adjoint in general.
This module separates its genuinely Hermitian forward pair from the metric
coframe leakage.  The latter is exactly the canonical target-commutator
response used by the current completed-kernel Gate 3U route.

Thus the transition-skew obstruction from the old Schur-row ledger and the
canonical completed-kernel target are the same analytic channel.  No skew
term is set to zero, no trace is cycled, and no uniform estimate is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurBoundaryMomentCanonicalSkew

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurEndpointAlignmentResidual
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurRowBoundaryMoment
open CCM24FiniteSActualSchurTransitionOrientation
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSCoframeResponse
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

private theorem rectangularAdjointPair_adjoint_eq
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (forward inclusion : H →L[ℂ] K) (detector : K →L[ℂ] K)
    (hdetector : detector† = detector) :
    (forward† ∘L detector ∘L inclusion +
        inclusion† ∘L detector ∘L forward)† =
      forward† ∘L detector ∘L inclusion +
        inclusion† ∘L detector ∘L forward := by
  rw [ContinuousLinearMap.adjoint.map_add]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hdetector,
    ContinuousLinearMap.comp_assoc, add_comm]

/-! ## Hermitian and leakage coordinates -/

/-- The named Schur endpoint still compresses to the source inclusion. -/
theorem sourceSoninProjection_comp_suffixActualSchurForwardEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninProjection lambda ∘L
        suffixActualSchurForwardEndpointCoframe lambda stepData S =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro x
  have hforward := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceSoninProjection_comp_sourceActualBandForwardSchurCoframe_eq_zero
      lambda stepData S)
  have hmetric := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceSoninProjection_comp_suffixActualBandMetricCoframe lambda S)
  simp only [suffixActualSchurForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply] at hforward hmetric ⊢
  rw [map_add, hforward, hmetric, zero_add]

/-- The conjugate forward crossings in the boundary moment. -/
noncomputable def suffixActualBandNamedSchurForwardHermitianResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (sourceActualBandForwardSchurCoframe lambda stepData S)† ∘L
      detectorOperator owner ∘L sourceInclusion lambda +
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceActualBandForwardSchurCoframe lambda stepData S

/-- The only non-Hermitian coordinate of the boundary moment. -/
noncomputable def suffixActualBandMetricLeakageTargetResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixActualBandMetricCoframe lambda S - sourceInclusion lambda)† ∘L
    detectorOperator owner ∘L sourceInclusion lambda

theorem suffixActualBandNamedSchurForwardHermitianResponse_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandNamedSchurForwardHermitianResponse
      owner lambda stepData S)† =
      suffixActualBandNamedSchurForwardHermitianResponse
        owner lambda stepData S := by
  exact rectangularAdjointPair_adjoint_eq
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (sourceInclusion lambda) (detectorOperator owner)
    (detectorOperator_isSelfAdjoint owner)

/-! ## Exact boundary-moment decomposition -/

/-- The actual Schur boundary moment is a Hermitian forward pair plus one
metric-leakage target.  In particular, its skew part is independent of the
chosen Schur forward coframe. -/
theorem suffixActualBandNamedSchurBoundaryMomentRow_eq_forwardHermitian_add_metricLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S =
      suffixActualBandNamedSchurForwardHermitianResponse
          owner lambda stepData S +
        suffixActualBandMetricLeakageTargetResponse owner lambda S := by
  unfold suffixActualBandNamedSchurBoundaryMomentRow
  rw [rawCoframeBoundaryMoment_eq_leakage_of_endpoint_compression
    owner lambda
      (sourceActualBandForwardSchurCoframe lambda stepData S)
      (suffixActualSchurForwardEndpointCoframe lambda stepData S)
      (sourceSoninProjection_comp_suffixActualSchurForwardEndpointCoframe
        lambda stepData S)]
  rw [suffixActualSchurForwardEndpointCoframe]
  have hsplit :
      sourceActualBandForwardSchurCoframe lambda stepData S +
            suffixActualBandMetricCoframe lambda S - sourceInclusion lambda =
        sourceActualBandForwardSchurCoframe lambda stepData S +
          (suffixActualBandMetricCoframe lambda S - sourceInclusion lambda) := by
    abel
  rw [hsplit, ContinuousLinearMap.adjoint.map_add]
  unfold suffixActualBandNamedSchurForwardHermitianResponse
    suffixActualBandMetricLeakageTargetResponse
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  abel

/-- The skew part of the boundary moment is exactly the skew part of the
metric-leakage target. -/
theorem suffixActualBandNamedSchurBoundaryMomentRow_sub_adjoint_eq_metricLeakage_sub_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S -
        (suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S)† =
      suffixActualBandMetricLeakageTargetResponse owner lambda S -
        (suffixActualBandMetricLeakageTargetResponse owner lambda S)† := by
  rw [suffixActualBandNamedSchurBoundaryMomentRow_eq_forwardHermitian_add_metricLeakage,
    ContinuousLinearMap.adjoint.map_add,
    suffixActualBandNamedSchurForwardHermitianResponse_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  abel

/-! ## Identification with the current Gate target -/

theorem suffixActualBandMetricLeakageTargetResponse_visiblePrimes_eq_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandMetricLeakageTargetResponse
        owner lambda family.visiblePrimes =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  rw [suffixActualBandMetricLeakageTargetResponse,
    suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe,
    finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage]
  unfold finiteEulerPhysicalCoframeLeakageResponse
  rw [← sourceSoninCoframeLeakage_eq_physical,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]

/-- On an actual finite family, the full skew part is precisely the skew part
of the current canonical Gate target. -/
theorem suffixActualBandNamedSchurBoundaryMomentRow_visiblePrimes_sub_adjoint_eq_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData
          family.visiblePrimes -
        (suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData
          family.visiblePrimes)† =
      finiteEulerTargetCommutatorResponse owner lambda family -
        (finiteEulerTargetCommutatorResponse owner lambda family)† := by
  rw [suffixActualBandNamedSchurBoundaryMomentRow_sub_adjoint_eq_metricLeakage_sub_adjoint,
    suffixActualBandMetricLeakageTargetResponse_visiblePrimes_eq_targetCommutator]

/-- On an actual finite family, the Schur boundary moment is self-adjoint
exactly when the canonical Gate target is self-adjoint.  No such producer is
assumed here. -/
theorem suffixActualBandNamedSchurBoundaryMomentRow_visiblePrimes_adjoint_eq_iff_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    (suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData
        family.visiblePrimes)† =
        suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData
          family.visiblePrimes ↔
      (finiteEulerTargetCommutatorResponse owner lambda family)† =
        finiteEulerTargetCommutatorResponse owner lambda family := by
  rw [suffixActualBandNamedSchurBoundaryMomentRow_eq_forwardHermitian_add_metricLeakage,
    suffixActualBandMetricLeakageTargetResponse_visiblePrimes_eq_targetCommutator,
    ContinuousLinearMap.adjoint.map_add,
    suffixActualBandNamedSchurForwardHermitianResponse_adjoint_eq]
  constructor
  · exact add_left_cancel
  · intro htarget
    rw [htarget]

end CCM24FiniteSActualSchurBoundaryMomentCanonicalSkew
end CCM25Concrete
end Source
end ConnesWeilRH
