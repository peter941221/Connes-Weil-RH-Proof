/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateRow

/-!
# Root-commutator form of the completed Hardy--prolate row

Proof 779 keeps the compact root after one completed `L2` row.  This module
moves that root to the two source boundary commutators while retaining the
same row carrier.  Thus compact-root locality enters before any future scalar
estimate, without replacing the outer and Sonin coordinates by separate norm
bounds.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateRowRootCommutator

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24RadialBoundaryPairTransport
open CCM24FiniteSGatePhysicalHardyProlateGram
open CCM24FiniteSGatePhysicalHardyProlateRow

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The completed Hardy/prolate analysis kills the fixed Sonin range.  This
follows from its exact Gram, not from a coordinatewise estimate. -/
theorem sourceHardyProlateCompletedAnalysis_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) :
    sourceHardyProlateCompletedAnalysis lambda ∘L sourceSoninProjection lambda =
      0 := by
  apply ContinuousLinearMap.ext
  intro u
  change sourceHardyProlateCompletedAnalysis lambda
      (sourceSoninProjection lambda u) = 0
  change sourceSoninProjection lambda u ∈
    (sourceHardyProlateCompletedAnalysis lambda).ker
  rw [← ContinuousLinearMap.ker_adjoint_comp_self]
  change ((sourceHardyProlateCompletedAnalysis lambda).adjoint ∘L
      sourceHardyProlateCompletedAnalysis lambda)
      (sourceSoninProjection lambda u) = 0
  rw [sourceHardyProlateCompletedAnalysis_adjoint_comp_self_eq_completedGram,
    sourceHardyProlateCompletedGram_eq_sourceBandProjection]
  exact DFunLike.congr_fun
    (sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda) u

/-- On the fixed Sonin inclusion, the outer coordinate sees the compact root
only through the actual radial detector commutator `[W,E]`. -/
theorem radialComplement_comp_detector_comp_sourceInclusion_eq_detectorRadialCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    radialComplementProjection lambda ∘L detectorOperator owner ∘L
        sourceInclusion lambda =
      radialComplementProjection lambda ∘L
        (detectorOperator owner ∘L radialSupportProjection lambda -
          radialSupportProjection lambda ∘L detectorOperator owner) ∘L
        sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hSupport := DFunLike.congr_fun
    (radialSupportProjection_comp_sourceInclusion lambda) u
  have hProjectionSq : radialSupportProjection lambda ∘L
      radialSupportProjection lambda = radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hIdempotent := DFunLike.congr_fun hProjectionSq
    (detectorOperator owner (sourceInclusion lambda u))
  simp only [ContinuousLinearMap.comp_apply] at hSupport hIdempotent
  simp only [radialComplementProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [hSupport, hIdempotent]
  abel

/-- The completed Hardy/prolate coordinate sees the compact root only through
the fixed source Sonin commutator `[W,R]`. -/
theorem sourceHardyProlateCompletedAnalysis_comp_detector_comp_sourceInclusion_eq_sourceBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceHardyProlateCompletedAnalysis lambda ∘L detectorOperator owner ∘L
        sourceInclusion lambda =
      sourceHardyProlateCompletedAnalysis lambda ∘L
        sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hSource : sourceSoninProjection lambda (sourceInclusion lambda u) =
      sourceInclusion lambda u := by
    rw [← sourceInclusion_comp_adjoint]
    change sourceInclusion lambda
      (((sourceInclusion lambda)† ∘L sourceInclusion lambda) u) = _
    rw [sourceInclusion_adjoint_comp_self]
    rfl
  have hKilled := DFunLike.congr_fun
    (sourceHardyProlateCompletedAnalysis_comp_sourceSoninProjection_eq_zero lambda)
    (detectorOperator owner (sourceInclusion lambda u))
  simp only [ContinuousLinearMap.comp_apply] at hSource hKilled
  simp only [sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hSource, hKilled]
  simp only [ContinuousLinearMap.zero_apply, sub_zero]

/-- The root-local right row.  Its outer and Sonin entries stay in the same
Hilbert `L2` row, so this definition does not authorize separate estimates. -/
noncomputable def finiteEulerCausalHardyProlateRowRootCommutatorRight
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteEulerCausalHardyProlateRowCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
      sourceHardyProlateCompletedAnalysisCarrier).symm.toContinuousLinearMap ∘L
    ((finiteEulerTransportOperator family ∘L radialComplementProjection lambda ∘L
        (detectorOperator owner ∘L radialSupportProjection lambda -
          radialSupportProjection lambda ∘L detectorOperator owner) ∘L
        sourceInclusion lambda).prod
      (sourceHardyProlateCompletedAnalysis lambda ∘L
        sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda))

/-- Moving the root into the two boundary commutators leaves the complete
right row unchanged. -/
theorem finiteEulerRowRight_comp_detector_comp_sourceInclusion_eq_rootCommutatorRight
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalHardyProlateRowRight lambda family ∘L detectorOperator owner ∘L
        sourceInclusion lambda =
      finiteEulerCausalHardyProlateRowRootCommutatorRight owner lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hOuter := DFunLike.congr_fun
    (radialComplement_comp_detector_comp_sourceInclusion_eq_detectorRadialCommutator
      owner lambda) u
  have hSonin := DFunLike.congr_fun
    (sourceHardyProlateCompletedAnalysis_comp_detector_comp_sourceInclusion_eq_sourceBoundary
      owner lambda) u
  simp only [ContinuousLinearMap.comp_apply] at hOuter hSonin
  simp only [finiteEulerCausalHardyProlateRowRight,
    finiteEulerCausalHardyProlateRowRootCommutatorRight,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [hOuter, hSonin]

/-- The literal target is the same completed row pairing after compact-root
locality has entered through the outer and Sonin commutators. -/
theorem target_eq_rootCommutatorRowCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      ((finiteEulerCausalHardyProlateRowLeft lambda family ∘L
        finiteEulerDualFrame lambda family).adjoint) ∘L
          finiteEulerCausalHardyProlateRowRootCommutatorRight owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootCorner]
  apply ContinuousLinearMap.ext
  intro u
  have hRow := DFunLike.congr_fun
    (finiteEulerRowRight_comp_detector_comp_sourceInclusion_eq_rootCommutatorRight
      owner lambda family) u
  simp only [ContinuousLinearMap.comp_apply] at hRow ⊢
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution] at hRow
  simp only [ContinuousLinearMap.comp_apply] at hRow
  rw [hRow]

/-- The root-local completed-row scalar that a future Gate 3U estimate must
bound without separating its two coordinates. -/
noncomputable def finiteEulerCausalHardyProlateRowRootCommutatorPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) : ℂ :=
  inner ℂ
    (finiteEulerCausalHardyProlateRowLeft lambda family
      (finiteEulerDualFrame lambda family x))
    (finiteEulerCausalHardyProlateRowRootCommutatorRight owner lambda family y)

/-- Every target coefficient is the root-local completed-row pairing. -/
theorem inner_target_eq_rootCommutatorPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family y) =
      finiteEulerCausalHardyProlateRowRootCommutatorPairing owner lambda family x y := by
  unfold finiteEulerCausalHardyProlateRowRootCommutatorPairing
  rw [target_eq_rootCommutatorRowCorner,
    ContinuousLinearMap.comp_apply]
  exact (finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family).adjoint_inner_right x _

/-- The ordinary target trace is the one signed diagonal series of root-local
completed-row pairings. -/
theorem ordinaryTraceAlong_target_eq_rootCommutatorPairing
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ∑' i, finiteEulerCausalHardyProlateRowRootCommutatorPairing owner lambda family
        (sourceBasis i) (sourceBasis i) := by
  unfold ordinaryTraceAlong
  apply tsum_congr
  intro i
  exact
    inner_target_eq_rootCommutatorPairing
      owner lambda family (sourceBasis i) (sourceBasis i)

end CCM24FiniteSGatePhysicalHardyProlateRowRootCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
