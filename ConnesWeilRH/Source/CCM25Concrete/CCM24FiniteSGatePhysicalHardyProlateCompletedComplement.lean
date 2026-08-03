/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateRowRootCommutator
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Completed-complement form of the root-local Hardy--prolate row

Proof 780 puts the compact root into the outer and Sonin commutator
coordinates of one completed `L2` row.  This module identifies those two
coordinates as a single source-Sonin boundary commutator after the actual
Hardy/prolate complement analysis.  The row remains packed throughout.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateCompletedComplement

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
open CCM24FiniteSGatePhysicalHardyProlateRowRootCommutator
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete analysis of the orthogonal complement of the source Sonin
space.  Its first coordinate is the outer half-line complement and its second
coordinate is the joint Hardy/prolate analysis. -/
noncomputable def sourceHardyProlateComplementAnalysis
    (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteEulerCausalHardyProlateRowCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
      sourceHardyProlateCompletedAnalysisCarrier).symm.toContinuousLinearMap ∘L
    (radialComplementProjection lambda).prod
      (sourceHardyProlateCompletedAnalysis lambda)

private theorem radialComplementProjection_adjoint_eq_self
    (lambda : CCM24SoninScale) :
    (radialComplementProjection lambda).adjoint = radialComplementProjection lambda := by
  unfold radialComplementProjection
  rw [map_sub, ContinuousLinearMap.adjoint_id,
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]

private theorem radialComplementProjection_comp_self
    (lambda : CCM24SoninScale) :
    radialComplementProjection lambda ∘L radialComplementProjection lambda =
      radialComplementProjection lambda := by
  have hE : radialSupportProjection lambda * radialSupportProjection lambda =
      radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  unfold radialComplementProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (1 - radialSupportProjection lambda) *
        (1 - radialSupportProjection lambda) =
      1 - radialSupportProjection lambda by
    calc
      (1 - radialSupportProjection lambda) *
          (1 - radialSupportProjection lambda) =
        1 - radialSupportProjection lambda - radialSupportProjection lambda +
          radialSupportProjection lambda * radialSupportProjection lambda := by
          noncomm_ring
      _ = 1 - radialSupportProjection lambda := by
        rw [hE]
        abel

/-- The two coordinates are an exact Gram factor of the full source Sonin
complement.  This is the identity that permits them to share one boundary
commutator below. -/
theorem sourceHardyProlateComplementAnalysis_adjoint_comp_self_eq_sourceSoninComplement
    (lambda : CCM24SoninScale) :
    (sourceHardyProlateComplementAnalysis lambda).adjoint ∘L
        sourceHardyProlateComplementAnalysis lambda =
      sourceSoninComplementProjection lambda := by
  calc
    (sourceHardyProlateComplementAnalysis lambda).adjoint ∘L
        sourceHardyProlateComplementAnalysis lambda =
      (radialComplementProjection lambda).adjoint ∘L
          radialComplementProjection lambda +
        (sourceHardyProlateCompletedAnalysis lambda).adjoint ∘L
          sourceHardyProlateCompletedAnalysis lambda := by
        apply ContinuousLinearMap.ext
        intro u
        apply (ext_iff_inner_left ℂ).mpr
        intro z
        rw [ContinuousLinearMap.comp_apply,
          (sourceHardyProlateComplementAnalysis lambda).adjoint_inner_right]
        dsimp only [sourceHardyProlateComplementAnalysis]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
        change inner ℂ
          ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
            sourceHardyProlateCompletedAnalysisCarrier).symm
            (radialComplementProjection lambda z,
              sourceHardyProlateCompletedAnalysis lambda z))
          ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
            sourceHardyProlateCompletedAnalysisCarrier).symm
            (radialComplementProjection lambda u,
              sourceHardyProlateCompletedAnalysis lambda u)) = _
        rw [WithLp.prodContinuousLinearEquiv_symm_apply,
          WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.prod_inner_apply]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          inner_add_right]
        rw [← (radialComplementProjection lambda).adjoint_inner_right z
          (radialComplementProjection lambda u)]
        rw [← (sourceHardyProlateCompletedAnalysis lambda).adjoint_inner_right z
          (sourceHardyProlateCompletedAnalysis lambda u)]
    _ = radialComplementProjection lambda +
        sourceHardyProlateCompletedGram lambda := by
      rw [radialComplementProjection_adjoint_eq_self,
        radialComplementProjection_comp_self,
        sourceHardyProlateCompletedAnalysis_adjoint_comp_self_eq_completedGram]
    _ = sourceSoninComplementProjection lambda := by
      rw [sourceHardyProlateCompletedGram_eq_sourceBandProjection]
      unfold sourceSoninComplementProjection radialComplementProjection
        sourceBandProjection
      abel

/-- The completed complement analysis kills the source Sonin range before any
coordinate is exposed. -/
theorem sourceHardyProlateComplementAnalysis_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) :
    sourceHardyProlateComplementAnalysis lambda ∘L sourceSoninProjection lambda =
      0 := by
  apply ContinuousLinearMap.ext
  intro u
  change sourceHardyProlateComplementAnalysis lambda
      (sourceSoninProjection lambda u) = 0
  change sourceSoninProjection lambda u ∈
    (sourceHardyProlateComplementAnalysis lambda).ker
  rw [← ContinuousLinearMap.ker_adjoint_comp_self]
  change ((sourceHardyProlateComplementAnalysis lambda).adjoint ∘L
      sourceHardyProlateComplementAnalysis lambda)
      (sourceSoninProjection lambda u) = 0
  rw [sourceHardyProlateComplementAnalysis_adjoint_comp_self_eq_sourceSoninComplement]
  have hR : sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
      sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hRAt := DFunLike.congr_fun hR u
  simp only [ContinuousLinearMap.comp_apply] at hRAt
  simp only [sourceSoninComplementProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hRAt]
  abel

/-- After the complete complement analysis, the compact root enters through
one actual source-Sonin commutator `[W,R]`, with no separate outer estimate. -/
theorem sourceHardyProlateComplementAnalysis_comp_detector_comp_sourceInclusion_eq_sourceBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceHardyProlateComplementAnalysis lambda ∘L detectorOperator owner ∘L
        sourceInclusion lambda =
      sourceHardyProlateComplementAnalysis lambda ∘L
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
    (sourceHardyProlateComplementAnalysis_comp_sourceSoninProjection_eq_zero lambda)
    (detectorOperator owner (sourceInclusion lambda u))
  simp only [ContinuousLinearMap.comp_apply] at hSource hKilled
  simp only [sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hSource, hKilled]
  simpa only [ContinuousLinearMap.zero_apply] using
    (sub_zero (sourceHardyProlateComplementAnalysis lambda
      (detectorOperator owner (sourceInclusion lambda u)))).symm

/-- Apply the finite Euler transport only to the outer coordinate of the
completed complement analysis. -/
noncomputable def finiteEulerCausalHardyProlateTransportLift
    (_lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalHardyProlateRowCarrier →L[ℂ]
      finiteEulerCausalHardyProlateRowCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
      sourceHardyProlateCompletedAnalysisCarrier).symm.toContinuousLinearMap ∘L
    ((finiteEulerTransportOperator family).prodMap
      (ContinuousLinearMap.id ℂ sourceHardyProlateCompletedAnalysisCarrier)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
        sourceHardyProlateCompletedAnalysisCarrier).toContinuousLinearMap

/-- The pre-root right row is exactly the transported complete-complement
analysis. -/
theorem finiteEulerCausalHardyProlateRowRight_eq_transportLift_comp_complementAnalysis
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalHardyProlateRowRight lambda family =
      finiteEulerCausalHardyProlateTransportLift lambda family ∘L
        sourceHardyProlateComplementAnalysis lambda := by
  apply ContinuousLinearMap.ext
  intro u
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
    sourceHardyProlateCompletedAnalysisCarrier).injective
  change
    (finiteEulerTransportOperator family (radialComplementProjection lambda u),
      sourceHardyProlateCompletedAnalysis lambda u) =
      ((finiteEulerTransportOperator family).prodMap
        (ContinuousLinearMap.id ℂ sourceHardyProlateCompletedAnalysisCarrier))
        (radialComplementProjection lambda u,
          sourceHardyProlateCompletedAnalysis lambda u)
  rfl

/-- Proof 780's root-local right row is one transported completed-complement
analysis of the actual source boundary commutator. -/
theorem finiteEulerCausalHardyProlateRowRootCommutatorRight_eq_completeBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalHardyProlateRowRootCommutatorRight owner lambda family =
      finiteEulerCausalHardyProlateTransportLift lambda family ∘L
        sourceHardyProlateComplementAnalysis lambda ∘L
          sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hRoot := DFunLike.congr_fun
    (finiteEulerRowRight_comp_detector_comp_sourceInclusion_eq_rootCommutatorRight
      owner lambda family) u
  have hLift := DFunLike.congr_fun
    (finiteEulerCausalHardyProlateRowRight_eq_transportLift_comp_complementAnalysis
      lambda family)
    (detectorOperator owner (sourceInclusion lambda u))
  have hBoundary := DFunLike.congr_fun
    (sourceHardyProlateComplementAnalysis_comp_detector_comp_sourceInclusion_eq_sourceBoundary
      owner lambda) u
  simp only [ContinuousLinearMap.comp_apply] at hRoot hLift hBoundary ⊢
  calc
    finiteEulerCausalHardyProlateRowRootCommutatorRight owner lambda family u =
        finiteEulerCausalHardyProlateRowRight lambda family
          (detectorOperator owner (sourceInclusion lambda u)) := hRoot.symm
    _ = finiteEulerCausalHardyProlateTransportLift lambda family
          (sourceHardyProlateComplementAnalysis lambda
            (detectorOperator owner (sourceInclusion lambda u))) := hLift
    _ = finiteEulerCausalHardyProlateTransportLift lambda family
          (sourceHardyProlateComplementAnalysis lambda
            (sourceBoundaryCommutator owner lambda (sourceInclusion lambda u))) := by
          rw [hBoundary]

/-- The literal target is a single completed-complement row paired against
the complete source boundary commutator. -/
theorem target_eq_completeBoundaryRowCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      ((finiteEulerCausalHardyProlateRowLeft lambda family ∘L
        finiteEulerDualFrame lambda family).adjoint) ∘L
          finiteEulerCausalHardyProlateTransportLift lambda family ∘L
            sourceHardyProlateComplementAnalysis lambda ∘L
              sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  rw [target_eq_rootCommutatorRowCorner,
    finiteEulerCausalHardyProlateRowRootCommutatorRight_eq_completeBoundary]

/-- The one signed root-local boundary pairing which remains after the outer
and Hardy/prolate coordinates have been reassembled through `[W,R]`. -/
noncomputable def finiteEulerCausalHardyProlateCompleteBoundaryPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) : ℂ :=
  inner ℂ
    (finiteEulerCausalHardyProlateRowLeft lambda family
      (finiteEulerDualFrame lambda family x))
    (finiteEulerCausalHardyProlateTransportLift lambda family
      (sourceHardyProlateComplementAnalysis lambda
        (sourceBoundaryCommutator owner lambda (sourceInclusion lambda y))))

/-- Every target coefficient is the one completed-complement boundary
pairing. -/
theorem inner_target_eq_completeBoundaryPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family y) =
      finiteEulerCausalHardyProlateCompleteBoundaryPairing owner lambda family x y := by
  unfold finiteEulerCausalHardyProlateCompleteBoundaryPairing
  rw [target_eq_completeBoundaryRowCorner,
    ContinuousLinearMap.comp_apply]
  exact (finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family).adjoint_inner_right x _

/-- The ordinary target trace is the one signed diagonal series of completed
complement boundary pairings. -/
theorem ordinaryTraceAlong_target_eq_completeBoundaryPairing
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ∑' i, finiteEulerCausalHardyProlateCompleteBoundaryPairing owner lambda family
        (sourceBasis i) (sourceBasis i) := by
  unfold ordinaryTraceAlong
  apply tsum_congr
  intro i
  exact inner_target_eq_completeBoundaryPairing
    owner lambda family (sourceBasis i) (sourceBasis i)

end CCM24FiniteSGatePhysicalHardyProlateCompletedComplement
end CCM25Concrete
end Source
end ConnesWeilRH
