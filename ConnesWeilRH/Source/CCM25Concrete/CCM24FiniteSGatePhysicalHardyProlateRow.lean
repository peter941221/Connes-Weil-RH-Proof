/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateGram
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# One-row factorization of the causal Hardy--prolate bracket

Proof 778 makes the source quotient band one positive Hardy/prolate Gram.
This module keeps that Gram together with the causal outer crossing in one
rectangular `X^* Y` row.  The compact root remains on the right of `Y`.

The row is an exact operator organization only.  In particular, downstream
arguments must not bound its three coordinates separately: that would discard
the signed cancellation retained by the single row pairing.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateRow

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSBandTrace
open CCM24FiniteSGatePhysicalCausalCompletedBracket
open CCM24FiniteSGatePhysicalCausalDualFrameCorner
open CCM24FiniteSGatePhysicalHardyProlateGram
open CCM24FiniteSGatePhysicalMetricDetectorCorner
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The Hilbert `L2` sum of the actual Hardy leakage and prolate analysis
legs.  This is deliberately not the ordinary product norm. -/
noncomputable abbrev sourceHardyProlateCompletedAnalysisCarrier :=
  WithLp 2 (finiteSCarrier × finiteSCarrier)

/-- The joint source analysis column for Proof 778's two Gram legs. -/
noncomputable def sourceHardyProlateCompletedAnalysis
  (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] sourceHardyProlateCompletedAnalysisCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier finiteSCarrier).symm.toContinuousLinearMap ∘L
    (sourceHardyFourierLeakageFactor lambda).prod
      (sourceProlateHilbertSchmidtFactor lambda)

/-- Proof 778's positive source band is the Gram of one joint analysis
column, rather than two independently owned estimates. -/
theorem sourceHardyProlateCompletedAnalysis_adjoint_comp_self_eq_completedGram
    (lambda : CCM24SoninScale) :
    (sourceHardyProlateCompletedAnalysis lambda).adjoint ∘L
        sourceHardyProlateCompletedAnalysis lambda =
      sourceHardyProlateCompletedGram lambda := by
  apply ContinuousLinearMap.ext
  intro u
  apply (ext_iff_inner_left ℂ).mpr
  intro z
  rw [ContinuousLinearMap.comp_apply,
    (sourceHardyProlateCompletedAnalysis lambda).adjoint_inner_right]
  unfold sourceHardyProlateCompletedAnalysis sourceHardyProlateCompletedGram
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  change inner ℂ
    ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier finiteSCarrier).symm
      (sourceHardyFourierLeakageFactor lambda z,
        sourceProlateHilbertSchmidtFactor lambda z))
    ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier finiteSCarrier).symm
      (sourceHardyFourierLeakageFactor lambda u,
        sourceProlateHilbertSchmidtFactor lambda u)) = _
  rw [WithLp.prodContinuousLinearEquiv_symm_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.prod_inner_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right]

/-- The Hilbert row carrier whose first coordinate is the causal outer
crossing and whose second coordinate is the completed Hardy/prolate analysis.
-/
noncomputable abbrev finiteEulerCausalHardyProlateRowCarrier :=
  WithLp 2 (finiteSCarrier × sourceHardyProlateCompletedAnalysisCarrier)

/-- The left row keeps the Euler adjoint on the completed Gram coordinate. -/
noncomputable def finiteEulerCausalHardyProlateRowLeft
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteEulerCausalHardyProlateRowCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
      sourceHardyProlateCompletedAnalysisCarrier).symm.toContinuousLinearMap ∘L
    (radialSupportProjection lambda).prod
      (sourceHardyProlateCompletedAnalysis lambda ∘L
        (finiteEulerTransportOperator family).adjoint)

/-- The right row holds the causal outer input and the unchanged completed
Hardy/prolate analysis. -/
noncomputable def finiteEulerCausalHardyProlateRowRight
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteEulerCausalHardyProlateRowCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
      sourceHardyProlateCompletedAnalysisCarrier).symm.toContinuousLinearMap ∘L
    (finiteEulerTransportOperator family ∘L radialComplementProjection lambda).prod
      (sourceHardyProlateCompletedAnalysis lambda)

/-- The complete causal bracket is one `X^* Y` product.  The proof uses the
Hilbert `L2` row inner product; no triangle inequality is taken. -/
theorem finiteEulerCausalHardyProlateRow_adjoint_comp_eq_causalCompleted
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerCausalHardyProlateRowLeft lambda family).adjoint ∘L
        finiteEulerCausalHardyProlateRowRight lambda family =
      finiteEulerCausalHardyProlateCompletedSoninComplement lambda family := by
  calc
    (finiteEulerCausalHardyProlateRowLeft lambda family).adjoint ∘L
        finiteEulerCausalHardyProlateRowRight lambda family =
      (radialSupportProjection lambda).adjoint ∘L
          finiteEulerTransportOperator family ∘L radialComplementProjection lambda +
        finiteEulerTransportOperator family ∘L
          (sourceHardyProlateCompletedAnalysis lambda).adjoint ∘L
            sourceHardyProlateCompletedAnalysis lambda := by
        apply ContinuousLinearMap.ext
        intro u
        apply (ext_iff_inner_left ℂ).mpr
        intro z
        rw [ContinuousLinearMap.comp_apply,
          (finiteEulerCausalHardyProlateRowLeft lambda family).adjoint_inner_right]
        dsimp only [finiteEulerCausalHardyProlateRowLeft,
          finiteEulerCausalHardyProlateRowRight]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
        change inner ℂ
          ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
            sourceHardyProlateCompletedAnalysisCarrier).symm
            (radialSupportProjection lambda z,
              sourceHardyProlateCompletedAnalysis lambda
                ((finiteEulerTransportOperator family).adjoint z)))
          ((WithLp.prodContinuousLinearEquiv 2 ℂ finiteSCarrier
            sourceHardyProlateCompletedAnalysisCarrier).symm
            (finiteEulerTransportOperator family
                (radialComplementProjection lambda u),
              sourceHardyProlateCompletedAnalysis lambda u)) = _
        rw [WithLp.prodContinuousLinearEquiv_symm_apply,
          WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.prod_inner_apply]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          inner_add_right]
        rw [← (radialSupportProjection lambda).adjoint_inner_right z
          (finiteEulerTransportOperator family
            (radialComplementProjection lambda u))]
        rw [← (sourceHardyProlateCompletedAnalysis lambda).adjoint_inner_right
          ((finiteEulerTransportOperator family).adjoint z)
          (sourceHardyProlateCompletedAnalysis lambda u)]
        rw [(finiteEulerTransportOperator family).adjoint_inner_left]
    _ = radialSupportProjection lambda ∘L finiteEulerTransportOperator family ∘L
          radialComplementProjection lambda +
        finiteEulerTransportOperator family ∘L
          sourceHardyProlateCompletedGram lambda := by
        rw [(radialSupportProjection_isStarProjection lambda)
          |>.isSelfAdjoint.adjoint_eq,
          sourceHardyProlateCompletedAnalysis_adjoint_comp_self_eq_completedGram]
    _ = finiteEulerCausalHardyProlateCompletedSoninComplement lambda family := rfl

/-- The literal finite-S Gate target is a single completed-row/root corner.
The root remains after the full row product. -/
theorem finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      ((finiteEulerCausalHardyProlateRowLeft lambda family ∘L
        finiteEulerDualFrame lambda family).adjoint) ∘L
          finiteEulerCausalHardyProlateRowRight lambda family ∘L
            (rootConvolution owner).adjoint ∘L rootConvolution owner ∘L
              sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRootCorner,
    ← finiteEulerCausalHardyProlateRow_adjoint_comp_eq_causalCompleted,
    ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The row/root scalar pairing which reads the literal Gate target without
opening its outer, Hardy, or prolate coordinates. -/
noncomputable def finiteEulerCausalHardyProlateRowRootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) : ℂ :=
  inner ℂ
    (finiteEulerCausalHardyProlateRowLeft lambda family
      (finiteEulerDualFrame lambda family x))
    (finiteEulerCausalHardyProlateRowRight lambda family
      ((rootConvolution owner).adjoint
        (rootConvolution owner (sourceInclusion lambda y))))

/-- Every matrix coefficient of the literal target is the one completed
row/root pairing. -/
theorem inner_finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x y : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family y) =
      finiteEulerCausalHardyProlateRowRootPairing owner lambda family x y := by
  unfold finiteEulerCausalHardyProlateRowRootPairing
  rw [finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootCorner,
    ContinuousLinearMap.comp_apply]
  exact (finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family).adjoint_inner_right x _

/-- The ordinary target trace is one signed diagonal series of completed
row/root pairings.  This is the exact scalar which a future root-relative
Toeplitz or Wiener--Hopf estimate must control. -/
theorem ordinaryTraceAlong_finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootPairing
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ∑' i, finiteEulerCausalHardyProlateRowRootPairing owner lambda family
        (sourceBasis i) (sourceBasis i) := by
  unfold ordinaryTraceAlong
  apply tsum_congr
  intro i
  exact inner_finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRowRootPairing
    owner lambda family (sourceBasis i) (sourceBasis i)

end CCM24FiniteSGatePhysicalHardyProlateRow
end CCM25Concrete
end Source
end ConnesWeilRH
