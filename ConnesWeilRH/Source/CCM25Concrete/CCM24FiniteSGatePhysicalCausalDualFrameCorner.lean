/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalMetricDetectorCorner
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

/-!
# Causal dual-frame form of the finite-S metric-detector corner

Proof 775 expresses the literal Gate target through the ambient Gram
`H_S = T_S† T_S`. The finite Euler transport preserves the actual radial
half-line, so the target admits a sharper source-specific form with only one
forward transport between the dual frame and the complete source complement.

The root remains on the right of that complete complement. In particular,
the result does not split the outer, reflected second-support, and prolate
branches before compact-root support can act.

This is an exact operator identity. It does not estimate the resulting
corner or prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalCausalDualFrameCorner

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCausalSupport
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGatePhysicalMetricDetectorCorner
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSRootCompletedFirstJet

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The adjoint dual frame reads only the actual radial-support component.
This is where the one-sided finite-Euler geometry enters the corner identity. -/
theorem finiteEulerDualFrame_adjoint_comp_radialSupport_eq_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerDualFrame lambda family)† ∘L radialSupportProjection lambda =
      (finiteEulerDualFrame lambda family)† := by
  have hFrame :
      (finiteEulerFrame lambda family)† ∘L radialSupportProjection lambda =
        (finiteEulerFrame lambda family)† := by
    have h := congrArg ContinuousLinearMap.adjoint
      (radialSupportProjection_comp_finiteEulerFrame lambda family)
    simpa only [ContinuousLinearMap.adjoint_comp,
      (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]
      using h
  rw [finiteEulerDualFrame, ContinuousLinearMap.adjoint_comp,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      finiteEulerGramInv lambda family (operator u)) hFrame
  simpa only [ContinuousLinearMap.comp_apply] using hu

/-- Before the radial projection is inserted, the dual frame followed by one
forward Euler transport is exactly the Gram-weighted source readback. -/
theorem finiteEulerDualFrame_adjoint_comp_transport_eq_ambientGramReadback
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerDualFrame lambda family)† ∘L
        finiteEulerTransportOperator family =
      finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
        finiteEulerAmbientGram family := by
  rw [finiteEulerDualFrame, ContinuousLinearMap.adjoint_comp,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq,
    finiteEulerFrame_eq_transport_comp_inclusion,
    ContinuousLinearMap.adjoint_comp, finiteEulerTransportOperator,
    finiteEulerAmbientGram]
  rfl

/-- The current Gate target is one causal dual-frame corner with the compact
root at the end of the complete source complement. The projection between
the dual frame and transport is the actual invariant radial half-line. -/
theorem finiteEulerTargetCommutatorResponse_eq_causalDualFrameRootCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      (finiteEulerDualFrame lambda family)† ∘L
        radialSupportProjection lambda ∘L
          finiteEulerTransportOperator family ∘L
            sourceSoninComplementProjection lambda ∘L
              (rootConvolution owner)† ∘L rootConvolution owner ∘L
                sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_singleMetricDetectorCorner,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  let z := sourceSoninComplementProjection lambda
    (((rootConvolution owner)†)
      (rootConvolution owner (sourceInclusion lambda u)))
  have hReadback := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator z)
    (finiteEulerDualFrame_adjoint_comp_transport_eq_ambientGramReadback
      lambda family)
  have hSupport := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (finiteEulerTransportOperator family z))
    (finiteEulerDualFrame_adjoint_comp_radialSupport_eq_self lambda family)
  simp only [ContinuousLinearMap.comp_apply] at hReadback hSupport
  simpa only [z, ContinuousLinearMap.comp_apply] using hReadback.symm.trans
    hSupport.symm

end CCM24FiniteSGatePhysicalCausalDualFrameCorner
end CCM25Concrete
end Source
end ConnesWeilRH
