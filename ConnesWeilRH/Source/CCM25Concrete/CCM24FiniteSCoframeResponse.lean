/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInverseMetric

/-!
# Biorthogonal coframe form of the finite-S band response

The Gram inverse is kept inside the metric coframe
`D = (T†T) J (J†T†TJ)⁻¹ = T†F`.  The coframe is biorthogonal to the
source Sonin inclusion, and its source-Sonin compression is exactly that
inclusion.  Consequently the route response is one completed commutator
paired with the off-Sonin coframe leakage.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCoframeResponse

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The inverse-metric source coframe `D = H J G⁻¹`. -/
noncomputable def finiteEulerMetricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
    finiteEulerGramInv lambda family

theorem finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      (finiteEulerTransportOperator family)† ∘L
        finiteEulerDualFrame lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Biorthogonality: `J†D=I` on the source Sonin carrier. -/
theorem sourceInclusionAdjoint_comp_metricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L finiteEulerMetricCoframe lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame]
  calc
    (sourceInclusion lambda)† ∘L
          ((finiteEulerTransportOperator family)† ∘L
            finiteEulerDualFrame lambda family) =
        (finiteEulerFrame lambda family)† ∘L
          finiteEulerDualFrame lambda family := by
      apply ContinuousLinearMap.ext
      intro u
      rw [finiteEulerFrame_eq_transport_comp_inclusion,
        finiteEulerTransportOperator,
        ContinuousLinearMap.adjoint_comp]
      rfl
    _ = _ := frameAdjoint_comp_dualFrame lambda family

theorem metricCoframeAdjoint_comp_sourceInclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerMetricCoframe lambda family)† ∘L
        sourceInclusion lambda =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have h := congrArg ContinuousLinearMap.adjoint
    (sourceInclusionAdjoint_comp_metricCoframe lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id] using h

/-- Compressing the metric coframe back to the source Sonin space deletes
the Gram correction: `R₀D=J`. -/
theorem sourceSoninProjection_comp_metricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        finiteEulerMetricCoframe lambda family =
      sourceInclusion lambda := by
  rw [← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  change sourceInclusion lambda
      (((sourceInclusion lambda)†) (finiteEulerMetricCoframe lambda family u)) =
    sourceInclusion lambda u
  rw [show ((sourceInclusion lambda)†)
      (finiteEulerMetricCoframe lambda family u) = u by
    exact congrFun (congrArg DFunLike.coe
      (sourceInclusionAdjoint_comp_metricCoframe lambda family)) u]

/-- The off-Sonin part of the coframe.  This is a completed boundary object;
neither `C_g J` nor `C_g A` is asserted Hilbert--Schmidt. -/
noncomputable def sourceSoninCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
    finiteEulerMetricCoframe lambda family

theorem sourceSoninCoframeLeakage_eq_coframe_sub_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCoframeLeakage lambda family =
      finiteEulerMetricCoframe lambda family - sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceSoninCoframeLeakage, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [show sourceSoninProjection lambda
      (finiteEulerMetricCoframe lambda family u) = sourceInclusion lambda u by
    exact congrFun (congrArg DFunLike.coe
      (sourceSoninProjection_comp_metricCoframe lambda family)) u]

/-- The completed-commutator owner reduces to one detector applied to the
off-Sonin coframe leakage.  This is an exact operator identity, not a trace
cycle and not a uniform estimate. -/
theorem sourceBandGramResponse_eq_neg_detector_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
        sourceSoninCoframeLeakage lambda family := by
  rw [sourceBandGramResponse_eq_completedCommutator]
  change (sourceInclusion lambda)† ∘L
      sourceBoundaryCommutator owner lambda ∘L
      finiteEulerMetricCoframe lambda family = _
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  rw [show sourceSoninProjection lambda
      (finiteEulerMetricCoframe lambda family u) = sourceInclusion lambda u by
    exact congrFun (congrArg DFunLike.coe
      (sourceSoninProjection_comp_metricCoframe lambda family)) u]
  rw [map_sub]
  rw [show ((sourceInclusion lambda)†)
      (sourceSoninProjection lambda
        (detectorOperator owner (finiteEulerMetricCoframe lambda family u))) =
      ((sourceInclusion lambda)†)
        (detectorOperator owner (finiteEulerMetricCoframe lambda family u)) by
    exact congrFun (congrArg DFunLike.coe
      (sourceInclusionAdjoint_comp_sourceProjection lambda)) _]
  rw [sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  abel

end CCM24FiniteSCoframeResponse
end CCM25Concrete
end Source
end ConnesWeilRH
