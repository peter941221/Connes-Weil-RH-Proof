/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse

/-!
# Physical outer/second-support/prolate coframe leakage

This module expands the off-Sonin coframe only after it has been completed.
The outer boundary, second support, and prolate correction remain assembled in
one operator.  No branchwise Schatten or norm estimate is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalLeakage

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCoframeResponse

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The completed outer radial-boundary leakage. -/
noncomputable def sourceOuterCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
    finiteEulerMetricCoframe lambda family

/-- The completed second-support leakage, with both radial projections kept. -/
noncomputable def sourceSecondSupportCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
    (ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceFourierSupportProjection lambda) ∘L
    radialSupportProjection lambda ∘L
    finiteEulerMetricCoframe lambda family

/-- The prolate correction on the same coframe. -/
noncomputable def sourceProlateCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceProlateRemainder lambda ∘L finiteEulerMetricCoframe lambda family

/-- The physical three-branch leakage.  Keep this sum whole before applying
compact support or an absolute value. -/
noncomputable def sourcePhysicalCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceOuterCoframeLeakage lambda family +
    sourceSecondSupportCoframeLeakage lambda family +
    sourceProlateCoframeLeakage lambda family

theorem sourceSoninCoframeLeakage_eq_physical
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCoframeLeakage lambda family =
      sourcePhysicalCoframeLeakage lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hradial : radialSupportProjection lambda
      (radialSupportProjection lambda (finiteEulerMetricCoframe lambda family u)) =
      radialSupportProjection lambda (finiteEulerMetricCoframe lambda family u) := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
      (Submodule.starProjection_apply_mem _ _)
  simp only [sourceSoninCoframeLeakage, sourcePhysicalCoframeLeakage,
    sourceOuterCoframeLeakage, sourceSecondSupportCoframeLeakage,
    sourceProlateCoframeLeakage, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [sourceSoninProjection_eq_compression_sub_prolate]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  rw [hradial]
  abel

/-- Final exact Gate 3U owner after the coframe and physical-boundary
collapses.  This theorem still does not provide trace legality or a uniform
bound. -/
theorem sourceBandGramResponse_eq_neg_physical_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSBandTrace.sourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
        sourcePhysicalCoframeLeakage lambda family := by
  rw [sourceBandGramResponse_eq_neg_detector_leakage,
    sourceSoninCoframeLeakage_eq_physical]

end CCM24FiniteSPhysicalLeakage
end CCM25Concrete
end Source
end ConnesWeilRH
