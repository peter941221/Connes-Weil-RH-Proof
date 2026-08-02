/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointContractionGuard

/-!
# Channel split for the physical cancellation target

Proof 723 leaves one same-object cancellation target.  This file splits the
completed physical leakage into its radial-complement channel and its source
band channel.  The split is algebraic; it does not prove either channel
vanishes.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalCancellationChannelSplit

open CC20Concrete
open CCM24FiniteSCoframeResponse
open CCM24FiniteSEndpointContractionGuard
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The metric coframe projected to the source radial-Sonin band. -/
noncomputable def sourceBandMetricCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceBandProjection lambda ∘L finiteEulerMetricCoframe lambda family

/-- The second-support and prolate pieces recombine to the source-band
projection of the metric coframe. -/
theorem sourceSecondSupport_add_prolateCoframeLeakage_eq_bandMetricCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSecondSupportCoframeLeakage lambda family +
        sourceProlateCoframeLeakage lambda family =
      sourceBandMetricCoframeLeakage lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hradial : radialSupportProjection lambda
      (radialSupportProjection lambda (finiteEulerMetricCoframe lambda family u)) =
      radialSupportProjection lambda (finiteEulerMetricCoframe lambda family u) := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
      (Submodule.starProjection_apply_mem _ _)
  simp only [sourceSecondSupportCoframeLeakage, sourceProlateCoframeLeakage,
    sourceBandMetricCoframeLeakage, sourceBandProjection,
    sourceProlateRemainder, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hradial]
  abel

/-- The completed physical leakage is the sum of the outer radial leakage and
the source-band metric leakage. -/
theorem sourcePhysicalCoframeLeakage_eq_outer_add_bandMetric
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourcePhysicalCoframeLeakage lambda family =
      sourceOuterCoframeLeakage lambda family +
        sourceBandMetricCoframeLeakage lambda family := by
  change sourceOuterCoframeLeakage lambda family +
      sourceSecondSupportCoframeLeakage lambda family +
        sourceProlateCoframeLeakage lambda family =
    sourceOuterCoframeLeakage lambda family +
      sourceBandMetricCoframeLeakage lambda family
  rw [← sourceSecondSupport_add_prolateCoframeLeakage_eq_bandMetricCoframeLeakage
    lambda family]
  abel

/-- The Proof 723 cancellation target, rewritten as an outer radial channel
plus a source-band channel. -/
theorem sourceActualBandForward_add_physicalLeakage_eq_outer_add_forward_add_bandMetric
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandForwardCoframe lambda family +
        sourcePhysicalCoframeLeakage lambda family =
      sourceOuterCoframeLeakage lambda family +
        (sourceActualBandForwardCoframe lambda family +
          sourceBandMetricCoframeLeakage lambda family) := by
  rw [sourcePhysicalCoframeLeakage_eq_outer_add_bandMetric]
  abel

/-- Endpoint contraction is equivalently the vanishing of the recombined outer
radial channel and source-band channel.  This is still one same-object
equation, not two independent estimates. -/
theorem
    norm_sourceActualBandForwardEndpointCoframe_le_one_iff_outer_add_forward_add_bandMetric_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1 ↔
      sourceOuterCoframeLeakage lambda family +
          (sourceActualBandForwardCoframe lambda family +
            sourceBandMetricCoframeLeakage lambda family) = 0 := by
  rw [norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero,
    sourceActualBandForward_add_physicalLeakage_eq_outer_add_forward_add_bandMetric]

end CCM24FiniteSPhysicalCancellationChannelSplit
end CCM25Concrete
end Source
end ConnesWeilRH
