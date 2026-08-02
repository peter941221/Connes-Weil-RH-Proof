/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationChannelSplit

/-!
# Endpoint split for the physical cancellation target

Proof 724 rewrote the physical leakage as an outer radial channel plus a
source-band metric channel. This file removes the remaining artificial split
between the raw forward coframe and the source-band metric coframe: their sum
is the source-band projection of the full endpoint coframe.

No cancellation, sign, norm estimate, Gate 3U bound, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalCancellationEndpointSplit

open CC20Concrete
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSCoframeResponse
open CCM24FiniteSEndpointContractionGuard
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSPhysicalCancellationChannelSplit
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRootCompletedFirstJet

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The radial complement cannot see the raw forward coframe because that
coframe already lands in the source radial-Sonin band. -/
theorem radialComplement_comp_sourceActualBandForwardCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
        sourceActualBandForwardCoframe lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hradial := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (normalizedFiniteEulerInverse family (sourceInclusion lambda u)))
    (radialSupportProjection_comp_sourceBandProjection_eq_self lambda)
  simp only [sourceActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hradial ⊢
  rw [hradial, sub_self]

/-- The outer radial leakage is the radial-complement projection of the full
endpoint coframe. The forward part drops out before any estimate is taken. -/
theorem sourceOuterCoframeLeakage_eq_radialComplement_comp_endpoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOuterCoframeLeakage lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L
        sourceActualBandForwardEndpointCoframe lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hforward :=
    congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator u)
      (radialComplement_comp_sourceActualBandForwardCoframe_eq_zero
        lambda family)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hforward
  have hradialForward :
      radialSupportProjection lambda
          (sourceActualBandForwardCoframe lambda family u) =
        sourceActualBandForwardCoframe lambda family u := by
    exact (sub_eq_zero.mp hforward).symm
  simp only [sourceOuterCoframeLeakage,
    sourceActualBandForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hradialForward]
  abel

/-- The forward coframe and the band-projected metric coframe are exactly the
source-band projection of the full endpoint coframe. -/
theorem sourceBandProjection_comp_endpoint_eq_forward_add_bandMetric
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L
        sourceActualBandForwardEndpointCoframe lambda family =
      sourceActualBandForwardCoframe lambda family +
        sourceBandMetricCoframeLeakage lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hBandIdem : IsIdempotentElem (sourceBandProjection lambda) :=
    (sourceBandProjection_isStarProjection lambda).isIdempotentElem
  have hband := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (normalizedFiniteEulerInverse family (sourceInclusion lambda u)))
    hBandIdem
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at hband
  simp only [sourceActualBandForwardEndpointCoframe,
    sourceActualBandForwardCoframe, sourceBandMetricCoframeLeakage,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hband]

/-- Proof 724's active target is the outer radial endpoint channel plus the
source-band endpoint channel. -/
theorem sourceOuter_add_forward_add_bandMetric_eq_outer_add_endpointBand
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOuterCoframeLeakage lambda family +
        (sourceActualBandForwardCoframe lambda family +
          sourceBandMetricCoframeLeakage lambda family) =
      sourceOuterCoframeLeakage lambda family +
        sourceBandProjection lambda ∘L
          sourceActualBandForwardEndpointCoframe lambda family := by
  rw [sourceBandProjection_comp_endpoint_eq_forward_add_bandMetric]

/-- The endpoint-channel target is exactly the complete off-Sonin leakage of
the endpoint coframe. This is the hard object that must vanish. -/
theorem sourceOuter_add_endpointBand_eq_combinedCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOuterCoframeLeakage lambda family +
        sourceBandProjection lambda ∘L
          sourceActualBandForwardEndpointCoframe lambda family =
      sourceActualBandCombinedCoframeLeakage lambda family := by
  rw [sourceOuterCoframeLeakage_eq_radialComplement_comp_endpoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceActualBandCombinedCoframeLeakage, sourceBandProjection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  abel

/-- Endpoint contraction is equivalently the vanishing of the two endpoint
channels, namely radial complement plus source band. -/
theorem
    norm_sourceActualBandForwardEndpointCoframe_le_one_iff_outer_add_endpointBand_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1 ↔
      sourceOuterCoframeLeakage lambda family +
          sourceBandProjection lambda ∘L
            sourceActualBandForwardEndpointCoframe lambda family = 0 := by
  rw [norm_sourceActualBandForwardEndpointCoframe_le_one_iff_combined_leakage_eq_zero,
    ← sourceOuter_add_endpointBand_eq_combinedCoframeLeakage]

end CCM24FiniteSPhysicalCancellationEndpointSplit
end CCM25Concrete
end Source
end ConnesWeilRH
