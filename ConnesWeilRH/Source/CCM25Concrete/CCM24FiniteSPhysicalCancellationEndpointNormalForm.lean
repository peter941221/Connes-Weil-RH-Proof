/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointSplit

/-!
# Normal form for the endpoint cancellation residual

Proof 725 identifies the two endpoint channels with the complete off-Sonin
leakage, but downstream physical owners still need a stable name for that
object. This file gives the residual one name and records its exact forms:

```text
outer + band = (I - R) endpoint
             = endpoint - inclusion
             = forward + physicalLeakage.
```

The identities are algebraic. No cancellation, norm estimate, Gate 3U bound,
finite-S sign, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalCancellationEndpointNormalForm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSEndpointContractionGuard
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointSplit
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The two projected endpoint channels, kept as one same-object residual. -/
noncomputable def sourceEndpointCancellationResidual
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceOuterCoframeLeakage lambda family +
    sourceBandProjection lambda ∘L
      sourceActualBandForwardEndpointCoframe lambda family

/-- Pure projection algebra for the radial complement and source band. -/
theorem radialComplement_add_sourceBandProjection_eq_sourceSoninComplement
    (lambda : CCM24SoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) +
        sourceBandProjection lambda =
      ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceBandProjection, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  abel

/-- The named residual is exactly Proof 725's complete off-Sonin leakage. -/
theorem sourceEndpointCancellationResidual_eq_combinedCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      sourceActualBandCombinedCoframeLeakage lambda family := by
  simpa only [sourceEndpointCancellationResidual] using
    sourceOuter_add_endpointBand_eq_combinedCoframeLeakage lambda family

/-- The endpoint residual has one projection formula; the two channels are
only its radial-complement plus source-band expansion. -/
theorem sourceEndpointCancellationResidual_eq_sourceSoninComplement_comp_endpoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        sourceActualBandForwardEndpointCoframe lambda family := by
  rw [sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  rfl

/-- The explicit two-channel expansion of the named residual. -/
theorem sourceEndpointCancellationResidual_eq_radialComplement_add_band_comp_endpoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L
          sourceActualBandForwardEndpointCoframe lambda family) +
        (sourceBandProjection lambda ∘L
          sourceActualBandForwardEndpointCoframe lambda family) := by
  unfold sourceEndpointCancellationResidual
  rw [sourceOuterCoframeLeakage_eq_radialComplement_comp_endpoint]

/-- The residual is the endpoint coframe minus its fixed source-Sonin
inclusion. -/
theorem sourceEndpointCancellationResidual_eq_endpoint_sub_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      sourceActualBandForwardEndpointCoframe lambda family -
        sourceInclusion lambda := by
  rw [sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  exact sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion
    lambda family

/-- The same residual is the raw forward coframe plus the complete physical
leakage. This is the handoff form consumed by the Gate bridge. -/
theorem sourceEndpointCancellationResidual_eq_forward_add_physicalLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      sourceActualBandForwardCoframe lambda family +
        sourcePhysicalCoframeLeakage lambda family := by
  rw [sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  exact sourceActualBandCombinedCoframeLeakage_eq_forward_add_physicalLeakage
    lambda family

/-- Vanishing of the endpoint residual is exactly the missing endpoint-range
inclusion. This is an equivalence, not a proof of either side. -/
theorem sourceEndpointCancellationResidual_eq_zero_iff_endpoint_eq_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family = 0 ↔
      sourceActualBandForwardEndpointCoframe lambda family =
        sourceInclusion lambda := by
  rw [sourceEndpointCancellationResidual_eq_endpoint_sub_inclusion]
  exact sub_eq_zero

/-- The residual is genuinely off the source-Sonin carrier. -/
theorem sourceSoninProjection_comp_sourceEndpointCancellationResidual_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceEndpointCancellationResidual lambda family = 0 := by
  rw [sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  exact sourceSoninProjection_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
    lambda family

/-- The source inclusion adjoint also annihilates the complete residual. -/
theorem sourceInclusionAdjoint_comp_sourceEndpointCancellationResidual_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        sourceEndpointCancellationResidual lambda family = 0 := by
  rw [sourceEndpointCancellationResidual_eq_combinedCoframeLeakage]
  exact sourceInclusionAdjoint_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
    lambda family

end CCM24FiniteSPhysicalCancellationEndpointNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
