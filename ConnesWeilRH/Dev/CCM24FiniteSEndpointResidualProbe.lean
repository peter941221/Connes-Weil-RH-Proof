/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSForwardOffSoninReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationChannelSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedCoframeGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointContractionGuard

/-!
# Proof-717 endpoint residual probe

The forward branch of `sourceActualBandForwardEndpointCoframe` is the exact
off-Sonin normalized inverse `(I-Q) ∘ (N ∘ L)` (closed in
`CCM24FiniteSForwardOffSoninReduction`).  The physical coframe leakage is
`(I-Q) ∘ M`.  This probe records the block-triangular arithmetic that pushes
the two off-Sonin branches onto one band.

* The forward band is exactly `(I-Q) ∘ (N ∘ L)`, from the two in-library
  radial facts `R ∘ (N ∘ L) = N ∘ L` (inverse preserves the radial support)
  and `R ∘ L = L`.

* The endpoint residual therefore equals

      (I-Q) ∘ (N + M) ∘ L ,

  so that `residual = 0 ⟺ (N + M) ∘ L ∈ range(Q)` — the residual is the
  off-Sonin defect of the combined normalized-inverse and metric Gram term.

* The Proof-723 channel split (final theorem) records the exact wall: the
  residual splits into the outer-radial channel `(I−R) ∘ M` plus the
  source-band channel `forward + (R−Q) ∘ M`.  The true unresolved analytic
  content is the outer-radial channel `(I−R) ∘ M`; it is NOT equal to zero
  in-library (only the tautology `R(R(Mu))=R(Mu)` holds), and it is not
  supplied by closure.  Recombining these channels is the analytic content.

This probe makes no norm estimate, Gate-3U bound, sign statement, or RH
premise; it is pure operator algebra on the source Sonin carrier.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointResidualProbe

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCoframeResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSPhysicalCancellationChannelSplit
open CCM24FiniteSPhysicalCancellationEndpointSplit
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSEndpointContractionGuard
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSInverseMetric
open CCM24FiniteSCausalSupport
open CCM24FiniteSForwardOffSoninReduction

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The endpoint cancellation residual: forward plus the completed physical
coframe leakage.  Both riders are off-Sonin; only their sum matters. -/
noncomputable def sourceEndpointCancellationResidual
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardCoframe lambda family +
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
      finiteEulerMetricCoframe lambda family

/-- The residual is the off-Sonin projection of the combined normalized
inverse and metric coframe.  Everything rides on the same source inclusion. -/
theorem sourceEndpointCancellationResidual_eq_offSonin_sum
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        ((normalizedFiniteEulerInverse family ∘L sourceInclusion lambda) +
          finiteEulerMetricCoframe lambda family) := by
  rw [sourceEndpointCancellationResidual,
    sourceActualBandForwardCoframe_eq_offSonin_normalizedInverse]
  apply ContinuousLinearMap.ext
  intro u
  have h : ((ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda)
        (((normalizedFiniteEulerInverse family) ∘L sourceInclusion lambda) u +
          (finiteEulerMetricCoframe lambda family) u) : finiteSCarrier) =
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda)
        (((normalizedFiniteEulerInverse family) ∘L sourceInclusion lambda) u) +
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda)
        ((finiteEulerMetricCoframe lambda family) u) := map_add _ _ _
  simpa using h

/-- The diagnostic: the residual differs from the `(R−Q)`-band sum of the
combined coframes by exactly `(R−I) ∘ M`, the outer-radial correction of the
metric coframe.  The forward branch already is radially supported, by
`radialSupportProjection_normalizedInverse_sourceInclusion_eq_self`; the
metric coframe is not, so the band-sum gap is precisely `(R−I) ∘ M`. -/
theorem sourceEndpointCancellationResidual_band_sum_gap
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
        ((normalizedFiniteEulerInverse family ∘L sourceInclusion lambda) +
          finiteEulerMetricCoframe lambda family) -
      sourceEndpointCancellationResidual lambda family =
      (radialSupportProjection lambda - ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        finiteEulerMetricCoframe lambda family := by
  rw [sourceEndpointCancellationResidual_eq_offSonin_sum]
  apply ContinuousLinearMap.ext
  intro u
  have hforward : radialSupportProjection lambda
        (normalizedFiniteEulerInverse family (sourceInclusion lambda u)) =
      normalizedFiniteEulerInverse family (sourceInclusion lambda u) :=
    congrFun (congrArg DFunLike.coe
      (radialSupportProjection_normalizedInverse_sourceInclusion_eq_self
        lambda family)) u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
  rw [hforward]
  abel

/-- The Proof-723 channel split: the residual is the outer-radial channel
`(I−R) ∘ M` plus the source-band channel `forward + B ∘ M`.  This is the exact
wall — the genuine metric-boundary content rides entirely on
`sourceOuterCoframeLeakage`, and its recombination against the band channel is
analytic content not supplied by closure. -/
theorem sourceEndpointCancellationResidual_eq_outer_add_forward_add_bandMetric
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      sourceOuterCoframeLeakage lambda family +
        (sourceActualBandForwardCoframe lambda family +
          sourceBandMetricCoframeLeakage lambda family) := by
  rw [sourceEndpointCancellationResidual]
  rw [show
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        finiteEulerMetricCoframe lambda family =
      sourceSoninCoframeLeakage lambda family by
    rw [sourceSoninCoframeLeakage]]
  rw [sourceSoninCoframeLeakage_eq_physical,
    sourcePhysicalCoframeLeakage_eq_outer_add_bandMetric]
  abel

/-- The outer-radial channel IS the radial complement of the metric coframe:
`(I−R) ∘ M`.  With `M = T† ∘ D` and `D` already radial (`R ∘ D = D`), the
channel is nonzero precisely because the adjoint transport `T†` fails to map
the radial image of the dual frame back into the radial subspace.  The
Hilbert–Schmidt certificate for this channel would need `(I−R)∘T†∘D`; it is
not supplied by closure. -/
theorem sourceOuterCoframeLeakage_eq_radial_support_comp_metricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOuterCoframeLeakage lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
        finiteEulerMetricCoframe lambda family := by
  rw [sourceOuterCoframeLeakage]

/-- The two-channel orthogonal split (Proof 723/724).  The residual
`(I−Q)∘endpoint` decomposes through the two projections `(I−R)` and `(R−Q)`:
the outer-radial part `(I−R)∘endpoint` and the source-band part `(R−Q)∘endpoint`.
Because `Q ≤ R` (`R∘Q = Q`), the ranges of `(I−R)` and `(R−Q)` are orthogonal,
so the vanishing of the residual is equivalently the joint vanishing of its two
orthogonal components.  This is the fine-cancellation content of the metric
wall: it is not a trace-vanish (both operators are infinite-rank). -/
theorem sourceEndpointCancellationResidual_eq_outer_add_endpointBand
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationResidual lambda family =
      sourceOuterCoframeLeakage lambda family +
        (sourceBandProjection lambda ∘L
          sourceActualBandForwardEndpointCoframe lambda family) := by
  rw [sourceEndpointCancellationResidual_eq_outer_add_forward_add_bandMetric,
    ← sourceOuter_add_forward_add_bandMetric_eq_outer_add_endpointBand]

/-- Proof 717 in one line: the endpoint is a contraction iff it equals the
source inclusion, equivalently iff the complete off-Sonin leakage vanishes.
The forward part is annihilated by `Q` (`Q∘forward = 0`), and the metric part
satisfies `Q∘M = J`, so `Q∘endpoint = J`. The remaining content is entirely
the off-Sonin identity `(I−Q)(forward + M) = 0`, which is not in closure. -/
theorem sourceActualBandForwardEndpointCoframe_eq_inclusion_iff_combined_leakage_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
        CCM24FiniteSGramResponse.sourceInclusion lambda ↔
      sourceActualBandCombinedCoframeLeakage lambda family = 0 := by
  constructor
  · intro heq
    rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion, heq, sub_self]
  · intro hleakage
    exact sourceActualBandForwardEndpointCoframe_eq_inclusion_of_combined_leakage_eq_zero
      lambda family hleakage

end CCM24FiniteSEndpointResidualProbe
end CCM25Concrete
end Source
end ConnesWeilRH