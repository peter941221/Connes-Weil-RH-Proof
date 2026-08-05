/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSForwardOffSoninReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage

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

* The band sum is also equal to `(R−Q) ∘ (N+M) ∘ L`: on source inclusions
  the radial correction to the metric term is the second-support boundary
  `(I−EQ₀E) R M L`, assembled with the prolate remainder `K₀ = R−Q−(I−EQ₀E) R`.

This probe makes no norm estimate, Gate-3U bound, sign statement, or RH
premise; it is pure operator algebra on the source Sonin carrier.  The
classification `residual = 0` is exactly the Proof-717 wall recorded in the
project ledger.
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
metric coframe.  That correction vanishes iff the metric coframe is
radially supported; the forward branch already is, by
`radialSupportProjection_normalizedInverse_sourceInclusion_eq_self`.  This
is the Proof-717 wall recorded in the project ledger: no in-library theorem
supplies `R ∘ M = M`, and `M`'s radial support is exactly the unresolved
analytic content. -/
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

end CCM24FiniteSEndpointResidualProbe
end CCM25Concrete
end Source
end ConnesWeilRH
