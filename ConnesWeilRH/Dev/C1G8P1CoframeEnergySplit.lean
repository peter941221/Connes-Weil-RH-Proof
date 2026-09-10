import ConnesWeilRH.Dev.C1G8P1CoframePythagorean

/-!
# G8 P1 pointwise coframe energy split

The survivor--boundary orthogonality is used pointwise on the source carrier.
This gives the exact norm-square split for the literal metric coframe.  It is
an energy consumer only: no detector-weighted cancellation or radial
identification is inferred.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1CoframeEnergySplit

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSTransportBounds
open C1G8P1MetricChannels
open C1G8P1CoframePythagorean
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem finiteEulerMetricCoframe_apply_normSq_eq_survivor_add_boundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ‖finiteEulerMetricCoframe lambda family x‖ ^ 2 =
      ‖g8MetricSurvivorCoframe lambda family x‖ ^ 2 +
        ‖g8MetricVisibleBoundaryCoframe lambda family x‖ ^ 2 := by
  have hsplit :=
    finiteEulerMetricCoframe_eq_g8MetricSurvivor_add_visibleBoundary
      lambda family
  have horth :=
    g8MetricSurvivor_adjoint_comp_visibleBoundary_eq_zero lambda family
  have hinner : inner ℂ
      (g8MetricSurvivorCoframe lambda family x)
      (g8MetricVisibleBoundaryCoframe lambda family x) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hz := DFunLike.congr_fun horth x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hz
    rw [hz]
    simp
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (g8MetricSurvivorCoframe lambda family x)
    (g8MetricVisibleBoundaryCoframe lambda family x) hinner
  have hsplitPoint := congrArg (fun T => T x) hsplit
  simp only [ContinuousLinearMap.add_apply] at hsplitPoint
  rw [hsplitPoint]
  simpa only [pow_two] using hpyth

end
end C1G8P1CoframeEnergySplit
end Source
end ConnesWeilRH
