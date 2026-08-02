/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout

/-!
# Metric-history guard for the completed physical readout

The completed metric history has an exact readout of the raw metric coframe.
Gate 3U needs the strictly larger forward/endpoint physical coframe.  This
module records the exact algebraic gap: using the metric-history readout as
the full physical endpoint is equivalent to forcing the actual forward
coframe to vanish.

No vanishing, norm estimate, Gate 3U bound, finite-S sign, or RH premise is
introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalHistoryMetricGuard

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCompletedMetricCoframeReadout
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSFixedSourcePolar

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The metric completed-history readout equals the full forward/endpoint
coframe exactly when the actual forward coframe is zero.  Thus the existing
metric readout cannot be used as the completed physical readout unless a new
source theorem kills the forward channel. -/
theorem metricHistoryReadout_eq_forwardEndpoint_iff_forward_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframeHistoryReadout lambda family ∘L
        finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num) =
      sourceActualBandForwardEndpointCoframe lambda family ↔
    sourceActualBandForwardCoframe lambda family = 0 := by
  rw [finiteEulerMetricCoframeHistoryReadout_comp_column_eq]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x) h
    simp only [sourceActualBandForwardEndpointCoframe,
      ContinuousLinearMap.add_apply] at hx
    have hcancel :
        sourceActualBandForwardCoframe lambda family x +
            finiteEulerMetricCoframe lambda family x =
          0 + finiteEulerMetricCoframe lambda family x := by
      simpa only [zero_add] using hx.symm
    exact add_right_cancel hcancel
  · intro hzero
    rw [sourceActualBandForwardEndpointCoframe, hzero]
    simp only [zero_add]

/-- Contrapositive form: a nonzero forward coframe rules out identifying the
metric-history readout with the full forward/endpoint coframe. -/
theorem metricHistoryReadout_ne_forwardEndpoint_of_forward_ne_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hforward :
      sourceActualBandForwardCoframe lambda family ≠ 0) :
    finiteEulerMetricCoframeHistoryReadout lambda family ∘L
        finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num) ≠
      sourceActualBandForwardEndpointCoframe lambda family := by
  intro hmetric
  exact hforward
    ((metricHistoryReadout_eq_forwardEndpoint_iff_forward_zero
      lambda family).mp hmetric)

end CCM24FiniteSCompletedPhysicalHistoryMetricGuard
end CCM25Concrete
end Source
end ConnesWeilRH
