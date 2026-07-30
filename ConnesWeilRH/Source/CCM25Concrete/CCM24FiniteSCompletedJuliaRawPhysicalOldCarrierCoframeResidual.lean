/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence

/-!
# Metric-coframe survivor residual

Proof 596 expands the adjacent metric coframe before it is inserted into the
signed old-carrier telescope.  The exact survivor is the mismatch between the
two scalar-normalized terminal Gram square roots.  The genuine Schur boundary
dagger is recorded as a separate residual channel.

No cancellation between these channels is asserted.  In particular, the
forward coframe recurrence is not silently substituted for the metric
coframe recurrence.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
    finiteSCarrier

/-! ## The two exact residual channels -/

/-- The survivor channel.  It retains both endpoint scalar normalizations and
the two terminal inverse-Gram square roots. -/
noncomputable def suffixActualBandMetricCoframeSurvivorResidual
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (finiteEulerUpperFactor (p :: S) : ℂ) •
      (newSuffixFrame lambda S ∘L
        (suffixEulerFrameTransition lambda p S)† ∘L
        suffixActualBandMetricCoframeSqrt lambda (p :: S)) -
    (finiteEulerUpperFactor S : ℂ) •
      (newSuffixFrame lambda S ∘L
        suffixActualBandMetricCoframeSqrt lambda S ∘L
        (suffixEulerFrameTransition lambda p S)†)

/-- The genuine rectangular boundary channel, including the new endpoint
inverse-Gram square root. -/
noncomputable def suffixActualBandMetricCoframeBoundaryResidual
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (finiteEulerUpperFactor (p :: S) : ℂ) •
    ((suffixEulerFrameSchurStep lambda p S).boundaryDagger ∘L
      suffixActualBandMetricCoframeSqrt lambda (p :: S))

/-! ## Exact adjacent readback -/

theorem suffixActualBandMetricCoframe_cons_sub_comp_transitionAdj_eq_ambientAdjoint_comp_residual
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframe lambda (p :: S) -
        suffixActualBandMetricCoframe lambda S ∘L
          (suffixEulerFrameTransition lambda p S)† =
      (suffixEulerAmbientProduct S)† ∘L
        (suffixActualBandMetricCoframeSurvivorResidual lambda p S +
          suffixActualBandMetricCoframeBoundaryResidual lambda p S) := by
  rw [suffixActualBandMetricCoframe_cons_eq_survivor_add_boundary,
    suffixActualBandMetricCoframe_eq_upperFactor_schurPolarProduct]
  have hnewFrame :
      (suffixEulerFrameSchurStep lambda p S).newFrame =
        newSuffixFrame lambda S := by
    simp [suffixEulerFrameSchurStep]
  rw [hnewFrame]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandMetricCoframeSurvivorResidual,
    suffixActualBandMetricCoframeBoundaryResidual,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_add, map_sub, map_smul]
  module

/-! ## The forward recurrence remains a separate exact object -/

theorem suffixActualBandForwardCoframe_cons_eq_normalized_forward_recurrence
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandForwardCoframe lambda (p :: S) =
      sourceBandProjection lambda ∘L
        normalizedFiniteEulerInverseList S ∘L
          normalizedPrimeEulerInverse p ∘L
            sourceInclusion lambda :=
  suffixActualBandForwardCoframe_cons lambda p S

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual
end CCM25Concrete
end Source
end ConnesWeilRH
