/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTelescoping

/-!
# Completed-history carrier mismatch

The completed physical history stores the terminal survivor together with the
metric rectangular boundary daggers.  The actual Schur endpoint uses a
different boundary dagger, followed by the physical/Schur endpoint residual.

This module records the exact difference.  It does not assert that either
residual vanishes or has a uniform bound.  In particular, assembling the
existing per-step Julia readouts cannot by itself produce the physical
completed-history readout required by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalHistoryMismatch

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurTelescoping
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The metric and coherence parts of the actual output list -/

/-- The output list obtained when the completed history's metric boundary
dagger is propagated through the remaining ambient adjoint. -/
noncomputable def suffixActualSchurMetricBoundaryOutputMaps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime →
      List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
  | [] => []
  | p :: S =>
      ((suffixActualSchurAmbientProduct lambda stepData S)† ∘L
          (suffixActualSchurFrameStep lambda stepData p S).boundaryDagger) ::
        (suffixActualSchurMetricBoundaryOutputMaps lambda stepData S).map
          (fun output => output ∘L
            ContinuousLinearMap.adjoint
              (suffixActualSchurFrameStep lambda stepData p S).transition)

/-- The output list contributed by the actual-versus-metric boundary-dagger
coherence residual. -/
noncomputable def suffixActualSchurCoherenceBoundaryOutputMaps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime →
      List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
  | [] => []
  | p :: S =>
      ((suffixActualSchurAmbientProduct lambda stepData S)† ∘L
          suffixActualSchurBoundaryCoherenceResidual lambda stepData p S) ::
        (suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData S).map
          (fun output => output ∘L
            ContinuousLinearMap.adjoint
              (suffixActualSchurFrameStep lambda stepData p S).transition)

theorem suffixActualSchurMetricBoundaryOutputMaps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurMetricBoundaryOutputMaps lambda stepData S).length =
      S.length := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      simp [suffixActualSchurMetricBoundaryOutputMaps, ih]

theorem suffixActualSchurCoherenceBoundaryOutputMaps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData S).length =
      S.length := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      simp [suffixActualSchurCoherenceBoundaryOutputMaps, ih]

theorem suffixActualSchurBoundaryOutputMaps_sum_eq_metric_add_coherence
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurBoundaryOutputMaps lambda stepData S).sum =
      (suffixActualSchurMetricBoundaryOutputMaps lambda stepData S).sum +
        (suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData S).sum := by
  induction S with
  | nil => simp [suffixActualSchurBoundaryOutputMaps,
      suffixActualSchurMetricBoundaryOutputMaps,
      suffixActualSchurCoherenceBoundaryOutputMaps]
  | cons p S ih =>
      let transition :=
        ContinuousLinearMap.adjoint
          (suffixActualSchurFrameStep lambda stepData p S).transition
      have htail :
          ((suffixActualSchurBoundaryOutputMaps lambda stepData S).map
              (fun output => output ∘L transition)).sum =
            ((suffixActualSchurMetricBoundaryOutputMaps lambda stepData S).map
                (fun output => output ∘L transition)).sum +
              ((suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData S).map
                (fun output => output ∘L transition)).sum := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.add_apply]
        rw [sum_map_comp_apply, sum_map_comp_apply, sum_map_comp_apply]
        exact congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          T (transition x)) ih
      have hlocal :
          ((suffixActualSchurAmbientProduct lambda stepData S)† ∘L
              suffixActualSchurAdjointBoundaryDagger lambda stepData p S) =
            (suffixActualSchurAmbientProduct lambda stepData S)† ∘L
                (suffixActualSchurFrameStep lambda stepData p S).boundaryDagger +
              (suffixActualSchurAmbientProduct lambda stepData S)† ∘L
                suffixActualSchurBoundaryCoherenceResidual lambda stepData p S := by
        rw [suffixActualSchurAdjointBoundaryDagger_eq_metricBoundary_add_coherence]
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.add_apply, map_add]
      simp only [suffixActualSchurBoundaryOutputMaps,
        suffixActualSchurMetricBoundaryOutputMaps,
        suffixActualSchurCoherenceBoundaryOutputMaps, List.sum_cons]
      rw [hlocal, htail]
      abel

/-! ## The endpoint normal form with both missing terms visible -/

theorem suffixActualSchurBoundaryOutputMaps_comp_gramInvSqrt_eq_metric_add_coherence
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    ((suffixActualSchurBoundaryOutputMaps lambda stepData
        family.visiblePrimes).map (fun output => output ∘L
          parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
            (by norm_num))).sum =
      ((suffixActualSchurMetricBoundaryOutputMaps lambda stepData
          family.visiblePrimes).map (fun output => output ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
              (by norm_num))).sum +
        ((suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData
          family.visiblePrimes).map (fun output => output ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
              (by norm_num))).sum := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply]
  rw [sum_map_comp_apply, sum_map_comp_apply, sum_map_comp_apply]
  have h := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      T (parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
        (by norm_num) x))
    (suffixActualSchurBoundaryOutputMaps_sum_eq_metric_add_coherence
      lambda stepData family.visiblePrimes)
  simpa only [ContinuousLinearMap.add_apply] using h

theorem sourceActualBandForwardEndpointCoframe_eq_upperFactor_metric_coherence_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (newSuffixFrame lambda [] ∘L
            (suffixActualSchurTransitionProduct lambda stepData
              family.visiblePrimes)† ∘L
              parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                (by norm_num) +
          ((suffixActualSchurMetricBoundaryOutputMaps lambda stepData
              family.visiblePrimes).map (fun output => output ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
              (by norm_num))).sum +
          ((suffixActualSchurCoherenceBoundaryOutputMaps lambda stepData
              family.visiblePrimes).map (fun output => output ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
              (by norm_num))).sum) +
        suffixActualSchurEndpointResidual lambda stepData family := by
  rw [sourceActualBandForwardEndpointCoframe_eq_actualSchurEndpoint_add_residual
    (G := G) lambda stepData family]
  rw [suffixActualSchurEndpointCoframe_eq_upperFactor_survivor_add_boundarySum
    (G := G) lambda stepData family]
  rw [suffixActualSchurBoundaryOutputMaps_comp_gramInvSqrt_eq_metric_add_coherence
    (G := G) lambda stepData family]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_add]
  abel

end CCM24FiniteSCompletedPhysicalHistoryMismatch
end CCM25Concrete
end Source
end ConnesWeilRH
