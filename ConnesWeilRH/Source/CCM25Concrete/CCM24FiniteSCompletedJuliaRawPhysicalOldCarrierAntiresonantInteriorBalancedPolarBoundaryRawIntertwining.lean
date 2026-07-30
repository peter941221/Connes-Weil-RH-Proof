/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarBoundaryReduction

/-!
# Balanced polar-boundary residual as the raw intertwinement

Proof 667 removes the uniformly controlled polar detector boundary and leaves
the coupled residual

```text
H E_S-E_(p::S)H+L_(p::S)(D_(p::S)-D_S)R_S.
```

This module identifies that residual without estimating either summand.  The
same-suffix combination is exactly the balanced raw quadratic response, so
the adjacent residual is

```text
Raw_(p::S) H-H Raw_S
  =-(1+q_p) RawIntertwiningDefect_(p,S).
```

After the genuine square-root route scaling it is the negative of the
existing ambient-loss-scaled raw defect.  Thus the polar-boundary reduction
has isolated, rather than solved, the original Bone 1A survivor.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace BalancedPolarBoundaryRawIntertwining

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarBoundaryReduction
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarFirstJetRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaSynthesis
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

private theorem balanced_raw_identity
    {A : Type*} [Ring A]
    (coframe frame detector firstJet base gramInv : A)
    (hcoframeFrame : coframe * frame = 1)
    (hframeCoframe : frame * coframe = 1)
    (hgramInvFrame : gramInv * frame = coframe) :
    coframe *
          (firstJet + ((frame * detector * frame) * gramInv - base)) *
        frame =
      detector - coframe * (base - firstJet) * frame := by
  calc
    coframe *
          (firstJet + ((frame * detector * frame) * gramInv - base)) *
        frame =
      coframe * firstJet * frame +
          coframe * frame * detector * frame * (gramInv * frame) -
        coframe * base * frame := by
      noncomm_ring
    _ = coframe * firstJet * frame +
          detector * (frame * coframe) - coframe * base * frame := by
      rw [hcoframeFrame, hgramInvFrame]
      noncomm_ring
    _ = detector - coframe * (base - firstJet) * frame := by
      rw [hframeCoframe]
      noncomm_ring

/-! ## Same-suffix identification -/

/-- The coupled detector/base/first-jet expression left by Proof 667 is
exactly the already named balanced raw quadratic response. -/
theorem suffixActualBandBalancedRawQuadraticResponse_eq_polar_sub_baseFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedRawQuadraticResponse owner lambda S =
      suffixPolarDetectorCompression owner lambda S -
        suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandBaseFirstJetDifferenceKernel owner lambda S ∘L
            suffixActualBandMetricFrameGauge lambda S := by
  rw [suffixActualBandBalancedRawQuadraticResponse,
    suffixActualBandRawQuadraticCycledResponse_eq_physical_add_sourceGram]
  change
    suffixActualBandMetricCoframeSqrt lambda S ∘L
          (suffixActualBandPhysicalFirstJetResponse owner lambda S +
            (suffixActualBandFrameDetectorCompression owner lambda S ∘L
                suffixActualBandGramInv lambda S -
              suffixActualBandFixedSourceDetectorCompression owner lambda)) ∘L
        suffixActualBandMetricFrameGauge lambda S = _
  rw [suffixActualBandFrameDetectorCompression_eq_frameGauge_polar_frameGauge]
  have hcoframeFrame :
      suffixActualBandMetricCoframeSqrt lambda S *
          suffixActualBandMetricFrameGauge lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  have hframeCoframe :
      suffixActualBandMetricFrameGauge lambda S *
          suffixActualBandMetricCoframeSqrt lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  have hgramInvFrame :
      suffixActualBandGramInv lambda S *
          suffixActualBandMetricFrameGauge lambda S =
        suffixActualBandMetricCoframeSqrt lambda S := by
    simpa only [ContinuousLinearMap.mul_def] using
      (suffixActualBandGramInv_comp_metricFrameGauge_eq_coframeSqrt lambda S)
  simpa only [suffixActualBandBaseFirstJetDifferenceKernel,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      (balanced_raw_identity
        (coframe := suffixActualBandMetricCoframeSqrt lambda S)
        (frame := suffixActualBandMetricFrameGauge lambda S)
        (detector := suffixPolarDetectorCompression owner lambda S)
        (firstJet := suffixActualBandPhysicalFirstJetResponse owner lambda S)
        (base := suffixActualBandFixedSourceDetectorCompression owner lambda)
        (gramInv := suffixActualBandGramInv lambda S)
        hcoframeFrame hframeCoframe hgramInvFrame)

private theorem residual_to_balanced_difference_identity
    {A : Type*} [Ring A]
    (oldCoframe oldFrame newCoframe newFrame oldDetector newDetector
      oldDifference newDifference : A)
    (holdFrameCoframe : oldFrame * oldCoframe = 1)
    (hnewFrameCoframe : newFrame * newCoframe = 1) :
    (newFrame * oldCoframe) * oldDifference -
          newDifference * (newFrame * oldCoframe) +
        newFrame * (newDetector - oldDetector) * oldCoframe =
      newFrame *
          ((newDetector - newCoframe * newDifference * newFrame) -
            (oldDetector - oldCoframe * oldDifference * oldFrame)) *
        oldCoframe := by
  symm
  calc
    newFrame *
          ((newDetector - newCoframe * newDifference * newFrame) -
            (oldDetector - oldCoframe * oldDifference * oldFrame)) *
        oldCoframe =
      newFrame * newDetector * oldCoframe -
          (newFrame * newCoframe) * newDifference * newFrame * oldCoframe -
        newFrame * oldDetector * oldCoframe +
          newFrame * oldCoframe * oldDifference *
            (oldFrame * oldCoframe) := by
      noncomm_ring
    _ = newFrame * newDetector * oldCoframe -
          newDifference * newFrame * oldCoframe -
        newFrame * oldDetector * oldCoframe +
          newFrame * oldCoframe * oldDifference := by
      rw [holdFrameCoframe, hnewFrameCoframe]
      noncomm_ring
    _ = (newFrame * oldCoframe) * oldDifference -
          newDifference * (newFrame * oldCoframe) +
        newFrame * (newDetector - oldDetector) * oldCoframe := by
      noncomm_ring

/-! ## Adjacent gauge cancellation -/

/-- Proof 667's two-term residual is one adjacent difference of the balanced
raw response, with the endpoint gauges retained outside the difference. -/
theorem suffixActualBandPolarBoundaryResidualColumn_eq_balancedRawDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarBoundaryResidualColumn owner lambda p S =
      suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
        (suffixActualBandBalancedRawQuadraticResponse
            owner lambda (p :: S) -
          suffixActualBandBalancedRawQuadraticResponse owner lambda S) ∘L
        suffixActualBandMetricCoframeSqrt lambda S := by
  rw [suffixActualBandPolarBoundaryResidualColumn,
    suffixActualBandOldCarrierTransitionGauge,
    suffixActualBandBalancedRawQuadraticResponse_eq_polar_sub_baseFirstJet,
    suffixActualBandBalancedRawQuadraticResponse_eq_polar_sub_baseFirstJet]
  have holdFrameCoframe :
      suffixActualBandMetricFrameGauge lambda S *
          suffixActualBandMetricCoframeSqrt lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  have hnewFrameCoframe :
      suffixActualBandMetricFrameGauge lambda (p :: S) *
          suffixActualBandMetricCoframeSqrt lambda (p :: S) = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt
          lambda (p :: S))
  simpa only [ContinuousLinearMap.mul_def] using
    (residual_to_balanced_difference_identity
      (oldCoframe := suffixActualBandMetricCoframeSqrt lambda S)
      (oldFrame := suffixActualBandMetricFrameGauge lambda S)
      (newCoframe := suffixActualBandMetricCoframeSqrt lambda (p :: S))
      (newFrame := suffixActualBandMetricFrameGauge lambda (p :: S))
      (oldDetector := suffixPolarDetectorCompression owner lambda S)
      (newDetector := suffixPolarDetectorCompression owner lambda (p :: S))
      (oldDifference :=
        suffixActualBandBaseFirstJetDifferenceKernel owner lambda S)
      (newDifference :=
        suffixActualBandBaseFirstJetDifferenceKernel owner lambda (p :: S))
      holdFrameCoframe hnewFrameCoframe)

private theorem balanced_difference_to_raw_identity
    {A : Type*} [Ring A]
    (oldCoframe newCoframe oldFrame newFrame oldRaw newRaw : A)
    (holdFrameCoframe : oldFrame * oldCoframe = 1)
    (hnewFrameCoframe : newFrame * newCoframe = 1) :
    newFrame *
          (newCoframe * newRaw * newFrame -
            oldCoframe * oldRaw * oldFrame) *
        oldCoframe =
      newRaw * (newFrame * oldCoframe) -
        (newFrame * oldCoframe) * oldRaw := by
  calc
    newFrame *
          (newCoframe * newRaw * newFrame -
            oldCoframe * oldRaw * oldFrame) *
        oldCoframe =
      (newFrame * newCoframe) * newRaw * newFrame * oldCoframe -
        newFrame * oldCoframe * oldRaw *
          (oldFrame * oldCoframe) := by
      noncomm_ring
    _ = newRaw * newFrame * oldCoframe -
        newFrame * oldCoframe * oldRaw := by
      rw [holdFrameCoframe, hnewFrameCoframe]
      noncomm_ring
    _ = newRaw * (newFrame * oldCoframe) -
        (newFrame * oldCoframe) * oldRaw := by
      noncomm_ring

/-- After the endpoint gauges cancel, the residual is the reverse-oriented
one-sided intertwinement of the complete raw quadratic response. -/
theorem suffixActualBandPolarBoundaryResidualColumn_eq_rawReverseIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarBoundaryResidualColumn owner lambda p S =
      suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) ∘L
          suffixActualBandOldCarrierTransitionGauge lambda p S -
        suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixActualBandRawQuadraticCycledResponse owner lambda S := by
  rw [suffixActualBandPolarBoundaryResidualColumn_eq_balancedRawDifference,
    suffixActualBandBalancedRawQuadraticResponse,
    suffixActualBandBalancedRawQuadraticResponse,
    suffixActualBandOldCarrierTransitionGauge]
  have holdFrameCoframe :
      suffixActualBandMetricFrameGauge lambda S *
          suffixActualBandMetricCoframeSqrt lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  have hnewFrameCoframe :
      suffixActualBandMetricFrameGauge lambda (p :: S) *
          suffixActualBandMetricCoframeSqrt lambda (p :: S) = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt
          lambda (p :: S))
  simpa only [ContinuousLinearMap.mul_def] using
    (balanced_difference_to_raw_identity
      (oldCoframe := suffixActualBandMetricCoframeSqrt lambda S)
      (newCoframe := suffixActualBandMetricCoframeSqrt lambda (p :: S))
      (oldFrame := suffixActualBandMetricFrameGauge lambda S)
      (newFrame := suffixActualBandMetricFrameGauge lambda (p :: S))
      (oldRaw := suffixActualBandRawQuadraticCycledResponse owner lambda S)
      (newRaw :=
        suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S))
      holdFrameCoframe hnewFrameCoframe)

/-! ## Exact return to the raw Bone 1A survivor -/

/-- The residual is the negative raw intertwinement multiplied by the upper
Euler scalar.  No triangle inequality is used. -/
theorem suffixActualBandPolarBoundaryResidualColumn_eq_neg_upperFactor_rawDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarBoundaryResidualColumn owner lambda p S =
      -((1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S) := by
  rw [suffixActualBandPolarBoundaryResidualColumn_eq_rawReverseIntertwining,
    suffixActualBandOldCarrierTransitionGauge_eq_smul_transition,
    suffixActualBandRawQuadraticIntertwiningDefect]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_smul, smul_sub]
  abel

/-- Genuine route scaling converts Proof 667's survivor exactly into the
negative ambient-loss-scaled raw defect. -/
theorem routeScaledPolarBoundaryResidualColumn_eq_neg_rawIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledPolarBoundaryResidualColumn owner index =
      -(routeScaledRawQuadraticIntertwiningDefect owner index) := by
  rw [routeScaledPolarBoundaryResidualColumn,
    suffixActualBandPolarBoundaryResidualColumn_eq_neg_upperFactor_rawDefect,
    routeScaledRawQuadraticIntertwiningDefect]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_neg, smul_smul]
  rw [inv_sqrtCoefficient_mul_upperFactor_eq_inv_ambientLossScale]

/-- The residual and the existing raw defect have exactly the same scaled
operator norm at every route-valid step. -/
theorem norm_routeScaledPolarBoundaryResidualColumn_eq_rawIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    ‖routeScaledPolarBoundaryResidualColumn owner index‖ =
      ‖routeScaledRawQuadraticIntertwiningDefect owner index‖ := by
  rw [routeScaledPolarBoundaryResidualColumn_eq_neg_rawIntertwining,
    norm_neg]

/-- Proof 666's recurrence is exactly the controlled polar boundary minus
the route-scaled raw intertwinement. -/
theorem routeScaledBalancedPolarFirstJetRecurrenceColumn_eq_boundary_sub_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledBalancedPolarFirstJetRecurrenceColumn owner index =
      routeScaledOldCarrierPolarBoundaryChannel owner index -
        routeScaledRawQuadraticIntertwiningDefect owner index := by
  rw [
    routeScaledBalancedPolarFirstJetRecurrenceColumn_eq_boundary_add_residual,
    routeScaledPolarBoundaryResidualColumn_eq_neg_rawIntertwining]
  abel

/-- A route-uniform residual bound and the existing route-uniform raw-defect
bound are the same proposition with the same constant. -/
theorem polarBoundaryResidualRouteUniformScaledBound_iff_rawIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixPolarBoundaryResidualRouteUniformScaledBound owner bound ↔
      SuffixRawRouteUniformScaledIntertwiningBound owner bound := by
  constructor
  · rintro ⟨hbound, hresidual⟩
    refine ⟨hbound, ?_⟩
    intro index
    rw [← norm_routeScaledPolarBoundaryResidualColumn_eq_rawIntertwining]
    exact hresidual index
  · rintro ⟨hbound, hraw⟩
    refine ⟨hbound, ?_⟩
    intro index
    rw [norm_routeScaledPolarBoundaryResidualColumn_eq_rawIntertwining]
    exact hraw index

/-- Proof 667's survivor equivalence closes the algebraic loop: Bone 1A is
still exactly the existence of a route-uniform scaled raw intertwinement
bound. -/
theorem
    exists_routeUniformScaledCompleteTargetBound_iff_rawIntertwining_afterPolarBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixRawRouteUniformScaledIntertwiningBound owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_polarBoundaryResidual]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (polarBoundaryResidualRouteUniformScaledBound_iff_rawIntertwining
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (polarBoundaryResidualRouteUniformScaledBound_iff_rawIntertwining
        owner bound).mpr data⟩

end BalancedPolarBoundaryRawIntertwining
end CCM25Concrete
end Source
end ConnesWeilRH
