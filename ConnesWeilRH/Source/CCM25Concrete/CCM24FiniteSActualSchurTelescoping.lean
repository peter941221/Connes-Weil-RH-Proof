/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair

/-!
# Actual Schur-cascade telescope

The metric telescope uses the source-independent rectangular Schur steps.
This file repeats only its exact algebra for the source-owned actual Schur
steps.  The two cascades are deliberately kept as different definitions: no
coherence between the metric transport and the physical step data is assumed.

No physical boundary readout, Gate 3U estimate, finite-S sign, or RH
conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurTelescoping

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Ordered products of the actual steps -/

/-- The ambient product of the actual source-owned Schur transports. -/
noncomputable def suffixActualSchurAmbientProduct
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime -> finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S =>
      (suffixActualSchurFrameStep lambda stepData p S).transport ∘L
        suffixActualSchurAmbientProduct lambda stepData S

/-- The compressed source transition product of the same actual steps. -/
noncomputable def suffixActualSchurTransitionProduct
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime ->
      sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [] => ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)
  | p :: S =>
      (suffixActualSchurFrameStep lambda stepData p S).transition ∘L
        suffixActualSchurTransitionProduct lambda stepData S

/-- The actual Julia survivor is the adjoint of the ordered actual source
transition product. -/
theorem juliaSurvivor_suffixActualSchurFrameCoDefectSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    juliaSurvivor
        (suffixActualSchurCoDefectSteps lambda stepData S) =
      (suffixActualSchurTransitionProduct lambda stepData S)† := by
  induction S with
  | nil =>
      simp [suffixActualSchurCoDefectSteps, suffixActualSchurFrameSteps,
        suffixActualSchurTransitionProduct, juliaSurvivor]
  | cons p S ih =>
      simp only [suffixActualSchurCoDefectSteps,
        suffixActualSchurFrameSteps, List.map_cons, juliaSurvivor,
        suffixActualSchurTransitionProduct,
        ContinuousLinearMap.adjoint_comp,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_transfer]
      rw [show juliaSurvivor
          ((suffixActualSchurFrameSteps lambda stepData S).map
            (fun step => step.toAdjointCoDefectJuliaStep)) =
          (suffixActualSchurTransitionProduct lambda stepData S)† by
        simpa only [suffixActualSchurCoDefectSteps] using ih]

/-! ## Boundary outputs and the adjoint telescope -/

/-!
The generic Schur dagger is aligned with the metric orientation
`T† oldFrame = newFrame transition†`.  The actual source step has
`T newFrame = oldFrame transition`, so the endpoint-facing dagger is the
following separately named complement.  It is a definition, not an
identification with the metric boundary dagger.
-/

noncomputable def suffixActualSchurAdjointBoundaryDagger
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.adjoint
      (suffixActualSchurFrameStep lambda stepData p S).transport) ∘L
      (suffixActualSchurFrameStep lambda stepData p S).newFrame -
    (suffixActualSchurFrameStep lambda stepData p S).oldFrame ∘L
      (ContinuousLinearMap.adjoint
        (suffixActualSchurFrameStep lambda stepData p S).transition)

/- The difference between the endpoint-facing actual dagger and the metric
boundary dagger.  Keeping this as a named map makes the missing coherence
producer an explicit downstream input. -/
noncomputable def suffixActualSchurBoundaryCoherenceResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualSchurAdjointBoundaryDagger lambda stepData p S -
    (suffixActualSchurFrameStep lambda stepData p S).boundaryDagger

theorem suffixActualSchurAdjointBoundaryDagger_eq_metricBoundary_add_coherence
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualSchurAdjointBoundaryDagger lambda stepData p S =
        (suffixActualSchurFrameStep lambda stepData p S).boundaryDagger +
      suffixActualSchurBoundaryCoherenceResidual lambda stepData p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualSchurBoundaryCoherenceResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply]
  abel

/-- Every actual boundary dagger after its remaining ambient adjoint suffix
and its preceding source-adjoint prefix. -/
noncomputable def suffixActualSchurBoundaryOutputMaps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime ->
      List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
  | [] => []
  | p :: S =>
      ((suffixActualSchurAmbientProduct lambda stepData S)† ∘L
          (suffixActualSchurAdjointBoundaryDagger lambda stepData p S)) ::
        (suffixActualSchurBoundaryOutputMaps lambda stepData S).map
          (fun output => output ∘L
            ContinuousLinearMap.adjoint
              (suffixActualSchurFrameStep lambda stepData p S).transition)

theorem suffixActualSchurBoundaryOutputMaps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurBoundaryOutputMaps lambda stepData S).length =
      S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [suffixActualSchurBoundaryOutputMaps, ih]

/-- The adjoint of the actual ambient product equals the actual terminal
survivor plus the ordered actual boundary output sum. -/
theorem suffixActualSchurAmbientProduct_adjoint_comp_terminalPolarFrame
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurAmbientProduct lambda stepData S)† ∘L
        newSuffixFrame lambda S =
      newSuffixFrame lambda [] ∘L
          (suffixActualSchurTransitionProduct lambda stepData S)† +
        (suffixActualSchurBoundaryOutputMaps lambda stepData S).sum := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [suffixActualSchurAmbientProduct,
        suffixActualSchurTransitionProduct,
        suffixActualSchurBoundaryOutputMaps]
  | cons p S ih =>
      let step := suffixActualSchurFrameStep lambda stepData p S
      have hone' :
          (ContinuousLinearMap.adjoint step.transport) ∘L step.newFrame =
            step.oldFrame ∘L (ContinuousLinearMap.adjoint step.transition) +
            suffixActualSchurAdjointBoundaryDagger lambda stepData p S := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [suffixActualSchurAdjointBoundaryDagger,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.add_apply]
        abel
      apply ContinuousLinearMap.ext
      intro x
      have ihPoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator (ContinuousLinearMap.adjoint step.transition x)) ih
      have ihPoint' :
          (ContinuousLinearMap.adjoint
            (suffixActualSchurAmbientProduct lambda stepData S))
              (step.oldFrame (ContinuousLinearMap.adjoint step.transition x)) =
            (newSuffixFrame lambda [])
                ((ContinuousLinearMap.adjoint
                  (suffixActualSchurTransitionProduct lambda stepData S))
                  (ContinuousLinearMap.adjoint step.transition x)) +
              (suffixActualSchurBoundaryOutputMaps lambda stepData S).sum
                (ContinuousLinearMap.adjoint step.transition x) := by
        simpa only [step, suffixActualSchurFrameStep, newSuffixFrame] using
          ihPoint
      have honePoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator x) hone'
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply] at ihPoint honePoint
      simp only [suffixActualSchurAmbientProduct,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.comp_apply] at ⊢
      change (ContinuousLinearMap.adjoint
          (suffixActualSchurAmbientProduct lambda stepData S))
          ((ContinuousLinearMap.adjoint step.transport) (step.newFrame x)) = _
      rw [honePoint, map_add, ihPoint']
      simp only [suffixActualSchurTransitionProduct,
        suffixActualSchurBoundaryOutputMaps,
        ContinuousLinearMap.adjoint_comp, List.sum_cons,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
      rw [sum_map_comp_apply]
      dsimp only [step]
      abel

/-! ## Endpoint object and the physical coherence residual -/

/-- The endpoint built from the actual Schur ambient cascade.  It has the
same upper scalar and terminal inverse-Gram coordinate as the metric
coframe, but its ambient product and boundary data are source-owned actual
objects. -/
noncomputable def suffixActualSchurEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
    ((suffixActualSchurAmbientProduct lambda stepData family.visiblePrimes)† ∘L
      newSuffixFrame lambda family.visiblePrimes ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num))

/-- The exact physical/actual-Schur endpoint mismatch.  It is kept as an
explicit residual rather than being silently identified with zero. -/
noncomputable def suffixActualSchurEndpointResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardEndpointCoframe lambda family -
    suffixActualSchurEndpointCoframe lambda stepData family

theorem sourceActualBandForwardEndpointCoframe_eq_actualSchurEndpoint_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      suffixActualSchurEndpointCoframe lambda stepData family +
        suffixActualSchurEndpointResidual lambda stepData family := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualSchurEndpointResidual,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  abel

/-- The actual-Schur endpoint itself has the exact survivor-plus-boundary
expansion.  This theorem is algebraic; it does not identify the displayed
boundary outputs with the physical common-boundary readout. -/
theorem suffixActualSchurEndpointCoframe_eq_upperFactor_survivor_add_boundarySum
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    suffixActualSchurEndpointCoframe lambda stepData family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (newSuffixFrame lambda [] ∘L
            (suffixActualSchurTransitionProduct lambda stepData
              family.visiblePrimes)† ∘L
              parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                (by norm_num) +
          ((suffixActualSchurBoundaryOutputMaps lambda stepData
              family.visiblePrimes).map
            (fun output => output ∘L
              parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                (by norm_num))).sum) := by
  unfold suffixActualSchurEndpointCoframe
  have htelescope :=
    suffixActualSchurAmbientProduct_adjoint_comp_terminalPolarFrame
      lambda stepData family.visiblePrimes
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (parameterizedSoninGramInvSqrt lambda 1
        family.visiblePrimes (by norm_num) x)) htelescope
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at hpoint ⊢
  rw [hpoint, sum_map_comp_apply]

end CCM24FiniteSActualSchurTelescoping
end CCM25Concrete
end Source
end ConnesWeilRH
