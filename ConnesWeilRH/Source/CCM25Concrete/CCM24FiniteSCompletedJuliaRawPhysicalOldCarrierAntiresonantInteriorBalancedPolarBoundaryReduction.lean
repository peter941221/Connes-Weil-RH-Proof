/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarFirstJetRecurrence

/-!
# Balanced polar-boundary reduction

Proof 666 leaves the old-carrier recurrence

```text
H P_S-P_(p::S) H+L_(p::S)(D_(p::S)-D_S)R_S,
```

where `P_S=B_0+D_S-F_S`.  This module keeps the complete recurrence intact
while identifying its detector intertwinement subchannel:

```text
H D_S-D_(p::S)H
  =(1+q_p)(T D_S-D_(p::S)T)
  =(1+q_p) BoundaryDefect_(p,S).
```

The boundary defect factors through the actual left Julia co-defect.  After
the genuine `q_p^(-1/2)` route scaling, its norm is at most `6 ||W||`,
uniformly in the prime and suffix.  Bone 1A is therefore equivalent, up to
this explicit additive constant, to uniform control of the remaining signed
base/first-jet covariance plus metric detector increment.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarBoundaryReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarFirstJetRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaSynthesis
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

/-! ## Exact polar detector subchannel -/

/-- The detector covariance inside Proof 666's old-carrier transition is
exactly the upper Euler scalar times the physical moving-boundary defect. -/
theorem suffixActualBandOldCarrierDetectorIntertwining_eq_boundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixActualBandOldCarrierTransitionGauge lambda p S =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        suffixEulerDetectorBoundaryDefect owner lambda p S := by
  rw [suffixActualBandOldCarrierTransitionGauge_eq_smul_transition]
  calc
    ((1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
          suffixEulerFrameTransition lambda p S) ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          ((1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
            suffixEulerFrameTransition lambda p S) =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        (suffixEulerFrameTransition lambda p S ∘L
            suffixPolarDetectorCompression owner lambda S -
          suffixPolarDetectorCompression owner lambda (p :: S) ∘L
            suffixEulerFrameTransition lambda p S) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        map_smul, smul_sub]
    _ = (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        suffixEulerDetectorBoundaryDefect owner lambda p S := by
      rw [suffixEulerDetectorIntertwiningDefect_eq_boundary]

/-- The named uniformly controlled polar boundary subchannel. -/
noncomputable def suffixActualBandOldCarrierPolarBoundaryChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
    suffixEulerDetectorBoundaryDefect owner lambda p S

/-- The right factor after extracting the actual left Julia co-defect from
the moving detector boundary. -/
noncomputable def suffixActualBandPolarBoundaryRightFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  ((suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor)† ∘L
    detectorOperator owner ∘L newSuffixFrame lambda S

/-- The physical boundary defect factors through the actual left Julia
co-defect, before any norm is taken. -/
theorem suffixEulerDetectorBoundaryDefect_eq_leftCoDefect_comp_rightFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerDetectorBoundaryDefect owner lambda p S =
      -((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        suffixActualBandPolarBoundaryRightFactor owner lambda p S) := by
  rw [suffixEulerDetectorBoundaryDefect_eq_juliaCoDefect]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Every factor to the right of the left Julia co-defect is contractive
except for the detector itself. -/
theorem norm_suffixActualBandPolarBoundaryRightFactor_le_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandPolarBoundaryRightFactor owner lambda p S‖ ≤
      ‖detectorOperator owner‖ := by
  let factor :=
    (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor
  let detector := detectorOperator owner
  let frame := newSuffixFrame lambda S
  have hfactorAdjoint : ‖factor†‖ ≤ (1 : ℝ) := by
    simpa only [factor] using
      (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor
        |>.factor_adjoint_norm_le_one
  have hframe : ‖frame‖ ≤ (1 : ℝ) := by
    simpa only [frame] using newSuffixFrame_norm_le_one lambda S
  change ‖factor† ∘L detector ∘L frame‖ ≤ ‖detector‖
  calc
    ‖factor† ∘L detector ∘L frame‖ ≤
        ‖factor† ∘L detector‖ * ‖frame‖ :=
      ContinuousLinearMap.opNorm_comp_le (factor† ∘L detector) frame
    _ ≤ (‖factor†‖ * ‖detector‖) * ‖frame‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le (factor†) detector)
        (norm_nonneg frame)
    _ ≤ (1 * ‖detector‖) * 1 := by
      gcongr
    _ = ‖detector‖ := by ring

/-- Before route scaling, the moving detector boundary has the exact
`O(s_p)` size required by Bone 1A. -/
theorem norm_suffixEulerDetectorBoundaryDefect_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixEulerDetectorBoundaryDefect owner lambda p S‖ ≤
      6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
  rw [suffixEulerDetectorBoundaryDefect_eq_leftCoDefect_comp_rightFactor,
    norm_neg]
  calc
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        suffixActualBandPolarBoundaryRightFactor owner lambda p S‖ ≤
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ *
        ‖suffixActualBandPolarBoundaryRightFactor owner lambda p S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (6 * primeEulerAmbientLossScale p) *
        ‖detectorOperator owner‖ := by
      exact mul_le_mul
        (norm_suffixEulerFrameLeftCoDefect_le_six_ambientLossScale
          lambda p S)
        (norm_suffixActualBandPolarBoundaryRightFactor_le_detector
          owner lambda p S)
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (primeEulerAmbientLossScale_nonneg p))
    _ = 6 * primeEulerAmbientLossScale p *
        ‖detectorOperator owner‖ := rfl

/-! ## Genuine route scaling -/

/-- Multiplying the inverse square-root route scale by the upper Euler factor
is exactly the inverse ambient-loss scale. -/
theorem inv_sqrtCoefficient_mul_upperFactor_eq_inv_ambientLossScale
    (p : CCM24VisiblePrime) :
    ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)⁻¹) *
        (1 + (ccm24PrimeEulerCoefficient p : ℂ)) =
      (primeEulerAmbientLossScale p : ℂ)⁻¹ := by
  have hsqrt : (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos p))
  have hupper : (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one
        (ccm24PrimeEulerCoefficient_nonneg p))
  rw [primeEulerAmbientLossScale]
  push_cast
  field_simp [hsqrt, hupper]

/-- The genuine square-root-scaled polar boundary channel. -/
noncomputable def routeScaledOldCarrierPolarBoundaryChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) : SourceOp unitSoninScale :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandOldCarrierPolarBoundaryChannel
      owner unitSoninScale index.prime index.suffix

/-- Route scaling cancels the upper Euler factor and leaves exactly the
inverse ambient-loss scale on the physical boundary defect. -/
theorem routeScaledOldCarrierPolarBoundaryChannel_eq_ambientLossScaled
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledOldCarrierPolarBoundaryChannel owner index =
      ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
        suffixEulerDetectorBoundaryDefect owner unitSoninScale
          index.prime index.suffix := by
  rw [routeScaledOldCarrierPolarBoundaryChannel,
    suffixActualBandOldCarrierPolarBoundaryChannel]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  rw [inv_sqrtCoefficient_mul_upperFactor_eq_inv_ambientLossScale]

/-- The route-scaled polar boundary channel has the uniform constant
`6 ||W||`, independently of the prime and suffix. -/
theorem norm_routeScaledOldCarrierPolarBoundaryChannel_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    ‖routeScaledOldCarrierPolarBoundaryChannel owner index‖ ≤
      6 * ‖detectorOperator owner‖ := by
  have hscale : 0 < primeEulerAmbientLossScale index.prime := by
    rw [primeEulerAmbientLossScale]
    exact div_pos
      (Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos index.prime))
      (add_pos_of_pos_of_nonneg zero_lt_one
        (ccm24PrimeEulerCoefficient_nonneg index.prime))
  rw [routeScaledOldCarrierPolarBoundaryChannel_eq_ambientLossScaled,
    norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale index.prime)⁻¹ *
        ‖suffixEulerDetectorBoundaryDefect owner unitSoninScale
          index.prime index.suffix‖ ≤
      (primeEulerAmbientLossScale index.prime)⁻¹ *
        (6 * primeEulerAmbientLossScale index.prime *
          ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left
        (norm_suffixEulerDetectorBoundaryDefect_le owner unitSoninScale
          index.prime index.suffix)
        (inv_nonneg.mpr hscale.le)
    _ = 6 * ‖detectorOperator owner‖ := by
      field_simp [ne_of_gt hscale]

/-! ## Residual after deleting the controlled polar channel -/

/-- The fixed base detector response minus the physical first jet. -/
noncomputable def suffixActualBandBaseFirstJetDifferenceKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandFixedSourceDetectorCompression owner lambda -
    suffixActualBandPhysicalFirstJetResponse owner lambda S

/-- The remaining old-carrier column after deleting the controlled polar
detector intertwinement.  Its two terms must remain signed and coupled. -/
noncomputable def suffixActualBandPolarBoundaryResidualColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
      suffixActualBandBaseFirstJetDifferenceKernel owner lambda S -
    suffixActualBandBaseFirstJetDifferenceKernel owner lambda (p :: S) ∘L
      suffixActualBandOldCarrierTransitionGauge lambda p S +
    suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
      (suffixPolarDetectorCompression owner lambda (p :: S) -
        suffixPolarDetectorCompression owner lambda S) ∘L
      suffixActualBandMetricCoframeSqrt lambda S

private theorem polarBoundary_split_identity
    {A : Type*} [Ring A]
    (transition base oldDetector newDetector oldFirstJet newFirstJet
      metricIncrement : A) :
    transition * (base + oldDetector - oldFirstJet) -
          (base + newDetector - newFirstJet) * transition +
        metricIncrement =
      (transition * oldDetector - newDetector * transition) +
        (transition * (base - oldFirstJet) -
          (base - newFirstJet) * transition + metricIncrement) := by
  noncomm_ring

/-- Proof 666's complete recurrence is the controlled polar boundary plus
one remaining signed base/first-jet and metric-increment residual. -/
theorem suffixActualBandPolarFirstJetRecurrenceColumn_eq_boundary_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarFirstJetRecurrenceColumn owner lambda p S =
      suffixActualBandOldCarrierPolarBoundaryChannel owner lambda p S +
        suffixActualBandPolarBoundaryResidualColumn owner lambda p S := by
  rw [suffixActualBandPolarFirstJetRecurrenceColumn,
    suffixActualBandPolarFirstJetDefectKernel,
    suffixActualBandPolarBoundaryResidualColumn,
    suffixActualBandBaseFirstJetDifferenceKernel]
  let metricIncrement : SourceOp lambda :=
    suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
      (suffixPolarDetectorCompression owner lambda (p :: S) -
        suffixPolarDetectorCompression owner lambda S) ∘L
      suffixActualBandMetricCoframeSqrt lambda S
  calc
    suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          (suffixActualBandFixedSourceDetectorCompression owner lambda +
            suffixPolarDetectorCompression owner lambda S -
            suffixActualBandPhysicalFirstJetResponse owner lambda S) -
        (suffixActualBandFixedSourceDetectorCompression owner lambda +
            suffixPolarDetectorCompression owner lambda (p :: S) -
            suffixActualBandPhysicalFirstJetResponse owner lambda (p :: S)) ∘L
          suffixActualBandOldCarrierTransitionGauge lambda p S +
        metricIncrement =
      (suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixActualBandOldCarrierTransitionGauge lambda p S) +
        (suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
            (suffixActualBandFixedSourceDetectorCompression owner lambda -
              suffixActualBandPhysicalFirstJetResponse owner lambda S) -
          (suffixActualBandFixedSourceDetectorCompression owner lambda -
              suffixActualBandPhysicalFirstJetResponse
                owner lambda (p :: S)) ∘L
            suffixActualBandOldCarrierTransitionGauge lambda p S +
          metricIncrement) := by
        simpa only [ContinuousLinearMap.mul_def] using
          (polarBoundary_split_identity
            (transition :=
              suffixActualBandOldCarrierTransitionGauge lambda p S)
            (base :=
              suffixActualBandFixedSourceDetectorCompression owner lambda)
            (oldDetector := suffixPolarDetectorCompression owner lambda S)
            (newDetector :=
              suffixPolarDetectorCompression owner lambda (p :: S))
            (oldFirstJet :=
              suffixActualBandPhysicalFirstJetResponse owner lambda S)
            (newFirstJet :=
              suffixActualBandPhysicalFirstJetResponse
                owner lambda (p :: S))
            (metricIncrement := metricIncrement))
    _ = suffixActualBandOldCarrierPolarBoundaryChannel owner lambda p S +
        (suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
            (suffixActualBandFixedSourceDetectorCompression owner lambda -
              suffixActualBandPhysicalFirstJetResponse owner lambda S) -
          (suffixActualBandFixedSourceDetectorCompression owner lambda -
              suffixActualBandPhysicalFirstJetResponse
                owner lambda (p :: S)) ∘L
            suffixActualBandOldCarrierTransitionGauge lambda p S +
          metricIncrement) := by
      rw [suffixActualBandOldCarrierPolarBoundaryChannel,
        suffixActualBandOldCarrierDetectorIntertwining_eq_boundary]

/-- The genuine route-scaled residual after removing the polar boundary. -/
noncomputable def routeScaledPolarBoundaryResidualColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) : SourceOp unitSoninScale :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandPolarBoundaryResidualColumn
      owner unitSoninScale index.prime index.suffix

/-- The route-scaled Proof 666 recurrence is the sum of the uniformly
controlled polar channel and the route-scaled residual. -/
theorem routeScaledBalancedPolarFirstJetRecurrenceColumn_eq_boundary_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledBalancedPolarFirstJetRecurrenceColumn owner index =
      routeScaledOldCarrierPolarBoundaryChannel owner index +
        routeScaledPolarBoundaryResidualColumn owner index := by
  rw [routeScaledBalancedPolarFirstJetRecurrenceColumn,
    routeScaledOldCarrierPolarBoundaryChannel,
    routeScaledPolarBoundaryResidualColumn,
    suffixActualBandPolarFirstJetRecurrenceColumn_eq_boundary_add_residual]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_add]

/-- A route-uniform bound for the residual after deleting the polar boundary
channel. -/
def SuffixPolarBoundaryResidualRouteUniformScaledBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledPolarBoundaryResidualColumn owner index‖ ≤ bound

/-- A residual bound produces a Proof 666 recurrence bound after adding the
explicit polar constant `6 ||W||`. -/
theorem polarBoundaryResidualRouteUniformScaledBound_to_recurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {bound : ℝ}
    (data : SuffixPolarBoundaryResidualRouteUniformScaledBound owner bound) :
    SuffixBalancedPolarFirstJetRecurrenceRouteUniformScaledBound owner
      (bound + 6 * ‖detectorOperator owner‖) := by
  refine ⟨add_nonneg data.1 (mul_nonneg (by norm_num) (norm_nonneg _)), ?_⟩
  intro index
  rw [routeScaledBalancedPolarFirstJetRecurrenceColumn_eq_boundary_add_residual]
  calc
    ‖routeScaledOldCarrierPolarBoundaryChannel owner index +
        routeScaledPolarBoundaryResidualColumn owner index‖ ≤
      ‖routeScaledOldCarrierPolarBoundaryChannel owner index‖ +
        ‖routeScaledPolarBoundaryResidualColumn owner index‖ :=
      norm_add_le _ _
    _ ≤ 6 * ‖detectorOperator owner‖ + bound :=
      add_le_add
        (norm_routeScaledOldCarrierPolarBoundaryChannel_le owner index)
        (data.2 index)
    _ = bound + 6 * ‖detectorOperator owner‖ := by ring

/-- Conversely, a Proof 666 recurrence bound controls the residual after the
same explicit polar constant is added. -/
theorem polarFirstJetRecurrenceRouteUniformScaledBound_to_boundaryResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {bound : ℝ}
    (data :
      SuffixBalancedPolarFirstJetRecurrenceRouteUniformScaledBound
        owner bound) :
    SuffixPolarBoundaryResidualRouteUniformScaledBound owner
      (bound + 6 * ‖detectorOperator owner‖) := by
  refine ⟨add_nonneg data.1 (mul_nonneg (by norm_num) (norm_nonneg _)), ?_⟩
  intro index
  have hresidual :
      routeScaledPolarBoundaryResidualColumn owner index =
        routeScaledBalancedPolarFirstJetRecurrenceColumn owner index -
          routeScaledOldCarrierPolarBoundaryChannel owner index := by
    rw [
      routeScaledBalancedPolarFirstJetRecurrenceColumn_eq_boundary_add_residual]
    abel
  rw [hresidual]
  calc
    ‖routeScaledBalancedPolarFirstJetRecurrenceColumn owner index -
        routeScaledOldCarrierPolarBoundaryChannel owner index‖ ≤
      ‖routeScaledBalancedPolarFirstJetRecurrenceColumn owner index‖ +
        ‖routeScaledOldCarrierPolarBoundaryChannel owner index‖ :=
      norm_sub_le _ _
    _ ≤ bound + 6 * ‖detectorOperator owner‖ :=
      add_le_add (data.2 index)
        (norm_routeScaledOldCarrierPolarBoundaryChannel_le owner index)

/-- Bone 1A exists exactly when the remaining base/first-jet covariance and
metric detector increment have a route-uniform bound.  The conversion costs
only the explicit controlled polar constant `6 ||W||`. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_polarBoundaryResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixPolarBoundaryResidualRouteUniformScaledBound owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_polarFirstJetRecurrence]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound + 6 * ‖detectorOperator owner‖,
      polarFirstJetRecurrenceRouteUniformScaledBound_to_boundaryResidual
        owner data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound + 6 * ‖detectorOperator owner‖,
      polarBoundaryResidualRouteUniformScaledBound_to_recurrence owner data⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarBoundaryReduction
end CCM25Concrete
end Source
end ConnesWeilRH
