/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRawIntertwiningAmbientReduction

/-!
# The recombined ambient metric/first-jet residual

Proof 661 moves the raw intertwinement isometrically to one ambient covariance
column.  This module separates only the part already controlled by the
adjacent polar projections.  If `U_S` is the actual polar frame and `P_S` its
range projection, then

```text
U_S (U_S^dagger W U_S) U_S^dagger = P_S W P_S.
```

The remaining response is the polar/raw mismatch.  On the source carrier it
has the exact recombined form

```text
RoutePolarKernel_S - FirstJetResponse_S.
```

Its ambient covariance is therefore named the metric/first-jet residual and
kept intact.  The exact split is

```text
RawCovariance_(p,S)
  = PolarProjectionCovariance_(p,S)
    - MetricFirstJetResidual_(p,S).
```

The polar column has the already proved `6 s_p ||W||` bound.  Consequently a
route-uniform scaled raw bound exists exactly when one exists for the
recombined residual.  This is another exact reduction, not the missing
uniform estimate.  It does not license separate bounds for the metric and
first-jet summands.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientMetricFirstJetResidual

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaRouteKernelNormalForm
open CCM24FiniteSCompletedJuliaSynthesis
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRawIntertwiningAmbientReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "SourceToFinite" lambda =>
  sourceSoninCarrier lambda →L[ℂ] finiteSCarrier

/-! ## The controlled adjacent projection channel -/

/-- Ambient lift of the detector compressed through the actual suffix polar
frame. -/
noncomputable def suffixActualBandPolarLiftedDetectorCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  newSuffixFrame lambda S ∘L
    suffixPolarDetectorCompression owner lambda S ∘L
      (newSuffixFrame lambda S)†

/-- The polar lift is literally the detector sandwiched by the actual range
projection. -/
theorem suffixActualBandPolarLiftedDetectorCompression_eq_projectionSandwich
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandPolarLiftedDetectorCompression owner lambda S =
      newSuffixRangeProjection lambda S ∘L detectorOperator owner ∘L
        newSuffixRangeProjection lambda S := by
  rfl

/-- The adjacent covariance column of the polar projection sandwich. -/
noncomputable def suffixActualBandAmbientPolarProjectionCovarianceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (normalizedPrimeEulerFrameTransport p ∘L
        suffixActualBandPolarLiftedDetectorCompression owner lambda S -
      suffixActualBandPolarLiftedDetectorCompression owner lambda (p :: S) ∘L
        normalizedPrimeEulerFrameTransport p) ∘L
    newSuffixFrame lambda S

/-- The polar ambient covariance is the old-frame lift of the familiar polar
intertwining defect. -/
theorem suffixActualBandAmbientPolarProjectionCovarianceColumn_eq_oldFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientPolarProjectionCovarianceColumn owner lambda p S =
      oldSuffixFrame lambda p S ∘L
        suffixActualBandPolarIntertwiningDefect owner lambda p S := by
  have hnew : (newSuffixFrame lambda S)† ∘L newSuffixFrame lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) :=
    (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hold : (oldSuffixFrame lambda p S)† ∘L
        oldSuffixFrame lambda p S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) :=
    (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have htransport : normalizedPrimeEulerFrameTransport p ∘L
        newSuffixFrame lambda S =
      oldSuffixFrame lambda p S ∘L
        suffixEulerFrameTransition lambda p S := by
    simpa only [suffixEulerFrameSchurStep] using
      (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  simpa only [suffixActualBandAmbientPolarProjectionCovarianceColumn,
    suffixActualBandPolarLiftedDetectorCompression,
    suffixActualBandPolarIntertwiningDefect] using
    (frameLiftedCovarianceColumn_eq
      (newSuffixFrame lambda S) (oldSuffixFrame lambda p S)
      (normalizedPrimeEulerFrameTransport p)
      (suffixEulerFrameTransition lambda p S)
      (suffixPolarDetectorCompression owner lambda S)
      (suffixPolarDetectorCompression owner lambda (p :: S))
      hnew hold htransport)

/-- The controlled ambient projection channel has exactly the same norm as
its source intertwinement. -/
theorem norm_suffixActualBandAmbientPolarProjectionCovarianceColumn_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandAmbientPolarProjectionCovarianceColumn
        owner lambda p S‖ =
      ‖suffixActualBandPolarIntertwiningDefect owner lambda p S‖ := by
  rw [suffixActualBandAmbientPolarProjectionCovarianceColumn_eq_oldFrame]
  apply norm_isometric_postcomp_eq
  exact
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (oldSuffixFrame lambda p S)).mpr (by
        simpa only [ContinuousLinearMap.one_def] using
          (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry)

/-- The polar projection covariance retains the proved `6 s_p` bound. -/
theorem norm_suffixActualBandAmbientPolarProjectionCovarianceColumn_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandAmbientPolarProjectionCovarianceColumn
        owner lambda p S‖ ≤
      6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
  rw [norm_suffixActualBandAmbientPolarProjectionCovarianceColumn_eq]
  exact norm_suffixActualBandPolarIntertwiningDefect_le owner lambda p S

/-- After division by the genuine ambient-loss scale, the adjacent polar
projection channel costs at most `6 ||W||`. -/
theorem
    norm_ambientLossScaled_suffixActualBandAmbientPolarProjectionCovarianceColumn_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandAmbientPolarProjectionCovarianceColumn
          owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale p)⁻¹ *
        ‖suffixActualBandAmbientPolarProjectionCovarianceColumn
          owner lambda p S‖ ≤
      (primeEulerAmbientLossScale p)⁻¹ *
        (6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left
        (norm_suffixActualBandAmbientPolarProjectionCovarianceColumn_le
          owner lambda p S)
        (inv_nonneg.mpr hscale.le)
    _ = 6 * ‖detectorOperator owner‖ := by
      field_simp [ne_of_gt hscale]

/-! ## The recombined metric/first-jet residual -/

/-- Ambient lift of the same-object polar/raw mismatch.  This response is
kept recombined before taking its adjacent covariance. -/
noncomputable def suffixActualBandPolarRawMismatchLiftedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  newSuffixFrame lambda S ∘L
    suffixActualBandRoutePolarRawMismatchKernel owner lambda S ∘L
      (newSuffixFrame lambda S)†

/-- The mismatch lift is exactly the route metric kernel minus the complete
first-jet response, still inside one frame sandwich. -/
theorem suffixActualBandPolarRawMismatchLiftedResponse_eq_metric_sub_firstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandPolarRawMismatchLiftedResponse owner lambda S =
      newSuffixFrame lambda S ∘L
        (suffixActualBandRoutePolarKernel owner lambda S -
          suffixActualBandFirstJetCycledResponse owner lambda S) ∘L
        (newSuffixFrame lambda S)† := by
  rw [suffixActualBandPolarRawMismatchLiftedResponse,
    suffixActualBandRoutePolarRawMismatchKernel_eq_routePolarKernel_sub_firstJet]

/-- The intact ambient covariance of the recombined metric/first-jet
residual. -/
noncomputable def suffixActualBandAmbientMetricFirstJetResidualColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (normalizedPrimeEulerFrameTransport p ∘L
        suffixActualBandPolarRawMismatchLiftedResponse owner lambda S -
      suffixActualBandPolarRawMismatchLiftedResponse owner lambda (p :: S) ∘L
        normalizedPrimeEulerFrameTransport p) ∘L
    newSuffixFrame lambda S

/-- The ambient residual is the isometric old-frame lift of the complete
polar/raw mismatch intertwinement. -/
theorem suffixActualBandAmbientMetricFirstJetResidualColumn_eq_oldFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientMetricFirstJetResidualColumn owner lambda p S =
      oldSuffixFrame lambda p S ∘L
        suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S := by
  have hnew : (newSuffixFrame lambda S)† ∘L newSuffixFrame lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) :=
    (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hold : (oldSuffixFrame lambda p S)† ∘L
        oldSuffixFrame lambda p S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) :=
    (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have htransport : normalizedPrimeEulerFrameTransport p ∘L
        newSuffixFrame lambda S =
      oldSuffixFrame lambda p S ∘L
        suffixEulerFrameTransition lambda p S := by
    simpa only [suffixEulerFrameSchurStep] using
      (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  simpa only [suffixActualBandAmbientMetricFirstJetResidualColumn,
    suffixActualBandPolarRawMismatchLiftedResponse,
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect] using
    (frameLiftedCovarianceColumn_eq
      (newSuffixFrame lambda S) (oldSuffixFrame lambda p S)
      (normalizedPrimeEulerFrameTransport p)
      (suffixEulerFrameTransition lambda p S)
      (suffixActualBandRoutePolarRawMismatchKernel owner lambda S)
      (suffixActualBandRoutePolarRawMismatchKernel owner lambda (p :: S))
      hnew hold htransport)

/-- Exact ambient split: the raw covariance is the controlled polar
projection covariance minus the recombined metric/first-jet residual. -/
theorem suffixActualBandAmbientRawCovarianceColumn_eq_polar_sub_metricFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      suffixActualBandAmbientPolarProjectionCovarianceColumn
          owner lambda p S -
        suffixActualBandAmbientMetricFirstJetResidualColumn
          owner lambda p S := by
  have hsource :=
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw
      owner lambda p S
  have hcomp :
      oldSuffixFrame lambda p S ∘L
          suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S =
        oldSuffixFrame lambda p S ∘L
            suffixActualBandPolarIntertwiningDefect owner lambda p S -
          oldSuffixFrame lambda p S ∘L
            suffixActualBandRawQuadraticIntertwiningDefect
              owner lambda p S := by
    rw [hsource]
    apply ContinuousLinearMap.ext
    intro x
    simp only [suffixActualBandPolarIntertwiningDefect,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, map_sub]
  rw [suffixActualBandAmbientRawCovarianceColumn_eq_oldFrame_comp_rawDefect,
    suffixActualBandAmbientPolarProjectionCovarianceColumn_eq_oldFrame,
    suffixActualBandAmbientMetricFirstJetResidualColumn_eq_oldFrame,
    hcomp]
  abel

/-- The converse exact split, used to compare the two remaining route-uniform
statements without losing more than the controlled polar term. -/
theorem suffixActualBandAmbientMetricFirstJetResidualColumn_eq_polar_sub_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientMetricFirstJetResidualColumn owner lambda p S =
      suffixActualBandAmbientPolarProjectionCovarianceColumn
          owner lambda p S -
        suffixActualBandAmbientRawCovarianceColumn owner lambda p S := by
  rw [suffixActualBandAmbientRawCovarianceColumn_eq_polar_sub_metricFirstJet]
  abel

/-! ## Route-uniform residual equivalence -/

/-- The recombined ambient residual divided by the genuine one-prime loss
scale at one route-valid adjacent step. -/
noncomputable def routeScaledAmbientMetricFirstJetResidualColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[ℂ] finiteSCarrier :=
  ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
    suffixActualBandAmbientMetricFirstJetResidualColumn
      owner unitSoninScale index.prime index.suffix

/-- One bound for the recombined scaled residual on every route-valid
adjacent step. -/
def SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledAmbientMetricFirstJetResidualColumn owner index‖ ≤ bound

/-- A route-uniform raw ambient bound gives a residual bound after adding the
fixed controlled polar cost. -/
theorem SuffixAmbientRawRouteUniformScaledCovarianceBound.toMetricFirstJetBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : ℝ}
    (data : SuffixAmbientRawRouteUniformScaledCovarianceBound owner bound) :
    SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound owner
      (6 * ‖detectorOperator owner‖ + bound) := by
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _)) data.1, ?_⟩
  intro index
  unfold routeScaledAmbientMetricFirstJetResidualColumn
  rw [suffixActualBandAmbientMetricFirstJetResidualColumn_eq_polar_sub_raw]
  exact norm_smul_sub_le_of_norm_smul_left_le
    ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹)
    (suffixActualBandAmbientPolarProjectionCovarianceColumn
      owner unitSoninScale index.prime index.suffix)
    (suffixActualBandAmbientRawCovarianceColumn
      owner unitSoninScale index.prime index.suffix)
    (6 * ‖detectorOperator owner‖)
    (norm_ambientLossScaled_suffixActualBandAmbientPolarProjectionCovarianceColumn_le
      owner unitSoninScale index.prime index.suffix) |>.trans
        (add_le_add (le_refl _) (data.2 index))

/-- Conversely, a route-uniform residual bound gives the raw ambient bound
with the same fixed polar cost. -/
theorem
    SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound.toRawCovarianceBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : ℝ}
    (data :
      SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound owner bound) :
    SuffixAmbientRawRouteUniformScaledCovarianceBound owner
      (6 * ‖detectorOperator owner‖ + bound) := by
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _)) data.1, ?_⟩
  intro index
  unfold routeScaledAmbientRawCovarianceColumn
  rw [suffixActualBandAmbientRawCovarianceColumn_eq_polar_sub_metricFirstJet]
  exact norm_smul_sub_le_of_norm_smul_left_le
    ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹)
    (suffixActualBandAmbientPolarProjectionCovarianceColumn
      owner unitSoninScale index.prime index.suffix)
    (suffixActualBandAmbientMetricFirstJetResidualColumn
      owner unitSoninScale index.prime index.suffix)
    (6 * ‖detectorOperator owner‖)
    (norm_ambientLossScaled_suffixActualBandAmbientPolarProjectionCovarianceColumn_le
      owner unitSoninScale index.prime index.suffix) |>.trans
        (add_le_add (le_refl _) (data.2 index))

/-- The remaining route-uniform raw covariance bound exists exactly when a
bound exists for the recombined metric/first-jet residual. -/
theorem exists_routeUniformScaledAmbientRawCovarianceBound_iff_metricFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixAmbientRawRouteUniformScaledCovarianceBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound
          owner bound := by
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨6 * ‖detectorOperator owner‖ + bound,
      SuffixAmbientRawRouteUniformScaledCovarianceBound.toMetricFirstJetBound
        data⟩
  · rintro ⟨bound, data⟩
    exact ⟨6 * ‖detectorOperator owner‖ + bound,
      SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound.toRawCovarianceBound
        data⟩

/-- Combining Proofs 660--662, Bone 1A is exactly the existence of a
route-uniform scaled bound for the recombined ambient metric/first-jet
residual. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_metricFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound
          owner bound :=
  (exists_routeUniformScaledCompleteTargetBound_iff_ambientCovarianceBound
    owner).trans
      (exists_routeUniformScaledAmbientRawCovarianceBound_iff_metricFirstJet
        owner)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientMetricFirstJetResidual
end CCM25Concrete
end Source
end ConnesWeilRH
