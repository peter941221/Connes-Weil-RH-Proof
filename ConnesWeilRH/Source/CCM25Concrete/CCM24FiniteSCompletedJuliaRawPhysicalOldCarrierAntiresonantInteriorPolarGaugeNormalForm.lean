/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientMetricFirstJetResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence

/-!
# Balanced polar-gauge normal form

Proof 662 leaves the one-sided covariance of the recombined polar/raw
mismatch

```text
M_S = RoutePolarKernel_S - FirstJetResponse_S.
```

This module changes source coordinates before estimating it.  Write
`R_S = Gamma_S^(-1/2)` and `L_S = R_S Gamma_S`.  The two factors are exact
inverses.  The adjacent compressed transition therefore has the literal form

```text
T_(p,S) = (1 + q_p)^(-1) L_(p::S) R_S.
```

For the balanced response `X_S = R_S M_S L_S`, the unknown one-sided defect
becomes

```text
T_(p,S) M_S - M_(p::S) T_(p,S)
  = (1 + q_p)^(-1) L_(p::S) (X_S - X_(p::S)) R_S.
```

After the old polar frame is restored, its left gauge cancels exactly.  After
division by the ambient-loss scale, the remaining scalar is `q_p^(-1/2)`.
Thus Bone 1A is reduced, without loss of constants, to a square-root-scale
adjacent difference of the balanced response.

This is an exact normal form, not the missing uniform estimate.  In
particular it proves no route-uniform control of the unpolarized frame,
`R_S`, or `X_S - X_(p::S)` separately.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaRouteKernelNormalForm
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientMetricFirstJetResidual
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "SourceToFinite" lambda =>
  sourceSoninCarrier lambda →L[ℂ] finiteSCarrier

/-! ## Literal-list polar gauges -/

/-- The inverse partner `L_S = Gamma_S^(-1/2) Gamma_S` of the literal
inverse-Gram square root. -/
noncomputable def suffixActualBandMetricFrameGauge
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandMetricCoframeSqrt lambda S ∘L
    parameterizedSoninGram lambda 1 S

/-- The coframe gauge followed by the frame gauge is the identity. -/
theorem suffixActualBandMetricCoframeSqrt_comp_frameGauge
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframeSqrt lambda S ∘L
        suffixActualBandMetricFrameGauge lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [suffixActualBandMetricFrameGauge,
    ← ContinuousLinearMap.comp_assoc,
    suffixActualBandMetricCoframeSqrt]
  rw [parameterizedSoninGramInvSqrt_mul_self]
  simpa only [ContinuousLinearMap.mul_def,
    ContinuousLinearMap.one_def] using
      parameterizedSoninGramInv_mul_gram lambda 1 S (by norm_num)

/-- The two literal gauges are inverses in the opposite order as well. -/
theorem suffixActualBandMetricFrameGauge_comp_coframeSqrt
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricFrameGauge lambda S ∘L
        suffixActualBandMetricCoframeSqrt lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun operator : SourceOp lambda => operator x)
    (parameterizedSoninGramInvSqrt_gram_mul
      lambda 1 S (by norm_num))
  simpa only [suffixActualBandMetricFrameGauge,
    suffixActualBandMetricCoframeSqrt,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

/-- Restoring the left gauge turns the polar frame back into the literal
unpolarized restricted Euler frame. -/
theorem newSuffixFrame_comp_metricFrameGauge_eq_parameterizedSoninFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixFrame lambda S ∘L
        suffixActualBandMetricFrameGauge lambda S =
      parameterizedSoninFrame lambda 1 S := by
  apply ContinuousLinearMap.ext
  intro x
  have hinverse := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  simpa only [newSuffixFrame, parameterizedSoninPolarFrame,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using
      congrArg (parameterizedSoninFrame lambda 1 S) hinverse

/-! ## Exact adjacent transition -/

/-- The normalized one-prime transport sends the suffix polar frame to the
next unpolarized frame with the old right gauge still attached. -/
theorem normalizedPrimeEulerFrameTransport_comp_newSuffixFrame_eq_polarGauge
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L newSuffixFrame lambda S =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        (parameterizedSoninFrame lambda 1 (p :: S) ∘L
          suffixActualBandMetricCoframeSqrt lambda S) := by
  apply ContinuousLinearMap.ext
  intro x
  change ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
      ccm24PrimeEulerTransportEquiv p
        (parameterizedSoninFrame lambda 1 S
          (suffixActualBandMetricCoframeSqrt lambda S x)) =
    ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
      parameterizedSoninFrame lambda 1 (p :: S)
        (suffixActualBandMetricCoframeSqrt lambda S x)
  let u := parameterizedSoninFrame lambda 1 S
    (suffixActualBandMetricCoframeSqrt lambda S x)
  have hfactor : ccm24PrimeEulerTransportEquiv p u =
      parameterizedPrimeEulerFactor 1 p u := by
    change (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap u = _
    rw [← parameterizedPrimeEulerFactor_one]
  rw [show parameterizedSoninFrame lambda 1 S
      (suffixActualBandMetricCoframeSqrt lambda S x) = u by rfl,
    hfactor]
  rfl

/-- Exact balanced-gauge formula for the actual compressed forward Schur
transition.  No self-adjointness of the transition is used. -/
theorem suffixEulerFrameTransition_eq_polarGauge
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameTransition lambda p S =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        (suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
          suffixActualBandMetricCoframeSqrt lambda S) := by
  apply ContinuousLinearMap.ext
  intro x
  have htransport := congrArg
    (fun operator : SourceToFinite lambda => operator x)
    (normalizedPrimeEulerFrameTransport_comp_newSuffixFrame_eq_polarGauge
      lambda p S)
  have hframe := congrArg
    (fun operator : SourceToFinite lambda =>
      operator (suffixActualBandMetricCoframeSqrt lambda S x))
    (newSuffixFrame_comp_metricFrameGauge_eq_parameterizedSoninFrame
      lambda (p :: S))
  have hisometry := congrArg
    (fun operator : SourceOp lambda =>
      operator
        (suffixActualBandMetricFrameGauge lambda (p :: S)
          (suffixActualBandMetricCoframeSqrt lambda S x)))
    (parameterizedSoninPolarFrame_adjoint_comp_self
      lambda 1 (p :: S) (by norm_num))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at htransport hframe
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hisometry
  change ContinuousLinearMap.adjoint (newSuffixFrame lambda (p :: S))
      (normalizedPrimeEulerFrameTransport p (newSuffixFrame lambda S x)) =
    ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
      suffixActualBandMetricFrameGauge lambda (p :: S)
        (suffixActualBandMetricCoframeSqrt lambda S x)
  rw [htransport, ← hframe, map_smul]
  simpa only [newSuffixFrame] using congrArg
    (fun y : sourceSoninCarrier lambda =>
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) • y)
    hisometry

/-! ## Balanced mismatch difference -/

/-- The recombined polar/raw mismatch in the balanced source gauge
`X_S = R_S M_S L_S`. -/
noncomputable def suffixActualBandBalancedPolarRawMismatchKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandMetricCoframeSqrt lambda S ∘L
    suffixActualBandRoutePolarRawMismatchKernel owner lambda S ∘L
      suffixActualBandMetricFrameGauge lambda S

/-- The balanced response is exactly the recombined metric/first-jet response
in the new gauge. -/
theorem suffixActualBandBalancedPolarRawMismatchKernel_eq_metric_sub_firstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPolarRawMismatchKernel owner lambda S =
      suffixActualBandMetricCoframeSqrt lambda S ∘L
        (suffixActualBandRoutePolarKernel owner lambda S -
          suffixActualBandFirstJetCycledResponse owner lambda S) ∘L
        suffixActualBandMetricFrameGauge lambda S := by
  rw [suffixActualBandBalancedPolarRawMismatchKernel,
    suffixActualBandRoutePolarRawMismatchKernel_eq_routePolarKernel_sub_firstJet]

/-- The one-sided mismatch intertwinement is a balanced adjacent difference
surrounded by the two exact gauge factors. -/
theorem
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polarGaugeDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        (suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
          (suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
            suffixActualBandBalancedPolarRawMismatchKernel
              owner lambda (p :: S)) ∘L
          suffixActualBandMetricCoframeSqrt lambda S) := by
  rw [suffixActualBandRoutePolarRawMismatchIntertwiningDefect,
    suffixEulerFrameTransition_eq_polarGauge]
  apply ContinuousLinearMap.ext
  intro x
  have hsource := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  have htarget (y : sourceSoninCarrier lambda) := congrArg
    (fun operator : SourceOp lambda => operator y)
    (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda (p :: S))
  simp only [suffixActualBandBalancedPolarRawMismatchKernel,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_sub, map_smul, smul_sub] at hsource htarget ⊢
  rw [hsource, htarget]

/-! ## Ambient and route-scaled readback -/

/-- The ambient column after the left polar gauge has cancelled. -/
noncomputable def suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  parameterizedSoninFrame lambda 1 (p :: S) ∘L
    (suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
      suffixActualBandBalancedPolarRawMismatchKernel
        owner lambda (p :: S)) ∘L
    suffixActualBandMetricCoframeSqrt lambda S

/-- Exact ambient normal form for Proof 662's recombined residual. -/
theorem suffixActualBandAmbientMetricFirstJetResidualColumn_eq_polarGaugeDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientMetricFirstJetResidualColumn owner lambda p S =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn
          owner lambda p S := by
  rw [suffixActualBandAmbientMetricFirstJetResidualColumn_eq_oldFrame,
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polarGaugeDifference]
  apply ContinuousLinearMap.ext
  intro x
  have hframe := congrArg
    (fun operator : SourceToFinite lambda =>
      operator
        ((suffixActualBandBalancedPolarRawMismatchKernel owner lambda S -
          suffixActualBandBalancedPolarRawMismatchKernel
            owner lambda (p :: S))
          (suffixActualBandMetricCoframeSqrt lambda S x)))
    (newSuffixFrame_comp_metricFrameGauge_eq_parameterizedSoninFrame
      lambda (p :: S))
  simp only [ContinuousLinearMap.comp_apply] at hframe
  simp only [suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul]
  simpa only [oldSuffixFrame, newSuffixFrame] using congrArg
    (fun y : finiteSCarrier =>
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) • y)
    hframe

/-- Dividing the normalized transition scalar by the ambient-loss scale
leaves exactly the inverse square root of the Euler coefficient. -/
theorem inv_ambientLossScale_mul_inv_upperFactor_eq_inv_sqrt_coefficient
    (p : CCM24VisiblePrime) :
    ((primeEulerAmbientLossScale p : ℂ)⁻¹) *
        ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) =
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)⁻¹ := by
  have hsqrt : (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos p))
  have hden : (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one
        (ccm24PrimeEulerCoefficient_nonneg p))
  rw [primeEulerAmbientLossScale]
  push_cast
  field_simp [hsqrt, hden]

/-- The square-root-scaled balanced adjacent difference at one route-valid
step. -/
noncomputable def routeScaledBalancedPolarGaugeDifferenceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[ℂ] finiteSCarrier :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandAmbientBalancedPolarGaugeDifferenceColumn
      owner unitSoninScale index.prime index.suffix

/-- Proof 662's scaled residual is literally the square-root-scaled balanced
adjacent difference. -/
theorem routeScaledAmbientMetricFirstJetResidualColumn_eq_polarGaugeDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledAmbientMetricFirstJetResidualColumn owner index =
      routeScaledBalancedPolarGaugeDifferenceColumn owner index := by
  rw [routeScaledAmbientMetricFirstJetResidualColumn,
    suffixActualBandAmbientMetricFirstJetResidualColumn_eq_polarGaugeDifference,
    routeScaledBalancedPolarGaugeDifferenceColumn]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  rw [inv_ambientLossScale_mul_inv_upperFactor_eq_inv_sqrt_coefficient]

/-- One bound for all route-valid square-root-scaled balanced differences. -/
def SuffixBalancedPolarGaugeRouteUniformScaledDifferenceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledBalancedPolarGaugeDifferenceColumn owner index‖ ≤ bound

/-- The remaining Proof 662 bound and the balanced-gauge bound are the same
statement with the same constant. -/
theorem metricFirstJetRouteUniformScaledResidualBound_iff_polarGaugeDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixAmbientMetricFirstJetRouteUniformScaledResidualBound owner bound ↔
      SuffixBalancedPolarGaugeRouteUniformScaledDifferenceBound
        owner bound := by
  constructor
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [← routeScaledAmbientMetricFirstJetResidualColumn_eq_polarGaugeDifference]
    exact data.2 index
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [routeScaledAmbientMetricFirstJetResidualColumn_eq_polarGaugeDifference]
    exact data.2 index

/-- Bone 1A is exactly the existence of a route-uniform bound for the
square-root-scaled balanced adjacent response. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_polarGaugeDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixBalancedPolarGaugeRouteUniformScaledDifferenceBound
          owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_metricFirstJet]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (metricFirstJetRouteUniformScaledResidualBound_iff_polarGaugeDifference
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (metricFirstJetRouteUniformScaledResidualBound_iff_polarGaugeDifference
        owner bound).mpr data⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
