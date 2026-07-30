/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovUniformBound

/-!
# Normalized arbitrary-suffix metric row

The raw metric coframe at a long suffix can carry the full finite-Euler
condition number.  The exact Schur--Markov scalar

```text
rho_S = finiteEulerLowerFactor(S) / finiteEulerUpperFactor(S)
```

removes that condition number before a norm is taken.  This module first
proves the contraction for every literal suffix list, rather than only for a
list presented as `family.visiblePrimes`.

The two hard metric rows are then recombined in their actual orientation.  If
`Hard_(p,S)` denotes `metric orientation + metric residual`, Lean proves

```text
||rho_(p::S) Hard_(p,S)|| <= 2 ||detector||.
```

This is a genuine route-uniform normalized bound.  It is not an unnormalized
Bone 1 estimate: removing `rho_(p::S)` costs its reciprocal, for which route
validity (`(p :: S).Nodup`) supplies no uniform bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNormalizedSuffixMetricRow

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (frameCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## A literal-list normalized dual frame -/

noncomputable abbrev suffixTargetTransportedSoninCarrier
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :=
  (transportedClosedSubmodule
    (parameterizedFiniteEulerEquiv 1 S (by norm_num))
    (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule

noncomputable local instance suffixTargetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    CompleteSpace (suffixTargetTransportedSoninCarrier lambda S) :=
  (transportedClosedSubmodule
    (parameterizedFiniteEulerEquiv 1 S (by norm_num))
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

noncomputable def suffixTargetTransportedSoninInclusion
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixTargetTransportedSoninCarrier lambda S →L[ℂ] finiteSCarrier :=
  (transportedClosedSubmodule
    (parameterizedFiniteEulerEquiv 1 S (by norm_num))
    (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule.subtypeL

noncomputable def suffixEulerRestrictedInverse
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixTargetTransportedSoninCarrier lambda S →L[ℂ]
      frameCarrier lambda :=
  restrictedClosedTransportInverse
    (parameterizedFiniteEulerEquiv 1 S (by norm_num))
    (ccm24ArchimedeanSoninClosedSubspace lambda)

set_option maxHeartbeats 4000000 in
-- The subtype equivalence and its rectangular adjoint elaborate together.
/-- The literal-list dual frame has the same restricted-inverse
factorization as the finite-family dual frame. -/
theorem suffixActualBandDualFrame_eq_targetInclusion_comp_inverseAdjoint
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandDualFrame lambda S =
      suffixTargetTransportedSoninInclusion lambda S ∘L
        (suffixEulerRestrictedInverse lambda S)† := by
  let T := parameterizedFiniteEulerEquiv 1 S (by norm_num)
  let source := ccm24ArchimedeanSoninClosedSubspace lambda
  let E := (restrictedClosedTransportEquiv T source).toContinuousLinearMap
  let B := restrictedClosedTransportInverse T source
  let J := (transportedClosedSubmodule T source).toSubmodule.subtypeL
  rw [suffixActualBandDualFrame, suffixActualBandFrame,
    suffixActualBandGramInv,
    parameterizedSoninFrame_eq_restrictedClosedTransport
      lambda 1 S (by norm_num)]
  change restrictedClosedTransport T source ∘L (B ∘L B†) = J ∘L B†
  rw [restrictedClosedTransport_eq_subtype_comp_equiv]
  apply ContinuousLinearMap.ext
  intro u
  change J (E (B ((B†) u))) = J ((B†) u)
  exact congrArg J (by
    simp [E, B, restrictedClosedTransportInverse])

theorem norm_lowerFactor_smul_suffixRestrictedInverse_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        suffixEulerRestrictedInverse lambda S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [one_mul, ContinuousLinearMap.smul_apply]
  have h := norm_lowerFactor_smul_finiteEulerInverse_le S
    (u : finiteSCarrier)
  change ‖(finiteEulerLowerFactor S : ℂ) •
      ((((restrictedClosedTransportEquiv
        (parameterizedFiniteEulerEquiv 1 S (by norm_num))
        (ccm24ArchimedeanSoninClosedSubspace lambda)).symm u :
          frameCarrier lambda) : finiteSCarrier))‖ ≤
      ‖(u : finiteSCarrier)‖
  rw [restrictedClosedTransportEquiv_symm_apply_coe]
  have happly :
      (parameterizedFiniteEulerEquiv 1 S (by norm_num)).symm
          (u : finiteSCarrier) =
        (ccm24FiniteEulerTransportEquiv S).symm (u : finiteSCarrier) := by
    rw [parameterizedFiniteEulerEquiv_one]
  rw [happly]
  exact h

theorem norm_lowerFactor_smul_suffixRestrictedInverseAdjoint_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        (suffixEulerRestrictedInverse lambda S)†‖ ≤ 1 := by
  have hadj : ‖(suffixEulerRestrictedInverse lambda S)†‖ =
      ‖suffixEulerRestrictedInverse lambda S‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    _ = ‖(finiteEulerLowerFactor S : ℂ) •
        suffixEulerRestrictedInverse lambda S‖ := by
      rw [norm_smul, norm_smul, hadj]
    _ ≤ 1 := norm_lowerFactor_smul_suffixRestrictedInverse_le_one lambda S

/-- The lower-factor-normalized literal-list dual frame is contractive. -/
theorem norm_lowerFactor_smul_suffixActualBandDualFrame_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        suffixActualBandDualFrame lambda S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [one_mul]
  rw [suffixActualBandDualFrame_eq_targetInclusion_comp_inverseAdjoint]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  have hinclude (v : suffixTargetTransportedSoninCarrier lambda S) :
      ‖suffixTargetTransportedSoninInclusion lambda S v‖ = ‖v‖ := rfl
  rw [norm_smul, hinclude]
  calc
    _ = ‖((finiteEulerLowerFactor S : ℂ) •
        (suffixEulerRestrictedInverse lambda S)†) u‖ := by
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    _ ≤ ‖(finiteEulerLowerFactor S : ℂ) •
          (suffixEulerRestrictedInverse lambda S)†‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_lowerFactor_smul_suffixRestrictedInverseAdjoint_le_one lambda S)
        (norm_nonneg u)
    _ = ‖u‖ := one_mul _

/-! ## The mixed literal-list metric coframe -/

theorem norm_invUpperFactor_smul_suffixTransportAdjoint_le_one
    (S : List CCM24VisiblePrime) :
    ‖((finiteEulerUpperFactor S : ℂ)⁻¹) •
        (suffixActualBandTransportOperator S)†‖ ≤ 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (finiteEulerUpperFactor_pos S),
    ContinuousLinearMap.adjoint.norm_map]
  have hupper : 0 ≤ (finiteEulerUpperFactor S)⁻¹ :=
    le_of_lt (inv_pos.mpr (finiteEulerUpperFactor_pos S))
  calc
    (finiteEulerUpperFactor S)⁻¹ *
        ‖suffixActualBandTransportOperator S‖ ≤
      (finiteEulerUpperFactor S)⁻¹ * finiteEulerUpperFactor S := by
        exact mul_le_mul_of_nonneg_left
          (by
            simpa only [suffixActualBandTransportOperator] using
              norm_finiteEulerTransportOperator_le_upperFactor S)
          hupper
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (finiteEulerUpperFactor_pos S))

noncomputable def suffixSchurMarkovMixedMetricCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    frameCarrier lambda →L[ℂ] finiteSCarrier :=
  (suffixEulerSchurMarkovScalar S : ℂ) •
    suffixActualBandMetricCoframe lambda S

theorem suffixActualBandMetricCoframe_eq_transportAdjoint_comp_dualFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframe lambda S =
      (suffixActualBandTransportOperator S)† ∘L
        suffixActualBandDualFrame lambda S := by
  rw [suffixActualBandMetricCoframe_eq_transportAdjoint_comp_frame_inv,
    suffixActualBandDualFrame]

theorem suffixSchurMarkovMixedMetricCoframe_eq_normalized_factors
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixSchurMarkovMixedMetricCoframe lambda S =
      (((finiteEulerUpperFactor S : ℂ)⁻¹) •
          (suffixActualBandTransportOperator S)†) ∘L
        ((finiteEulerLowerFactor S : ℂ) •
          suffixActualBandDualFrame lambda S) := by
  rw [suffixSchurMarkovMixedMetricCoframe,
    suffixActualBandMetricCoframe_eq_transportAdjoint_comp_dualFrame,
    suffixEulerSchurMarkovScalar_eq_lower_div_upper]
  have hscalar :
      ((finiteEulerLowerFactor S / finiteEulerUpperFactor S : ℝ) : ℂ) =
        (finiteEulerUpperFactor S : ℂ)⁻¹ *
          (finiteEulerLowerFactor S : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    ring
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul]
  rw [hscalar]
  module

/-- Exact family-scalar normalization makes the metric coframe contractive
for every literal suffix list. -/
theorem norm_suffixSchurMarkovMixedMetricCoframe_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖suffixSchurMarkovMixedMetricCoframe lambda S‖ ≤ 1 := by
  rw [suffixSchurMarkovMixedMetricCoframe_eq_normalized_factors]
  calc
    _ ≤ ‖((finiteEulerUpperFactor S : ℂ)⁻¹ •
          (suffixActualBandTransportOperator S)†)‖ *
        ‖(finiteEulerLowerFactor S : ℂ) •
          suffixActualBandDualFrame lambda S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (norm_invUpperFactor_smul_suffixTransportAdjoint_le_one S)
      (norm_lowerFactor_smul_suffixActualBandDualFrame_le_one lambda S)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The longer scalar also contracts the tail coframe.  The extra head
factor is at most one. -/
theorem norm_consScalar_smul_tailMetricCoframe_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        frameMetricCoframe lambda S‖ ≤ 1 := by
  have hpNonneg : 0 ≤ primeSchurMarkovScalar p :=
    (primeSchurMarkovScalar_pos p).le
  have hpOne : primeSchurMarkovScalar p ≤ 1 :=
    primeSchurMarkovScalar_le_one p
  have htail := norm_suffixSchurMarkovMixedMetricCoframe_le_one lambda S
  change ‖((primeSchurMarkovScalar p *
      suffixEulerSchurMarkovScalar S : ℝ) : ℂ) •
        suffixActualBandMetricCoframe lambda S‖ ≤ 1
  rw [show ((primeSchurMarkovScalar p *
      suffixEulerSchurMarkovScalar S : ℝ) : ℂ) =
      (primeSchurMarkovScalar p : ℂ) *
        (suffixEulerSchurMarkovScalar S : ℂ) by
          push_cast
          rfl,
    mul_smul]
  calc
    ‖(primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerSchurMarkovScalar S : ℂ) •
          suffixActualBandMetricCoframe lambda S)‖ ≤
      ‖(primeSchurMarkovScalar p : ℂ)‖ *
        ‖(suffixEulerSchurMarkovScalar S : ℂ) •
          suffixActualBandMetricCoframe lambda S‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = primeSchurMarkovScalar p *
        ‖suffixSchurMarkovMixedMetricCoframe lambda S‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpNonneg]
      rfl
    _ ≤ 1 * 1 := mul_le_mul hpOne htail (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ## The complete normalized boundary moment -/

theorem norm_scalar_smul_suffixForwardCoframe_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandForwardCoframe lambda S‖ ≤ 1 := by
  have hrhoNonneg : 0 ≤ suffixEulerSchurMarkovScalar S :=
    (suffixEulerSchurMarkovScalar_pos S).le
  have hrhoOne : suffixEulerSchurMarkovScalar S ≤ 1 :=
    suffixEulerSchurMarkovScalar_le_one S
  have hforward := frameForwardCoframe_norm_le_one lambda S
  calc
    ‖(suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandForwardCoframe lambda S‖ ≤
      ‖(suffixEulerSchurMarkovScalar S : ℂ)‖ *
        ‖suffixActualBandForwardCoframe lambda S‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = suffixEulerSchurMarkovScalar S *
        ‖frameForwardCoframe lambda S‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrhoNonneg]
      rfl
    _ ≤ 1 * 1 := mul_le_mul hrhoOne hforward (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_scalar_smul_suffixForwardEndpointCoframe_le_two
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandForwardEndpointCoframe lambda S‖ ≤ 2 := by
  rw [suffixActualBandForwardEndpointCoframe, smul_add]
  calc
    ‖(suffixEulerSchurMarkovScalar S : ℂ) •
          suffixActualBandForwardCoframe lambda S +
        (suffixEulerSchurMarkovScalar S : ℂ) •
          suffixActualBandMetricCoframe lambda S‖ ≤
      ‖(suffixEulerSchurMarkovScalar S : ℂ) •
          suffixActualBandForwardCoframe lambda S‖ +
        ‖suffixSchurMarkovMixedMetricCoframe lambda S‖ :=
      norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_scalar_smul_suffixForwardCoframe_le_one lambda S)
      (norm_suffixSchurMarkovMixedMetricCoframe_le_one lambda S)
    _ = 2 := by norm_num

/-- The existing three-detector bound extends from `family.visiblePrimes` to
every literal suffix list.  The endpoint remains the coupled forward-plus-
metric coframe. -/
theorem norm_scalar_smul_rawCoframeBoundaryMoment_literal_le_three_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar S : ℂ) •
        rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda S)‖ ≤
      3 * ‖detectorOperator owner‖ := by
  exact norm_smul_rawCoframeBoundaryMoment_le_three_mul_detector
    owner lambda (suffixEulerSchurMarkovScalar S)
    (suffixActualBandForwardCoframe lambda S)
    (suffixActualBandForwardEndpointCoframe lambda S)
    (norm_scalar_smul_suffixForwardCoframe_le_one lambda S)
    (norm_scalar_smul_suffixForwardEndpointCoframe_le_two lambda S)

theorem norm_consScalar_smul_tailBoundaryMoment_le_three_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda S)‖ ≤
      3 * ‖detectorOperator owner‖ := by
  let moment := rawCoframeBoundaryMoment owner lambda
    (suffixActualBandForwardCoframe lambda S)
    (suffixActualBandForwardEndpointCoframe lambda S)
  have hpNonneg : 0 ≤ primeSchurMarkovScalar p :=
    (primeSchurMarkovScalar_pos p).le
  have hpOne : primeSchurMarkovScalar p ≤ 1 :=
    primeSchurMarkovScalar_le_one p
  have htail :=
    norm_scalar_smul_rawCoframeBoundaryMoment_literal_le_three_mul_detector
      owner lambda S
  change ‖((primeSchurMarkovScalar p *
      suffixEulerSchurMarkovScalar S : ℝ) : ℂ) • moment‖ ≤
    3 * ‖detectorOperator owner‖
  rw [show ((primeSchurMarkovScalar p *
      suffixEulerSchurMarkovScalar S : ℝ) : ℂ) =
      (primeSchurMarkovScalar p : ℂ) *
        (suffixEulerSchurMarkovScalar S : ℂ) by
          push_cast
          rfl,
    mul_smul]
  calc
    ‖(primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerSchurMarkovScalar S : ℂ) • moment)‖ ≤
      ‖(primeSchurMarkovScalar p : ℂ)‖ *
        ‖(suffixEulerSchurMarkovScalar S : ℂ) • moment‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = primeSchurMarkovScalar p *
        ‖(suffixEulerSchurMarkovScalar S : ℂ) • moment‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpNonneg]
    _ ≤ 1 * (3 * ‖detectorOperator owner‖) :=
      mul_le_mul hpOne (by simpa only [moment] using htail)
        (norm_nonneg _) zero_le_one
    _ = 3 * ‖detectorOperator owner‖ := one_mul _

/-! ## The coupled adjacent metric row -/

private theorem norm_adjoint_detector_telescope_le_two
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C₀ C₁ D : H →L[ℂ] K) (T : H →L[ℂ] H) (O : K →L[ℂ] H)
    (hC₀ : ‖C₀‖ ≤ 1) (hC₁ : ‖C₁‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) (hO : ‖O‖ ≤ 1) :
    ‖((C₀† ∘L D ∘L T) - (T ∘L C₁† ∘L D)) ∘L O‖ ≤
      2 * ‖D‖ := by
  have hC₀Adj : ‖C₀†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hC₀
  have hC₁Adj : ‖C₁†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hC₁
  have hleft : ‖C₀† ∘L D ∘L T‖ ≤ ‖D‖ := by
    calc
      _ ≤ ‖C₀† ∘L D‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖C₀†‖ * ‖D‖) * ‖T‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg T)
      _ ≤ (1 * ‖D‖) * 1 := by
        gcongr
      _ = ‖D‖ := by ring
  have hright : ‖T ∘L C₁† ∘L D‖ ≤ ‖D‖ := by
    calc
      _ ≤ ‖T ∘L C₁†‖ * ‖D‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖T‖ * ‖C₁†‖) * ‖D‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg D)
      _ ≤ (1 * 1) * ‖D‖ := by
        gcongr
      _ = ‖D‖ := by ring
  calc
    ‖((C₀† ∘L D ∘L T) - (T ∘L C₁† ∘L D)) ∘L O‖ ≤
        ‖(C₀† ∘L D ∘L T) - (T ∘L C₁† ∘L D)‖ * ‖O‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖C₀† ∘L D ∘L T‖ + ‖T ∘L C₁† ∘L D‖) *
        ‖O‖ := by
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg O)
    _ ≤ (‖D‖ + ‖D‖) * 1 :=
      mul_le_mul (add_le_add hleft hright) hO
        (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖D‖ := by ring

private theorem norm_operator_telescope_le_two_mul
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A₀ A₁ T : H →L[ℂ] H) (O : K →L[ℂ] H) (bound : ℝ)
    (hA₀ : ‖A₀‖ ≤ bound) (hA₁ : ‖A₁‖ ≤ bound)
    (hT : ‖T‖ ≤ 1) (hO : ‖O‖ ≤ 1) :
    ‖A₀ ∘L T ∘L O - (T ∘L A₁) ∘L O‖ ≤ 2 * bound := by
  have hbound : 0 ≤ bound := le_trans (norm_nonneg A₀) hA₀
  have hTO : ‖T ∘L O‖ ≤ (1 : ℝ) := by
    calc
      ‖T ∘L O‖ ≤ ‖T‖ * ‖O‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hT hO (norm_nonneg O) zero_le_one
      _ = 1 := one_mul 1
  have hTA₁ : ‖T ∘L A₁‖ ≤ bound := by
    calc
      ‖T ∘L A₁‖ ≤ ‖T‖ * ‖A₁‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * bound :=
        mul_le_mul hT hA₁ (norm_nonneg A₁) zero_le_one
      _ = bound := one_mul bound
  have hleft : ‖A₀ ∘L T ∘L O‖ ≤ bound := by
    calc
      ‖A₀ ∘L T ∘L O‖ ≤ ‖A₀‖ * ‖T ∘L O‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 :=
        mul_le_mul hA₀ hTO (norm_nonneg _) hbound
      _ = bound := mul_one bound
  have hright : ‖(T ∘L A₁) ∘L O‖ ≤ bound := by
    calc
      ‖(T ∘L A₁) ∘L O‖ ≤ ‖T ∘L A₁‖ * ‖O‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 :=
        mul_le_mul hTA₁ hO (norm_nonneg O) hbound
      _ = bound := mul_one bound
  calc
    ‖A₀ ∘L T ∘L O - (T ∘L A₁) ∘L O‖ ≤
        ‖A₀ ∘L T ∘L O‖ + ‖(T ∘L A₁) ∘L O‖ := norm_sub_le _ _
    _ ≤ bound + bound := add_le_add hleft hright
    _ = 2 * bound := by ring

/-- Scaling the coupled hard row is exactly the telescope of the two scaled
metric coframes.  Orientation and survivor/boundary residual are not bounded
separately. -/
theorem scalar_smul_coframeHardRow_eq_scaledMetricTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        coframeHardRow owner lambda p S =
      ((((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          frameMetricCoframe lambda S)† ∘L
            suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
              frameTransitionAdjoint lambda p S -
        frameTransitionAdjoint lambda p S ∘L
          ((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
            frameMetricCoframe lambda (p :: S))† ∘L
              suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda) ∘L
        frameOldFrameAdjoint lambda p S) := by
  rw [coframeHardRow_eq_metricCoframeAdjointTelescope]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
  simp only [ContinuousLinearMap.smul_apply, map_smul,
    Complex.conj_ofReal, smul_sub]

/-- The exact family scalar gives a route-uniform bound for the complete
orientation-plus-residual metric row. -/
theorem norm_scalar_smul_coframeHardRow_le_two_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        coframeHardRow owner lambda p S‖ ≤
      2 * ‖detectorOperator owner‖ := by
  rw [scalar_smul_coframeHardRow_eq_scaledMetricTelescope]
  have hC₀ := norm_consScalar_smul_tailMetricCoframe_le_one lambda p S
  have hC₁ :=
    norm_suffixSchurMarkovMixedMetricCoframe_le_one lambda (p :: S)
  have hT : ‖frameTransitionAdjoint lambda p S‖ ≤ (1 : ℝ) := by
    calc
      ‖frameTransitionAdjoint lambda p S‖ =
          ‖suffixEulerFrameTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameTransition_norm_le_one lambda p S
  have hO : ‖frameOldFrameAdjoint lambda p S‖ ≤ (1 : ℝ) := by
    calc
      ‖frameOldFrameAdjoint lambda p S‖ =
          ‖(suffixEulerFrameSchurStep lambda p S).oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 :=
        CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion _ (by
          intro x
          exact parameterizedSoninPolarFrame_isometry
            lambda 1 (p :: S) (by norm_num) x)
  have htelescope := norm_adjoint_detector_telescope_le_two
    ((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
      frameMetricCoframe lambda S)
    ((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
      frameMetricCoframe lambda (p :: S))
    (suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)
    (frameTransitionAdjoint lambda p S)
    (frameOldFrameAdjoint lambda p S) hC₀ hC₁ hT hO
  calc
    _ ≤ 2 *
        ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ :=
      htelescope
    _ ≤ 2 * ‖detectorOperator owner‖ := by
      exact mul_le_mul_of_nonneg_left (detectorLeg_norm_le owner lambda)
        (by norm_num)

/-! ## The complete normalized row and numerator -/

set_option maxHeartbeats 4000000 in
-- This rebuilds the elementary `2 + 4` estimate from exported contraction
-- lemmas; the similarly named block in the old ledger is intentionally inert.
private theorem norm_coframeKnownBoundedRow_le_six_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖coframeKnownBoundedRow owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
  let J := CCM24FiniteSGramResponse.sourceInclusion lambda
  let D := suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda
  let T := frameTransitionAdjoint lambda p S
  let O := frameOldFrameAdjoint lambda p S
  let bound := ‖detectorOperator owner‖
  have hJ : ‖J‖ ≤ (1 : ℝ) := by
    simpa only [J] using
      (Submodule.norm_subtypeL_le
        (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule)
  have hJAdj : ‖J†‖ ≤ (1 : ℝ) := by
    calc
      ‖J†‖ = ‖J‖ := ContinuousLinearMap.adjoint.norm_map J
      _ ≤ 1 := hJ
  have hD : ‖D‖ ≤ bound := by
    simpa only [D, bound] using detectorLeg_norm_le owner lambda
  have hT : ‖T‖ ≤ (1 : ℝ) := by
    calc
      ‖T‖ = ‖suffixEulerFrameTransition lambda p S‖ := by
        simpa only [T, frameTransitionAdjoint] using
          (ContinuousLinearMap.adjoint.norm_map
            (suffixEulerFrameTransition lambda p S))
      _ ≤ 1 := suffixEulerFrameTransition_norm_le_one lambda p S
  have hO : ‖O‖ ≤ (1 : ℝ) := by
    calc
      ‖O‖ = ‖(suffixEulerFrameSchurStep lambda p S).oldFrame‖ := by
        simpa only [O, frameOldFrameAdjoint] using
          (ContinuousLinearMap.adjoint.norm_map
            (suffixEulerFrameSchurStep lambda p S).oldFrame)
      _ ≤ 1 :=
        CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion _ (by
          intro x
          exact parameterizedSoninPolarFrame_isometry
            lambda 1 (p :: S) (by norm_num) x)
  have hJD : ‖J† ∘L D‖ ≤ bound := by
    calc
      ‖J† ∘L D‖ ≤ ‖J†‖ * ‖D‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * bound :=
        mul_le_mul hJAdj hD (norm_nonneg D) zero_le_one
      _ = bound := one_mul bound
  have hmetricTelescope := norm_operator_telescope_le_two_mul
    (J† ∘L D) (J† ∘L D) T O bound hJD hJD hT hO
  have hmetric :
      ‖suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
          owner lambda p S‖ ≤ 2 * bound := by
    rw [show suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
        owner lambda p S =
          -(J† ∘L D ∘L T ∘L O - (T ∘L (J† ∘L D)) ∘L O) by
      unfold suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
      apply ContinuousLinearMap.ext
      intro x
      simp only [J, D, T, O, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      abel,
      norm_neg]
    exact hmetricTelescope
  have hforwardAdj :
      ‖suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
          owner lambda p S‖ ≤ 2 * bound := by
    simpa only [
      suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope,
      T, O, bound] using
      (norm_operator_telescope_le_two_mul
        (suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
          owner lambda S)
        (suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
          owner lambda (p :: S)) T O bound
        (by simpa only [bound] using
          forwardAdjointLeakage_norm_le owner lambda S)
        (by simpa only [bound] using
          forwardAdjointLeakage_norm_le owner lambda (p :: S)) hT hO)
  have hforward :
      ‖suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
          owner lambda p S‖ ≤ 2 * bound := by
    simpa only [
      suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope,
      T, O, bound, frameTransitionAdjoint, frameOldFrameAdjoint] using
      (norm_operator_telescope_le_two_mul
        (suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S)
        (suffixActualBandRawCoframeBoundaryForwardLeakage
          owner lambda (p :: S)) T O bound
        (by simpa only [bound] using forwardLeakage_norm_le owner lambda S)
        (by simpa only [bound] using
          forwardLeakage_norm_le owner lambda (p :: S)) hT hO)
  have hforwardComplete :
      ‖suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
          owner lambda p S‖ ≤ 4 * bound := by
    unfold suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
    calc
      _ ≤ ‖suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
              owner lambda p S‖ +
            ‖suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
              owner lambda p S‖ := norm_add_le _ _
      _ ≤ 2 * bound + 2 * bound := add_le_add hforwardAdj hforward
      _ = 4 * bound := by ring
  unfold coframeKnownBoundedRow
  calc
    _ ≤ ‖suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
            owner lambda p S‖ +
          ‖suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
            owner lambda p S‖ := norm_add_le _ _
    _ ≤ 2 * bound + 4 * bound := add_le_add hmetric hforwardComplete
    _ = 6 * ‖detectorOperator owner‖ := by simp only [bound]; ring

/-- The elementary inclusion/forward row keeps its existing bound after the
same suffix scalar is inserted. -/
theorem norm_scalar_smul_coframeKnownBoundedRow_le_six_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        coframeKnownBoundedRow owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
  have hrhoPos : 0 < suffixEulerSchurMarkovScalar (p :: S) :=
    suffixEulerSchurMarkovScalar_pos (p :: S)
  have hrhoOne : suffixEulerSchurMarkovScalar (p :: S) ≤ 1 :=
    suffixEulerSchurMarkovScalar_le_one (p :: S)
  have hknown : ‖coframeKnownBoundedRow owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
    exact norm_coframeKnownBoundedRow_le_six_mul_detector
      owner lambda p S
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hrhoPos]
  calc
    suffixEulerSchurMarkovScalar (p :: S) *
        ‖coframeKnownBoundedRow owner lambda p S‖ ≤
      1 * (6 * ‖detectorOperator owner‖) :=
        mul_le_mul hrhoOne hknown (norm_nonneg _) zero_le_one
    _ = 6 * ‖detectorOperator owner‖ := one_mul _

/-- After the orientation and residual pieces are recombined, the complete
old-carrier signed telescope has a family-uniform bound in the exact suffix
scalar gauge. -/
theorem norm_scalar_smul_signedTelescope_le_eight_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        suffixActualBandRawPhysicalOldCarrierSignedTelescope
          owner lambda p S‖ ≤
      8 * ‖detectorOperator owner‖ := by
  rw [signedTelescope_eq_hard_add_known, smul_add]
  calc
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          coframeHardRow owner lambda p S +
        (suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          coframeKnownBoundedRow owner lambda p S‖ ≤
      ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          coframeHardRow owner lambda p S‖ +
        ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          coframeKnownBoundedRow owner lambda p S‖ := norm_add_le _ _
    _ ≤ 2 * ‖detectorOperator owner‖ +
        6 * ‖detectorOperator owner‖ :=
      add_le_add
        (norm_scalar_smul_coframeHardRow_le_two_mul_detector
          owner lambda p S)
        (norm_scalar_smul_coframeKnownBoundedRow_le_six_mul_detector
          owner lambda p S)
    _ = 8 * ‖detectorOperator owner‖ := by ring

/-- The same normalized bound holds for the literal reduced row. -/
theorem norm_scalar_smul_reducedRow_le_eight_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        suffixActualBandRawPhysicalReducedRow owner lambda p S‖ ≤
      8 * ‖detectorOperator owner‖ := by
  rw [suffixActualBandRawPhysicalReducedRow_eq_signedTelescope]
  exact norm_scalar_smul_signedTelescope_le_eight_mul_detector
    owner lambda p S

set_option maxHeartbeats 4000000 in
-- The final scalar distribution and rectangular compositions need more time.
set_option maxRecDepth 4096 in
-- The three nested operator-norm products need a larger elaboration depth.
/-- The complete signed interior numerator inherits the normalized bound;
the inverse adjoint and the actual new suffix frame are contractions. -/
theorem norm_scalar_smul_signedCompressedInteriorOwner_le_eight_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
        signedCompressedInteriorOwner owner lambda p S‖ ≤
      8 * ‖detectorOperator owner‖ := by
  have heq :
      (suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          signedCompressedInteriorOwner owner lambda p S =
        ((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
            suffixActualBandRawPhysicalReducedRow owner lambda p S) ∘L
          (normalizedPrimeEulerInverse p)† ∘L
            newSuffixFrame lambda S := by
    rw [signedCompressedInteriorOwner_eq_reducedRow_comp_inverseAdjoint_comp_newFrame]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply]
  rw [heq]
  have hinverse : ‖(normalizedPrimeEulerInverse p)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(normalizedPrimeEulerInverse p)†‖ =
          ‖normalizedPrimeEulerInverse p‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := norm_normalizedPrimeEulerInverse_le_one p
  have hframe : ‖newSuffixFrame lambda S‖ ≤ (1 : ℝ) :=
    newSuffixFrame_norm_le_one lambda S
  have htail :
      ‖(normalizedPrimeEulerInverse p)† ∘L newSuffixFrame lambda S‖ ≤
        (1 : ℝ) := by
    calc
      _ ≤ ‖(normalizedPrimeEulerInverse p)†‖ *
          ‖newSuffixFrame lambda S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hinverse hframe (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc
    ‖((suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          suffixActualBandRawPhysicalReducedRow owner lambda p S) ∘L
        (normalizedPrimeEulerInverse p)† ∘L
          newSuffixFrame lambda S‖ ≤
      ‖(suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
          suffixActualBandRawPhysicalReducedRow owner lambda p S‖ *
        ‖(normalizedPrimeEulerInverse p)† ∘L
          newSuffixFrame lambda S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (8 * ‖detectorOperator owner‖) * 1 :=
      mul_le_mul
        (norm_scalar_smul_reducedRow_le_eight_mul_detector
          owner lambda p S)
        htail (norm_nonneg _) (by positivity)
    _ = 8 * ‖detectorOperator owner‖ := by ring

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNormalizedSuffixMetricRow
end CCM25Concrete
end Source
end ConnesWeilRH
