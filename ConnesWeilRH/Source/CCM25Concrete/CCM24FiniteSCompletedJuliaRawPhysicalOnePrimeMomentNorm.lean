/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurEndpointAlignmentResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedPhysicalResponse
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovUniformBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer

/-!
# One-prime boundary-moment norm bound

Proof 582 estimates the actual signed boundary moment after the exact
Schur--Markov normalization.  The endpoint is kept as the sum of the
contractive forward coframe and the normalized metric coframe; no branchwise
physical split is used.

The one-prime corollary removes the scalar at cost `8`, using the elementary
lower bound `rho_p >= 1/8`.  This is an operator-norm bound for the moment
itself.  It is deliberately not a Douglas factorization through the
old-carrier analysis.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurEndpointAlignmentResidual
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSCoframeResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSGramResponse
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## A generic scaled moment estimate -/

set_option maxHeartbeats 4000000 in
-- The rectangular operator-norm chain needs a larger deterministic budget.
set_option maxRecDepth 10000 in
theorem rawCoframeBoundaryMoment_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    ‖rawCoframeBoundaryMoment owner lambda forward endpoint‖ ≤
      ‖endpoint‖ * ‖sourceSoninComplement lambda‖ *
          ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ +
        ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
          ‖forward‖ := by
  have hfirst :
      ‖endpoint† ∘L sourceSoninComplement lambda ∘L
          detectorOperator owner ∘L sourceInclusion lambda‖ ≤
        ‖endpoint‖ * ‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ := by
    calc
      ‖endpoint† ∘L sourceSoninComplement lambda ∘L
          detectorOperator owner ∘L sourceInclusion lambda‖ ≤
          ‖endpoint† ∘L sourceSoninComplement lambda ∘L
            detectorOperator owner‖ * ‖sourceInclusion lambda‖ :=
        by
          simpa only [ContinuousLinearMap.comp_assoc] using
            (ContinuousLinearMap.opNorm_comp_le
              (endpoint† ∘L sourceSoninComplement lambda ∘L
                detectorOperator owner)
              (sourceInclusion lambda))
      _ ≤ (‖endpoint† ∘L sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖) * ‖sourceInclusion lambda‖ := by
        exact mul_le_mul_of_nonneg_right
          (by
            simpa only [ContinuousLinearMap.comp_assoc] using
              (ContinuousLinearMap.opNorm_comp_le
                (endpoint† ∘L sourceSoninComplement lambda)
                (detectorOperator owner)))
          (norm_nonneg (sourceInclusion lambda))
      _ ≤ ((‖endpoint†‖ * ‖sourceSoninComplement lambda‖) *
            ‖detectorOperator owner‖) * ‖sourceInclusion lambda‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg (detectorOperator owner)))
          (norm_nonneg (sourceInclusion lambda))
      _ = ‖endpoint‖ * ‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ := by
        have hendpointAdj : ‖endpoint†‖ = ‖endpoint‖ :=
          ContinuousLinearMap.adjoint.norm_map _
        rw [hendpointAdj]

  have hsecond :
      ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward‖ ≤
        ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
          ‖forward‖ := by
    calc
      ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward‖ ≤
          ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ *
            ‖forward‖ := by
        simpa only [ContinuousLinearMap.comp_assoc] using
          (ContinuousLinearMap.opNorm_comp_le
            ((sourceInclusion lambda)† ∘L detectorOperator owner) forward)
      _ ≤ (‖(sourceInclusion lambda)†‖ *
            ‖detectorOperator owner‖) * ‖forward‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg forward)
      _ = ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
            ‖forward‖ := by ring

  unfold rawCoframeBoundaryMoment
  calc
    ‖endpoint† ∘L sourceSoninComplement lambda ∘L
        detectorOperator owner ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward‖ ≤
        ‖endpoint† ∘L sourceSoninComplement lambda ∘L
            detectorOperator owner ∘L sourceInclusion lambda‖ +
        ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L
            forward‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖endpoint‖ * ‖sourceSoninComplement lambda‖ *
          ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ +
        ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
          ‖forward‖ := by
      exact add_le_add
        (by simpa only [ContinuousLinearMap.comp_assoc] using hfirst)
        (by simpa only [ContinuousLinearMap.comp_assoc] using hsecond)

theorem smul_rawCoframeBoundaryMoment_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (rho : ℝ)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    (rho : ℂ) • rawCoframeBoundaryMoment owner lambda forward endpoint =
      rawCoframeBoundaryMoment owner lambda
        ((rho : ℂ) • forward) ((rho : ℂ) • endpoint) := by
  have hAdj :
      ContinuousLinearMap.adjoint ((rho : ℂ) • endpoint) =
        (rho : ℂ) • ContinuousLinearMap.adjoint endpoint := by
    have h := ContinuousLinearMap.adjoint.map_smulₛₗ
      (rho : ℂ) endpoint
    calc
      ContinuousLinearMap.adjoint ((rho : ℂ) • endpoint) =
          (starRingEnd ℂ) (rho : ℂ) •
            ContinuousLinearMap.adjoint endpoint := h
      _ = star (rho : ℂ) • ContinuousLinearMap.adjoint endpoint := by rfl
      _ = (rho : ℂ) • ContinuousLinearMap.adjoint endpoint := by
        rw [Complex.star_def, Complex.conj_ofReal]
  apply ContinuousLinearMap.ext
  intro x
  simp only [rawCoframeBoundaryMoment, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [hAdj]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  rw [smul_add]

theorem norm_smul_rawCoframeBoundaryMoment_le_three_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (rho : ℝ)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hforward : ‖(rho : ℂ) • forward‖ ≤ 1)
    (hendpoint : ‖(rho : ℂ) • endpoint‖ ≤ 2) :
    ‖(rho : ℂ) • rawCoframeBoundaryMoment owner lambda forward endpoint‖ ≤
      3 * ‖detectorOperator owner‖ := by
  have hComplement : ‖sourceSoninComplement lambda‖ ≤ (1 : ℝ) :=
    norm_sourceSoninComplement_le_one lambda
  have hInclusion : ‖sourceInclusion lambda‖ ≤ (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  have hInclusionAdj : ‖(sourceInclusion lambda)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(sourceInclusion lambda)†‖ = ‖sourceInclusion lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hInclusion
  have hMoment := rawCoframeBoundaryMoment_norm_le owner lambda
    ((rho : ℂ) • forward) ((rho : ℂ) • endpoint)
  have hfirstInner :
      ‖sourceSoninComplement lambda‖ * ‖detectorOperator owner‖ *
          ‖sourceInclusion lambda‖ ≤
        1 * ‖detectorOperator owner‖ * 1 := by
    calc
      ‖sourceSoninComplement lambda‖ * ‖detectorOperator owner‖ *
          ‖sourceInclusion lambda‖ ≤
          1 * ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hComplement
            (norm_nonneg (detectorOperator owner)))
          (norm_nonneg (sourceInclusion lambda))
      _ ≤ 1 * ‖detectorOperator owner‖ * 1 := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_left hInclusion
            (norm_nonneg (detectorOperator owner)))
  have hsecondInner :
      ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ ≤
        1 * ‖detectorOperator owner‖ * 1 := by
    calc
      ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ ≤
          1 * ‖detectorOperator owner‖ := by
        exact mul_le_mul_of_nonneg_right hInclusionAdj
          (norm_nonneg (detectorOperator owner))
      _ ≤ 1 * ‖detectorOperator owner‖ * 1 := by
        simpa only [one_mul, mul_one] using
          (le_refl (‖detectorOperator owner‖))
  have hfirstScaled :
      ‖(rho : ℂ) • endpoint‖ *
          (‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖) ≤
        2 * (1 * ‖detectorOperator owner‖ * 1) := by
    have hinnerNonneg :
        0 ≤ ‖sourceSoninComplement lambda‖ *
          ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ := by
      exact mul_nonneg
        (mul_nonneg (norm_nonneg (sourceSoninComplement lambda))
          (norm_nonneg (detectorOperator owner)))
        (norm_nonneg (sourceInclusion lambda))
    calc
      ‖(rho : ℂ) • endpoint‖ *
          (‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖) ≤
          2 * (‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖) := by
        exact mul_le_mul_of_nonneg_right hendpoint hinnerNonneg
      _ ≤ 2 * (1 * ‖detectorOperator owner‖ * 1) := by
        exact mul_le_mul_of_nonneg_left hfirstInner (by norm_num)
  have hsecondScaled :
      (‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖) *
          ‖(rho : ℂ) • forward‖ ≤
        1 * (1 * ‖detectorOperator owner‖ * 1) := by
    have hdetNonneg : 0 ≤ ‖detectorOperator owner‖ :=
      norm_nonneg _
    calc
      (‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖) *
          ‖(rho : ℂ) • forward‖ ≤
          (1 * ‖detectorOperator owner‖ * 1) *
            ‖(rho : ℂ) • forward‖ := by
        exact mul_le_mul_of_nonneg_right hsecondInner
          (norm_nonneg ((rho : ℂ) • forward))
      _ ≤ 1 * (1 * ‖detectorOperator owner‖ * 1) := by
        simpa only [one_mul, mul_one] using
          (mul_le_mul_of_nonneg_left hforward hdetNonneg)
  rw [smul_rawCoframeBoundaryMoment_eq]
  calc
    ‖rawCoframeBoundaryMoment owner lambda
        ((rho : ℂ) • forward) ((rho : ℂ) • endpoint)‖ ≤
        ‖(rho : ℂ) • endpoint‖ * ‖sourceSoninComplement lambda‖ *
            ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ +
          ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ *
            ‖(rho : ℂ) • forward‖ := hMoment
    _ ≤ 2 * (1 * ‖detectorOperator owner‖ * 1) +
        1 * (1 * ‖detectorOperator owner‖ * 1) := by
      have hadd := add_le_add hfirstScaled hsecondScaled
      simpa only [mul_assoc] using hadd
    _ = 3 * ‖detectorOperator owner‖ := by ring

/-! ## The family-normalized moment -/

theorem norm_schurMarkovScaledRawCoframeBoundaryMoment_le_three_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖(suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
        rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda family.visiblePrimes)
          (suffixActualBandForwardEndpointCoframe lambda
            family.visiblePrimes)‖ ≤
      3 * ‖detectorOperator owner‖ := by
  let rho := suffixEulerSchurMarkovScalar family.visiblePrimes
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact suffixEulerSchurMarkovScalar_pos family.visiblePrimes
  have hrho : rho ≤ 1 := by
    dsimp only [rho]
    exact suffixEulerSchurMarkovScalar_le_one family.visiblePrimes
  have hforward :
      ‖(rho : ℂ) •
          suffixActualBandForwardCoframe lambda family.visiblePrimes‖ ≤ 1 := by
    rw [suffixActualBandForwardCoframe_visiblePrimes_eq_sourceActualBandForwardCoframe]
    calc
      ‖(rho : ℂ) • sourceActualBandForwardCoframe lambda family‖ ≤
          ‖(rho : ℂ)‖ * ‖sourceActualBandForwardCoframe lambda family‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = rho * ‖sourceActualBandForwardCoframe lambda family‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhoPos]
      _ ≤ 1 * 1 := by
        exact mul_le_mul hrho
          (norm_sourceActualBandForwardCoframe_le_one lambda family)
          (norm_nonneg (sourceActualBandForwardCoframe lambda family))
          (by norm_num)
      _ = 1 := by norm_num
  have hmetric :
      ‖(rho : ℂ) •
          suffixActualBandMetricCoframe lambda family.visiblePrimes‖ ≤ 1 := by
    rw [suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe]
    change ‖schurMarkovMixedMetricCoframe lambda family‖ ≤ 1
    exact norm_schurMarkovMixedMetricCoframe_le_one lambda family
  have hforwardSource :
      ‖(rho : ℂ) • sourceActualBandForwardCoframe lambda family‖ ≤ 1 := by
    rw [← suffixActualBandForwardCoframe_visiblePrimes_eq_sourceActualBandForwardCoframe]
    exact hforward
  have hmetricSource :
      ‖(rho : ℂ) • finiteEulerMetricCoframe lambda family‖ ≤ 1 := by
    rw [← suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe]
    exact hmetric
  have hendpoint :
      ‖(rho : ℂ) •
          suffixActualBandForwardEndpointCoframe lambda
            family.visiblePrimes‖ ≤ 2 := by
    rw [
      suffixActualBandForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardEndpointCoframe]
    change ‖(rho : ℂ) •
        (sourceActualBandForwardCoframe lambda family +
          finiteEulerMetricCoframe lambda family)‖ ≤ 2
    rw [smul_add]
    calc
      ‖(rho : ℂ) • sourceActualBandForwardCoframe lambda family +
          (rho : ℂ) • finiteEulerMetricCoframe lambda family‖ ≤
          ‖(rho : ℂ) • sourceActualBandForwardCoframe lambda family‖ +
            ‖(rho : ℂ) • finiteEulerMetricCoframe lambda family‖ :=
        norm_add_le
          ((rho : ℂ) • sourceActualBandForwardCoframe lambda family)
          ((rho : ℂ) • finiteEulerMetricCoframe lambda family)
      _ ≤ 1 + 1 := add_le_add hforwardSource hmetricSource
      _ = 2 := by norm_num
  dsimp only [rho] at hforward hendpoint ⊢
  exact norm_smul_rawCoframeBoundaryMoment_le_three_mul_detector owner lambda
    (suffixEulerSchurMarkovScalar family.visiblePrimes)
    (suffixActualBandForwardCoframe lambda family.visiblePrimes)
    (suffixActualBandForwardEndpointCoframe lambda family.visiblePrimes)
    hforward hendpoint

/-! ## One-prime unscaling -/

theorem norm_onePrimeRawCoframeBoundaryMoment_le_twentyFour_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = [p]) :
    ‖rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda [p])
        (suffixActualBandForwardEndpointCoframe lambda [p])‖ ≤
      24 * ‖detectorOperator owner‖ := by
  have hscaled :=
    norm_schurMarkovScaledRawCoframeBoundaryMoment_le_three_mul_detector
      owner lambda family
  rw [hvisible] at hscaled
  simp only [suffixEulerSchurMarkovScalar, mul_one] at hscaled
  have hrhoPos : 0 < primeSchurMarkovScalar p :=
    primeSchurMarkovScalar_pos p
  let hraw : SourceOp lambda := rawCoframeBoundaryMoment owner lambda
    (suffixActualBandForwardCoframe lambda [p])
    (suffixActualBandForwardEndpointCoframe lambda [p])
  have hscaled' :
      ‖(primeSchurMarkovScalar p : ℂ) • hraw‖ ≤
        3 * ‖detectorOperator owner‖ := by
    simpa only [hraw] using hscaled
  have hscalarInv :
      ‖(primeSchurMarkovScalar p : ℂ)⁻¹‖ =
        (primeSchurMarkovScalar p)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrhoPos]
  have hraw_eq_scaled :
      hraw = (primeSchurMarkovScalar p : ℂ)⁻¹ •
        ((primeSchurMarkovScalar p : ℂ) • hraw) := by
    rw [smul_smul, inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hrhoPos)), one_smul]
  have hinv : (primeSchurMarkovScalar p)⁻¹ ≤ (8 : ℝ) := by
    have hmul : primeSchurMarkovScalar p *
        (primeSchurMarkovScalar p)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hrhoPos)
    have hinvNonneg : 0 ≤ (primeSchurMarkovScalar p)⁻¹ :=
      le_of_lt (inv_pos.mpr hrhoPos)
    nlinarith [primeSchurMarkovScalar_ge_one_eighth p]
  have hrawBound : ‖hraw‖ ≤ 24 * ‖detectorOperator owner‖ := by
    rw [hraw_eq_scaled]
    calc
      ‖(primeSchurMarkovScalar p : ℂ)⁻¹ •
          ((primeSchurMarkovScalar p : ℂ) • hraw)‖ ≤
          ‖(primeSchurMarkovScalar p : ℂ)⁻¹‖ *
            ‖(primeSchurMarkovScalar p : ℂ) • hraw‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = (primeSchurMarkovScalar p)⁻¹ *
          ‖(primeSchurMarkovScalar p : ℂ) • hraw‖ := by
        rw [hscalarInv]
      _ ≤ (primeSchurMarkovScalar p)⁻¹ *
          (3 * ‖detectorOperator owner‖) := by
        exact mul_le_mul_of_nonneg_left hscaled'
          (le_of_lt (inv_pos.mpr hrhoPos))
      _ ≤ 8 * (3 * ‖detectorOperator owner‖) := by
        exact mul_le_mul_of_nonneg_right hinv
          (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = 24 * ‖detectorOperator owner‖ := by ring
  simpa only [hraw] using hrawBound

end CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
end CCM25Concrete
end Source
end ConnesWeilRH
