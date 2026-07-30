/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction

/-!
# One-prime moment reduction for the raw physical quotient

The empty suffix has zero boundary moment.  Its raw row is therefore the
adjoint transition followed by the first nontrivial boundary moment.  The
Schur--Markov reverse transition has an exact two-sided scalar inverse.  After
pulling the row back to the old carrier, the adjoint reverse transition cancels
the adjoint forward transition exactly.

This gives a genuine necessary condition for bone 1: any bounded raw
old-carrier quotient produces a bounded quotient for the one-prime boundary
moment on the same old-carrier physical analysis.  No estimate is inferred
for the moment itself, and no uniform producer is claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact one-prime old-carrier identity -/

theorem suffixActualBandRawPhysicalReducedRow_cons_nil_eq_neg_transitionAdjoint_moment_oldFrameAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    suffixActualBandRawPhysicalReducedRow owner lambda p [] =
      -(ContinuousLinearMap.adjoint (suffixEulerFrameTransition lambda p [])) ∘L
        rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda [p])
          (suffixActualBandForwardEndpointCoframe lambda [p]) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame := by
  rw [suffixActualBandRawPhysicalReducedRow,
    suffixActualBandRawPhysicalFourTermRow_cons_nil_eq_neg_boundaryMoment]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]

/-! The scalar cancellation used by the extracted moment readout. -/

theorem scaled_reverseAdjoint_comp_transitionAdjoint_eq_id
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ((primeSchurMarkovScalar p : ℂ)⁻¹ •
        ContinuousLinearMap.adjoint
          (suffixEulerFrameReverseTransition lambda p [])) ∘L
        ContinuousLinearMap.adjoint (suffixEulerFrameTransition lambda p []) =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hpair := congrArg ContinuousLinearMap.adjoint
    (suffixEulerFrameTransition_comp_reverse lambda p [])
  have hstar : star (primeSchurMarkovScalar p : ℂ) =
      (primeSchurMarkovScalar p : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hp : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun T : SourceOp lambda => T x) hpair
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply] at hx
  have hscalarPoint := congrArg
    (fun T : SourceOp lambda => T x)
    (ContinuousLinearMap.adjoint.map_smulₛₗ
      (primeSchurMarkovScalar p : ℂ)
      (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)))
  simp only [starRingEnd_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at hscalarPoint
  rw [hstar] at hscalarPoint
  rw [hscalarPoint] at hx
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at ⊢
  rw [hx]
  simp only [smul_smul, inv_mul_cancel₀ hp, one_smul]

/-! ## A readout extracted from any old-carrier raw readout -/

noncomputable def onePrimeMomentReadoutOfOldCarrierReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
    (ContinuousLinearMap.adjoint
      (suffixEulerFrameReverseTransition lambda p [])) ∘L readout

set_option maxHeartbeats 4000000 in
-- The operator-norm composition and adjoint elaboration needs a larger local budget.
theorem onePrimeMomentReadoutOfOldCarrierReadout_norm_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda) :
    ‖onePrimeMomentReadoutOfOldCarrierReadout lambda p readout‖ ≤
      ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * ‖readout‖ := by
  unfold onePrimeMomentReadoutOfOldCarrierReadout
  calc
    ‖(-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          ContinuousLinearMap.adjoint
            (suffixEulerFrameReverseTransition lambda p []) ∘L readout‖ ≤
        ‖(-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
            ContinuousLinearMap.adjoint
              (suffixEulerFrameReverseTransition lambda p [])‖ *
          ‖readout‖ := ContinuousLinearMap.opNorm_comp_le
            (-((primeSchurMarkovScalar p : ℂ)⁻¹) •
              ContinuousLinearMap.adjoint
                (suffixEulerFrameReverseTransition lambda p [])) readout
    _ ≤ (‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
          ‖ContinuousLinearMap.adjoint
            (suffixEulerFrameReverseTransition lambda p [])‖) *
          ‖readout‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg readout)
      simpa only [norm_neg] using
        (ContinuousLinearMap.opNorm_smul_le
          (-((primeSchurMarkovScalar p : ℂ)⁻¹))
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameReverseTransition lambda p [])))
    _ = ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
          ‖suffixEulerFrameReverseTransition lambda p []‖ * ‖readout‖ := by
      have hnorm :
          ‖ContinuousLinearMap.adjoint
              (suffixEulerFrameReverseTransition lambda p [])‖ =
            ‖suffixEulerFrameReverseTransition lambda p []‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      rw [hnorm]
    _ ≤ ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * ‖readout‖ := by
      have hreverse := suffixEulerFrameReverseTransition_norm_le_one
        lambda p []
      have hscalar : 0 ≤ ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ :=
        norm_nonneg _
      calc
        ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
              ‖suffixEulerFrameReverseTransition lambda p []‖ * ‖readout‖ ≤
            ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * 1 * ‖readout‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hreverse hscalar) (norm_nonneg readout)
        _ = ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * ‖readout‖ := by
          ring

theorem onePrimeMomentReadoutOfOldCarrierReadout_comp_analysis_eq_moment_oldFrameAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda)
    (hfactor :
      readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
          lambda p [] =
        suffixActualBandRawPhysicalReducedRow owner lambda p []) :
    onePrimeMomentReadoutOfOldCarrierReadout lambda p readout ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] =
      rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda [p])
          (suffixActualBandForwardEndpointCoframe lambda [p]) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame := by
  have hcancel :=
    scaled_reverseAdjoint_comp_transitionAdjoint_eq_id lambda p
  have hrow :=
    suffixActualBandRawPhysicalReducedRow_cons_nil_eq_neg_transitionAdjoint_moment_oldFrameAdjoint
      owner lambda p
  apply ContinuousLinearMap.ext
  intro y
  have hfactorPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ]
        sourceSoninCarrier lambda => T y) hfactor
  have hrowPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => T y) hrow
  have hfactorPoint' :
      readout (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
        lambda p [] y) =
        suffixActualBandRawPhysicalReducedRow owner lambda p [] y := by
    simpa only [ContinuousLinearMap.comp_apply] using hfactorPoint
  have hrowPoint' :
      suffixActualBandRawPhysicalReducedRow owner lambda p [] y =
        -(ContinuousLinearMap.adjoint
          (suffixEulerFrameTransition lambda p []))
          ((rawCoframeBoundaryMoment owner lambda
            (suffixActualBandForwardCoframe lambda [p])
            (suffixActualBandForwardEndpointCoframe lambda [p]))
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p []).oldFrame y)) := by
    simpa only [ContinuousLinearMap.comp_apply] using hrowPoint
  simp only [onePrimeMomentReadoutOfOldCarrierReadout,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at ⊢
  rw [hfactorPoint', hrowPoint']
  simp only [map_neg, smul_neg, neg_smul, neg_neg]
  have hcancelPoint := congrArg
    (fun T : SourceOp lambda =>
      T ((rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda [p])
        (suffixActualBandForwardEndpointCoframe lambda [p]))
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame y))) hcancel
  have hcancelPoint' :
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameReverseTransition lambda p []))
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameTransition lambda p []))
              ((rawCoframeBoundaryMoment owner lambda
                (suffixActualBandForwardCoframe lambda [p])
                (suffixActualBandForwardEndpointCoframe lambda [p]))
                (ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p []).oldFrame y))) =
        (rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda [p])
          (suffixActualBandForwardEndpointCoframe lambda [p]))
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p []).oldFrame y) := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using
        hcancelPoint
  rw [hcancelPoint']

theorem exists_onePrimeMomentReadout_of_oldCarrierReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (bound : ℝ)
    (readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda)
    (hbound : ‖readout‖ ≤ bound)
    (hfactor :
      readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
          lambda p [] =
        suffixActualBandRawPhysicalReducedRow owner lambda p []) :
    ∃ momentReadout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
        sourceSoninCarrier lambda,
      ‖momentReadout‖ ≤
          ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * bound ∧
        momentReadout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
            lambda p [] =
          rawCoframeBoundaryMoment owner lambda
              (suffixActualBandForwardCoframe lambda [p])
              (suffixActualBandForwardEndpointCoframe lambda [p]) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p []).oldFrame := by
  let momentReadout :=
    onePrimeMomentReadoutOfOldCarrierReadout lambda p readout
  refine ⟨momentReadout, ?_, ?_⟩
  · calc
      ‖momentReadout‖ ≤
          ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * ‖readout‖ :=
        onePrimeMomentReadoutOfOldCarrierReadout_norm_le lambda p readout
      _ ≤ ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * bound := by
        exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  · exact onePrimeMomentReadoutOfOldCarrierReadout_comp_analysis_eq_moment_oldFrameAdjoint
      owner lambda p readout hfactor

end CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction
end CCM25Concrete
end Source
end ConnesWeilRH
