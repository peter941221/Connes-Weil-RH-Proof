/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

/-!
# One-prime moment obstruction for the old-carrier quotient

Proof 583 turns the empty-suffix reduction into a source-facing obstruction.
If the uniform old-carrier Douglas quotient exists with bound `C`, then the
actual one-prime boundary moment factors through the same two-channel
old-carrier analysis with bound at most `8 * C`.  Therefore an approximate
kernel for that actual moment rules out the uniform quotient.

The theorem is deliberately stated for the genuine global-log carrier.  It
does not assert that the approximate-kernel sequence exists; constructing or
excluding that sequence remains the analytic part of bone 1.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSCompletedJuliaJointProducer

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The actual one-prime moment -/

/-- The first nontrivial signed boundary moment on the old-carrier route. -/
noncomputable def onePrimeBoundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) : SourceOp lambda :=
  rawCoframeBoundaryMoment owner lambda
    (suffixActualBandForwardCoframe lambda [p])
    (suffixActualBandForwardEndpointCoframe lambda [p])

/-! ## Scalar bookkeeping -/

theorem primeSchurMarkovScalar_inv_le_eight
    (p : CCM24VisiblePrime) :
    (primeSchurMarkovScalar p)⁻¹ ≤ (8 : ℝ) := by
  have hpos : 0 < primeSchurMarkovScalar p :=
    primeSchurMarkovScalar_pos p
  have hmul : primeSchurMarkovScalar p *
      (primeSchurMarkovScalar p)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hpos)
  have hinvNonneg : 0 ≤ (primeSchurMarkovScalar p)⁻¹ :=
    le_of_lt (inv_pos.mpr hpos)
  nlinarith [primeSchurMarkovScalar_ge_one_eighth p]

theorem norm_primeSchurMarkovScalar_inv_le_eight
    (p : CCM24VisiblePrime) :
    ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ ≤ (8 : ℝ) := by
  have hpos : 0 < primeSchurMarkovScalar p :=
    primeSchurMarkovScalar_pos p
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos]
  exact primeSchurMarkovScalar_inv_le_eight p

/-! ## The one-prime quotient estimate -/

set_option maxHeartbeats 4000000 in
-- Douglas construction plus the sequential obstruction needs a larger local budget.
set_option maxRecDepth 10000 in
theorem onePrimeBoundaryMoment_oldCarrier_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (bound : ℝ)
    (hdom : SuffixRawOldCarrierDomination owner lambda p [] bound)
    (y : finiteSCarrier) :
    ‖onePrimeBoundaryMoment owner lambda p
        ((ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame) y)‖ ≤
      8 * bound *
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y‖ := by
  obtain ⟨readout, hreadoutNorm, hfactor⟩ :=
    exists_factor_of_norm_sq_le
      (suffixActualBandRawPhysicalReducedRow owner lambda p [])
      (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [])
      bound hdom.1 hdom.2
  obtain ⟨momentReadout, hmomentNorm, hmomentFactor⟩ :=
    exists_onePrimeMomentReadout_of_oldCarrierReadout owner lambda p bound
      readout hreadoutNorm hfactor
  have hmomentReadoutNorm : ‖momentReadout‖ ≤ 8 * bound := by
    calc
      ‖momentReadout‖ ≤
          ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ * bound := hmomentNorm
      _ ≤ 8 * bound := by
        exact mul_le_mul_of_nonneg_right
          (norm_primeSchurMarkovScalar_inv_le_eight p) hdom.1
  have hfactorPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => T y)
    hmomentFactor
  have hpoint :
      onePrimeBoundaryMoment owner lambda p
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p []).oldFrame) y) =
        momentReadout
          (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y) := by
    simpa only [onePrimeBoundaryMoment, ContinuousLinearMap.comp_apply] using
      hfactorPoint.symm
  rw [hpoint]
  calc
    ‖momentReadout
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y)‖ ≤
        ‖momentReadout‖ *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y‖ :=
      momentReadout.le_opNorm _
    _ ≤ (8 * bound) *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y‖ := by
      exact mul_le_mul_of_nonneg_right hmomentReadoutNorm
        (norm_nonneg _)
    _ = 8 * bound *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p [] y‖ := by
      ring

/-! ## Approximate-kernel obstruction -/

/-- A moment approximate kernel is incompatible with any finite uniform
old-carrier Douglas bound.  The output is the actual one-prime moment, while
the denominator is the actual global-log two-channel analysis. -/
theorem noExistsUniformOldCarrierDomination_of_onePrimeMomentApproximateKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (y : ℕ → finiteSCarrier)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hmoment : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖onePrimeBoundaryMoment owner lambda (prime n)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
              (y n))‖)
    (hanalysis : Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
          (prime n) [] (y n)‖)
      Filter.atTop (𝓝 0)) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  rintro ⟨bound, ⟨data⟩⟩
  have hbound : 0 ≤ bound := data.bound_nonneg
  let gain : ℝ := 8 * bound
  have hgain : 0 ≤ gain := by
    dsimp only [gain]
    positivity
  have hdenom : 0 < gain + 1 := by linarith
  have hdelta : 0 < epsilon / (gain + 1) :=
    div_pos hepsilon hdenom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendsto_nhds.mp hanalysis (epsilon / (gain + 1)) hdelta)
  obtain ⟨n, hn⟩ :=
    (hmoment.and (Filter.eventually_ge_atTop N)).exists
  have hsmallDist := hN n hn.2
  have hsmall :
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
          (prime n) [] (y n)‖ < epsilon / (gain + 1) := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hsmallDist
  have hmomentUpper := onePrimeBoundaryMoment_oldCarrier_norm_le owner lambda
    (prime n) bound (data.domination (prime n) []) (y n)
  have hmomentUpper' :
      ‖onePrimeBoundaryMoment owner lambda (prime n)
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
            (y n))‖ ≤
        gain *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
            (prime n) [] (y n)‖ := by
    simpa only [gain, mul_assoc] using hmomentUpper
  have hscaled :
      gain *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
            (prime n) [] (y n)‖ ≤
        gain * (epsilon / (gain + 1)) :=
    mul_le_mul_of_nonneg_left hsmall.le hgain
  have hratio : gain * (epsilon / (gain + 1)) < epsilon := by
    calc
      gain * (epsilon / (gain + 1)) =
          (gain * epsilon) / (gain + 1) := by ring
      _ < epsilon := by
        apply (div_lt_iff₀ hdenom).2
        nlinarith
  have hlt :
      ‖onePrimeBoundaryMoment owner lambda (prime n)
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
            (y n))‖ < epsilon :=
    lt_of_le_of_lt hmomentUpper'
      (hscaled.trans_lt hratio)
  exact (not_lt_of_ge hn.1) hlt

end CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
