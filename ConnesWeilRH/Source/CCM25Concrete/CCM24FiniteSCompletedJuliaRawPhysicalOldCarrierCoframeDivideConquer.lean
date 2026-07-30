/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalDouglasBridge

/-!
# Divide-and-conquer package for the old-carrier coframe row

The old-carrier row has three logically different pieces:

* the metric orientation row;
* the metric survivor/boundary residual row;
* the inclusion/forward row already controlled by elementary contractions.

This module composes those pieces only after each one has a readout through
the same old-carrier analysis.  A norm bound on a row is deliberately not
accepted as a substitute for that factorization.  The final conversion to the
two physical coordinates and to the existing Gate 3U handoff is exact.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaNonpolarGapDouglas
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "OldRow" lambda =>
  finiteSCarrier →L[ℂ] sourceSoninCarrier lambda

/-! The two bookkeeping rows are repeated here as local owners so this module
does not depend on the larger audit-only owner. -/

noncomputable def coframeKnownBoundedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  suffixActualBandRawPhysicalOldCarrierMetricInclusionRow owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
      owner lambda p S

noncomputable def coframeHardRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  suffixActualBandRawPhysicalOldCarrierMetricOrientationRow owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow owner lambda p S

/-!
The orientation and survivor-residual rows must be recombined before any
estimate.  Their intermediate `T† * T * metricCoframe†` terms cancel exactly;
the result is the single adjacent metric-coframe telescope below.
-/
theorem coframeHardRow_eq_metricCoframeAdjointTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeHardRow owner lambda p S =
      ((frameMetricCoframe lambda S)† ∘L
          suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
            frameTransitionAdjoint lambda p S -
        frameTransitionAdjoint lambda p S ∘L
          (frameMetricCoframe lambda (p :: S))† ∘L
            suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda) ∘L
        frameOldFrameAdjoint lambda p S := by
  rw [coframeHardRow,
    suffixActualBandRawPhysicalOldCarrierMetricOrientationRow,
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow,
    suffixActualBandMetricCoframeAdjointOrientationGap_eq_expanded]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, map_sub]
  abel

/-! The actual Schur transport relation, in the row orientation. -/
theorem frameTransitionAdjoint_comp_frameOldFrameAdjoint_eq_newFrameAdjoint_comp_transportAdjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    frameTransitionAdjoint lambda p S ∘L frameOldFrameAdjoint lambda p S =
      ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transport := by
  have hintertwining :=
    (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  have hadjoint := congrArg ContinuousLinearMap.adjoint hintertwining
  simpa only [ContinuousLinearMap.adjoint_comp, frameTransitionAdjoint,
    frameOldFrameAdjoint] using hadjoint.symm

noncomputable def coframeHardAmbientRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  (frameMetricCoframe lambda S)† ∘L
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).newFrame

/-!
The first term of the hard row is the ambient coboundary.  The other term is
kept as a named boundary remainder.  Naming it is important: it is not
automatically supported by the new-frame complement, and therefore cannot be
sent through `rangeFactor` without a separate source annihilation theorem.
-/
noncomputable def coframeHardBoundaryRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : OldRow lambda :=
  -(frameTransitionAdjoint lambda p S ∘L
      (frameMetricCoframe lambda (p :: S))† ∘L
        suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
          frameOldFrameAdjoint lambda p S)

theorem coframeHardRow_firstMetricTerm_eq_ambientCoboundaryTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ((frameMetricCoframe lambda S)† ∘L
        suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
          frameTransitionAdjoint lambda p S) ∘L
        frameOldFrameAdjoint lambda p S =
      coframeHardAmbientRow owner lambda p S ∘L
        (normalizedPrimeEulerFrameTransport p)† := by
  apply ContinuousLinearMap.ext
  intro y
  have htransition :=
    frameTransitionAdjoint_comp_frameOldFrameAdjoint_eq_newFrameAdjoint_comp_transportAdjoint
      lambda p S
  have htransitionPoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator y) htransition
  have hpoint := congrArg
    (fun z : sourceSoninCarrier lambda =>
      ((frameMetricCoframe lambda S)† ∘L
        suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda) z)
    htransitionPoint
  simp only [coframeHardAmbientRow, ContinuousLinearMap.comp_apply] at hpoint ⊢
  exact hpoint

theorem coframeHardRow_eq_ambient_add_boundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeHardRow owner lambda p S =
    coframeHardAmbientRow owner lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)† +
        coframeHardBoundaryRow owner lambda p S := by
  rw [coframeHardRow_eq_metricCoframeAdjointTelescope]
  unfold coframeHardBoundaryRow
  apply ContinuousLinearMap.ext
  intro y
  have hfirstPoint := DFunLike.congr_fun
    (coframeHardRow_firstMetricTerm_eq_ambientCoboundaryTerm
      owner lambda p S) y
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, sub_eq_add_neg] at hfirstPoint ⊢
  rw [hfirstPoint]

theorem signedTelescope_eq_hard_add_known
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      coframeHardRow owner lambda p S + coframeKnownBoundedRow owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_metric_add_forwardComplete,
    suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope_eq_orientation_add_residual_add_inclusion,
    coframeHardRow, coframeKnownBoundedRow]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.add_apply]
  abel

/-! ## The ambient one-step divide-and-conquer owner -/

/-!
The ambient Euler coboundary is an actual first-channel readout.  This is the
local algebraic step used below; it is stronger than a norm estimate because
the factorization is kept through the same packed old-carrier analysis.
-/
noncomputable def ambientDifferenceReadout
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime)
    (row : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  suffixEulerFrameAmbientBoundaryReadoutOfRows
    (-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row))
    (0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)

theorem ambientDifferenceReadout_norm_le
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime)
    (row : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    ‖ambientDifferenceReadout p row‖ ≤
      ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ * ‖row‖ := by
  unfold ambientDifferenceReadout
  calc
    ‖suffixEulerFrameAmbientBoundaryReadoutOfRows
        (-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row))
        (0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ ≤
        ‖-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row)‖ +
          ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ :=
      suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add _ _
    _ ≤ ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ * ‖row‖ := by
      calc
        ‖-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row)‖ +
            ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ =
          ‖((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row)‖ := by
            have hzero :
                ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ = 0 :=
              ContinuousLinearMap.opNorm_zero
            rw [hzero, add_zero, ContinuousLinearMap.opNorm_neg]
        _ ≤ ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ * ‖row‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _

theorem ambientDifferenceReadout_comp_oldCarrierAnalysis_eq
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (row : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    ambientDifferenceReadout p row ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      row ∘L (normalizedPrimeEulerFrameTransport p)† - row := by
  unfold ambientDifferenceReadout
  rw [suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis]
  apply ContinuousLinearMap.ext
  intro y
  have hambient :=
    comp_normalizedPrimeEulerFrameTransport_adjoint_sub_comp_eq_neg_sqrtCoefficient_comp_ambientLossFactor_adjoint
      p row
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => operator y)
    hambient
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply] at hpoint ⊢
  simpa only [add_zero, map_neg, map_smul] using hpoint.symm

/-! ## One ambient difference plus one moving-boundary row -/

noncomputable def ambientDifferencePlusBoundaryReadout
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime)
    (row boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  suffixEulerFrameAmbientBoundaryReadoutOfRows
    (-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row))
    boundaryRow

theorem ambientDifferencePlusBoundaryReadout_norm_le
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime)
    (row boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    ‖ambientDifferencePlusBoundaryReadout p row boundaryRow‖ ≤
      ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ * ‖row‖ +
        ‖boundaryRow‖ := by
  unfold ambientDifferencePlusBoundaryReadout
  calc
    ‖suffixEulerFrameAmbientBoundaryReadoutOfRows
        (-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row))
        boundaryRow‖ ≤
        ‖-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) • row)‖ +
          ‖boundaryRow‖ :=
      suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add _ _
    _ ≤ ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ * ‖row‖ +
          ‖boundaryRow‖ := by
      exact add_le_add
        (by
          rw [ContinuousLinearMap.opNorm_neg]
          exact ContinuousLinearMap.opNorm_smul_le _ _)
        (le_refl _)

theorem ambientDifferencePlusBoundaryReadout_comp_oldCarrierAnalysis_eq
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (row boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    ambientDifferencePlusBoundaryReadout p row boundaryRow ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      row ∘L (normalizedPrimeEulerFrameTransport p)† - row +
        boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) := by
  unfold ambientDifferencePlusBoundaryReadout
  rw [suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis]
  apply ContinuousLinearMap.ext
  intro y
  have hambient :=
    comp_normalizedPrimeEulerFrameTransport_adjoint_sub_comp_eq_neg_sqrtCoefficient_comp_ambientLossFactor_adjoint
      p row
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => operator y)
    hambient
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply] at hpoint ⊢
  simpa only [add_zero, map_neg, map_smul] using congrArg
    (fun z : sourceSoninCarrier lambda => z +
      boundaryRow (((ContinuousLinearMap.id ℂ finiteSCarrier -
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transport) y))
    hpoint.symm

/-! ## The step-level source contract -/

/-!
The ambient channel is useful only when a physical row has the matching
adjacent decomposition.  This structure records that decomposition together
with the two row bounds.  In particular, it does not infer a readout from a
norm estimate for the target row.
-/
structure SuffixRawOldCarrierCoframeStepReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (target : OldRow lambda)
    (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  ambientRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  ambient_norm_le : ‖ambientRow‖ ≤ ambientBound
  boundary_norm_le : ‖boundaryRow‖ ≤ boundaryBound
  decomposition :
    target =
      ambientRow ∘L (normalizedPrimeEulerFrameTransport p)† - ambientRow +
        boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport)

theorem sqrtPrimeEulerCoefficient_norm_le_one
    (p : CCM24VisiblePrime) :
    ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ ≤ (1 : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hq_one : ccm24PrimeEulerCoefficient p ≤ (1 : ℝ) :=
    (ccm24PrimeEulerCoefficient_lt_one p).le
  have hsqrt_nonneg : 0 ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (ccm24PrimeEulerCoefficient p) ^ 2 =
      ccm24PrimeEulerCoefficient p :=
    Real.sq_sqrt hq
  nlinarith

/-! ## One row, one old-carrier readout -/

/-- A row is usable only when it factors through the actual two-channel
old-carrier analysis.  The bound is part of the contract, not inferred from a
separate operator-norm estimate. -/
structure SuffixRawOldCarrierCoframeRowReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (row : OldRow lambda) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
    sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S = row

/-!
Turn the exact step decomposition into the existing row-readout contract.
The coefficient bound is deliberately discharged here, at the producer
boundary, so every later consumer sees a family-independent `ambientBound +
boundaryBound` estimate.
-/
noncomputable def
    SuffixRawOldCarrierCoframeStepReadoutData.toRowReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {target : OldRow lambda}
    {ambientBound boundaryBound : ℝ}
    (data : SuffixRawOldCarrierCoframeStepReadoutData owner lambda p S
      target ambientBound boundaryBound) :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S target
      (ambientBound + boundaryBound) := by
  refine
    { bound_nonneg := add_nonneg data.ambient_bound_nonneg
        data.boundary_bound_nonneg
      readout := ambientDifferencePlusBoundaryReadout p data.ambientRow
        data.boundaryRow
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖ambientDifferencePlusBoundaryReadout p data.ambientRow
          data.boundaryRow‖ ≤
          ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ *
              ‖data.ambientRow‖ + ‖data.boundaryRow‖ :=
        ambientDifferencePlusBoundaryReadout_norm_le p data.ambientRow
          data.boundaryRow
      _ ≤ (1 : ℝ) * ambientBound + boundaryBound := by
        exact add_le_add
          (mul_le_mul (sqrtPrimeEulerCoefficient_norm_le_one p)
            data.ambient_norm_le (norm_nonneg data.ambientRow) zero_le_one)
          data.boundary_norm_le
      _ = ambientBound + boundaryBound := by simp
  · calc
      ambientDifferencePlusBoundaryReadout p data.ambientRow
          data.boundaryRow ∘L
            suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
          data.ambientRow ∘L (normalizedPrimeEulerFrameTransport p)† -
              data.ambientRow +
            data.boundaryRow ∘L
              ((ContinuousLinearMap.id ℂ finiteSCarrier -
                  (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                    ContinuousLinearMap.adjoint
                      (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).transport) :=
        ambientDifferencePlusBoundaryReadout_comp_oldCarrierAnalysis_eq
          p S data.ambientRow data.boundaryRow
      _ = target := data.decomposition.symm

/-- The three row contracts used by the divide-and-conquer owner. -/
structure SuffixRawOldCarrierCoframeDivideConquerData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (orientationBound residualBound knownBound : ℝ) where
  orientation :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S
      (suffixActualBandRawPhysicalOldCarrierMetricOrientationRow
        owner lambda p S) orientationBound
  residual :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S
      (suffixActualBandRawPhysicalOldCarrierMetricResidualRow
        owner lambda p S) residualBound
  known :
      SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S
      (coframeKnownBoundedRow owner lambda p S) knownBound

/-! ## Hard-row absorption -/

noncomputable def
    SuffixRawOldCarrierCoframeDivideConquerData.toHardReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S
      (coframeHardRow owner lambda p S)
      (orientationBound + residualBound) := by
  refine
    { bound_nonneg := add_nonneg data.orientation.bound_nonneg
        data.residual.bound_nonneg
      readout := data.orientation.readout + data.residual.readout
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖data.orientation.readout + data.residual.readout‖ ≤
          ‖data.orientation.readout‖ + ‖data.residual.readout‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ orientationBound + residualBound := add_le_add
        data.orientation.readout_norm_le data.residual.readout_norm_le
  · calc
      (data.orientation.readout + data.residual.readout) ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
          (data.orientation.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) +
            (data.residual.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) := by
        apply ContinuousLinearMap.ext
        intro y
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.add_apply]
      _ = suffixActualBandRawPhysicalOldCarrierMetricOrientationRow
            owner lambda p S +
          suffixActualBandRawPhysicalOldCarrierMetricResidualRow
            owner lambda p S := by
        rw [data.orientation.factorization, data.residual.factorization]
      _ = coframeHardRow owner lambda p S := by
        rfl

/-! ## Absorbing the known row into the same readout -/

noncomputable def
    SuffixRawOldCarrierCoframeDivideConquerData.toSignedReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S
      (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S)
      ((orientationBound + residualBound) + knownBound) := by
  let hardData := data.toHardReadout
  refine
    { bound_nonneg := add_nonneg hardData.bound_nonneg
        data.known.bound_nonneg
      readout := hardData.readout + data.known.readout
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖hardData.readout + data.known.readout‖ ≤
          ‖hardData.readout‖ + ‖data.known.readout‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ (orientationBound + residualBound) + knownBound :=
        add_le_add hardData.readout_norm_le data.known.readout_norm_le
  · calc
      (hardData.readout + data.known.readout) ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
          (hardData.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) +
            (data.known.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) := by
        apply ContinuousLinearMap.ext
        intro y
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.add_apply]
      _ = coframeHardRow owner lambda p S +
          coframeKnownBoundedRow owner lambda p S := by
        rw [hardData.factorization, data.known.factorization]
      _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S := by
        exact
          (signedTelescope_eq_hard_add_known owner lambda p S).symm

/-! ## Recovering the two physical columns -/

noncomputable def
    SuffixRawOldCarrierCoframeDivideConquerData.toAmbientRow
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) : OldRow lambda :=
  data.toSignedReadout.readout ∘L
    suffixEulerFrameAmbientBoundaryLeftEmbedding

noncomputable def
    SuffixRawOldCarrierCoframeDivideConquerData.toBoundaryRow
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) : OldRow lambda :=
  data.toSignedReadout.readout ∘L
    suffixEulerFrameAmbientBoundaryRightEmbedding

theorem SuffixRawOldCarrierCoframeDivideConquerData.toAmbientRow_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    ‖data.toAmbientRow‖ ≤
      (orientationBound + residualBound) + knownBound := by
  let totalBound : ℝ := (orientationBound + residualBound) + knownBound
  have htotal : 0 ≤ totalBound := by
    exact add_nonneg
      (add_nonneg data.orientation.bound_nonneg data.residual.bound_nonneg)
      data.known.bound_nonneg
  change ‖data.toSignedReadout.readout ∘L
      suffixEulerFrameAmbientBoundaryLeftEmbedding‖ ≤ totalBound
  calc
    ‖data.toSignedReadout.readout ∘L
        suffixEulerFrameAmbientBoundaryLeftEmbedding‖ ≤
        ‖data.toSignedReadout.readout‖ *
          ‖suffixEulerFrameAmbientBoundaryLeftEmbedding‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ totalBound * 1 := by
      exact mul_le_mul data.toSignedReadout.readout_norm_le
        suffixEulerFrameAmbientBoundaryLeftEmbedding_norm_le_one
        (norm_nonneg _) htotal
    _ = totalBound := by simp

theorem SuffixRawOldCarrierCoframeDivideConquerData.toBoundaryRow_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    ‖data.toBoundaryRow‖ ≤
      (orientationBound + residualBound) + knownBound := by
  let totalBound : ℝ := (orientationBound + residualBound) + knownBound
  have htotal : 0 ≤ totalBound := by
    exact add_nonneg
      (add_nonneg data.orientation.bound_nonneg data.residual.bound_nonneg)
      data.known.bound_nonneg
  change ‖data.toSignedReadout.readout ∘L
      suffixEulerFrameAmbientBoundaryRightEmbedding‖ ≤ totalBound
  calc
    ‖data.toSignedReadout.readout ∘L
        suffixEulerFrameAmbientBoundaryRightEmbedding‖ ≤
        ‖data.toSignedReadout.readout‖ *
          ‖suffixEulerFrameAmbientBoundaryRightEmbedding‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ totalBound * 1 := by
      exact mul_le_mul data.toSignedReadout.readout_norm_le
        suffixEulerFrameAmbientBoundaryRightEmbedding_norm_le_one
        (norm_nonneg _) htotal
    _ = totalBound := by simp

noncomputable def
    SuffixRawOldCarrierCoframeDivideConquerData.toTwoChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    SuffixRawOldCarrierTwoChannelFactorData owner lambda p S
      ((orientationBound + residualBound) + knownBound)
      ((orientationBound + residualBound) + knownBound) := by
  let totalBound : ℝ := (orientationBound + residualBound) + knownBound
  have htotal : 0 ≤ totalBound := by
    exact add_nonneg
      (add_nonneg data.orientation.bound_nonneg data.residual.bound_nonneg)
      data.known.bound_nonneg
  refine
    { ambient_bound_nonneg := htotal
      boundary_bound_nonneg := htotal
      ambientRow := data.toAmbientRow
      boundaryRow := data.toBoundaryRow
      ambient_norm_le := ?_
      boundary_norm_le := ?_
      factorization := ?_ }
  · exact data.toAmbientRow_norm_le
  · exact data.toBoundaryRow_norm_le
  · let signedData := data.toSignedReadout
    have hcomponents :=
      suffixEulerFrameAmbientBoundaryReadoutOfRows_components_eq
        signedData.readout
    calc
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
          signedData.readout ∘L
            suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S :=
        signedData.factorization.symm
      _ = suffixEulerFrameAmbientBoundaryReadoutOfRows
              data.toAmbientRow data.toBoundaryRow ∘L
            suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S := by
        exact congrArg
          (fun readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
              sourceSoninCarrier lambda =>
            readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
          hcomponents.symm
      _ = data.toAmbientRow ∘L
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) +
          data.toBoundaryRow ∘L
            ((ContinuousLinearMap.id ℂ finiteSCarrier -
                (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                  ContinuousLinearMap.adjoint
                    (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).transport) := by
        exact
          suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis
            p S data.toAmbientRow data.toBoundaryRow

theorem SuffixRawOldCarrierCoframeDivideConquerData.toOldCarrierDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound) :
    SuffixRawOldCarrierDomination owner lambda p S
      (((orientationBound + residualBound) + knownBound) +
        ((orientationBound + residualBound) + knownBound)) :=
  (data.toTwoChannelFactorData).toOldCarrierDomination

/-! ## Family-uniform packaging and Gate 3U handoff -/

structure SuffixRawOldCarrierCoframeUniformDivideConquerData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (orientationBound residualBound knownBound : ℝ) where
  orientation_bound_nonneg : 0 ≤ orientationBound
  residual_bound_nonneg : 0 ≤ residualBound
  known_bound_nonneg : 0 ≤ knownBound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierCoframeDivideConquerData owner lambda p S
      orientationBound residualBound knownBound

noncomputable def
    SuffixRawOldCarrierCoframeUniformDivideConquerData.toUniformTwoChannelFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformDivideConquerData owner lambda
      orientationBound residualBound knownBound) :
    SuffixRawOldCarrierTwoChannelUniformFactorData owner lambda
      ((orientationBound + residualBound) + knownBound)
      ((orientationBound + residualBound) + knownBound) :=
  { ambient_bound_nonneg := add_nonneg
      (add_nonneg data.orientation_bound_nonneg data.residual_bound_nonneg)
      data.known_bound_nonneg
    boundary_bound_nonneg := add_nonneg
      (add_nonneg data.orientation_bound_nonneg data.residual_bound_nonneg)
      data.known_bound_nonneg
    factor := fun p S => (data.factor p S).toTwoChannelFactorData }

noncomputable def
    SuffixRawOldCarrierCoframeUniformDivideConquerData.toUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformDivideConquerData owner lambda
      orientationBound residualBound knownBound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda
      (((orientationBound + residualBound) + knownBound) +
        ((orientationBound + residualBound) + knownBound))) :=
  (data.toUniformTwoChannelFactor).toUniformDomination

noncomputable def coframeToUniformRawDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierUniformDominationData owner lambda bound) :
    SuffixRawAmbientBoundaryUniformDominationData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    domination := fun p S =>
      suffixRawOldCarrierDomination_implies_rawDomination owner lambda p S
        bound (data.domination p S) }

theorem
    SuffixRawOldCarrierCoframeUniformDivideConquerData.toUniformGate3UHandoff
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    {orientationBound residualBound knownBound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformDivideConquerData owner lambda
      orientationBound residualBound knownBound) :
    Nonempty (SuffixLocalNonpolarGapUniformDouglasData owner lambda
      (‖detectorOperator owner‖ +
        (((orientationBound + residualBound) + knownBound) +
          ((orientationBound + residualBound) + knownBound)))) := by
  obtain ⟨oldData⟩ := data.toUniformDomination
  refine ⟨?_⟩
  exact
    SuffixRawAmbientBoundaryUniformDominationData.toNonpolarGapDouglas
      (coframeToUniformRawDomination oldData)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
end CCM25Concrete
end Source
end ConnesWeilRH
