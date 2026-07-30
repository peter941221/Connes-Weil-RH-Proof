/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

/-!
# Leakage expansion of the signed old-carrier telescope

The old-carrier signed telescope is the exact adjacent difference of two
boundary moments.  This module expands each moment into its endpoint-leakage
and forward-coframe channels, then records the precise two-channel factor
contract that would close Bone 1.

The expansion is algebraic only.  It does not claim that either channel has a
uniform readout through the ambient loss or moving-boundary column.  The
contract below is therefore the remaining source theorem, not an axiom or a
derived estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact leakage channels -/

/-- The endpoint leakage part of the actual boundary moment. -/
noncomputable def suffixActualBandRawCoframeBoundaryAmbientLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixActualBandForwardEndpointCoframe lambda S -
      CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
    detectorOperator owner ∘L CCM24FiniteSGramResponse.sourceInclusion lambda

/-- The forward-coframe part of the actual boundary moment. -/
noncomputable def suffixActualBandRawCoframeBoundaryForwardLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
    detectorOperator owner ∘L
    suffixActualBandForwardCoframe lambda S

theorem suffixActualBandRawCoframeBoundaryMoment_eq_leakage_channels
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S) =
      suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda S +
        suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S := by
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_leakage]
  rfl

/-! ## The signed adjacent difference -/

/-- The endpoint-leakage telescope, with the signed adjacent difference kept
intact. -/
noncomputable def suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda S ∘L
      (suffixEulerFrameTransition lambda p S)† ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame -
    ((suffixEulerFrameTransition lambda p S)† ∘L
      suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda (p :: S)) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame

/-- The forward-coframe telescope, with the signed adjacent difference kept
intact. -/
noncomputable def suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
      (suffixEulerFrameTransition lambda p S)† ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame -
    ((suffixEulerFrameTransition lambda p S)† ∘L
      suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda (p :: S)) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_leakage_telescopes
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
          owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope,
    suffixActualBandRawCoframeBoundaryMoment_eq_leakage_channels,
    suffixActualBandRawCoframeBoundaryMoment_eq_leakage_channels]
  apply ContinuousLinearMap.ext
  intro y
  simp only [suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope,
    suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_add]
  abel_nf

/-! ## What a genuine two-channel producer must provide -/

/-- A source-side factor contract for the complete signed telescope.  The two
rows are allowed to depend on `(p,S)`, but their bounds are shared by the
whole family. -/
structure SuffixRawOldCarrierTwoChannelFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  ambientRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  ambient_norm_le : ‖ambientRow‖ ≤ ambientBound
  boundary_norm_le : ‖boundaryRow‖ ≤ boundaryBound
  factorization :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      ambientRow ∘L
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) +
        boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport)

/-! ## The packed readout and the old-carrier handoff -/

noncomputable def SuffixRawOldCarrierTwoChannelFactorData.readout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawOldCarrierTwoChannelFactorData owner lambda p S
      ambientBound boundaryBound) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  suffixEulerFrameAmbientBoundaryReadoutOfRows data.ambientRow data.boundaryRow

theorem suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis
    {lambda : CCM24SoninScale} (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (ambientRow boundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryReadoutOfRows ambientRow boundaryRow ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      ambientRow ∘L
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) +
        boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply]
  rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply]
  simp only [suffixEulerFrameAmbientBoundaryReadoutOfRows_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rfl

theorem SuffixRawOldCarrierTwoChannelFactorData.toOldCarrierDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawOldCarrierTwoChannelFactorData owner lambda p S
      ambientBound boundaryBound) :
    SuffixRawOldCarrierDomination owner lambda p S
      (ambientBound + boundaryBound) := by
  apply (suffixRawOldCarrierDomination_iff_exists_bounded_oldCarrierReadout
    owner lambda p S (ambientBound + boundaryBound)).mpr
  have hbound : 0 ≤ ambientBound + boundaryBound :=
    add_nonneg data.ambient_bound_nonneg data.boundary_bound_nonneg
  refine ⟨hbound, ?_⟩
  refine ⟨data.readout, ?_, ?_⟩
  · change ‖suffixEulerFrameAmbientBoundaryReadoutOfRows
      data.ambientRow data.boundaryRow‖ ≤ ambientBound + boundaryBound
    calc
      ‖suffixEulerFrameAmbientBoundaryReadoutOfRows
          data.ambientRow data.boundaryRow‖ ≤
          ‖data.ambientRow‖ + ‖data.boundaryRow‖ :=
        suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add
          data.ambientRow data.boundaryRow
      _ ≤ ambientBound + boundaryBound :=
        add_le_add data.ambient_norm_le data.boundary_norm_le
  · calc
      data.readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
          lambda p S =
        data.ambientRow ∘L
              (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) +
          data.boundaryRow ∘L
            ((ContinuousLinearMap.id ℂ finiteSCarrier -
                (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                  ContinuousLinearMap.adjoint
                    (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).transport) :=
        suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis
          p S data.ambientRow data.boundaryRow
      _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S :=
        data.factorization.symm
      _ = suffixActualBandRawPhysicalReducedRow owner lambda p S :=
        (suffixActualBandRawPhysicalReducedRow_eq_signedTelescope
          owner lambda p S).symm

/-! ## Uniform family form -/

structure SuffixRawOldCarrierTwoChannelUniformFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierTwoChannelFactorData owner lambda p S
      ambientBound boundaryBound

theorem SuffixRawOldCarrierTwoChannelUniformFactorData.toUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawOldCarrierTwoChannelUniformFactorData owner lambda
      ambientBound boundaryBound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda
      (ambientBound + boundaryBound)) := by
  let domination : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRawOldCarrierDomination owner lambda p S
        (ambientBound + boundaryBound) := fun p S =>
    (data.factor p S).toOldCarrierDomination
  refine ⟨{ bound_nonneg := ?_, domination := domination }⟩
  exact add_nonneg data.ambient_bound_nonneg data.boundary_bound_nonneg

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
end CCM25Concrete
end Source
end ConnesWeilRH
