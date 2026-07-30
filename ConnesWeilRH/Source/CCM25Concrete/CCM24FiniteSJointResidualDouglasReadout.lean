/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurEndpointAlignmentResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization

/-!
# Joint residual Douglas/readout contract

Proof 565 aligns the actual Schur endpoint with the named suffix endpoint.
This module keeps the endpoint residuals together and lifts the existing
signed row ledger to a uniform component-row producer contract.

The contract is intentionally conditional: it does not manufacture Schur or
residual component rows, and it does not prove the Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJointResidualDouglasReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurEndpointAlignmentResidual
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSActualSchurTelescoping

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The joint endpoint residual ledger -/

theorem suffixActualSchurEndpointAlignmentResidual_add_endpointResidual_eq_transportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    suffixActualSchurEndpointAlignmentResidual lambda stepData family +
        suffixActualSchurEndpointResidual lambda stepData family =
      sourceActualBandForwardTransportResidual lambda stepData
        family.visiblePrimes := by
  unfold suffixActualSchurEndpointAlignmentResidual
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

/-! ## Named Schur row abbreviations -/

noncomputable def suffixActualBandNamedSchurRawPhysicalFourTermRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  rawPhysicalFourTermRowOfCoframes owner lambda p S
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
    (sourceActualBandForwardSchurCoframe lambda stepData (p :: S))

noncomputable def suffixActualBandNamedSchurCoframeResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  rawPhysicalCoframeResidualRow owner lambda p S
    (suffixActualBandForwardCoframe lambda S)
    (suffixActualBandForwardEndpointCoframe lambda S)
    (suffixActualBandForwardEndpointCoframe lambda (p :: S))
    (suffixActualBandForwardCoframe lambda (p :: S))
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
    (sourceActualBandForwardSchurCoframe lambda stepData (p :: S))

theorem suffixActualBandRawPhysicalFourTermRow_eq_namedSchurRow_add_namedResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S +
        suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S := by
  exact suffixActualBandRawPhysicalFourTermRow_eq_namedSchur_add_residual
    owner lambda stepData p S

/-! ## One-pair joint component data -/

structure SuffixNamedSchurResidualComponentReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ) where
  schur_ambient_bound_nonneg : 0 ≤ schurAmbientBound
  schur_boundary_bound_nonneg : 0 ≤ schurBoundaryBound
  residual_ambient_bound_nonneg : 0 ≤ residualAmbientBound
  residual_boundary_bound_nonneg : 0 ≤ residualBoundaryBound
  schurAmbientRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  schurBoundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  residualAmbientRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  residualBoundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  schur_ambient_norm_le : ‖schurAmbientRow‖ ≤ schurAmbientBound
  schur_boundary_norm_le : ‖schurBoundaryRow‖ ≤ schurBoundaryBound
  residual_ambient_norm_le : ‖residualAmbientRow‖ ≤ residualAmbientBound
  residual_boundary_norm_le : ‖residualBoundaryRow‖ ≤ residualBoundaryBound
  schur_factorization :
    schurAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
        schurBoundaryRow ∘L ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary =
      suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S
  residual_factorization :
    residualAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
        residualBoundaryRow ∘L ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary =
      suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S

noncomputable def
    SuffixNamedSchurResidualComponentReadoutData.toActualComponentReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ}
    (data : SuffixNamedSchurResidualComponentReadoutData owner lambda stepData
      p S schurAmbientBound schurBoundaryBound residualAmbientBound
        residualBoundaryBound) :
    SuffixRawAmbientBoundaryComponentReadoutData owner lambda p S
      (schurAmbientBound + residualAmbientBound)
      (schurBoundaryBound + residualBoundaryBound) := by
  have hrow :
      suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S +
          suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
    exact
      (suffixActualBandRawPhysicalFourTermRow_eq_namedSchurRow_add_namedResidualRow
        owner lambda stepData p S).symm
  have hfactor := componentRows_add_of_schur_and_residual owner p S
    data.schurAmbientRow data.schurBoundaryRow data.residualAmbientRow
    data.residualBoundaryRow
    (suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S)
    (suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S)
    hrow (by simpa using data.schur_factorization)
    (by simpa using data.residual_factorization)
  refine
    { ambient_bound_nonneg := add_nonneg
        data.schur_ambient_bound_nonneg data.residual_ambient_bound_nonneg
      boundary_bound_nonneg := add_nonneg
        data.schur_boundary_bound_nonneg data.residual_boundary_bound_nonneg
      ambientRow := data.schurAmbientRow + data.residualAmbientRow
      boundaryRow := data.schurBoundaryRow + data.residualBoundaryRow
      ambient_norm_le := ?_
      boundary_norm_le := ?_
      factorization := hfactor }
  · calc
      ‖data.schurAmbientRow + data.residualAmbientRow‖ ≤
          ‖data.schurAmbientRow‖ + ‖data.residualAmbientRow‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ schurAmbientBound + residualAmbientBound := add_le_add
        data.schur_ambient_norm_le data.residual_ambient_norm_le
  · calc
      ‖data.schurBoundaryRow + data.residualBoundaryRow‖ ≤
          ‖data.schurBoundaryRow‖ + ‖data.residualBoundaryRow‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ schurBoundaryBound + residualBoundaryBound := add_le_add
        data.schur_boundary_norm_le data.residual_boundary_norm_le

/-! ## Uniform producer handoff -/

structure SuffixNamedSchurResidualUniformComponentReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ) where
  schur_ambient_bound_nonneg : 0 ≤ schurAmbientBound
  schur_boundary_bound_nonneg : 0 ≤ schurBoundaryBound
  residual_ambient_bound_nonneg : 0 ≤ residualAmbientBound
  residual_boundary_bound_nonneg : 0 ≤ residualBoundaryBound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixNamedSchurResidualComponentReadoutData owner lambda stepData p S
      schurAmbientBound schurBoundaryBound residualAmbientBound
        residualBoundaryBound

noncomputable def
    SuffixNamedSchurResidualUniformComponentReadoutData.toRawUniformReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S}
    {schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ}
    (data : SuffixNamedSchurResidualUniformComponentReadoutData owner lambda
      stepData schurAmbientBound schurBoundaryBound residualAmbientBound
        residualBoundaryBound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda
      ((schurAmbientBound + residualAmbientBound) +
        (schurBoundaryBound + residualBoundaryBound)) :=
  { bound_nonneg := add_nonneg
      (add_nonneg data.schur_ambient_bound_nonneg
        data.residual_ambient_bound_nonneg)
      (add_nonneg data.schur_boundary_bound_nonneg
        data.residual_boundary_bound_nonneg)
    readout := fun p S =>
      (data.readout p S).toActualComponentReadout.toRawReadout }

noncomputable def
    SuffixNamedSchurResidualUniformComponentReadoutData.toPhysicalDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S}
    {schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ}
    (data : SuffixNamedSchurResidualUniformComponentReadoutData owner lambda
      stepData schurAmbientBound schurBoundaryBound residualAmbientBound
        residualBoundaryBound) :
    SuffixMismatchAmbientBoundaryUniformDominationData owner lambda
      (‖detectorOperator owner‖ +
        ((schurAmbientBound + residualAmbientBound) +
          (schurBoundaryBound + residualBoundaryBound))) :=
  SuffixMismatchAmbientBoundaryUniformReadoutData.toDomination
    (SuffixRawAmbientBoundaryUniformReadoutData.toMismatch
      data.toRawUniformReadout)

theorem uniformNamedSchurResidualComponentReadout_implies_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (schurAmbientBound schurBoundaryBound residualAmbientBound
      residualBoundaryBound : ℝ)
    (data : SuffixNamedSchurResidualUniformComponentReadoutData owner lambda
      stepData schurAmbientBound schurBoundaryBound residualAmbientBound
        residualBoundaryBound) :
    ∃ bound : ℝ,
      Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
        owner lambda bound) := by
  exact ⟨‖detectorOperator owner‖ +
      ((schurAmbientBound + residualAmbientBound) +
        (schurBoundaryBound + residualBoundaryBound)),
    ⟨data.toPhysicalDomination⟩⟩

end CCM24FiniteSJointResidualDouglasReadout
end CCM25Concrete
end Source
end ConnesWeilRH
