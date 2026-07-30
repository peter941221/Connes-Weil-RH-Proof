/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer

/-!
# Joint old-carrier readout for the coframe telescope

The coframe divide-and-conquer package originally accepted three independent
readouts.  That decomposition is useful for bookkeeping, but it can destroy
the cancellation which makes the signed telescope factor through the physical
analysis.  This module exposes the weaker and source-facing contract:

```text
signed telescope = one readout * old-carrier analysis.
```

The two ambient/boundary rows are recovered only after the joint readout has
been constructed.  Thus a producer can keep the survivor, Schur boundary, and
known terms together until the exact factorization is established.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "OldRow" lambda =>
  finiteSCarrier →L[ℂ] sourceSoninCarrier lambda

/-- The correct producer contract for the complete signed coframe telescope.
The readout is constructed before the two physical coordinates are separated.
-/
structure SuffixRawOldCarrierCoframeJointReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
    sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S

/-- An already-proved old-carrier domination produces the joint readout with
the same bound.  The conversion uses the exact reduced-row/signed-telescope
identity; it does not infer a readout from injectivity or from an operator-norm
bound. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointReadoutData.ofDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawOldCarrierDomination owner lambda p S bound) :
    SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound := by
  let witness :=
    (suffixRawOldCarrierDomination_iff_exists_bounded_oldCarrierReadout
      owner lambda p S bound).mp hdom
  let factorWitness := witness.2
  let readout := Classical.choose factorWitness
  have readoutSpec := Classical.choose_spec factorWitness
  refine
    { bound_nonneg := hdom.1
      readout := readout
      readout_norm_le := readoutSpec.1
      factorization := ?_ }
  calc
    readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
        suffixActualBandRawPhysicalReducedRow owner lambda p S := by
      simpa only [readout] using readoutSpec.2
    _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S :=
      suffixActualBandRawPhysicalReducedRow_eq_signedTelescope owner lambda p S

/-- Recover the ambient row from the joint readout. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointReadoutData.ambientRow
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding

/-- Recover the moving-boundary row from the joint readout. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointReadoutData.boundaryRow
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding

theorem SuffixRawOldCarrierCoframeJointReadoutData.ambientRow_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    ‖data.ambientRow‖ ≤ bound := by
  unfold SuffixRawOldCarrierCoframeJointReadoutData.ambientRow
  calc
    ‖data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding‖ ≤
        ‖data.readout‖ * ‖suffixEulerFrameAmbientBoundaryLeftEmbedding‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ bound * 1 := by
      exact mul_le_mul data.readout_norm_le
        suffixEulerFrameAmbientBoundaryLeftEmbedding_norm_le_one
        (norm_nonneg _) data.bound_nonneg
    _ = bound := by simp

theorem SuffixRawOldCarrierCoframeJointReadoutData.boundaryRow_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    ‖data.boundaryRow‖ ≤ bound := by
  unfold SuffixRawOldCarrierCoframeJointReadoutData.boundaryRow
  calc
    ‖data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding‖ ≤
        ‖data.readout‖ * ‖suffixEulerFrameAmbientBoundaryRightEmbedding‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ bound * 1 := by
      exact mul_le_mul data.readout_norm_le
        suffixEulerFrameAmbientBoundaryRightEmbedding_norm_le_one
        (norm_nonneg _) data.bound_nonneg
    _ = bound := by simp

theorem SuffixRawOldCarrierCoframeJointReadoutData.factorization_rows
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    data.ambientRow ∘L
          ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) +
        data.boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S := by
  have hcomponents :=
    suffixEulerFrameAmbientBoundaryReadoutOfRows_components_eq data.readout
  calc
    data.ambientRow ∘L
          ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) +
        data.boundaryRow ∘L
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) =
      suffixEulerFrameAmbientBoundaryReadoutOfRows
          data.ambientRow data.boundaryRow ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S := by
      exact
        suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis
          p S data.ambientRow data.boundaryRow |>.symm
    _ = data.readout ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S := by
      rw [← hcomponents]
      rfl
    _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S :=
      data.factorization

/-- A joint readout immediately supplies the existing two-channel factor data.
-/
noncomputable def
    SuffixRawOldCarrierCoframeJointReadoutData.toTwoChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    SuffixRawOldCarrierTwoChannelFactorData owner lambda p S bound bound := by
  refine
    { ambient_bound_nonneg := data.bound_nonneg
      boundary_bound_nonneg := data.bound_nonneg
      ambientRow := data.ambientRow
      boundaryRow := data.boundaryRow
      ambient_norm_le := data.ambientRow_norm_le
      boundary_norm_le := data.boundaryRow_norm_le
      factorization := data.factorization_rows.symm }

structure SuffixRawOldCarrierCoframeUniformJointReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound

/-- Uniform old-carrier domination can be repackaged as a uniform joint
coframe readout.  This conversion is exact at the readout level and does not
add a source estimate. -/
noncomputable def
    SuffixRawOldCarrierCoframeUniformJointReadoutData.ofUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierUniformDominationData owner lambda bound) :
    SuffixRawOldCarrierCoframeUniformJointReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      SuffixRawOldCarrierCoframeJointReadoutData.ofDomination
        (data.domination p S) }

noncomputable def
    SuffixRawOldCarrierCoframeUniformJointReadoutData.toUniformFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointReadoutData owner lambda bound) :
    SuffixRawOldCarrierTwoChannelUniformFactorData owner lambda bound bound :=
  { ambient_bound_nonneg := data.bound_nonneg
    boundary_bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      (data.readout p S).toTwoChannelFactorData }

noncomputable def
    SuffixRawOldCarrierCoframeUniformJointReadoutData.toUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointReadoutData owner lambda bound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda (2 * bound)) :=
  by
    simpa only [two_mul] using
      (data.toUniformFactor).toUniformDomination

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointReadout
end CCM25Concrete
end Source
end ConnesWeilRH
