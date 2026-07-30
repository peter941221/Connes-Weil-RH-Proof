/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadialFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse

/-!
# Signed-row reduction to the interior adjoint renewal

The old-carrier signed row ends in the adjoint of the actual old suffix frame.
That frame lies in the radial half-line, so the complete signed row annihilates
the radial complement.  Consequently the exterior adjoint renewal constructed
in Proofs 615--616 contributes exactly zero to the signed numerator.

For the genuine normalized inverse `N`, the surviving pullback is therefore

```text
signedRow * N^dagger * E
  = signedRow * E * N^dagger * E.
```

The right side contains the compressed interior renewal from Proof 614.  This
rules out further work on the exterior channel as a route to Bone 1.  It does
not control the interior metric/forward Gram correction.  Bone 1, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantSignedRadial

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadial
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRenewal
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The old frame sees only the radial half-line -/

theorem oldFrameAdjoint_comp_radialComplement_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
        radialComplement lambda = 0 := by
  let frame := (suffixEulerFrameSchurStep lambda p S).oldFrame
  let E := radialSupportProjection lambda
  have hframe : E ∘L frame = frame := by
    simpa only [frame, suffixEulerFrameSchurStep, oldSuffixFrame,
      newSuffixFrame] using
      (radialSupportProjection_comp_newSuffixFrame lambda (p :: S))
  have hEadj : E† = E :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hadjoint := congrArg ContinuousLinearMap.adjoint hframe
  have hframeAdj : frame† ∘L E = frame† := by
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hEadj] using hadjoint
  apply ContinuousLinearMap.ext
  intro x
  have hfixed := DFunLike.congr_fun hframeAdj x
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearMap.zero_apply, frame] at hfixed ⊢
  rw [hfixed, sub_self]

/-! ## Complete signed-row annihilation -/

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialComplement_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        radialComplement lambda = 0 := by
  have hold := oldFrameAdjoint_comp_radialComplement_eq_zero lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have holdPoint := DFunLike.congr_fun hold x
  simp only [suffixActualBandRawPhysicalOldCarrierSignedTelescope,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at holdPoint ⊢
  rw [holdPoint]
  simp

theorem suffixActualBandRawPhysicalReducedRow_comp_radialComplement_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        radialComplement lambda = 0 := by
  rw [suffixActualBandRawPhysicalReducedRow_eq_signedTelescope]
  exact
    suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialComplement_eq_zero
      owner lambda p S

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialSupport_eq_self
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        radialSupportProjection lambda =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S := by
  let row :=
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S
  let E := radialSupportProjection lambda
  let F := radialComplement lambda
  have hzero :=
    suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialComplement_eq_zero
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hzeroPoint := DFunLike.congr_fun hzero x
  have hsplit : x = E x + F x := by
    simp only [E, F, radialComplement,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzeroPoint ⊢
  change row (E x) = row x
  calc
    row (E x) = row (E x) + row (F x) := by
      rw [hzeroPoint, add_zero]
    _ = row (E x + F x) := by rw [map_add]
    _ = row x := by rw [← hsplit]

/-! ## Exterior renewal vanishes in the signed numerator -/

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_exteriorAdjointCrossing_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        primeEulerExteriorAdjointCrossing lambda p = 0 := by
  have hzero :=
    suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialComplement_eq_zero
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hzeroPoint := DFunLike.congr_fun hzero
    (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
      (radialSupportProjection lambda x))
  simpa only [primeEulerExteriorAdjointCrossing,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using
      hzeroPoint

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_exteriorReadout_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        primeEulerExteriorAdjointReadout lambda p ∘L
          (primeEulerAmbientLossFactor p)† ∘L
            radialSupportProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hfactor := DFunLike.congr_fun
    (primeEulerExteriorAdjointReadout_comp_ambientLoss_radialSupport
      lambda p) x
  have hzero := DFunLike.congr_fun
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_exteriorAdjointCrossing_eq_zero
      owner lambda p S) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hfactor hzero ⊢
  rw [hfactor]
  exact hzero

/-! ## The sole survivor is the compressed interior renewal -/

theorem signedTelescope_comp_inverseAdjoint_radialSupport_eq_compressed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (normalizedPrimeEulerInverse p)† ∘L
          radialSupportProjection lambda =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        primeEulerCompressedAdjointRenewal lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hradial := DFunLike.congr_fun
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialSupport_eq_self
      owner lambda p S)
    (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
      (radialSupportProjection lambda x))
  simpa only [primeEulerCompressedAdjointRenewal,
    ContinuousLinearMap.comp_apply] using hradial.symm

theorem signedTelescope_comp_scalarInverseAdjoint_eq_radialCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        radialSupportProjection lambda ∘L
          (scalarNormalizedPrimeEulerInverse p)† := by
  apply ContinuousLinearMap.ext
  intro x
  have hradial := DFunLike.congr_fun
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_radialSupport_eq_self
      owner lambda p S)
    (ContinuousLinearMap.adjoint (scalarNormalizedPrimeEulerInverse p) x)
  simpa only [ContinuousLinearMap.comp_apply] using hradial.symm

theorem signedTelescope_comp_scalarInverseAdjoint_newFrame_eq_radialCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        radialSupportProjection lambda ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame := by
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun
    (signedTelescope_comp_scalarInverseAdjoint_eq_radialCompression
      owner lambda p S)
    ((suffixEulerFrameSchurStep lambda p S).newFrame x)
  simpa only [ContinuousLinearMap.comp_apply] using hpoint

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantSignedRadial
end CCM25Concrete
end Source
end ConnesWeilRH
