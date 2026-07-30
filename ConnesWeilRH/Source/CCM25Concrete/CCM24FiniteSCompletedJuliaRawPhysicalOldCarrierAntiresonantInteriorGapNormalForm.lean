/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantScalarInteriorNormalization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer

/-!
# Interior renewal as the synchronized metric/forward gap

Proof 618 isolates the compressed interior adjoint renewal from the
scalar-normalized pullback.  The older joint-pullback ledger identifies that
same pullback with the synchronized boundary-moment gap.  Cancelling only the
nonzero scalar `rho_p^(-1)` gives the exact same-object normal form

```text
Interior_(p,S) = Gap_(p,S) * ReverseTransition_(p,S)^dagger.
```

The reverse transition is contractive and has the forward transition as a
scalar inverse.  Consequently the two operator norms are uniformly equivalent
within the fixed factor `8`.  This removes the renewal resolvent from the
analytic bottom: the remaining source problem is the complete signed
metric/forward gap itself.

No term of that gap is estimated separately here.  Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantScalarInterior
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

theorem comp_eq_smul_of_eq_comp_and_comp_eq_smul_id
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Y X B A : H →L[ℂ] H) (rho : ℂ)
    (hY : Y = X ∘L B)
    (hBA : B ∘L A = rho • ContinuousLinearMap.id ℂ H) :
    Y ∘L A = rho • X := by
  rw [hY, ContinuousLinearMap.comp_assoc, hBA]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul]

/-! ## The genuine interior owner -/

noncomputable def signedCompressedInteriorOwner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
    primeEulerCompressedAdjointRenewal lambda p ∘L
      newSuffixFrame lambda S

/-! ## Exact synchronized normal form -/

theorem oldFrameAdjoint_comp_radialSupport_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
        radialSupportProjection lambda =
      (suffixEulerFrameSchurStep lambda p S).oldFrame† := by
  let frame := (suffixEulerFrameSchurStep lambda p S).oldFrame
  have hframe : radialSupportProjection lambda ∘L frame = frame := by
    simpa only [frame, suffixEulerFrameSchurStep, oldSuffixFrame,
      newSuffixFrame] using
      (radialSupportProjection_comp_newSuffixFrame lambda (p :: S))
  have hprojectionAdjoint : (radialSupportProjection lambda)† =
      radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hadjoint := congrArg ContinuousLinearMap.adjoint hframe
  simpa only [frame, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hprojectionAdjoint] using hadjoint

theorem oldFrameAdjoint_comp_compressedRenewal_comp_newFrame_eq_reverseAdjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
        primeEulerCompressedAdjointRenewal lambda p ∘L
          newSuffixFrame lambda S =
      (suffixEulerFrameReverseTransition lambda p S)† := by
  have hold := oldFrameAdjoint_comp_radialSupport_eq_self lambda p S
  have hnew := radialSupportProjection_comp_newSuffixFrame lambda S
  have hinverse :
      (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
          (normalizedPrimeEulerInverse p)† ∘L
            newSuffixFrame lambda S =
        (suffixEulerFrameReverseTransition lambda p S)† := by
    simpa only [suffixEulerFrameSchurStep] using
      (oldFrameAdjoint_comp_inverseAdjoint_comp_newFrame_eq_reverseAdjoint
        lambda p S)
  apply ContinuousLinearMap.ext
  intro x
  have holdPoint := DFunLike.congr_fun hold
    (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
      (radialSupportProjection lambda (newSuffixFrame lambda S x)))
  have hnewPoint := DFunLike.congr_fun hnew x
  have hinversePoint := DFunLike.congr_fun hinverse x
  simp only [primeEulerCompressedAdjointRenewal,
    ContinuousLinearMap.comp_apply] at holdPoint hnewPoint hinversePoint ⊢
  rw [holdPoint, hnewPoint]
  exact hinversePoint

theorem signedCompressedInteriorOwner_eq_regroupedGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      (coframeBoundaryMomentGap owner lambda p S ∘L
        frameOldFrameAdjoint lambda p S) ∘L
          primeEulerCompressedAdjointRenewal lambda p ∘L
            newSuffixFrame lambda S := by
  have hrow :=
    suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint
      owner lambda p S
  have h := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator ∘L primeEulerCompressedAdjointRenewal lambda p ∘L
        newSuffixFrame lambda S) hrow
  simpa only [signedCompressedInteriorOwner] using h

theorem signedCompressedInteriorOwner_eq_gap_comp_reverseAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      coframeBoundaryMomentGap owner lambda p S ∘L
        (suffixEulerFrameReverseTransition lambda p S)† := by
  have hregroup :=
    signedCompressedInteriorOwner_eq_regroupedGap owner lambda p S
  have hcore :=
    oldFrameAdjoint_comp_compressedRenewal_comp_newFrame_eq_reverseAdjoint
      lambda p S
  have hcore' :
      frameOldFrameAdjoint lambda p S ∘L
          primeEulerCompressedAdjointRenewal lambda p ∘L
            newSuffixFrame lambda S =
        (suffixEulerFrameReverseTransition lambda p S)† := by
    simpa only [frameOldFrameAdjoint] using hcore
  have hsubstitute := congrArg
    (fun operator : SourceOp lambda =>
      coframeBoundaryMomentGap owner lambda p S ∘L operator) hcore'
  calc
    signedCompressedInteriorOwner owner lambda p S =
        (coframeBoundaryMomentGap owner lambda p S ∘L
          frameOldFrameAdjoint lambda p S) ∘L
            primeEulerCompressedAdjointRenewal lambda p ∘L
              newSuffixFrame lambda S := hregroup
    _ = coframeBoundaryMomentGap owner lambda p S ∘L
        (frameOldFrameAdjoint lambda p S ∘L
          primeEulerCompressedAdjointRenewal lambda p ∘L
            newSuffixFrame lambda S) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = coframeBoundaryMomentGap owner lambda p S ∘L
        (suffixEulerFrameReverseTransition lambda p S)† := hsubstitute

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
end CCM25Concrete
end Source
end ConnesWeilRH
