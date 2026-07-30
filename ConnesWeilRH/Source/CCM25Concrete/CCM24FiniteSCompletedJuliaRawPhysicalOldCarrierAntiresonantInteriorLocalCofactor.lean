/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining

/-!
# Local-cofactor ledger for the antiresonant interior owner

The reverse-intertwining owner from Proof 622 is closely related to the
existing local raw defect, but noncommutativity fixes a different order:

```text
Interior^dagger = Reverse * rawIntertwiningDefect,
localRawDefect  = -rawIntertwiningDefect * Reverse.
```

Thus the two objects differ by a commutator, not by a sign.  The exact bridge
is instead the two-sided cofactor identity

```text
Transition^dagger * localRawDefect^dagger * Reverse^dagger
  = -rho_p * Interior.
```

This module records both facts before any estimate is taken.  It transfers
fixed-object algebra only; it does not construct the family-uniform
old-carrier Douglas readout required by Bone 1.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawLocalCofactor
open CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## Raw-row orientation -/

/-- The interior owner is the physical four-term row followed on the right by
the adjoint reverse transition. -/
theorem signedCompressedInteriorOwner_eq_rawPhysicalFourTermRow_comp_reverseAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S ∘L
        (suffixEulerFrameReverseTransition lambda p S)† := by
  rw [signedCompressedInteriorOwner_eq_gap_comp_reverseAdjoint,
    coframeBoundaryMomentGap_eq_rawPhysicalFourTermRow]

/-- After taking adjoints, the reverse transition is on the left of the raw
intertwining defect. -/
theorem signedCompressedInteriorOwner_adjoint_eq_reverse_comp_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (signedCompressedInteriorOwner owner lambda p S)† =
      suffixEulerFrameReverseTransition lambda p S ∘L
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S := by
  rw [signedCompressedInteriorOwner_eq_rawPhysicalFourTermRow_comp_reverseAdjoint,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    suffixActualBandRawPhysicalFourTermRow_adjoint_eq_rawIntertwiningDefect]

/-! ## Exact comparison with the local raw defect -/

/-- Moving an adjacent reverse-intertwining defect past its paired forward
transition preserves the complete signed difference. -/
theorem reverseDressedDifference_comp_transition_eq_reverse_comp_forwardDifference
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (oldResponse newResponse transition reverse : H →L[ℂ] H)
    (rho : ℂ)
    (hpair : reverse ∘L transition =
      rho • ContinuousLinearMap.id ℂ H) :
    (reverse ∘L oldResponse - newResponse ∘L reverse) ∘L transition =
      reverse ∘L
        (oldResponse ∘L transition - transition ∘L newResponse) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpairPoint := DFunLike.congr_fun hpair x
  have hpairNewPoint := DFunLike.congr_fun hpair (newResponse x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    at hpairPoint hpairNewPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hpairPoint, map_smul, hpairNewPoint]

set_option maxHeartbeats 4000000 in
-- The adjacent physical responses and the local cofactor elaborate together.
/-- The new reverse-intertwining defect becomes the negative adjoint local
raw defect only after the forward transition is composed on the right. -/
theorem completeBoundaryReverseIntertwiningDefect_comp_transitionAdjoint_eq_neg_localRawDefectAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S ∘L
        (suffixEulerFrameTransition lambda p S)† =
      -(suffixActualBandLocalRawDefect owner lambda p S)† := by
  have hpair :=
    suffixEulerFrameReverseTransitionAdjoint_comp_transitionAdjoint_eq_scalar
      lambda p S
  have hS :=
    suffixActualBandRawCoframeBoundaryMoment_eq_completeBoundaryResponse
      owner lambda S
  have hpS :=
    suffixActualBandRawCoframeBoundaryMoment_eq_completeBoundaryResponse
      owner lambda (p :: S)
  have hgap :
      suffixActualBandCompleteBoundaryResponse owner lambda S ∘L
            (suffixEulerFrameTransition lambda p S)† -
          (suffixEulerFrameTransition lambda p S)† ∘L
            suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) =
        coframeBoundaryMomentGap owner lambda p S := by
    unfold coframeBoundaryMomentGap
    simp only [frameTransitionAdjoint]
    rw [hS, hpS]
  have hlocal :=
    suffixActualBandLocalRawDefect_adjoint_eq_neg_reverse_adjoint_comp_rawPhysicalRow
      owner lambda p S
  calc
    suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S ∘L
        (suffixEulerFrameTransition lambda p S)† =
      (suffixEulerFrameReverseTransition lambda p S)† ∘L
        (suffixActualBandCompleteBoundaryResponse owner lambda S ∘L
              (suffixEulerFrameTransition lambda p S)† -
          (suffixEulerFrameTransition lambda p S)† ∘L
              suffixActualBandCompleteBoundaryResponse
                owner lambda (p :: S)) := by
      simpa only [suffixActualBandCompleteBoundaryReverseIntertwiningDefect]
        using
          (reverseDressedDifference_comp_transition_eq_reverse_comp_forwardDifference
            (suffixActualBandCompleteBoundaryResponse owner lambda S)
            (suffixActualBandCompleteBoundaryResponse owner lambda (p :: S))
            ((suffixEulerFrameTransition lambda p S)†)
            ((suffixEulerFrameReverseTransition lambda p S)†)
            (primeSchurMarkovScalar p : ℂ) hpair)
    _ = (suffixEulerFrameReverseTransition lambda p S)† ∘L
          coframeBoundaryMomentGap owner lambda p S := by rw [hgap]
    _ = -(suffixActualBandLocalRawDefect owner lambda p S)† := by
      rw [coframeBoundaryMomentGap_eq_rawPhysicalFourTermRow, hlocal]
      simp

/-- Adjointing the preceding cofactor puts the actual forward transition on
the left of the reverse-intertwining adjoint. -/
theorem transition_comp_completeBoundaryReverseIntertwiningDefectAdjoint_eq_neg_localRawDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameTransition lambda p S ∘L
        (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S)† =
      -suffixActualBandLocalRawDefect owner lambda p S := by
  have h := congrArg ContinuousLinearMap.adjoint
    (completeBoundaryReverseIntertwiningDefect_comp_transitionAdjoint_eq_neg_localRawDefectAdjoint
      owner lambda p S)
  have hneg (operator : SourceOp lambda) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hneg,
    ContinuousLinearMap.adjoint_adjoint] at h
  exact h

/-- The interior adjoint and the local raw defect differ by the exact reverse
commutator.  In particular, they must not be identified by swapping factors.
-/
theorem signedCompressedInteriorOwner_adjoint_add_localRawDefect_eq_reverse_commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (signedCompressedInteriorOwner owner lambda p S)† +
        suffixActualBandLocalRawDefect owner lambda p S =
      suffixEulerFrameReverseTransition lambda p S ∘L
          suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S -
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S ∘L
          suffixEulerFrameReverseTransition lambda p S := by
  rw [signedCompressedInteriorOwner_adjoint_eq_reverse_comp_rawIntertwiningDefect,
    suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  abel

/-! ## Two-sided cofactor -/

/-- In inverse-free form, the old local raw defect and the new interior owner
are the same object up to the genuine two-sided Schur cofactor. -/
theorem transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint_eq_neg_scalar_interior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameTransition lambda p S)† ∘L
        (suffixActualBandLocalRawDefect owner lambda p S)† ∘L
          (suffixEulerFrameReverseTransition lambda p S)† =
      -((primeSchurMarkovScalar p : ℂ) •
        signedCompressedInteriorOwner owner lambda p S) := by
  have hpair :=
    suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
      lambda p S
  have hlocal :=
    suffixActualBandLocalRawDefect_adjoint_eq_neg_reverse_adjoint_comp_rawPhysicalRow
      owner lambda p S
  have hrow :=
    signedCompressedInteriorOwner_eq_rawPhysicalFourTermRow_comp_reverseAdjoint
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpairPoint := DFunLike.congr_fun hpair
    (suffixActualBandRawPhysicalFourTermRow owner lambda p S
      (((suffixEulerFrameReverseTransition lambda p S)†) x))
  have hlocalPoint := DFunLike.congr_fun hlocal
    (((suffixEulerFrameReverseTransition lambda p S)†) x)
  have hrowPoint := DFunLike.congr_fun hrow x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply]
    at hpairPoint hlocalPoint hrowPoint ⊢
  rw [hlocalPoint, map_neg, hpairPoint, hrowPoint]

/-- Scalar-normalized form of the two-sided cofactor.  The only numerical
cost introduced here is `rho_p^-1`; no source readout is constructed. -/
theorem signedCompressedInteriorOwner_eq_neg_scalarInv_smul_transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        ((suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalRawDefect owner lambda p S)† ∘L
            (suffixEulerFrameReverseTransition lambda p S)†) := by
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hcofactor :=
    transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint_eq_neg_scalar_interior
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hcofactorPoint := DFunLike.congr_fun hcofactor x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply] at hcofactorPoint ⊢
  rw [hcofactorPoint]
  simp only [smul_neg, smul_smul]
  simp [hscalar]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
end CCM25Concrete
end Source
end ConnesWeilRH
