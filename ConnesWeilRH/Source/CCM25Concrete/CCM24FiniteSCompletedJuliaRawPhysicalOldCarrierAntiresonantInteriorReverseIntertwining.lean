/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRadialBracketComparison

/-!
# Reverse-intertwining normal form of the antiresonant interior owner

Proof 621 writes the surviving interior owner as one adjacent pair of complete
physical boundary responses.  The scalar cancellation

```text
Transition_(p,S)^dagger * Reverse_(p,S)^dagger = rho_p I
```

extracts a common left transition from that pair:

```text
Interior_(p,S)
  = Transition_(p,S)^dagger
      * (Reverse_(p,S)^dagger * BoundaryResponse_S
          - BoundaryResponse_(p::S) * Reverse_(p,S)^dagger).
```

The inner parenthesis is a single reverse-intertwining defect.  The corrected
radial bracket and suffix-dressing channels have the same factorization, and
their inner defects recombine before any estimate is taken.  This is an exact
normal form only; no uniform Bone 1 readout is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSAntiresonantInteriorRadialBracketComparison
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## Generic extraction and recombination -/

/-- A scalar inverse pair extracts the common left transition from an
adjacent response. -/
theorem adjacentResponse_eq_transition_comp_dressedDifference
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (oldResponse newResponse transition reverse : H →L[ℂ] H)
    (rho : ℂ)
    (hpair : transition ∘L reverse =
      rho • ContinuousLinearMap.id ℂ H) :
    rho • oldResponse - transition ∘L newResponse ∘L reverse =
      transition ∘L
        (reverse ∘L oldResponse - newResponse ∘L reverse) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpairPoint := DFunLike.congr_fun hpair (oldResponse x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    at hpairPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub]
  rw [hpairPoint]

/-- Subtracting a fixed base response commutes with forming the complete
reverse-intertwining defect. -/
theorem dressedDifference_eq_base_add_residual
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (oldResponse newResponse base reverse : H →L[ℂ] H) :
    reverse ∘L oldResponse - newResponse ∘L reverse =
      (reverse ∘L base - base ∘L reverse) +
        (reverse ∘L (oldResponse - base) -
          (newResponse - base) ∘L reverse) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_sub]
  abel

/-! ## The three exact reverse-intertwining owners -/

/-- Reverse-intertwining defect of the fixed corrected radial bracket. -/
noncomputable def primeEulerCorrectedBracketReverseIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixEulerFrameReverseTransition lambda p S)† ∘L
      primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p -
    primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p ∘L
      (suffixEulerFrameReverseTransition lambda p S)†

/-- Reverse-intertwining defect of the two adjacent suffix-dressing
residuals. -/
noncomputable def suffixActualBandCorrectedBracketDressingReverseIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixEulerFrameReverseTransition lambda p S)† ∘L
      suffixActualBandCorrectedBracketDressingResidual owner lambda p S -
    suffixActualBandCorrectedBracketDressingResidual
        owner lambda p (p :: S) ∘L
      (suffixEulerFrameReverseTransition lambda p S)†

/-- The complete physical reverse-intertwining defect.  Both adjacent
endpoint/forward coframes remain inside this one signed owner. -/
noncomputable def suffixActualBandCompleteBoundaryReverseIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixEulerFrameReverseTransition lambda p S)† ∘L
      suffixActualBandCompleteBoundaryResponse owner lambda S -
    suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
      (suffixEulerFrameReverseTransition lambda p S)†

/-! ## Channel factorizations -/

/-- The corrected bracket covariance defect has the common transition on the
left. -/
theorem primeEulerCorrectedBracketTransitionCovarianceDefect_eq_transitionAdjoint_comp_reverseIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    primeEulerCorrectedBracketTransitionCovarianceDefect owner lambda p S =
      (suffixEulerFrameTransition lambda p S)† ∘L
        primeEulerCorrectedBracketReverseIntertwiningDefect
          owner lambda p S := by
  simpa only [primeEulerCorrectedBracketTransitionCovarianceDefect,
    primeEulerCorrectedBracketReverseIntertwiningDefect] using
    (adjacentResponse_eq_transition_comp_dressedDifference
      (primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p)
      (primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p)
      ((suffixEulerFrameTransition lambda p S)†)
      ((suffixEulerFrameReverseTransition lambda p S)†)
      (primeSchurMarkovScalar p : ℂ)
      (suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
        lambda p S))

/-- The adjacent dressing defect has the same common transition on the left.
-/
theorem suffixActualBandCorrectedBracketDressingAdjacentDefect_eq_transitionAdjoint_comp_reverseIntertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCorrectedBracketDressingAdjacentDefect owner lambda p S =
      (suffixEulerFrameTransition lambda p S)† ∘L
        suffixActualBandCorrectedBracketDressingReverseIntertwiningDefect
          owner lambda p S := by
  simpa only [suffixActualBandCorrectedBracketDressingAdjacentDefect,
    suffixActualBandCorrectedBracketDressingReverseIntertwiningDefect] using
    (adjacentResponse_eq_transition_comp_dressedDifference
      (suffixActualBandCorrectedBracketDressingResidual owner lambda p S)
      (suffixActualBandCorrectedBracketDressingResidual
        owner lambda p (p :: S))
      ((suffixEulerFrameTransition lambda p S)†)
      ((suffixEulerFrameReverseTransition lambda p S)†)
      (primeSchurMarkovScalar p : ℂ)
      (suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
        lambda p S))

/-- The complete inner defect is the signed sum of the two provenance
channels.  This theorem is for bookkeeping; estimates must retain the sum. -/
theorem suffixActualBandCompleteBoundaryReverseIntertwiningDefect_eq_correctedBracket_add_dressing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S =
      primeEulerCorrectedBracketReverseIntertwiningDefect owner lambda p S +
        suffixActualBandCorrectedBracketDressingReverseIntertwiningDefect
          owner lambda p S := by
  simpa only [suffixActualBandCompleteBoundaryReverseIntertwiningDefect,
    primeEulerCorrectedBracketReverseIntertwiningDefect,
    suffixActualBandCorrectedBracketDressingReverseIntertwiningDefect,
    suffixActualBandCorrectedBracketDressingResidual] using
    (dressedDifference_eq_base_add_residual
      (suffixActualBandCompleteBoundaryResponse owner lambda S)
      (suffixActualBandCompleteBoundaryResponse owner lambda (p :: S))
      (primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p)
      ((suffixEulerFrameReverseTransition lambda p S)†))

/-! ## Complete owner -/

/-- The actual antiresonant interior is one transition followed by the
complete reverse-intertwining defect. -/
theorem signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      (suffixEulerFrameTransition lambda p S)† ∘L
        suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S := by
  rw [signedCompressedInteriorOwner_eq_adjacentCompleteBoundaryResponses]
  simpa only [suffixActualBandCompleteBoundaryReverseIntertwiningDefect] using
    (adjacentResponse_eq_transition_comp_dressedDifference
      (suffixActualBandCompleteBoundaryResponse owner lambda S)
      (suffixActualBandCompleteBoundaryResponse owner lambda (p :: S))
      ((suffixEulerFrameTransition lambda p S)†)
      ((suffixEulerFrameReverseTransition lambda p S)†)
      (primeSchurMarkovScalar p : ℂ)
      (suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
        lambda p S))

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
end CCM25Concrete
end Source
end ConnesWeilRH
