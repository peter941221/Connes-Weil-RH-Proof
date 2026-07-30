/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse

/-!
# Corrected radial bracket comparison for the actual interior owner

The corrected radial quotient bracket lives on the global finite-S carrier
and has no suffix parameter.  The actual Proof 619 interior owner lives on the
source Sonin carrier and contains two suffix-dependent boundary responses.
This module compares them only after the canonical source compression.

The exact difference splits into two signed channels:

```text
Interior_(p,S)
  = [rho_p Q_p - T_(p,S)^dagger Q_p Reverse_(p,S)^dagger]
    + [rho_p Delta_(p,S)
       - T_(p,S)^dagger Delta_(p,p::S) Reverse_(p,S)^dagger],

Delta_(p,S) = BoundaryResponse_S - Q_p.
```

The first bracket is a transition-covariance defect.  The second is the
suffix coframe-dressing residual.  Neither is asserted to vanish or to have a
uniform bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSAntiresonantInteriorRadialBracketComparison

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutator
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## Canonical source compression -/

/-- The canonical source compression used here to compare the global
corrected quotient bracket with a source-side response. -/
noncomputable def primeEulerSourceCompressedCorrectedQuotientBracket
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) : SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
    primeEulerRadialCorrectedQuotientBracket owner lambda p ∘L
      sourceInclusion lambda

/-- Source compression preserves the exact physical expansion of the radial
corrected quotient bracket. -/
theorem primeEulerSourceCompressedCorrectedQuotientBracket_eq_physical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p =
      (sourceInclusion lambda)† ∘L
        primeEulerRadialCorrectedPhysicalBracket owner lambda p ∘L
          sourceInclusion lambda := by
  unfold primeEulerSourceCompressedCorrectedQuotientBracket
  rw [primeEulerRadialCorrectedQuotientBracket_eq_physical]

/-! ## Exact two-channel difference -/

/-- What remains after subtracting the canonical source compression from one
actual suffix boundary response.  This retains all endpoint and forward
coframe dressing. -/
noncomputable def suffixActualBandCorrectedBracketDressingResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandCompleteBoundaryResponse owner lambda S -
    primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p

/-- The fixed corrected bracket need not be covariant under the actual Schur
transition.  This definition names that exact failure. -/
noncomputable def primeEulerCorrectedBracketTransitionCovarianceDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p -
    (suffixEulerFrameTransition lambda p S)† ∘L
      primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p ∘L
        (suffixEulerFrameReverseTransition lambda p S)†

/-- The adjacent difference of the two suffix-dependent dressing residuals. -/
noncomputable def suffixActualBandCorrectedBracketDressingAdjacentDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandCorrectedBracketDressingResidual owner lambda p S -
    (suffixEulerFrameTransition lambda p S)† ∘L
      suffixActualBandCorrectedBracketDressingResidual
        owner lambda p (p :: S) ∘L
        (suffixEulerFrameReverseTransition lambda p S)†

/-- Carrier-independent algebra behind the two-channel comparison. -/
theorem adjacentResponse_eq_covariance_add_dressing
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (oldResponse newResponse base transition reverse : H →L[ℂ] H)
    (rho : ℂ) :
    rho • oldResponse - transition ∘L newResponse ∘L reverse =
      (rho • base - transition ∘L base ∘L reverse) +
        (rho • (oldResponse - base) -
          transition ∘L (newResponse - base) ∘L reverse) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_sub,
    smul_sub]
  abel

/-- The genuine interior owner is exactly the sum of the corrected bracket's
transition-covariance defect and the adjacent coframe-dressing residual. -/
theorem signedCompressedInteriorOwner_eq_correctedBracketCovariance_add_dressing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      primeEulerCorrectedBracketTransitionCovarianceDefect
          owner lambda p S +
        suffixActualBandCorrectedBracketDressingAdjacentDefect
          owner lambda p S := by
  calc
    signedCompressedInteriorOwner owner lambda p S =
        (primeSchurMarkovScalar p : ℂ) •
            suffixActualBandCompleteBoundaryResponse owner lambda S -
          (suffixEulerFrameTransition lambda p S)† ∘L
            suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
              (suffixEulerFrameReverseTransition lambda p S)† :=
      signedCompressedInteriorOwner_eq_adjacentCompleteBoundaryResponses
        owner lambda p S
    _ = primeEulerCorrectedBracketTransitionCovarianceDefect
          owner lambda p S +
        suffixActualBandCorrectedBracketDressingAdjacentDefect
          owner lambda p S := by
      simpa only [primeEulerCorrectedBracketTransitionCovarianceDefect,
        suffixActualBandCorrectedBracketDressingAdjacentDefect,
        suffixActualBandCorrectedBracketDressingResidual] using
        (adjacentResponse_eq_covariance_add_dressing
          (suffixActualBandCompleteBoundaryResponse owner lambda S)
          (suffixActualBandCompleteBoundaryResponse owner lambda (p :: S))
          (primeEulerSourceCompressedCorrectedQuotientBracket owner lambda p)
          ((suffixEulerFrameTransition lambda p S)†)
          ((suffixEulerFrameReverseTransition lambda p S)†)
          (primeSchurMarkovScalar p : ℂ))

end CCM24FiniteSAntiresonantInteriorRadialBracketComparison
end CCM25Concrete
end Source
end ConnesWeilRH
