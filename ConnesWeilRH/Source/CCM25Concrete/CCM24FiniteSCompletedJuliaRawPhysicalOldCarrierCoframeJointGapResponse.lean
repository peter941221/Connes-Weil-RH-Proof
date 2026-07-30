/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalCofactor

/-!
# Exact response identity for the old-carrier coframe gap

The synchronized boundary-moment gap is the adjoint-oriented raw physical row.
The existing local raw defect is the same complete quadratic response after the
one-prime Schur--Markov scalar and the reverse transition have been inserted.
This file puts those two descriptions on one exact ledger:

```text
L_(p,S) = rho_p * R_(p::S) - T_(p,S) * R_S * reverseT_(p,S)

G_(p,S)^dagger = -rho_p^(-1) * L_(p,S) * T_(p,S),
```

where `G` is the synchronized boundary-moment gap, `R` is the complete raw
quadratic response, and `T` is the forward Euler transition.  The scalar is
not silently dropped and the transition orientation is retained.

This is an exact response readback only.  It proves no family-uniform norm
bound, no source producer, and no Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The response named in the source obligation -/

/-- The complete one-step response before it is paired with the forward
transition.  This is written out instead of hiding it behind the older local
defect name so that the source-facing gap identity displays every orientation.
-/
noncomputable def suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S

/-- The displayed joint response is definitionally the existing local raw
defect.  Keeping this theorem named makes later source proofs use the response
ledger without unfolding its implementation. -/
theorem suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_eq_localRawDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
        owner lambda p S =
      suffixActualBandLocalRawDefect owner lambda p S := by
  rfl

/-! ## Gap-to-row identification -/

/-- The synchronized boundary-moment gap is exactly the raw physical row.  The
two boundary moments are already the adjoints of the complete raw responses;
the theorem only exposes that existing telescope in the gap-facing name.
-/
theorem coframeBoundaryMomentGap_eq_rawPhysicalFourTermRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeBoundaryMomentGap owner lambda p S =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
  symm
  simpa only [coframeBoundaryMomentGap, frameTransitionAdjoint] using
    (suffixActualBandRawPhysicalFourTermRow_eq_boundaryMoment_telescope
      owner lambda p S)

/-! ## Exact response identities -/

/-- The no-inverse version of the response readback.  This form is the safest
one for later algebra because it does not use nonzeroness of the scalar.
-/
theorem suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_comp_transition_eq_neg_scalar_gap_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
        owner lambda p S ∘L suffixEulerFrameTransition lambda p S =
      -((primeSchurMarkovScalar p : ℂ) •
        (coframeBoundaryMomentGap owner lambda p S)†) := by
  rw [suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_eq_localRawDefect,
    coframeBoundaryMomentGap_eq_rawPhysicalFourTermRow]
  exact suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawPhysicalRow_adjoint
    owner lambda p S

/-- The scalar-normalized adjoint readback of the synchronized gap.  The
orientation is the one required by the old-carrier source obligation:
the response is multiplied on the right by the forward transition.
-/
theorem coframeBoundaryMomentGap_adjoint_eq_neg_scalar_inv_smul_jointGapResponse_comp_transition
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (coframeBoundaryMomentGap owner lambda p S)† =
      (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        (suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
            owner lambda p S ∘L suffixEulerFrameTransition lambda p S) := by
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hcofactor :=
    suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_comp_transition_eq_neg_scalar_gap_adjoint
      owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hcofactorPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hcofactor
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply] at hcofactorPoint
  have hscalarPoint :
      ((coframeBoundaryMomentGap owner lambda p S)†) x =
        (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          (-((primeSchurMarkovScalar p : ℂ) •
            ((coframeBoundaryMomentGap owner lambda p S)†) x)) := by
    simp only [smul_neg, neg_smul, neg_neg]
    rw [smul_smul]
    simp [hscalar]
  calc
    ((coframeBoundaryMomentGap owner lambda p S)†) x =
        (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          (-((primeSchurMarkovScalar p : ℂ) •
            ((coframeBoundaryMomentGap owner lambda p S)†) x)) := hscalarPoint
    _ = (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        (suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
            owner lambda p S ∘L suffixEulerFrameTransition lambda p S) x := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [hcofactorPoint]
    _ = ((-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        (suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
            owner lambda p S ∘L suffixEulerFrameTransition lambda p S)) x := by
      simp only [ContinuousLinearMap.smul_apply]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse
end CCM25Concrete
end Source
end ConnesWeilRH
