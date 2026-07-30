/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor

/-!
# Physical cofactor owner for the antiresonant interior

This module places the expanded reverse-intertwining cofactor behind one
`.olean` boundary.  Downstream producer contracts consume only the named
owner and the two exact identities proved here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalCofactorOwner

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    finiteSCarrier

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-- Sandwich one source operator between the actual old frame and forward
transition.  This keeps later rewrites at the source-operator boundary. -/
noncomputable def suffixActualBandOldFrameTransitionSandwich
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (middle : SourceOp lambda) :
    SourceToFinite lambda :=
  (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L middle ∘L
    suffixEulerFrameTransition lambda p S

/-- The old response-facing cofactor. -/
noncomputable def suffixActualBandOldCarrierJointGapCofactorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  suffixActualBandOldFrameTransitionSandwich lambda p S
    (suffixActualBandLocalRawDefect owner lambda p S)

/-- The actual reverse-intertwining cofactor presented to the source
analysis. -/
noncomputable def suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  suffixActualBandOldFrameTransitionSandwich lambda p S
    (suffixEulerFrameTransition lambda p S ∘L
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)†)

/-- The physical cofactor is exactly the negative old response cofactor. -/
theorem suffixActualBandAntiresonantInteriorPhysicalCofactorResponse_eq_neg_jointGapCofactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S =
      -suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S := by
  rw [suffixActualBandAntiresonantInteriorPhysicalCofactorResponse,
    suffixActualBandOldCarrierJointGapCofactorResponse,
    transition_comp_completeBoundaryReverseIntertwiningDefectAdjoint_eq_neg_localRawDefect]
  unfold suffixActualBandOldFrameTransitionSandwich
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg]

/-- Reverse orientation of the preceding identity. -/
theorem suffixActualBandOldCarrierJointGapCofactorResponse_eq_neg_physical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S =
      -suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S := by
  rw [suffixActualBandAntiresonantInteriorPhysicalCofactorResponse_eq_neg_jointGapCofactor]
  simp

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalCofactorOwner
end CCM25Concrete
end Source
end ConnesWeilRH
