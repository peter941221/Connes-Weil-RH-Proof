/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization

/-!
# Ambient physical form of the antiresonant interior factor

The actual Schur owner stores

```text
transport * newFrame = oldFrame * Transition.
```

Applying this identity before the reverse-intertwining cofactor replaces the
last old-frame bookkeeping prefix by the genuine normalized Euler transport
on the new-frame range.  No factor or estimate changes.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalCofactorOwner
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    finiteSCarrier

/-- The complete cofactor on the genuine ambient transport/new-frame
carrier. -/
noncomputable def
    suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  ((suffixEulerFrameSchurStep lambda p S).transport ∘L
      (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
    ((suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)† ∘L
      suffixEulerFrameTransition lambda p S)

/-- The ambient and old-frame presentations are the same operator. -/
theorem suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse_eq_physical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse
        owner lambda p S =
      suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  have htransport := DFunLike.congr_fun
    (suffixEulerFrameSchurStep lambda p S).transport_intertwining
    (((suffixActualBandCompleteBoundaryReverseIntertwiningDefect
      owner lambda p S)†) (suffixEulerFrameTransition lambda p S x))
  simp only [suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse,
    suffixActualBandAntiresonantInteriorPhysicalCofactorResponse,
    suffixActualBandOldFrameTransitionSandwich,
    ContinuousLinearMap.comp_apply] at htransport ⊢
  exact htransport

/-- The physical Bone 1 factorization on the actual ambient carrier. -/
theorem SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.ambient_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound) :
    suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse
        owner lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor) := by
  calc
    suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse
        owner lambda p S =
      suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S :=
      suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse_eq_physical
        owner lambda p S
    _ = (primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor) := data.physical_factorization

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
