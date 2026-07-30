/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalCofactorOwner
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout

/-!
# Physical factor contract for the antiresonant interior owner

The existing Bone 1 response contract is stated with the local raw defect.
Proofs 622--623 replace that bookkeeping object by the complete physical
reverse-intertwining defect `K_(p,S)`.  The exact producer target becomes

```text
oldFrame * Transition * K_(p,S)^dagger * Transition
  = rho_p * oldCarrierAnalysis^dagger * factor.
```

This contract is equivalent, with the same bound, to both the old response
factor and the synchronized-gap readout.  The left physical carrier can also
be rewritten using
`transport * newFrame = oldFrame * Transition`.

The module changes the object presented to the source analysis; it does not
construct `factor` or prove a family-uniform bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalCofactorOwner
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Physical reverse-intertwining producer -/

/-- A source-to-physical factor for the complete reverse-intertwining owner.
The two actual transitions remain in the factorization; neither is inverted.
-/
structure SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    suffixEulerFrameAmbientBoundaryCarrier
  factor_norm_le : ‖factor‖ ≤ bound
  physical_factorization :
    suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          factor)

/-! ## Existing response factor -> physical factor -/

/-- The old response factor is already a factor for the actual physical
reverse-intertwining owner.  No norm cost is introduced. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toInteriorPhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData owner lambda p S
      bound := by
  refine
    { bound_nonneg := data.bound_nonneg
      factor := data.factor
      factor_norm_le := data.factor_norm_le
      physical_factorization := ?_ }
  have hresponse :
      suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S =
        -((primeSchurMarkovScalar p : ℂ) •
          ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
            data.factor)) := by
    simpa only [suffixActualBandOldCarrierJointGapCofactorResponse] using
      data.response_factorization
  calc
    suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S =
      -suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S :=
        suffixActualBandAntiresonantInteriorPhysicalCofactorResponse_eq_neg_jointGapCofactor
          owner lambda p S
    _ = -(-((primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor))) := by rw [hresponse]
    _ = (primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor) := by simp

/-! ## Physical factor -> existing response factor -/

/-- Conversely, the physical reverse-intertwining factor recovers the old
response-facing producer with the same factor and bound. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toResponseReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound) :
    SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner lambda p S
      bound := by
  refine
    { bound_nonneg := data.bound_nonneg
      factor := data.factor
      factor_norm_le := data.factor_norm_le
      response_factorization := ?_ }
  change suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S = _
  calc
    suffixActualBandOldCarrierJointGapCofactorResponse owner lambda p S =
      -suffixActualBandAntiresonantInteriorPhysicalCofactorResponse
        owner lambda p S :=
        suffixActualBandOldCarrierJointGapCofactorResponse_eq_neg_physical
          owner lambda p S
    _ = -((primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor)) := by rw [data.physical_factorization]

/-! ## Exact equivalences -/

theorem exists_interiorPhysicalFactor_iff_exists_responseReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    Nonempty (SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
        owner lambda p S bound) ↔
      Nonempty (SuffixRawOldCarrierCoframeJointGapResponseReadoutData
        owner lambda p S bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toResponseReadoutData⟩
  · rintro ⟨data⟩
    exact
      ⟨SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toInteriorPhysicalFactorData
        data⟩

theorem exists_interiorPhysicalFactor_iff_exists_jointGapReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    Nonempty (SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
        owner lambda p S bound) ↔
      Nonempty (SuffixRawOldCarrierCoframeJointGapReadoutData
        owner lambda p S bound) := by
  rw [exists_interiorPhysicalFactor_iff_exists_responseReadout,
    exists_jointGapResponseReadout_iff_exists_jointGapReadout]

/-! ## Family-uniform handoff -/

structure SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData.toUniformResponseReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
      owner lambda bound) :
    SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData owner lambda
      bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toResponseReadoutData
        (data.factor p S) }

noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformInteriorPhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData
      owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData owner
      lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toInteriorPhysicalFactorData
        (data.factor p S) }

theorem exists_uniformInteriorPhysicalFactor_iff_exists_uniformJointGapReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
          owner lambda bound) ↔
      Nonempty
        (SuffixRawOldCarrierCoframeUniformJointGapReadoutData owner lambda
          bound) := by
  constructor
  · rintro ⟨data⟩
    let responseData :=
      SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData.toUniformResponseReadoutData
        data
    exact ⟨CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout.SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformGapReadoutData
      responseData⟩
  · rintro ⟨data⟩
    let responseData :=
      CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout.SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformResponseReadoutData
        data
    exact ⟨SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformInteriorPhysicalFactorData
      responseData⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
