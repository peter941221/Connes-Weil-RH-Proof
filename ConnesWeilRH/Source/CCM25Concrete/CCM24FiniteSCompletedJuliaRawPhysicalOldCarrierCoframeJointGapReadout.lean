/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapExpansion

/-!
# Gap-facing producer contract for the old-carrier coframe row

The source calculation naturally produces the synchronized boundary-moment
gap

```text
G_(p,S) = Z_S T_(p,S)^dagger - T_(p,S)^dagger Z_(p::S),
```

while the old-carrier consumer names the same object after the old-frame
adjoint:

```text
signedTelescope_(p,S) = G_(p,S) oldFrame_(p,S)^dagger.
```

This module makes that equality part of the producer boundary.  A source
proof may therefore establish the factorization against `G` directly and
convert it to the existing joint-readout contract without unfolding the
four-term telescope again.

No readout, norm bound, spectral gap, or cancellation is constructed here.
The module only changes the exact target presented to the source producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaNonpolarGapDouglas
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "OldCarrierReadout" lambda =>
  suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
    sourceSoninCarrier lambda

/-! ## One-suffix exact target bridge -/

/-- A gap-facing source producer.  The factorization is stated against the
synchronized gap before the old-frame adjoint is absorbed into the target.
-/
structure SuffixRawOldCarrierCoframeJointGapReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : OldCarrierReadout lambda
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      coframeBoundaryMomentGap owner lambda p S ∘L
        frameOldFrameAdjoint lambda p S

/-- Convert the gap-facing target to the existing signed-telescope readout.
The conversion is an exact rewrite; it does not use a norm estimate. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointGapReadoutData.toJointReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S
      bound) :
    SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound :=
  { bound_nonneg := data.bound_nonneg
    readout := data.readout
    readout_norm_le := data.readout_norm_le
    factorization := by
      calc
        data.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
            coframeBoundaryMomentGap owner lambda p S ∘L
              frameOldFrameAdjoint lambda p S := data.factorization
        _ = suffixActualBandRawPhysicalOldCarrierSignedTelescope
              owner lambda p S :=
          (suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint
            owner lambda p S).symm }

/-- Recover the gap-facing form from the existing joint-readout contract.
This is the reverse exact rewrite, so both producer presentations have
identical numerical content. -/
noncomputable def jointReadoutData_toJointGapReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) :
    SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S bound :=
  { bound_nonneg := data.bound_nonneg
    readout := data.readout
    readout_norm_le := data.readout_norm_le
    factorization := by
      calc
        data.readout ∘L
              suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
            suffixActualBandRawPhysicalOldCarrierSignedTelescope
              owner lambda p S := data.factorization
        _ = coframeBoundaryMomentGap owner lambda p S ∘L
              frameOldFrameAdjoint lambda p S :=
          suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint
            owner lambda p S }

theorem exists_jointGapReadout_iff_exists_jointReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S bound) ↔
      Nonempty
        (SuffixRawOldCarrierCoframeJointReadoutData owner lambda p S bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toJointReadoutData⟩
  · rintro ⟨data⟩
    exact ⟨jointReadoutData_toJointGapReadoutData data⟩

/-! ## The scalar-normalized source-facing readback -/

/-
The following theorem is intentionally stated for the producer contract.  It
is the exact test a source proof can use while working on the synchronized
gap: after the scalar-normalized right inverse is inserted, the result is the
gap paired with the reverse transition.  In particular, the theorem does not
claim that the pullback vanishes.
-/
theorem SuffixRawOldCarrierCoframeJointGapReadoutData.scalarNormalizedPullback
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S
      bound) :
    data.readout ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
      (coframeBoundaryMomentGap owner lambda p S ∘L
          (suffixEulerFrameReverseTransition lambda p S)†) := by
  apply ContinuousLinearMap.ext
  intro x
  have hfactorPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      T (ContinuousLinearMap.adjoint (scalarNormalizedPrimeEulerInverse p)
        ((suffixEulerFrameSchurStep lambda p S).newFrame x))
    )
    data.factorization
  have hgapPoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      T (ContinuousLinearMap.adjoint (scalarNormalizedPrimeEulerInverse p)
        ((suffixEulerFrameSchurStep lambda p S).newFrame x))
    )
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint
      owner lambda p S).symm
  have hpullPoint := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda => T x)
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
      owner lambda p S)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hfactorPoint hgapPoint hpullPoint ⊢
  exact hfactorPoint.trans (hgapPoint.trans hpullPoint)

/-! ## Uniform producer handoff -/

/-- A family-uniform source producer for the synchronized gap.

The source calculation may keep the adjacent boundary-moment difference in
this gap-facing form for every visible prime and suffix.  The same readout
bound is required for the whole family; no per-suffix bound is silently
promoted here. -/
structure SuffixRawOldCarrierCoframeUniformJointGapReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S bound

/-- Convert the gap-facing family to the equivalent signed-telescope family.
The conversion is pointwise exact and preserves the numerical bound. -/
noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformJointReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapReadoutData
      owner lambda bound) :
    SuffixRawOldCarrierCoframeUniformJointReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      (data.readout p S).toJointReadoutData }

/-- The exact old-carrier domination handoff for a uniform gap producer.
The factor `2` is only the norm cost of projecting one joint readout onto its
two physical coordinates; it is not a source estimate. -/
noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformOldCarrierDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapReadoutData
      owner lambda bound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda
      (2 * bound)) :=
  (data.toUniformJointReadout).toUniformDomination

/-- Final Gate 3U handoff from the uniform synchronized-gap producer.

This theorem intentionally consumes, rather than proves, the source
readout.  It closes the integration path so the remaining source work is
exactly the construction of `data.readout`. -/
noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformGate3UHandoff
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapReadoutData
      owner lambda bound) :
    Nonempty (SuffixLocalNonpolarGapUniformDouglasData owner lambda
      (‖detectorOperator owner‖ + 2 * bound)) := by
  obtain ⟨oldData⟩ := data.toUniformOldCarrierDomination
  let rawData := coframeToUniformRawDomination oldData
  exact ⟨SuffixRawAmbientBoundaryUniformDominationData.toNonpolarGapDouglas
    rawData⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
end CCM25Concrete
end Source
end ConnesWeilRH
