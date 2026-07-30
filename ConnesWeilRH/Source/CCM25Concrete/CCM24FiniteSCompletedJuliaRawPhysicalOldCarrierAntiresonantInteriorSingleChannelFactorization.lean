/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelPacking
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard

/-!
# Single-channel form of the antiresonant physical factor

The Proof 625 physical factor has two packed coordinates.  This module
isolates the equivalent source-side channel

```text
K_(p,S)^dagger * Transition_(p,S)
  = newFrame_S^dagger * N_p * L_p * H_(p,S).
```

Here `N_p` is the normalized Euler inverse and `L_p` is the ambient loss
factor.  Their order is part of the statement.  The corresponding signed
relative energy inequality produces `H_(p,S)` by the Douglas lemma.  An
explicit packing then recovers the Proof 625 factor with norm cost at most
`17`, uniformly in `p` and `S`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSDouglasFactor
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
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

/-! ## The renewed single channel -/

/-- The source-facing denominator `L_p^dagger N_p^dagger newFrame_S`. -/
noncomputable def suffixEulerFrameRenewedAntiresonantColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (primeEulerAmbientLossFactor p)† ∘L
    (normalizedPrimeEulerInverse p)† ∘L
      (suffixEulerFrameSchurStep lambda p S).newFrame

theorem suffixEulerFrameRenewedAntiresonantColumn_adjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameRenewedAntiresonantColumn lambda p S)† =
      (suffixEulerFrameSchurStep lambda p S).newFrame† ∘L
        normalizedPrimeEulerInverse p ∘L
          primeEulerAmbientLossFactor p := by
  simp only [suffixEulerFrameRenewedAntiresonantColumn,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

/-- A bounded factor through the renewed ambient channel. -/
structure SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : Real) where
  bound_nonneg : 0 <= bound
  factor : SourceToFinite lambda
  factor_norm_le : ‖factor‖ <= bound
  factorization :
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
      (suffixEulerFrameSchurStep lambda p S).newFrame† ∘L
        normalizedPrimeEulerInverse p ∘L
          primeEulerAmbientLossFactor p ∘L factor

/-- The adjoint readout form used directly by the Douglas lemma. -/
structure SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : Real) where
  bound_nonneg : 0 <= bound
  readout : finiteSCarrier →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ <= bound
  factorization :
    readout ∘L suffixEulerFrameRenewedAntiresonantColumn lambda p S =
      signedCompressedInteriorOwner owner lambda p S

/-- The exact relative-energy statement left for source analysis. -/
def SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : Real) : Prop :=
  0 <= bound ∧ forall x :
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda,
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 <=
      bound ^ 2 * ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2

/-! ## Adjoint equivalence and Douglas construction -/

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData.toSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : Real}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
        owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound := by
  refine
    { bound_nonneg := data.bound_nonneg
      factor := data.readout†
      factor_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖data.readout†‖ = ‖data.readout‖ :=
        ContinuousLinearMap.adjoint.norm_map data.readout
      _ <= bound := data.readout_norm_le
  · have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
    rw [
      signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect]
      at hadjoint
    simpa only [suffixEulerFrameRenewedAntiresonantColumn_adjoint,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadjoint.symm

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData.toRenewedAmbientReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : Real}
    (data : SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
      owner lambda p S bound := by
  refine
    { bound_nonneg := data.bound_nonneg
      readout := data.factor†
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖data.factor†‖ = ‖data.factor‖ :=
        ContinuousLinearMap.adjoint.norm_map data.factor
      _ <= bound := data.factor_norm_le
  · have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
    rw [
      signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect]
    simpa only [suffixEulerFrameRenewedAntiresonantColumn,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadjoint.symm

theorem exists_singleChannelFactor_iff_exists_renewedAmbientReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : Real) :
    Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
          owner lambda p S bound) <->
      Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
          owner lambda p S bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toRenewedAmbientReadoutData⟩
  · rintro ⟨data⟩
    exact ⟨data.toSingleChannelFactorData⟩

noncomputable def renewedAmbientReadoutDataOfDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : Real}
    (hdom : SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientDomination
      owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
      owner lambda p S bound := by
  let factorWitness :=
    exists_factor_of_norm_sq_le
      (signedCompressedInteriorOwner owner lambda p S)
      (suffixEulerFrameRenewedAntiresonantColumn lambda p S)
      bound hdom.1 hdom.2
  let readout := Classical.choose factorWitness
  have readoutSpec := Classical.choose_spec factorWitness
  exact
    { bound_nonneg := hdom.1
      readout := readout
      readout_norm_le := readoutSpec.1
      factorization := readoutSpec.2 }

theorem renewedAmbientDomination_of_readoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : Real}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
        owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientDomination
      owner lambda p S bound := by
  refine ⟨data.bound_nonneg, ?_⟩
  intro x
  have hpoint := DFunLike.congr_fun data.factorization x
  have hnorm :
      ‖signedCompressedInteriorOwner owner lambda p S x‖ <=
        bound * ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ := by
    rw [← hpoint]
    calc
      ‖data.readout
          (suffixEulerFrameRenewedAntiresonantColumn lambda p S x)‖ <=
          ‖data.readout‖ *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ :=
        data.readout.le_opNorm _
      _ <= bound *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ :=
        mul_le_mul_of_nonneg_right data.readout_norm_le (norm_nonneg _)
  calc
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 <=
        (bound *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg data.bound_nonneg (norm_nonneg _))).mpr hnorm
    _ = bound ^ 2 *
        ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2 := by
      ring

theorem exists_renewedAmbientReadout_iff_domination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : Real) :
    Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientReadoutData
          owner lambda p S bound) <->
      SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientDomination
        owner lambda p S bound := by
  constructor
  · rintro ⟨data⟩
    exact renewedAmbientDomination_of_readoutData data
  · intro hdom
    exact ⟨renewedAmbientReadoutDataOfDomination hdom⟩

/-! ## Canonical packing into the Proof 625 carrier -/

/- The packed factor and its `17`-cost norm ledger live in the imported
`SingleChannelPacking` module so this source proof consumes them opaquely. -/

private theorem normalizedPrimeEulerInverseAdjoint_comp_transportAdjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerInverse p)† ∘L
        (normalizedPrimeEulerFrameTransport p)† =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  have hscalarAdjoint :
      ContinuousLinearMap.adjoint
          ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ finiteSCarrier) =
        (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ finiteSCarrier := by
    have hstar : star (primeSchurMarkovScalar p : ℂ) =
        (primeSchurMarkovScalar p : ℂ) := by
      rw [RCLike.star_def, Complex.conj_ofReal]
    simpa only [map_smulₛₗ, hstar, starRingEnd_apply,
      ContinuousLinearMap.adjoint_id] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ
        (primeSchurMarkovScalar p : ℂ)
        (ContinuousLinearMap.id ℂ finiteSCarrier))
  have hadjoint := congrArg ContinuousLinearMap.adjoint
    (normalizedPrimeEulerFrameTransport_comp_inverse p)
  simpa only [ContinuousLinearMap.adjoint_comp, hscalarAdjoint] using hadjoint

/-- The canonical packed readout reconstructs the adjoint physical cofactor. -/
theorem canonicalPackedPhysicalReadout_comp_oldCarrierAnalysis
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (H : SourceToFinite lambda)
    (hfactor :
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
        (suffixEulerFrameSchurStep lambda p S).newFrame† ∘L
          normalizedPrimeEulerInverse p ∘L
            primeEulerAmbientLossFactor p ∘L H) :
    (primeSchurMarkovScalar p : ℂ) •
        (canonicalPackedPhysicalReadout p H ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) =
      (suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse
        owner lambda p S)† := by
  rw [canonicalPackedPhysicalReadout,
    suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis]
  apply ContinuousLinearMap.ext
  intro x
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hpairPoint := DFunLike.congr_fun
    (normalizedPrimeEulerInverseAdjoint_comp_transportAdjoint p) x
  have htransport :
      (suffixEulerFrameSchurStep lambda p S).transport =
        normalizedPrimeEulerFrameTransport p := by
    rfl
  have hfactorAdjoint := congrArg ContinuousLinearMap.adjoint hfactor
  have hfactorPoint := DFunLike.congr_fun hfactorAdjoint
    (((suffixEulerFrameSchurStep lambda p S).newFrame†)
      (((normalizedPrimeEulerFrameTransport p)†) x))
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply] at hfactorPoint
  simp only [suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse,
    canonicalPackedPhysicalBoundaryRow,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    map_sub] at hpairPoint ⊢
  simp only [htransport]
  rw [hfactorPoint, hpairPoint]
  simp only [map_smul, smul_smul, inv_mul_cancel₀ hrho, one_smul]
  match_scalars <;> simp [hrho]

/-- One renewed single channel produces the Proof 625 physical factor with
uniform norm cost `17`. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData.toPhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S (17 * bound) := by
  refine
    { bound_nonneg := mul_nonneg (by norm_num) data.bound_nonneg
      factor := canonicalPackedPhysicalFactor p data.factor
      factor_norm_le := ?_
      physical_factorization := ?_ }
  · calc
      ‖canonicalPackedPhysicalFactor p data.factor‖ ≤ 17 * ‖data.factor‖ :=
        canonicalPackedPhysicalFactor_norm_le_seventeen p data.factor
      _ ≤ 17 * bound :=
        mul_le_mul_of_nonneg_left data.factor_norm_le (by norm_num)
  · letI : CompleteSpace
        (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
      (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe
    rw [←
      suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse_eq_physical]
    have hreadout := canonicalPackedPhysicalReadout_comp_oldCarrierAnalysis
      owner lambda p S data.factor data.factorization
    have hadjoint := congrArg ContinuousLinearMap.adjoint hreadout
    have hstar :
        star (primeSchurMarkovScalar p : ℂ) =
          (primeSchurMarkovScalar p : ℂ) := by
      rw [RCLike.star_def, Complex.conj_ofReal]
    have hscalarAdjoint :=
      ContinuousLinearMap.adjoint.map_smulₛₗ
        (primeSchurMarkovScalar p : ℂ)
        (canonicalPackedPhysicalReadout p data.factor ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
    rw [hscalarAdjoint] at hadjoint
    simpa only [canonicalPackedPhysicalFactor,
      starRingEnd_apply, hstar,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadjoint.symm

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
