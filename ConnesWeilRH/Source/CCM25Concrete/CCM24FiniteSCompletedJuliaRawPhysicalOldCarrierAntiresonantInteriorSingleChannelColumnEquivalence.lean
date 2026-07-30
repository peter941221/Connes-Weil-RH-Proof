/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRadialRecovery
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRouteDomination

/-!
# Equivalence of the renewed and raw antiresonant columns

The normalized inverse `N_p` and the ambient loss factor `L_p` are both
functions of the same logarithmic translation.  This module proves their
commutation from the concrete Euler definitions and only then changes their
order.  Consequently

```text
L_p^dagger N_p^dagger newFrame_(p,S)
  = N_p^dagger L_p^dagger newFrame_(p,S).
```

Since `N_p` is contractive and Proof 633 supplies the reverse readout, the
renewed and raw antiresonant columns are uniformly norm-equivalent with costs
`1` and `8`.  This removes an order ambiguity; it does not bound the complete
signed numerator or close Bone 1.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRadialRecovery
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Concrete commutation -/

/-- The unnormalized Euler factor commutes with the ambient loss factor
because both are polynomials in the same prime-log translation. -/
theorem primeEulerTransport_comp_ambientLossFactor_eq_commuted
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
        primeEulerAmbientLossFactor p =
      primeEulerAmbientLossFactor p ∘L
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change ccm24PrimeEulerTransportEquiv p
      (primeEulerAmbientLossFactor p x) =
    primeEulerAmbientLossFactor p (ccm24PrimeEulerTransportEquiv p x)
  rw [primeEulerAmbientLossFactor]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ccm24PrimeEulerTransportEquiv_apply, map_smul, map_add, map_sub]
  change
    (primeEulerAmbientLossScale p : ℂ) •
        (x - (ccm24PrimeEulerCoefficient p : ℂ) •
            cc20GlobalLogTranslation (-Real.log p) x +
          (cc20GlobalLogTranslation (-Real.log p) x -
            (ccm24PrimeEulerCoefficient p : ℂ) •
              cc20GlobalLogTranslation (-Real.log p)
                (cc20GlobalLogTranslation (-Real.log p) x))) =
      (primeEulerAmbientLossScale p : ℂ) •
          (x + cc20GlobalLogTranslation (-Real.log p) x) -
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (primeEulerAmbientLossScale p : ℂ) •
            (cc20GlobalLogTranslation (-Real.log p) x +
              cc20GlobalLogTranslation (-Real.log p)
                (cc20GlobalLogTranslation (-Real.log p) x))
  module

/-- The normalized inverse and the ambient loss factor commute.  The proof
uses invertibility only after the concrete forward commutation is known. -/
theorem primeEulerAmbientLossFactor_comp_normalizedPrimeEulerInverse_eq_commuted
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossFactor p ∘L normalizedPrimeEulerInverse p =
      normalizedPrimeEulerInverse p ∘L primeEulerAmbientLossFactor p := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ccm24PrimeEulerTransportEquiv p).injective
  have hcomm := DFunLike.congr_fun
    (primeEulerTransport_comp_ambientLossFactor_eq_commuted p)
    (normalizedPrimeEulerInverse p x)
  have hpair (y : finiteSCarrier) :
      ccm24PrimeEulerTransportEquiv p
          (normalizedPrimeEulerInverse p y) =
        ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • y := by
    change ccm24PrimeEulerTransportEquiv p
        (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
          (ccm24PrimeEulerTransportEquiv p).symm y) = _
    rw [map_smul, (ccm24PrimeEulerTransportEquiv p).apply_symm_apply]
  simp only [ContinuousLinearMap.comp_apply] at hcomm ⊢
  calc
    ccm24PrimeEulerTransportEquiv p
        (primeEulerAmbientLossFactor p
          (normalizedPrimeEulerInverse p x)) =
      primeEulerAmbientLossFactor p
        (ccm24PrimeEulerTransportEquiv p
          (normalizedPrimeEulerInverse p x)) := hcomm
    _ = primeEulerAmbientLossFactor p
        (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • x) := by
      rw [hpair]
    _ = ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        primeEulerAmbientLossFactor p x := by rw [map_smul]
    _ = ccm24PrimeEulerTransportEquiv p
        (normalizedPrimeEulerInverse p (primeEulerAmbientLossFactor p x)) := by
      rw [hpair]

/-- Adjoint commutation in the exact orientation used by the renewed source
column. -/
theorem primeEulerAmbientLossFactor_adjoint_comp_inverse_adjoint_eq_commuted
    (p : CCM24VisiblePrime) :
    (primeEulerAmbientLossFactor p)† ∘L
        (normalizedPrimeEulerInverse p)† =
      (normalizedPrimeEulerInverse p)† ∘L
        (primeEulerAmbientLossFactor p)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (primeEulerAmbientLossFactor_comp_normalizedPrimeEulerInverse_eq_commuted p)
  simpa only [ContinuousLinearMap.adjoint_comp] using h.symm

/-! ## Uniform column equivalence -/

/-- The renewed column is the contractive inverse adjoint applied after the
raw antiresonant column. -/
theorem suffixEulerFrameRenewedAntiresonantColumn_eq_inverseAdjoint_comp_raw
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameRenewedAntiresonantColumn lambda p S =
      (normalizedPrimeEulerInverse p)† ∘L
        newFrameAntiresonantColumn lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  have hcomm := DFunLike.congr_fun
    (primeEulerAmbientLossFactor_adjoint_comp_inverse_adjoint_eq_commuted p)
    (newSuffixFrame lambda S x)
  simpa only [suffixEulerFrameRenewedAntiresonantColumn,
    newFrameAntiresonantColumn, suffixEulerFrameSchurStep,
    ContinuousLinearMap.comp_apply] using hcomm

/-- Contractivity of the normalized inverse gives the cost-`1` direction. -/
theorem norm_renewedAntiresonantColumn_apply_le_raw
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ≤
      ‖newFrameAntiresonantColumn lambda p S x‖ := by
  rw [suffixEulerFrameRenewedAntiresonantColumn_eq_inverseAdjoint_comp_raw]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    ‖((normalizedPrimeEulerInverse p)†)
        (newFrameAntiresonantColumn lambda p S x)‖ ≤
      ‖(normalizedPrimeEulerInverse p)†‖ *
        ‖newFrameAntiresonantColumn lambda p S x‖ :=
      ((normalizedPrimeEulerInverse p)†).le_opNorm _
    _ = ‖normalizedPrimeEulerInverse p‖ *
        ‖newFrameAntiresonantColumn lambda p S x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖newFrameAntiresonantColumn lambda p S x‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_normalizedPrimeEulerInverse_le_one p) (norm_nonneg _)
    _ = ‖newFrameAntiresonantColumn lambda p S x‖ := by ring

/-- The canonical radial-recovery map gives the reverse cost-`8` direction. -/
theorem norm_rawAntiresonantColumn_apply_le_eight_mul_renewed
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖newFrameAntiresonantColumn lambda p S x‖ ≤
      8 * ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ := by
  have hpoint := DFunLike.congr_fun
    (primeEulerRenewedAntiresonantRecovery_comp_renewedColumn lambda p S) x
  simp only [ContinuousLinearMap.comp_apply] at hpoint
  rw [← hpoint]
  calc
    ‖primeEulerRenewedAntiresonantRecovery p
        (suffixEulerFrameRenewedAntiresonantColumn lambda p S x)‖ ≤
      ‖primeEulerRenewedAntiresonantRecovery p‖ *
        ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ :=
      (primeEulerRenewedAntiresonantRecovery p).le_opNorm _
    _ ≤ 8 * ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_primeEulerRenewedAntiresonantRecovery_le_eight p)
        (norm_nonneg _)

/-! ## Route-uniform equivalence -/

/-- Bone 1 written against the raw antiresonant loss column, with the
normalized inverse removed. -/
def SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S →
        ∀ x : sourceSoninCarrier lambda,
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
            bound ^ 2 *
              ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2

/-- A renewed-column domination also holds against the larger raw column,
with no change in the bound. -/
theorem routeUniformRawAmbientDomination_of_renewedAmbientDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
      owner lambda bound := by
  refine ⟨hdom.1, ?_⟩
  intro p S hvalid x
  calc
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2 :=
      hdom.2 p S hvalid x
    _ ≤ bound ^ 2 * ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
          (norm_renewedAntiresonantColumn_apply_le_raw lambda p S x))
        (sq_nonneg bound)

/-- A raw-column domination transfers back to the renewed column with only
the universal recovery cost `8`. -/
theorem renewedAmbientDomination_of_routeUniformRawAmbientDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
      owner lambda (8 * bound) := by
  refine ⟨mul_nonneg (by norm_num) hdom.1, ?_⟩
  intro p S hvalid x
  have hraw :=
    norm_rawAntiresonantColumn_apply_le_eight_mul_renewed lambda p S x
  calc
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        bound ^ 2 * ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 :=
      hdom.2 p S hvalid x
    _ ≤ bound ^ 2 *
        (8 *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hraw)
        (sq_nonneg bound)
    _ = (8 * bound) ^ 2 *
        ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2 := by
      ring

/-- Existence of a finite route-uniform Bone 1 constant is unchanged when
the normalized inverse is removed from the denominator. -/
theorem exists_routeUniformRenewedAmbientDomination_iff_exists_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) ↔
      ∃ bound : ℝ,
        SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
          owner lambda bound := by
  constructor
  · rintro ⟨bound, hbound⟩
    exact ⟨bound,
      routeUniformRawAmbientDomination_of_renewedAmbientDomination hbound⟩
  · rintro ⟨bound, hbound⟩
    exact ⟨8 * bound,
      renewedAmbientDomination_of_routeUniformRawAmbientDomination hbound⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
end CCM25Concrete
end Source
end ConnesWeilRH
