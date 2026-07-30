/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance

/-!
# Moving-range leakage in the ambient covariance factor

The ambient covariance factorization from the preceding module is sufficient
for Bone 1, but it is stronger than the exact single-channel factor.  Given a
genuine single-channel factor `H`, this module proves the exact normal form

```text
C_(p,S) = L_p H
  - rho_p^-1 F_p (I - J_S J_S^dagger) N_p L_p H.
```

Here `J_S` is the actual new suffix polar frame.  The second summand is the
moving-range leakage carried by the second coordinate of the canonical packed
physical factor.  It is uniformly bounded by `16 ||H||`, but it is not known
to vanish and must not be silently discarded.  No summand of the complete raw
quadratic response is estimated separately.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovarianceLeakage

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  sourceSoninCarrier lambda →L[ℂ] finiteSCarrier

/-! ## Carrier-independent operator algebra -/

private theorem adjoint_smul_fivefold_of_selfAdjoint_middle
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (scalar : ℂ) (forward middle inverse loss : K →L[ℂ] K)
    (factor : H →L[ℂ] K)
    (hscalar : star scalar = scalar) (hmiddle : middle† = middle) :
    (scalar • (forward ∘L middle ∘L inverse ∘L loss ∘L factor))† =
      scalar • (factor† ∘L loss† ∘L inverse† ∘L middle ∘L forward†) := by
  have hadjointSmul :
      (scalar • (forward ∘L middle ∘L inverse ∘L loss ∘L factor))† =
        star scalar •
          (forward ∘L middle ∘L inverse ∘L loss ∘L factor)† := by
    simpa only [starRingEnd_apply] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ scalar
        (forward ∘L middle ∘L inverse ∘L loss ∘L factor))
  rw [hadjointSmul, hscalar]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, hmiddle]

private theorem norm_threefold_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (left : F →L[ℂ] E) (middle right : F →L[ℂ] F) (bound : ℝ)
    (hleft : ‖left‖ ≤ bound) (hmiddle : ‖middle‖ ≤ 1)
    (hright : ‖right‖ ≤ 1) (hbound : 0 ≤ bound) :
    ‖left ∘L middle ∘L right‖ ≤ bound := by
  calc
    ‖left ∘L middle ∘L right‖ ≤ ‖left ∘L middle‖ * ‖right‖ :=
      ContinuousLinearMap.opNorm_comp_le (left ∘L middle) right
    _ ≤ (‖left‖ * ‖middle‖) * ‖right‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le left middle) (norm_nonneg right)
    _ ≤ (bound * 1) * 1 :=
      mul_le_mul (mul_le_mul hleft hmiddle (norm_nonneg _) hbound)
        hright (norm_nonneg _) (mul_nonneg hbound zero_le_one)
    _ = bound := by ring

/-! ## Exact covariance reconstruction -/

/-- The complete ambient covariance column is recovered from its normalized
inverse pullback by the actual new-frame projection.  This uses the exact
forward/reverse Schur--Markov pairing, not injectivity or a closed-range
argument. -/
theorem suffixActualBandAmbientRawCovarianceColumn_eq_projectedPullback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      ((primeSchurMarkovScalar p : ℂ)⁻¹) •
        (normalizedPrimeEulerFrameTransport p ∘L
          newSuffixFrame lambda S ∘L
            (newSuffixFrame lambda S)† ∘L
              normalizedPrimeEulerInverse p ∘L
                suffixActualBandAmbientRawCovarianceColumn
                  owner lambda p S) := by
  have hcovariance :=
    suffixActualBandAmbientRawCovarianceColumn_eq_oldFrame_comp_rawDefect
      owner lambda p S
  rw [hcovariance]
  apply ContinuousLinearMap.ext
  intro x
  let rawDefect :=
    suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S
  have hintertwining := DFunLike.congr_fun
    (suffixEulerFrameSchurStep lambda p S).transport_intertwining
    (suffixEulerFrameReverseTransition lambda p S (rawDefect x))
  have hpair := DFunLike.congr_fun
    (suffixEulerFrameTransition_comp_reverse lambda p S) (rawDefect x)
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  simp only [suffixEulerFrameSchurStep, suffixEulerFrameReverseTransition,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hintertwining hpair ⊢
  rw [hintertwining, hpair, map_smul, smul_smul,
    inv_mul_cancel₀ hrho, one_smul]

/-! ## The genuine leakage term -/

/-- The untransported moving-range residual of a proposed single-channel
factor.  Vanishing means that `N_p L_p H` lands in the actual new suffix-frame
range. -/
noncomputable def suffixActualBandAmbientCovarianceRangeResidual
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (factor : SourceToFinite lambda) :
    SourceToFinite lambda :=
  suffixEulerFrameNewRangeComplement lambda p S ∘L
    normalizedPrimeEulerInverse p ∘L
      primeEulerAmbientLossFactor p ∘L factor

/-- The part of an ambient covariance factor which exits the actual new
suffix-frame range before the normalized inverse is cancelled. -/
noncomputable def suffixActualBandAmbientCovarianceRangeLeakage
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (factor : SourceToFinite lambda) :
    SourceToFinite lambda :=
  ((primeSchurMarkovScalar p : ℂ)⁻¹) •
    (normalizedPrimeEulerFrameTransport p ∘L
      suffixActualBandAmbientCovarianceRangeResidual lambda p S factor)

/-- The forward transport and nonzero Schur--Markov scalar lose no
information: the transported leakage vanishes exactly when the moving-range
residual itself vanishes. -/
theorem suffixActualBandAmbientCovarianceRangeLeakage_eq_zero_iff
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (factor : SourceToFinite lambda) :
    suffixActualBandAmbientCovarianceRangeLeakage lambda p S factor = 0 ↔
      suffixActualBandAmbientCovarianceRangeResidual lambda p S factor = 0 := by
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  constructor
  · intro hleakage
    apply ContinuousLinearMap.ext
    intro x
    have hpoint := DFunLike.congr_fun hleakage x
    simp only [suffixActualBandAmbientCovarianceRangeLeakage,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply] at hpoint
    have htransportZero :
        normalizedPrimeEulerFrameTransport p
          (suffixActualBandAmbientCovarianceRangeResidual
            lambda p S factor x) = 0 :=
      (smul_eq_zero.mp hpoint).resolve_left (inv_ne_zero hrho)
    have hpair := DFunLike.congr_fun
      (normalizedPrimeEulerInverse_comp_frameTransport p)
      (suffixActualBandAmbientCovarianceRangeResidual lambda p S factor x)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hpair
    have hscaled :
        (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandAmbientCovarianceRangeResidual
            lambda p S factor x = 0 := by
      rw [← hpair, htransportZero, map_zero]
    exact (smul_eq_zero.mp hscaled).resolve_left hrho
  · intro hresidual
    rw [suffixActualBandAmbientCovarianceRangeLeakage, hresidual,
      ContinuousLinearMap.comp_zero, smul_zero]

/-- A supplied Bone 1 single-channel factor reconstructs the ambient
covariance only after the actual new-frame projection is inserted. -/
theorem ambientCovariance_eq_projectedFactor_of_singleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      ((primeSchurMarkovScalar p : ℂ)⁻¹) •
        (normalizedPrimeEulerFrameTransport p ∘L
          newSuffixFrame lambda S ∘L
            (newSuffixFrame lambda S)† ∘L
              normalizedPrimeEulerInverse p ∘L
                primeEulerAmbientLossFactor p ∘L data.factor) := by
  have hpullback :
      (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
          suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
        (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
          primeEulerAmbientLossFactor p ∘L data.factor := by
    rw [←
      completeBoundaryReverseIntertwiningDefect_adjoint_comp_transition_eq_ambientCovariancePullback
        owner lambda p S]
    exact data.factorization
  rw [suffixActualBandAmbientRawCovarianceColumn_eq_projectedPullback]
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun hpullback x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hpoint ⊢
  rw [hpoint]

/-- Exact leakage normal form.  The complete signed factor remains intact in
both terms; no first-jet, metric, boundary, or prolate summand is separated. -/
theorem ambientCovariance_eq_lossFactor_sub_rangeLeakage_of_singleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      primeEulerAmbientLossFactor p ∘L data.factor -
        suffixActualBandAmbientCovarianceRangeLeakage
          lambda p S data.factor := by
  rw [ambientCovariance_eq_projectedFactor_of_singleChannelFactorData data]
  apply ContinuousLinearMap.ext
  intro x
  let y := normalizedPrimeEulerInverse p
    (primeEulerAmbientLossFactor p (data.factor x))
  have hsplit :
      newSuffixFrame lambda S
          (ContinuousLinearMap.adjoint (newSuffixFrame lambda S) y) =
        y - suffixEulerFrameNewRangeComplement lambda p S y := by
    simp only [suffixEulerFrameNewRangeComplement,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply]
    abel
  have hpair := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_comp_inverse p)
    (primeEulerAmbientLossFactor p (data.factor x))
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  simp only [suffixActualBandAmbientCovarianceRangeLeakage,
    suffixActualBandAmbientCovarianceRangeResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at hpair ⊢
  change ((primeSchurMarkovScalar p : ℂ)⁻¹) •
      normalizedPrimeEulerFrameTransport p
        (newSuffixFrame lambda S
          (ContinuousLinearMap.adjoint (newSuffixFrame lambda S) y)) = _
  rw [hsplit, map_sub, hpair, smul_sub, smul_smul,
    inv_mul_cancel₀ hrho, one_smul]

/-- The stronger ambient divisibility condition is equivalent to a genuine
extra range premise on the selected Bone 1 factor.  The actual Schur owner's
zero right-boundary leakage does not prove this premise for an arbitrary
factor output. -/
theorem ambientCovariance_eq_lossFactor_iff_rangeResidual_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
        primeEulerAmbientLossFactor p ∘L data.factor ↔
      suffixActualBandAmbientCovarianceRangeResidual
        lambda p S data.factor = 0 := by
  constructor
  · intro hfactorization
    apply (suffixActualBandAmbientCovarianceRangeLeakage_eq_zero_iff
      lambda p S data.factor).1
    apply ContinuousLinearMap.ext
    intro x
    have hnormal := DFunLike.congr_fun
      (ambientCovariance_eq_lossFactor_sub_rangeLeakage_of_singleChannelFactorData
        data) x
    have hfactorizationPoint := DFunLike.congr_fun hfactorization x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply] at hnormal hfactorizationPoint
    have hneg :
        -(suffixActualBandAmbientCovarianceRangeLeakage
          lambda p S data.factor x) = 0 := by
      calc
        -(suffixActualBandAmbientCovarianceRangeLeakage
            lambda p S data.factor x) =
            (primeEulerAmbientLossFactor p (data.factor x) -
              suffixActualBandAmbientCovarianceRangeLeakage
                lambda p S data.factor x) -
              primeEulerAmbientLossFactor p (data.factor x) := by
                abel
        _ = suffixActualBandAmbientRawCovarianceColumn owner lambda p S x -
              primeEulerAmbientLossFactor p (data.factor x) := by
            rw [← hnormal]
        _ = 0 := by rw [hfactorizationPoint, sub_self]
    simpa only [ContinuousLinearMap.zero_apply] using neg_eq_zero.mp hneg
  · intro hresidual
    have hleakage :=
      (suffixActualBandAmbientCovarianceRangeLeakage_eq_zero_iff
        lambda p S data.factor).2 hresidual
    rw [ambientCovariance_eq_lossFactor_sub_rangeLeakage_of_singleChannelFactorData
      data, hleakage, sub_zero]

/-! ## Identification with the packed physical boundary coordinate -/

/-- The leakage adjoint is exactly the canonical packed boundary row applied
to the moving-range complement and the adjoint forward transport. -/
theorem suffixActualBandAmbientCovarianceRangeLeakage_adjoint_eq
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (factor : SourceToFinite lambda) :
    (suffixActualBandAmbientCovarianceRangeLeakage
        lambda p S factor)† =
      -(canonicalPackedPhysicalBoundaryRow p factor ∘L
        suffixEulerFrameNewRangeComplement lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)†) := by
  have hstar : star ((primeSchurMarkovScalar p : ℂ)⁻¹) =
      (primeSchurMarkovScalar p : ℂ)⁻¹ := by
    rw [RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal]
  have hcomplement :
      (suffixEulerFrameNewRangeComplement lambda p S)† =
        suffixEulerFrameNewRangeComplement lambda p S :=
    (suffixEulerFrameNewRangeComplement_isStarProjection lambda p S).isSelfAdjoint.adjoint_eq
  calc
    (suffixActualBandAmbientCovarianceRangeLeakage
        lambda p S factor)† =
        ((primeSchurMarkovScalar p : ℂ)⁻¹) •
          (factor† ∘L (primeEulerAmbientLossFactor p)† ∘L
            (normalizedPrimeEulerInverse p)† ∘L
              suffixEulerFrameNewRangeComplement lambda p S ∘L
                (normalizedPrimeEulerFrameTransport p)†) := by
      exact adjoint_smul_fivefold_of_selfAdjoint_middle
        ((primeSchurMarkovScalar p : ℂ)⁻¹)
        (normalizedPrimeEulerFrameTransport p)
        (suffixEulerFrameNewRangeComplement lambda p S)
        (normalizedPrimeEulerInverse p)
        (primeEulerAmbientLossFactor p) factor hstar hcomplement
    _ = -(canonicalPackedPhysicalBoundaryRow p factor ∘L
          suffixEulerFrameNewRangeComplement lambda p S ∘L
            (normalizedPrimeEulerFrameTransport p)†) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [canonicalPackedPhysicalBoundaryRow,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.neg_apply, neg_neg]

/-- The genuine moving-range leakage has precisely the uniform norm cost of
the second packed physical coordinate.  This is a bound on the intact factor,
not a claim that the leakage vanishes. -/
theorem norm_suffixActualBandAmbientCovarianceRangeLeakage_le_sixteen
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (factor : SourceToFinite lambda) :
    ‖suffixActualBandAmbientCovarianceRangeLeakage
        lambda p S factor‖ ≤ 16 * ‖factor‖ := by
  have hboundary :
      ‖canonicalPackedPhysicalBoundaryRow p factor‖ ≤ 16 * ‖factor‖ :=
    canonicalPackedPhysicalBoundaryRow_norm_le_sixteen p factor
  have hcomplement :
      ‖suffixEulerFrameNewRangeComplement lambda p S‖ ≤ (1 : ℝ) :=
    suffixEulerFrameNewRangeComplement_norm_le_one lambda p S
  have htransportAdjoint :
      ‖(normalizedPrimeEulerFrameTransport p)†‖ ≤ (1 : ℝ) := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact normalizedPrimeEulerFrameTransport_norm_le_one p
  calc
    ‖suffixActualBandAmbientCovarianceRangeLeakage lambda p S factor‖ =
        ‖(suffixActualBandAmbientCovarianceRangeLeakage
          lambda p S factor)†‖ :=
      (ContinuousLinearMap.adjoint.norm_map _).symm
    _ = ‖-(canonicalPackedPhysicalBoundaryRow p factor ∘L
          suffixEulerFrameNewRangeComplement lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)†)‖ := by
      rw [suffixActualBandAmbientCovarianceRangeLeakage_adjoint_eq]
    _ = ‖canonicalPackedPhysicalBoundaryRow p factor ∘L
          suffixEulerFrameNewRangeComplement lambda p S ∘L
          (normalizedPrimeEulerFrameTransport p)†‖ :=
      ContinuousLinearMap.opNorm_neg _
    _ ≤ 16 * ‖factor‖ :=
      norm_threefold_le
        (canonicalPackedPhysicalBoundaryRow p factor)
        (suffixEulerFrameNewRangeComplement lambda p S)
        ((normalizedPrimeEulerFrameTransport p)†)
        (16 * ‖factor‖) hboundary hcomplement htransportAdjoint (by positivity)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovarianceLeakage
end CCM25Concrete
end Source
end ConnesWeilRH
