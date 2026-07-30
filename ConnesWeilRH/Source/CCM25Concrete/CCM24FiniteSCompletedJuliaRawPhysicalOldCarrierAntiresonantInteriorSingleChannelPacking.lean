/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard

/-!
# Packed-factor norm ledger for the renewed antiresonant channel

This module isolates the explicit two-coordinate packing and its uniform norm
bound behind an `.olean` boundary.  The source-channel proof can therefore use
the bound without repeatedly elaborating the three-adjoint composition.
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
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance singleChannelPackingSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    finiteSCarrier

/-! ## Canonical packing into the Proof 625 carrier -/

/-- The boundary row paired with the ambient row `H^dagger`. -/
noncomputable def canonicalPackedPhysicalBoundaryRow
    (p : CCM24VisiblePrime) {lambda : CCM24SoninScale}
    (H : SourceToFinite lambda) :
    finiteSCarrier →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  -(((primeSchurMarkovScalar p : ℂ)⁻¹) •
    (H† ∘L (primeEulerAmbientLossFactor p)† ∘L
      (normalizedPrimeEulerInverse p)†))

/-- The packed readout whose adjoint is the physical factor. -/
noncomputable def canonicalPackedPhysicalReadout
    (p : CCM24VisiblePrime) {lambda : CCM24SoninScale}
    (H : SourceToFinite lambda) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  suffixEulerFrameAmbientBoundaryReadoutOfRows (H†)
    (canonicalPackedPhysicalBoundaryRow p H)

/-- The explicit Proof 625 factor associated with one source-side channel. -/
noncomputable def canonicalPackedPhysicalFactor
    (p : CCM24VisiblePrime) {lambda : CCM24SoninScale}
    (H : SourceToFinite lambda) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      suffixEulerFrameAmbientBoundaryCarrier :=
  (canonicalPackedPhysicalReadout p H)†

theorem primeEulerAmbientLossFactor_norm_le_two
    (p : CCM24VisiblePrime) :
    ‖primeEulerAmbientLossFactor p‖ ≤ (2 : ℝ) := by
  rw [← ContinuousLinearMap.adjoint.norm_map
    (primeEulerAmbientLossFactor p)]
  calc
    ‖(primeEulerAmbientLossFactor p)†‖ ≤
        2 * Real.sqrt (ccm24PrimeEulerCoefficient p) :=
      primeEulerAmbientLossFactor_adjoint_norm_le_two_sqrt_coefficient p
    _ ≤ 2 * 1 := by
      have hsqrt := sqrtPrimeEulerCoefficient_norm_le_one p
      have hsqrtReal :
          Real.sqrt (ccm24PrimeEulerCoefficient p) ≤ 1 := by
        simpa only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
      exact mul_le_mul_of_nonneg_left hsqrtReal (by norm_num)
    _ = 2 := by norm_num

private theorem adjoint_threefold_norm_le_two
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (H : E →L[ℂ] F) (L N : F →L[ℂ] F)
    (hL : ‖L‖ ≤ (2 : ℝ)) (hN : ‖N‖ ≤ (1 : ℝ)) :
    ‖H† ∘L L† ∘L N†‖ ≤ 2 * ‖H‖ := by
  have hHnorm : ‖H†‖ = ‖H‖ :=
    ContinuousLinearMap.adjoint.norm_map H
  have hLnorm : ‖L†‖ = ‖L‖ :=
    ContinuousLinearMap.adjoint.norm_map L
  have hNnorm : ‖N†‖ = ‖N‖ :=
    ContinuousLinearMap.adjoint.norm_map N
  calc
    ‖H† ∘L L† ∘L N†‖ ≤ ‖H† ∘L L†‖ * ‖N†‖ :=
      ContinuousLinearMap.opNorm_comp_le (H† ∘L L†) (N†)
    _ ≤ (‖H†‖ * ‖L†‖) * ‖N†‖ :=
      mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le (H†) (L†)) (norm_nonneg (N†))
    _ = (‖H‖ * ‖L‖) * ‖N‖ := by
      rw [hHnorm, hLnorm, hNnorm]
    _ ≤ (‖H‖ * 2) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hL (norm_nonneg H)) hN
        (norm_nonneg N) (mul_nonneg (norm_nonneg H) (by norm_num))
    _ = 2 * ‖H‖ := by ring

theorem canonicalPackedPhysicalBoundaryRow_norm_le_sixteen
    (p : CCM24VisiblePrime) {lambda : CCM24SoninScale}
    (H : SourceToFinite lambda) :
    ‖canonicalPackedPhysicalBoundaryRow p H‖ ≤ 16 * ‖H‖ := by
  have hcore :
      ‖H† ∘L (primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†‖ ≤ 2 * ‖H‖ :=
    adjoint_threefold_norm_le_two H
      (primeEulerAmbientLossFactor p) (normalizedPrimeEulerInverse p)
      (primeEulerAmbientLossFactor_norm_le_two p)
      (norm_normalizedPrimeEulerInverse_le_one p)
  calc
    ‖canonicalPackedPhysicalBoundaryRow p H‖ =
        ‖((primeSchurMarkovScalar p : ℂ)⁻¹) •
          (H† ∘L (primeEulerAmbientLossFactor p)† ∘L
            (normalizedPrimeEulerInverse p)†)‖ := by
      rw [canonicalPackedPhysicalBoundaryRow]
      exact norm_neg
        ((((primeSchurMarkovScalar p : ℂ)⁻¹) •
          (H† ∘L (primeEulerAmbientLossFactor p)† ∘L
            (normalizedPrimeEulerInverse p)†)) :
          finiteSCarrier →L[ℂ]
            CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda)
    _ ≤ ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
        ‖H† ∘L (primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 8 * (2 * ‖H‖) := by
      exact mul_le_mul
        (norm_primeSchurMarkovScalar_inv_le_eight p) hcore
        (norm_nonneg
          (H† ∘L (primeEulerAmbientLossFactor p)† ∘L
            (normalizedPrimeEulerInverse p)†)) (by norm_num)
    _ = 16 * ‖H‖ := by ring

theorem canonicalPackedPhysicalFactor_norm_le_seventeen
    (p : CCM24VisiblePrime) {lambda : CCM24SoninScale}
    (H : SourceToFinite lambda) :
    ‖canonicalPackedPhysicalFactor p H‖ ≤ 17 * ‖H‖ := by
  have hHnorm : ‖H†‖ = ‖H‖ :=
    ContinuousLinearMap.adjoint.norm_map H
  calc
    ‖canonicalPackedPhysicalFactor p H‖ =
        ‖canonicalPackedPhysicalReadout p H‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    ‖canonicalPackedPhysicalReadout p H‖ ≤
        ‖H†‖ + ‖canonicalPackedPhysicalBoundaryRow p H‖ :=
      suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add _ _
    _ ≤ ‖H‖ + 16 * ‖H‖ := by
      rw [hHnorm]
      exact add_le_add_right
        (canonicalPackedPhysicalBoundaryRow_norm_le_sixteen p H) _
    _ = 17 * ‖H‖ := by ring

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
