/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction

/-!
# Radial recovery from the renewed antiresonant channel

Proof 630 keeps the physical order

```text
L_p^dagger * N_p^dagger * newFrame_(p,S).
```

There is no need to commute `N_p` with `L_p` in order to recover the earlier
antiresonant column. Left multiplication by the genuine forward transport
uses the two exact identities

```text
T_p^dagger * N_p^dagger = rho_p I,
T_p^dagger - I = -sqrt(q_p) L_p^dagger
```

and gives

```text
T_p^dagger L_p^dagger N_p^dagger = rho_p L_p^dagger.
```

Thus the renewed column has a canonical readout of norm at most `8` onto the
raw antiresonant column. Composing this readout with the existing radial
recurrence transfers every genuine radial boundary-block identity to the
renewed denominator. This remains a radial recovery theorem; it does not
identify the complete second-support/prolate reverse-intertwining defect.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRadialRecovery

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Ordered ambient recovery -/

/-- The forward transport turns the normalized renewal deviation into the
raw antiresonant loss with the exact scalar `rho_p * sqrt(q_p)`. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_comp_renewalDeviation
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† ∘L
        ((normalizedPrimeEulerInverse p)† -
          (primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ finiteSCarrier) =
      (primeSchurMarkovScalar p : ℂ) •
        ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
          (primeEulerAmbientLossFactor p)†) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpair := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_comp_inverse_adjoint p) x
  have hdiff := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_sub_id_eq_neg_sqrtCoefficient_smul_primeEulerAmbientLossFactor_adjoint
      p) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply]
    at hpair hdiff ⊢
  calc
    ((normalizedPrimeEulerFrameTransport p)†)
        (((normalizedPrimeEulerInverse p)†) x -
          (primeSchurMarkovScalar p : ℂ) • x) =
        ((normalizedPrimeEulerFrameTransport p)†)
            (((normalizedPrimeEulerInverse p)†) x) -
          (primeSchurMarkovScalar p : ℂ) •
            (((normalizedPrimeEulerFrameTransport p)†) x) := by
      rw [map_sub, map_smul]
    _ = (primeSchurMarkovScalar p : ℂ) • x -
          (primeSchurMarkovScalar p : ℂ) •
            (((normalizedPrimeEulerFrameTransport p)†) x) := by
      rw [hpair]
    _ = -((primeSchurMarkovScalar p : ℂ) •
          (((normalizedPrimeEulerFrameTransport p)†) x - x)) := by
      module
    _ = (primeSchurMarkovScalar p : ℂ) •
          ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
            (((primeEulerAmbientLossFactor p)†) x)) := by
      rw [hdiff]
      module

/-- The forward transport recovers the raw antiresonant loss from the renewed
loss without exchanging the loss and inverse factors. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_comp_lossAdjoint_comp_inverseAdjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† ∘L
        ((primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†) =
      (primeSchurMarkovScalar p : ℂ) •
        (primeEulerAmbientLossFactor p)† := by
  apply ContinuousLinearMap.ext
  intro x
  have hdeviation := DFunLike.congr_fun
    (primeEulerRenewalDeviation_eq_sqrtCoefficient_smul_lossAdjoint_comp_inverseAdjoint
      p) x
  have htransport := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_comp_renewalDeviation p) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hdeviation htransport ⊢
  rw [hdeviation, map_smul] at htransport
  have hsqrtReal : 0 < Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos p)
  have hsqrt :
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrtReal.ne'
  have hscaled :
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
          (((normalizedPrimeEulerFrameTransport p)†)
            (((primeEulerAmbientLossFactor p)†)
              (((normalizedPrimeEulerInverse p)†) x))) =
        (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
          ((primeSchurMarkovScalar p : ℂ) •
            (((primeEulerAmbientLossFactor p)†) x)) := by
    simpa only [smul_smul, mul_comm] using htransport
  exact hsqrt.isUnit.smul_left_cancel.mp hscaled

/-! ## Canonical renewed-to-raw readout -/

/-- The canonical recovery map from the renewed physical column to the raw
antiresonant column. -/
noncomputable def primeEulerRenewedAntiresonantRecovery
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((primeSchurMarkovScalar p : ℂ)⁻¹) •
    (normalizedPrimeEulerFrameTransport p)†

/-- The recovery map sends every renewed source column to the earlier raw
antiresonant column, in the physical order. -/
theorem primeEulerRenewedAntiresonantRecovery_comp_renewedColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    primeEulerRenewedAntiresonantRecovery p ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S =
      newFrameAntiresonantColumn lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  have hrecovery := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_comp_lossAdjoint_comp_inverseAdjoint
      p) ((suffixEulerFrameSchurStep lambda p S).newFrame x)
  simp only [suffixEulerFrameSchurStep, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hrecovery
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  simp only [primeEulerRenewedAntiresonantRecovery,
    suffixEulerFrameRenewedAntiresonantColumn,
    newFrameAntiresonantColumn, suffixEulerFrameSchurStep,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  rw [hrecovery, smul_smul, inv_mul_cancel₀ hrho, one_smul]

/-- The renewed-to-raw recovery has one universal norm cost. -/
theorem norm_primeEulerRenewedAntiresonantRecovery_le_eight
    (p : CCM24VisiblePrime) :
    ‖primeEulerRenewedAntiresonantRecovery p‖ ≤ 8 := by
  rw [primeEulerRenewedAntiresonantRecovery, norm_smul,
    ContinuousLinearMap.adjoint.norm_map]
  calc
    ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
          ‖normalizedPrimeEulerFrameTransport p‖ ≤
        8 * 1 := by
      exact mul_le_mul
        (norm_primeSchurMarkovScalar_inv_le_eight p)
        (normalizedPrimeEulerFrameTransport_norm_le_one p)
        (norm_nonneg _) (by norm_num)
    _ = 8 := by norm_num

/-! ## Genuine radial-block recovery -/

/-- The existing radial block readout, preceded by the uniform recovery from
the renewed source column. -/
noncomputable def renewedAntiresonantRadialBlockReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  newFrameAntiresonantRadialBlockReadout lambda p n ∘L
    primeEulerRenewedAntiresonantRecovery p

/-- Every genuine radial boundary block is an exact readout of the renewed
single channel. -/
theorem renewedAntiresonantRadialBlockReadout_comp_renewedColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (n : ℕ) :
    renewedAntiresonantRadialBlockReadout lambda p n ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S =
      primeEulerRadialBoundaryStep lambda p ∘L
          ((primeEulerRadialTail lambda p) ^ n) ∘L
        newSuffixFrame lambda S := by
  rw [renewedAntiresonantRadialBlockReadout,
    ContinuousLinearMap.comp_assoc,
    primeEulerRenewedAntiresonantRecovery_comp_renewedColumn,
    newFrameAntiresonantRadialBlockReadout_comp_column]

/-- The transfer from the raw radial readout costs at most the fixed factor
`8`. -/
theorem norm_renewedAntiresonantRadialBlockReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖renewedAntiresonantRadialBlockReadout lambda p n‖ ≤
      8 * ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ * ((n : ℝ) + 1) := by
  calc
    ‖renewedAntiresonantRadialBlockReadout lambda p n‖ ≤
        ‖newFrameAntiresonantRadialBlockReadout lambda p n‖ *
          ‖primeEulerRenewedAntiresonantRecovery p‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖newFrameAntiresonantRadialBlockReadout lambda p n‖ * 8 := by
      exact mul_le_mul_of_nonneg_left
        (norm_primeEulerRenewedAntiresonantRecovery_le_eight p)
        (norm_nonneg _)
    _ ≤
        (‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ * ((n : ℝ) + 1)) * 8 := by
      exact mul_le_mul_of_nonneg_right
        (norm_newFrameAntiresonantRadialBlockReadout_le lambda p n)
        (by norm_num)
    _ = 8 * ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ * ((n : ℝ) + 1) := by
      ring

/-! ## Complete geometric radial recovery -/

/-- The complete Euler-weighted radial readout, preceded by the uniform
renewed-to-raw recovery. -/
noncomputable def renewedAntiresonantRadialGeometricReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  primeEulerRadialGeometricReadout lambda p ∘L
    primeEulerRenewedAntiresonantRecovery p

/-- The complete geometric radial boundary is an exact readout of the renewed
single channel on every suffix frame. -/
theorem renewedAntiresonantRadialGeometricReadout_comp_renewedColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    renewedAntiresonantRadialGeometricReadout lambda p ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S =
      primeEulerRadialGeometricBoundary lambda p ∘L
        newSuffixFrame lambda S := by
  rw [renewedAntiresonantRadialGeometricReadout,
    ContinuousLinearMap.comp_assoc,
    primeEulerRenewedAntiresonantRecovery_comp_renewedColumn,
    primeEulerRadialGeometricReadout_comp_ambientLossColumn]

/-- Summing the radial recurrence before estimating gives one universal
renewed-channel readout bound. -/
theorem norm_renewedAntiresonantRadialGeometricReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖renewedAntiresonantRadialGeometricReadout lambda p‖ ≤ 256 := by
  calc
    ‖renewedAntiresonantRadialGeometricReadout lambda p‖ ≤
        ‖primeEulerRadialGeometricReadout lambda p‖ *
          ‖primeEulerRenewedAntiresonantRecovery p‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 32 * 8 := by
      exact mul_le_mul
        (norm_primeEulerRadialGeometricReadout_le lambda p)
        (norm_primeEulerRenewedAntiresonantRecovery_le_eight p)
        (norm_nonneg _) (by norm_num)
    _ = 256 := by norm_num

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRadialRecovery
end CCM25Concrete
end Source
end ConnesWeilRH
