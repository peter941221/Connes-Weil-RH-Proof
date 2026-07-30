/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay

/-!
# Arbitrary-suffix renewal envelope

Proof 638 splits the complete signed interior numerator at every suffix as

```text
Interior_(p,S)
  = rho_p (ReducedRow_(p,S) newFrame_S)
    + sqrt(q_p) ReducedRow_(p,S) RenewedColumn_(p,S).
```

The second summand always gains the full Euler coefficient: its readout
contributes one `sqrt(q_p)` and the renewed column contributes the other.
This module records the resulting arbitrary-suffix estimate

```text
||renewal correction|| <= 2 q_p ||ReducedRow_(p,S)||.
```

It also gives two-sided envelopes comparing the complete numerator with the
leading reduced column. Consequently, under a supplied uniform reduced-row
bound, `O(q_p)` decay of either operator is equivalent, up to fixed constants,
to `O(q_p)` decay of the other.

Route validity alone is only a list-deduplication condition and supplies
neither bound. This module does not prove the missing leading-column decay,
Bone 1, Gate 3U, the finite-S sign, Burnol's identity, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSuffixRenewalEnvelope

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Exact arbitrary-suffix correction -/

/-- Subtracting the scalar leading column leaves exactly the renewal
correction. No route-validity or arithmetic-primality premise is needed. -/
theorem signedCompressedInteriorOwner_sub_scalar_reducedColumn_eq_correction
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S -
        (primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S) =
      suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S := by
  rw [signedCompressedInteriorOwner_eq_scalar_reducedColumn_add_correction]
  abel

/-- The arbitrary-suffix renewal correction gains one full Euler
coefficient. The remaining factor is exactly the norm of the complete
reduced row; it is not silently assumed to be route-uniform. -/
theorem norm_suffixInteriorRenewalCorrection_le_two_coefficient_mul_reducedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ ≤
      2 * ccm24PrimeEulerCoefficient p *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hreadout :
      ‖suffixInteriorRenewalCorrectionReadout owner lambda p S‖ =
        Real.sqrt (ccm24PrimeEulerCoefficient p) *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
    rw [suffixInteriorRenewalCorrectionReadout, norm_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ‖suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ ≤
        ‖suffixInteriorRenewalCorrectionReadout owner lambda p S‖ *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Real.sqrt (ccm24PrimeEulerCoefficient p) *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖) *
        (2 * Real.sqrt (ccm24PrimeEulerCoefficient p)) := by
      rw [hreadout]
      exact mul_le_mul_of_nonneg_left
        (norm_renewedAntiresonantColumn_le_two_sqrt_coefficient lambda p S)
        (by positivity)
    _ = 2 * Real.sqrt (ccm24PrimeEulerCoefficient p) ^ 2 *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by ring
    _ = 2 * ccm24PrimeEulerCoefficient p *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
      rw [Real.sq_sqrt hq]

/-- Norm form of the exact correction identity. -/
theorem norm_interior_sub_scalar_reducedColumn_le_two_coefficient_mul_reducedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖signedCompressedInteriorOwner owner lambda p S -
        (primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S)‖ ≤
      2 * ccm24PrimeEulerCoefficient p *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
  rw [signedCompressedInteriorOwner_sub_scalar_reducedColumn_eq_correction]
  exact
    norm_suffixInteriorRenewalCorrection_le_two_coefficient_mul_reducedRow
      owner lambda p S

/-! ## Two-sided numerator envelopes -/

private theorem norm_left_le_eight_total_add_eight_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (rho : ℝ) (left total correction : E) (bound : ℝ)
    (hrho : 0 ≤ rho) (hlower : (1 / 8 : ℝ) ≤ rho)
    (hsplit : total = (rho : ℂ) • left + correction)
    (hcorrection : ‖correction‖ ≤ bound) :
    ‖left‖ ≤ 8 * ‖total‖ + 8 * bound := by
  have hleadingEq : (rho : ℂ) • left = total - correction := by
    rw [hsplit]
    abel
  have hscaled : rho * ‖left‖ ≤ ‖total‖ + bound := by
    calc
      rho * ‖left‖ = ‖(rho : ℂ) • left‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hrho]
      _ = ‖total - correction‖ := congrArg norm hleadingEq
      _ ≤ ‖total‖ + ‖correction‖ := norm_sub_le _ _
      _ ≤ ‖total‖ + bound := add_le_add (le_refl _) hcorrection
  have hscaledLower : (1 / 8 : ℝ) * ‖left‖ ≤ rho * ‖left‖ :=
    mul_le_mul_of_nonneg_right hlower (norm_nonneg left)
  calc
    ‖left‖ = 8 * ((1 / 8 : ℝ) * ‖left‖) := by ring
    _ ≤ 8 * (rho * ‖left‖) :=
      mul_le_mul_of_nonneg_left hscaledLower (by norm_num)
    _ ≤ 8 * (‖total‖ + bound) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = 8 * ‖total‖ + 8 * bound := by ring

/-- The complete numerator is bounded by the leading reduced column plus the
full-Euler renewal correction. -/
theorem norm_signedCompressedInteriorOwner_le_reducedColumn_add_correction
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖signedCompressedInteriorOwner owner lambda p S‖ ≤
      ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S‖ +
        2 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
  have hrho : 0 ≤ primeSchurMarkovScalar p :=
    (primeSchurMarkovScalar_pos p).le
  have hrhoOne : primeSchurMarkovScalar p ≤ 1 :=
    primeSchurMarkovScalar_le_one p
  have hleading :
      ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S)‖ ≤
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hrhoOne
        (norm_nonneg
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S)))
  rw [signedCompressedInteriorOwner_eq_scalar_reducedColumn_add_correction]
  calc
    ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S) +
        suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ ≤
      ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S)‖ +
        ‖suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ :=
      norm_add_le _ _
    _ ≤ ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S‖ +
        2 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ :=
      add_le_add hleading
        (norm_suffixInteriorRenewalCorrection_le_two_coefficient_mul_reducedRow
          owner lambda p S)

/-- Conversely, the leading reduced column is controlled by the complete
numerator and the same renewal correction. The constant `8` is exactly the
uniform lower bound for `rho_p`. -/
theorem norm_reducedColumn_le_eight_interior_add_sixteen_coefficient_mul_reducedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        newSuffixFrame lambda S‖ ≤
      8 * ‖signedCompressedInteriorOwner owner lambda p S‖ +
        16 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
  let reducedColumn :=
    suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
      newSuffixFrame lambda S
  let correction :=
    suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
      suffixEulerFrameRenewedAntiresonantColumn lambda p S
  have hrho : 0 ≤ primeSchurMarkovScalar p :=
    (primeSchurMarkovScalar_pos p).le
  have hsplit :
      signedCompressedInteriorOwner owner lambda p S =
        (primeSchurMarkovScalar p : ℂ) • reducedColumn + correction := by
    simpa only [reducedColumn, correction] using
      signedCompressedInteriorOwner_eq_scalar_reducedColumn_add_correction
        owner lambda p S
  have hcorrection : ‖correction‖ ≤
      2 * ccm24PrimeEulerCoefficient p *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by
    simpa only [correction] using
      norm_suffixInteriorRenewalCorrection_le_two_coefficient_mul_reducedRow
        owner lambda p S
  have henvelope := norm_left_le_eight_total_add_eight_bound
    (primeSchurMarkovScalar p) reducedColumn
    (signedCompressedInteriorOwner owner lambda p S) correction
    (2 * ccm24PrimeEulerCoefficient p *
      ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖)
    hrho (primeSchurMarkovScalar_ge_one_eighth p) hsplit hcorrection
  have hrewrite :
      8 * (2 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖) =
        16 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ := by ring
  rw [hrewrite] at henvelope
  simpa only [reducedColumn] using henvelope

/-! ## A direct producer for `O(q_p)` -/

/-- A reduced-row norm bound plus `O(q_p)` decay of the leading column is
sufficient for `O(q_p)` decay of the complete numerator. -/
theorem norm_interior_le_coefficient_mul_of_reducedRow_and_column_bounds
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (rowBound columnBound : ℝ)
    (hrow : ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ ≤
      rowBound)
    (hcolumn :
      ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S‖ ≤
        columnBound * ccm24PrimeEulerCoefficient p) :
    ‖signedCompressedInteriorOwner owner lambda p S‖ ≤
      (columnBound + 2 * rowBound) * ccm24PrimeEulerCoefficient p := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  calc
    ‖signedCompressedInteriorOwner owner lambda p S‖ ≤
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
            newSuffixFrame lambda S‖ +
          2 * ccm24PrimeEulerCoefficient p *
            ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ :=
      norm_signedCompressedInteriorOwner_le_reducedColumn_add_correction
        owner lambda p S
    _ ≤ columnBound * ccm24PrimeEulerCoefficient p +
        2 * ccm24PrimeEulerCoefficient p * rowBound := by
      exact add_le_add hcolumn
        (mul_le_mul_of_nonneg_left hrow
          (mul_nonneg (by norm_num) hq))
    _ = (columnBound + 2 * rowBound) *
        ccm24PrimeEulerCoefficient p := by ring

/-- Conversely, `O(q_p)` decay of the complete numerator and a reduced-row
bound force `O(q_p)` decay of the leading column. Thus the arbitrary-suffix
problem cannot be discharged by the renewal correction alone. -/
theorem norm_reducedColumn_le_coefficient_mul_of_interior_and_reducedRow_bounds
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (rowBound interiorBound : ℝ)
    (hrow : ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ ≤
      rowBound)
    (hinterior : ‖signedCompressedInteriorOwner owner lambda p S‖ ≤
      interiorBound * ccm24PrimeEulerCoefficient p) :
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        newSuffixFrame lambda S‖ ≤
      (8 * interiorBound + 16 * rowBound) *
        ccm24PrimeEulerCoefficient p := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  calc
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        newSuffixFrame lambda S‖ ≤
      8 * ‖signedCompressedInteriorOwner owner lambda p S‖ +
        16 * ccm24PrimeEulerCoefficient p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ :=
      norm_reducedColumn_le_eight_interior_add_sixteen_coefficient_mul_reducedRow
        owner lambda p S
    _ ≤ 8 * (interiorBound * ccm24PrimeEulerCoefficient p) +
        16 * ccm24PrimeEulerCoefficient p * rowBound := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hinterior (by norm_num))
        (mul_le_mul_of_nonneg_left hrow
          (mul_nonneg (by norm_num) hq))
    _ = (8 * interiorBound + 16 * rowBound) *
        ccm24PrimeEulerCoefficient p := by ring

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSuffixRenewalEnvelope
end CCM25Concrete
end Source
end ConnesWeilRH
