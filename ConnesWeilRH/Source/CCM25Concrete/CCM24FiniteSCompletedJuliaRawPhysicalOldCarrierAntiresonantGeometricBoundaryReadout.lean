/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence

/-!
# Uniform geometric readout of the antiresonant radial boundary

Proof 612 recovers every radial boundary block `C V^n` from the actual
ambient-loss column. This module inserts the genuine one-prime renewal
coefficients and sums the recovered blocks in operator norm:

```text
G_(p,S) = sum_(n >= 0) q_p^(n+1) C V^n newFrame_S.
```

The corresponding readout is the same geometric sum of the scaled Proof 612
block readouts. Its norm is at most `32`, uniformly in the visible prime, the
suffix, and the Sonin scale. The uniform constant comes from
`q_p <= 3/4` and

```text
sum_(n >= 0) (n + 1) (3/4)^n = 16.
```

This closes one genuine renewal boundary channel. It does not identify the
complete signed raw numerator with that channel: the metric-coframe Gram
correction and the remaining signed leakage must still be recombined before
any norm estimate. Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and
RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The two operator-valued geometric series -/

/-- One genuine Euler-weighted radial boundary block. -/
noncomputable def primeEulerRadialGeometricBoundaryTerm
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) •
    (primeEulerRadialBoundaryStep lambda p ∘L
      ((primeEulerRadialTail lambda p) ^ n))

/-- The complete geometric radial boundary channel. -/
noncomputable def primeEulerRadialGeometricBoundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ∑' n : ℕ, primeEulerRadialGeometricBoundaryTerm lambda p n

/-- One scaled Proof 612 readout with its genuine Euler coefficient. -/
noncomputable def primeEulerRadialGeometricReadoutTerm
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) •
    newFrameAntiresonantRadialBlockReadout lambda p n

/-- The complete readout of the geometric radial boundary channel. -/
noncomputable def primeEulerRadialGeometricReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ∑' n : ℕ, primeEulerRadialGeometricReadoutTerm lambda p n

/-! ## Summability of the boundary series -/

theorem norm_primeEulerRadialTail_pow_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖(primeEulerRadialTail lambda p) ^ n‖ ≤ 1 := by
  induction n with
  | zero =>
      change ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [pow_succ']
      change ‖primeEulerRadialTail lambda p ∘L
        (primeEulerRadialTail lambda p) ^ n‖ ≤ 1
      calc
        _ ≤ ‖primeEulerRadialTail lambda p‖ *
            ‖(primeEulerRadialTail lambda p) ^ n‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := mul_le_mul
          (norm_primeEulerRadialTail_le_one lambda p) ih
          (norm_nonneg _) zero_le_one
        _ = 1 := by ring

theorem norm_primeEulerRadialBoundaryStep_comp_tail_pow_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖primeEulerRadialBoundaryStep lambda p ∘L
        ((primeEulerRadialTail lambda p) ^ n)‖ ≤ 1 := by
  calc
    _ ≤ ‖primeEulerRadialBoundaryStep lambda p‖ *
        ‖(primeEulerRadialTail lambda p) ^ n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (norm_primeEulerRadialBoundaryStep_le_one lambda p)
      (norm_primeEulerRadialTail_pow_le_one lambda p n)
      (norm_nonneg _) zero_le_one
    _ = 1 := by ring

theorem summable_primeEulerRadialGeometricBoundaryTerm
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    Summable (primeEulerRadialGeometricBoundaryTerm lambda p) := by
  let q := ccm24PrimeEulerCoefficient p
  have hq : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
  have hq_lt : q < 1 := ccm24PrimeEulerCoefficient_lt_one p
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq_lt
  have hmajorant : Summable (fun n : ℕ => q ^ (n + 1)) := by
    have hscaled := hgeom.mul_left q
    apply hscaled.congr
    intro n
    rw [pow_succ]
    ring
  apply Summable.of_norm_bounded hmajorant
  intro n
  rw [primeEulerRadialGeometricBoundaryTerm, norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left
      (norm_primeEulerRadialBoundaryStep_comp_tail_pow_le_one lambda p n)
      (pow_nonneg hq (n + 1)))

/-! ## Uniform summability of the readout -/

theorem norm_inv_primeEulerAmbientLossScale
    (p : CCM24VisiblePrime) :
    ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ =
      (1 + ccm24PrimeEulerCoefficient p) /
        Real.sqrt (ccm24PrimeEulerCoefficient p) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeEulerAmbientLossScale_pos p)]
  unfold primeEulerAmbientLossScale
  rw [inv_div]

theorem coefficient_pow_mul_norm_inv_ambientLossScale_le
    (p : CCM24VisiblePrime) (n : ℕ) :
    ccm24PrimeEulerCoefficient p ^ (n + 1) *
        ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ ≤
      2 * (3 / 4 : ℝ) ^ n := by
  let q := ccm24PrimeEulerCoefficient p
  have hq : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
  have hq_pos : 0 < q := ccm24PrimeEulerCoefficient_pos p
  have hq_bound : q ≤ (3 / 4 : ℝ) :=
    ccm24PrimeEulerCoefficient_le_three_quarters p
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq_pos
  have hsqrt_sq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hsqrt_le : Real.sqrt q ≤ 1 := by
    have hsqrt_nonneg := Real.sqrt_nonneg q
    nlinarith
  have hq_add : 1 + q ≤ 2 := by nlinarith
  have hpow : q ^ n ≤ (3 / 4 : ℝ) ^ n := by
    gcongr
  have hq_div_sqrt : q / Real.sqrt q = Real.sqrt q := by
    calc
      q / Real.sqrt q = Real.sqrt q ^ 2 / Real.sqrt q := by
        rw [hsqrt_sq]
      _ = Real.sqrt q := by
        field_simp [ne_of_gt hsqrt_pos]
  rw [norm_inv_primeEulerAmbientLossScale]
  change q ^ (n + 1) * ((1 + q) / Real.sqrt q) ≤ _
  have hrewrite :
      q ^ (n + 1) * ((1 + q) / Real.sqrt q) =
        Real.sqrt q * (1 + q) * q ^ n := by
    rw [pow_succ]
    calc
      q ^ n * q * ((1 + q) / Real.sqrt q) =
          q ^ n * (1 + q) * (q / Real.sqrt q) := by ring
      _ = Real.sqrt q * (1 + q) * q ^ n := by
        rw [hq_div_sqrt]
        ring
  rw [hrewrite]
  calc
    Real.sqrt q * (1 + q) * q ^ n ≤
        (1 * 2) * (3 / 4 : ℝ) ^ n := by
      exact mul_le_mul
        (mul_le_mul hsqrt_le hq_add (by positivity) zero_le_one)
        hpow (pow_nonneg hq n) (by norm_num)
    _ = 2 * (3 / 4 : ℝ) ^ n := by ring

theorem norm_primeEulerRadialGeometricReadoutTerm_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖primeEulerRadialGeometricReadoutTerm lambda p n‖ ≤
      2 * ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n := by
  have hq := ccm24PrimeEulerCoefficient_nonneg p
  rw [primeEulerRadialGeometricReadoutTerm, norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  calc
    ccm24PrimeEulerCoefficient p ^ (n + 1) *
          ‖newFrameAntiresonantRadialBlockReadout lambda p n‖ ≤
        ccm24PrimeEulerCoefficient p ^ (n + 1) *
          (‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left
        (norm_newFrameAntiresonantRadialBlockReadout_le lambda p n)
        (pow_nonneg hq _)
    _ = (ccm24PrimeEulerCoefficient p ^ (n + 1) *
          ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖) *
        ((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (2 * (3 / 4 : ℝ) ^ n) * ((n + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (coefficient_pow_mul_norm_inv_ambientLossScale_le p n)
        (Nat.cast_nonneg _)
    _ = 2 * ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n := by ring

theorem summable_linear_three_quarters :
    Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) := by
  simpa using
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := (3 / 4 : ℝ)) (by norm_num))

theorem tsum_linear_three_quarters :
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n = 16 := by
  calc
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n =
        ((1 - (3 / 4 : ℝ)) ^ 2)⁻¹ := by
      simpa using
        (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
          (r := (3 / 4 : ℝ)) (by norm_num))
    _ = 16 := by norm_num

theorem summable_primeEulerRadialGeometricReadoutTerm
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    Summable (primeEulerRadialGeometricReadoutTerm lambda p) := by
  have hmajorant := summable_linear_three_quarters.mul_left 2
  apply Summable.of_norm_bounded hmajorant
  intro n
  simpa only [mul_assoc] using
    norm_primeEulerRadialGeometricReadoutTerm_le lambda p n

theorem norm_primeEulerRadialGeometricReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖primeEulerRadialGeometricReadout lambda p‖ ≤ 32 := by
  let term := primeEulerRadialGeometricReadoutTerm lambda p
  have hterm : Summable term :=
    summable_primeEulerRadialGeometricReadoutTerm lambda p
  have hmajorant : Summable (fun n : ℕ =>
      2 * (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n)) :=
    summable_linear_three_quarters.mul_left 2
  have hpoint : ∀ n : ℕ,
      ‖term n‖ ≤ 2 * (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) := by
    intro n
    simpa only [term, mul_assoc] using
      norm_primeEulerRadialGeometricReadoutTerm_le lambda p n
  have hnorm : Summable (fun n : ℕ => ‖term n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (term n))
      hpoint hmajorant
  unfold primeEulerRadialGeometricReadout
  calc
    ‖∑' n : ℕ, term n‖ ≤ ∑' n : ℕ, ‖term n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        2 * (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) :=
      hnorm.tsum_le_tsum hpoint hmajorant
    _ = 2 * (∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) := by
      rw [tsum_mul_left]
    _ = 32 := by rw [tsum_linear_three_quarters]; norm_num

/-! ## Exact readout on every actual new suffix frame -/

theorem primeEulerRadialGeometricReadout_comp_ambientLossColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    primeEulerRadialGeometricReadout lambda p ∘L
        newFrameAntiresonantColumn lambda p S =
      primeEulerRadialGeometricBoundary lambda p ∘L
        newSuffixFrame lambda S := by
  have hreadout :=
    summable_primeEulerRadialGeometricReadoutTerm lambda p
  have hboundary :=
    summable_primeEulerRadialGeometricBoundaryTerm lambda p
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerRadialGeometricReadout,
    primeEulerRadialGeometricBoundary, ContinuousLinearMap.comp_apply]
  have hleft :
      (∑' n : ℕ, primeEulerRadialGeometricReadoutTerm lambda p n)
          (newFrameAntiresonantColumn lambda p S x) =
        ∑' n : ℕ, primeEulerRadialGeometricReadoutTerm lambda p n
          (newFrameAntiresonantColumn lambda p S x) := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier
        (newFrameAntiresonantColumn lambda p S x)).map_tsum hreadout
  have hright :
      (∑' n : ℕ, primeEulerRadialGeometricBoundaryTerm lambda p n)
          (newSuffixFrame lambda S x) =
        ∑' n : ℕ, primeEulerRadialGeometricBoundaryTerm lambda p n
          (newSuffixFrame lambda S x) := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier
        (newSuffixFrame lambda S x)).map_tsum hboundary
  rw [hleft, hright]
  apply tsum_congr
  intro n
  have hblock := DFunLike.congr_fun
    (newFrameAntiresonantRadialBlockReadout_comp_column
      lambda p S n) x
  simp only [primeEulerRadialGeometricReadoutTerm,
    primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  exact congrArg
    (fun y : finiteSCarrier =>
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) • y) hblock

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
end CCM25Concrete
end Source
end ConnesWeilRH
