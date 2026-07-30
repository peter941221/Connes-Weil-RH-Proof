/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit

/-!
# Radial block recurrence for the antiresonant Bone 1 column

Let `E` be the genuine radial-support projection, `U` translation by
`log(p)`, `V = E U E`, and `C = (I - E) U E`. On every radial vector `u`,
the complete unscaled antiresonant column has the two pieces

```text
E (I + U) u       = u + V u,
(I - E) (I + U) u = C u.
```

The recursively defined readouts

```text
B_0     = I - E,
B_(n+1) = C V^n E - B_n
```

therefore recover every successive radial boundary block exactly:

```text
B_n (I + U) u = C V^n u.
```

After division by the strictly positive ambient-loss scalar, the same
identity reads every block directly from the actual new-frame ambient-loss
column. The readout cost is at most linear: `||B_n|| <= n + 1`.

This is a denominator decomposition only. It does not show that the actual
signed numerator is a finite or summable combination of these blocks, and it
does not construct the missing uniform Bone 1 factor, close Gate 3U, prove the
finite-S sign, supply Burnol's identity, or prove RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The radial core, tail, and boundary operators -/

/-- The orthogonal complement of the genuine radial-support projection. -/
noncomputable def radialComplement
    (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda

/-- The unscaled antiresonant core `I + U_(log p)`. -/
noncomputable def primeEulerAntiresonantCore
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ContinuousLinearMap.id ℂ finiteSCarrier +
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap

/-- The part of one positive translation which remains in the radial
half-line. -/
noncomputable def primeEulerRadialTail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
      radialSupportProjection lambda

/-- The part of one positive translation which exits the radial half-line. -/
noncomputable def primeEulerRadialBoundaryStep
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialComplement lambda ∘L
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
      radialSupportProjection lambda

/-- Alternating readouts which recover successive radial boundary blocks
from the complete antiresonant core. -/
noncomputable def primeEulerRadialBlockReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ℕ → finiteSCarrier →L[ℂ] finiteSCarrier
  | 0 => radialComplement lambda
  | n + 1 =>
      primeEulerRadialBoundaryStep lambda p ∘L
          ((primeEulerRadialTail lambda p) ^ n) ∘L
            radialSupportProjection lambda -
        primeEulerRadialBlockReadout lambda p n

/-- The block readout after division by the genuine ambient-loss scalar. -/
noncomputable def newFrameAntiresonantRadialBlockReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((primeEulerAmbientLossScale p : ℂ)⁻¹) •
    primeEulerRadialBlockReadout lambda p n

/-! ## Exact recurrence -/

theorem radialComplement_apply_eq_zero_of_fixed
    (lambda : CCM24SoninScale) {u : finiteSCarrier}
    (hfixed : radialSupportProjection lambda u = u) :
    radialComplement lambda u = 0 := by
  simp only [radialComplement, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, hfixed, sub_self]

theorem radialSupportProjection_antiresonantCore_apply_of_fixed
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : finiteSCarrier}
    (hfixed : radialSupportProjection lambda u = u) :
    radialSupportProjection lambda (primeEulerAntiresonantCore p u) =
      u + primeEulerRadialTail lambda p u := by
  simp only [primeEulerAntiresonantCore, primeEulerRadialTail,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, hfixed]

theorem radialComplement_antiresonantCore_apply_of_fixed
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : finiteSCarrier}
    (hfixed : radialSupportProjection lambda u = u) :
    radialComplement lambda (primeEulerAntiresonantCore p u) =
      primeEulerRadialBoundaryStep lambda p u := by
  simp only [radialComplement, primeEulerAntiresonantCore,
    primeEulerRadialBoundaryStep, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, hfixed]
  abel

theorem primeEulerRadialTailIterate_succ_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (n : ℕ) (u : finiteSCarrier) :
    ((primeEulerRadialTail lambda p) ^ (n + 1)) u =
      ((primeEulerRadialTail lambda p) ^ n)
        (primeEulerRadialTail lambda p u) := by
  rw [pow_succ, ContinuousLinearMap.mul_apply]

/-- Every readout recovers one successive boundary block. The radial fixed
point condition is essential; no whole-space inverse of `I + U` is used. -/
theorem primeEulerRadialBlockReadout_antiresonantCore_apply_of_fixed
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (n : ℕ) {u : finiteSCarrier}
    (hfixed : radialSupportProjection lambda u = u) :
    primeEulerRadialBlockReadout lambda p n
        (primeEulerAntiresonantCore p u) =
      primeEulerRadialBoundaryStep lambda p
        (((primeEulerRadialTail lambda p) ^ n) u) := by
  induction n with
  | zero =>
      simpa only [primeEulerRadialBlockReadout, pow_zero,
        ContinuousLinearMap.one_apply] using
        radialComplement_antiresonantCore_apply_of_fixed lambda p hfixed
  | succ n ih =>
      simp only [primeEulerRadialBlockReadout,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
      rw [radialSupportProjection_antiresonantCore_apply_of_fixed
        lambda p hfixed]
      rw [map_add, map_add, ih]
      rw [← primeEulerRadialTailIterate_succ_apply lambda p n u]
      abel

/-! ## Readback on the actual ambient-loss column -/

theorem primeEulerAmbientLossScale_pos (p : CCM24VisiblePrime) :
    0 < primeEulerAmbientLossScale p := by
  unfold primeEulerAmbientLossScale
  exact div_pos
    (Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos p))
    (by linarith [ccm24PrimeEulerCoefficient_pos p])

theorem newFrameAntiresonantColumn_eq_scale_smul_core
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    newFrameAntiresonantColumn lambda p S =
      (primeEulerAmbientLossScale p : ℂ) •
        (primeEulerAntiresonantCore p ∘L newSuffixFrame lambda S) := by
  rw [newFrameAntiresonantColumn, primeEulerAmbientLossFactor_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerAntiresonantCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply]

/-- The scaled recurrence reads the `n`th radial boundary block from the
actual ambient-loss column on every genuine new suffix frame. -/
theorem newFrameAntiresonantRadialBlockReadout_comp_column
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (n : ℕ) :
    newFrameAntiresonantRadialBlockReadout lambda p n ∘L
        newFrameAntiresonantColumn lambda p S =
      primeEulerRadialBoundaryStep lambda p ∘L
          ((primeEulerRadialTail lambda p) ^ n) ∘L
        newSuffixFrame lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed :
      radialSupportProjection lambda (newSuffixFrame lambda S x) =
        newSuffixFrame lambda S x := by
    have h := DFunLike.congr_fun
      (radialSupportProjection_comp_newSuffixFrame lambda S) x
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hblock :=
    primeEulerRadialBlockReadout_antiresonantCore_apply_of_fixed
      lambda p n hfixed
  have hcolumn := DFunLike.congr_fun
    (newFrameAntiresonantColumn_eq_scale_smul_core lambda p S) x
  have hscaleReal : primeEulerAmbientLossScale p ≠ 0 :=
    ne_of_gt (primeEulerAmbientLossScale_pos p)
  have hscale : (primeEulerAmbientLossScale p : ℂ) ≠ 0 := by
    exact_mod_cast hscaleReal
  simp only [ContinuousLinearMap.comp_apply,
    newFrameAntiresonantRadialBlockReadout,
    ContinuousLinearMap.smul_apply] at hcolumn ⊢
  rw [hcolumn, map_smul, smul_smul, inv_mul_cancel₀ hscale, one_smul]
  exact hblock

/-! ## Quantitative readout cost -/

theorem norm_radialSupportProjection_le_one
    (lambda : CCM24SoninScale) :
    ‖radialSupportProjection lambda‖ ≤ 1 :=
  IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)

theorem norm_radialComplement_le_one
    (lambda : CCM24SoninScale) :
    ‖radialComplement lambda‖ ≤ 1 := by
  exact IsStarProjection.norm_le _
    (radialSupportProjection_isStarProjection lambda).one_sub

theorem norm_primeEulerPositiveTranslation_le_one
    (p : CCM24VisiblePrime) :
    ‖(cc20GlobalLogTranslation
      (Real.log p)).toContinuousLinearMap‖ ≤ 1 :=
  (cc20GlobalLogTranslation (Real.log p)).norm_toContinuousLinearMap_le

private theorem norm_threefold_comp_le_one
    (A B C : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖A ∘L B ∘L C‖ ≤ 1 := by
  have hAB : ‖A ∘L B‖ ≤ 1 := by
    calc
      _ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  calc
    _ ≤ ‖A ∘L B‖ * ‖C‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hAB hC (norm_nonneg _) zero_le_one
    _ = 1 := by ring

theorem norm_primeEulerRadialTail_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖primeEulerRadialTail lambda p‖ ≤ 1 := by
  have hE := norm_radialSupportProjection_le_one lambda
  have hU := norm_primeEulerPositiveTranslation_le_one p
  exact norm_threefold_comp_le_one _ _ _ hE hU hE

theorem norm_primeEulerRadialBoundaryStep_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖primeEulerRadialBoundaryStep lambda p‖ ≤ 1 := by
  have hC := norm_radialComplement_le_one lambda
  have hE := norm_radialSupportProjection_le_one lambda
  have hU := norm_primeEulerPositiveTranslation_le_one p
  exact norm_threefold_comp_le_one _ _ _ hC hU hE

theorem norm_primeEulerRadialBlockReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖primeEulerRadialBlockReadout lambda p n‖ ≤ (n : ℝ) + 1 := by
  induction n with
  | zero =>
      simpa only [primeEulerRadialBlockReadout, Nat.cast_zero, zero_add]
        using norm_radialComplement_le_one lambda
  | succ n ih =>
      have hE := norm_radialSupportProjection_le_one lambda
      have hC := norm_primeEulerRadialBoundaryStep_le_one lambda p
      have hV := norm_primeEulerRadialTail_le_one lambda p
      have hVpowAll : ∀ k : ℕ,
          ‖(primeEulerRadialTail lambda p) ^ k‖ ≤ 1 := by
        intro k
        induction k with
        | zero =>
            change ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1
            exact ContinuousLinearMap.norm_id_le
        | succ k hk =>
            rw [pow_succ']
            change ‖primeEulerRadialTail lambda p ∘L
              (primeEulerRadialTail lambda p) ^ k‖ ≤ 1
            calc
              _ ≤ ‖primeEulerRadialTail lambda p‖ *
                  ‖(primeEulerRadialTail lambda p) ^ k‖ :=
                ContinuousLinearMap.opNorm_comp_le _ _
              _ ≤ 1 * 1 :=
                mul_le_mul hV hk (norm_nonneg _) zero_le_one
              _ = 1 := by ring
      have hVpow := hVpowAll n
      have hterm :
          ‖primeEulerRadialBoundaryStep lambda p ∘L
              ((primeEulerRadialTail lambda p) ^ n) ∘L
                radialSupportProjection lambda‖ ≤ 1 := by
        exact norm_threefold_comp_le_one _ _ _ hC hVpow hE
      rw [primeEulerRadialBlockReadout]
      calc
        ‖primeEulerRadialBoundaryStep lambda p ∘L
              ((primeEulerRadialTail lambda p) ^ n) ∘L
                radialSupportProjection lambda -
            primeEulerRadialBlockReadout lambda p n‖ ≤
          ‖primeEulerRadialBoundaryStep lambda p ∘L
              ((primeEulerRadialTail lambda p) ^ n) ∘L
                radialSupportProjection lambda‖ +
            ‖primeEulerRadialBlockReadout lambda p n‖ := norm_sub_le _ _
        _ ≤ 1 + ((n : ℝ) + 1) := add_le_add hterm ih
        _ = ((n + 1 : ℕ) : ℝ) + 1 := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring

theorem norm_newFrameAntiresonantRadialBlockReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖newFrameAntiresonantRadialBlockReadout lambda p n‖ ≤
      ‖(primeEulerAmbientLossScale p : ℂ)⁻¹‖ * ((n : ℝ) + 1) := by
  rw [newFrameAntiresonantRadialBlockReadout, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_primeEulerRadialBlockReadout_le lambda p n) (norm_nonneg _)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
end CCM25Concrete
end Source
end ConnesWeilRH
