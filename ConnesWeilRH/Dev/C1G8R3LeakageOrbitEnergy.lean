/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageOrthonormalOrbit

namespace ConnesWeilRH
namespace Dev

open Filter
open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CompactLogConvolution
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open C1SameOwnerWeil
open scoped Topology

local notation "Carrier" => finiteSCarrier

/-- The actual unit-scale leakage output on the normalized separated
translation orbit. -/
noncomputable def normalizedSelectedSourceTranslationLeakageColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  (((‖owner.sourceTest.test.toLp 2‖⁻¹ : ℝ) : ℂ) •
    unitSourceTestTranslationLeakageColumn owner
      (n * selectedSourceTranslationSpacing owner))

private theorem normalizedSelectedSourceTranslationLeakageColumn_actual_eq_smul
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) :
    sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale
        (normalizedSelectedSourceTranslationOrbit owner n) =
      (((‖owner.sourceTest.test.toLp 2‖⁻¹ : ℝ) : ℂ) •
        unitSourceTestTranslationLeakageColumn owner
          (n * selectedSourceTranslationSpacing owner)) := by
  have hcenter : selectedSourceTranslationCenter owner n =
      ((n * selectedSourceTranslationSpacing owner : ℕ) : ℝ) := by
    simp [selectedSourceTranslationCenter, Nat.cast_mul]
  rw [normalizedSelectedSourceTranslationOrbit, map_smul,
    selectedSourceTranslationOrbit, hcenter,
    unitSourceTestTranslationLeakageColumn]

/-- The normalized energy column is exactly the actual leakage operator
applied to the normalized separated translation orbit. -/
theorem normalizedSelectedSourceTranslationLeakageColumn_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) :
    normalizedSelectedSourceTranslationLeakageColumn owner n =
      sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale
        (normalizedSelectedSourceTranslationOrbit owner n) := by
  exact (normalizedSelectedSourceTranslationLeakageColumn_actual_eq_smul
    owner n).symm

private theorem normalizedSelectedSourceTranslationLeakageColumn_norm_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    (n : ℕ) :
    ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ =
      ‖owner.sourceTest.test.toLp 2‖⁻¹ *
        ‖unitSourceTestTranslationLeakageColumn owner
          (n * selectedSourceTranslationSpacing owner)‖ := by
  rw [normalizedSelectedSourceTranslationLeakageColumn,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (selectedSourceTestLp_norm_pos owner rho hvalue))]

private theorem inv_mul_half_eq_div (a b : ℝ) (ha : a ≠ 0) :
    a⁻¹ * (b / 2) = b / (2 * a) := by
  field_simp [ha]

private theorem inv_mul_half_lower_bound
    (a b x : ℝ) (ha : 0 < a) (hx : b / 2 ≤ x) :
    b / (2 * a) ≤ a⁻¹ * x := by
  calc
    b / (2 * a) = a⁻¹ * (b / 2) :=
      (inv_mul_half_eq_div a b ha.ne').symm
    _ ≤ a⁻¹ * x :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr ha.le)

-- Reindexing the eventual translated lower bound by the integer spacing.
private theorem unitSourceTestTranslationLeakageColumn_spacing_norm_lowerBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    ∀ᶠ n in atTop,
      ‖unitSourceTestTranslationLeakageColumn owner
        (n * selectedSourceTranslationSpacing owner)‖ ≥
          sourceTestRootImageNorm owner / 2 := by
  have hraw :=
    sourceRootCompletedRightCommutatorLeftLeg_sourceTest_translate_norm_lowerBound
      owner rho hvalue
  have hspacing : 0 < selectedSourceTranslationSpacing owner := by
    unfold selectedSourceTranslationSpacing
    exact Nat.succ_pos _
  have hscaled : Tendsto
      (fun n : ℕ => n * selectedSourceTranslationSpacing owner) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (Nat.le_mul_of_pos_right n hspacing)
  exact hscaled.eventually hraw

set_option maxHeartbeats 500000 in
-- The selected L2 normalization requires reducing the subtype norm once.
private theorem normalizedSelectedSourceTranslationLeakageColumn_norm_ge_of_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    (n : ℕ)
    (hraw : ‖unitSourceTestTranslationLeakageColumn owner
      (n * selectedSourceTranslationSpacing owner)‖ ≥
        sourceTestRootImageNorm owner / 2) :
    ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ≥
      sourceTestRootImageNorm owner /
        (2 * ‖owner.sourceTest.test.toLp 2‖) := by
  have hsource := selectedSourceTestLp_norm_pos owner rho hvalue
  rw [normalizedSelectedSourceTranslationLeakageColumn_norm_eq owner rho hvalue n]
  exact inv_mul_half_lower_bound _ _ _ hsource hraw

/-- The actual leakage output on the normalized separated orbit retains a
uniform positive norm lower bound. -/
theorem normalizedSelectedSourceTranslationLeakageColumn_norm_lowerBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    ∀ᶠ n in atTop,
      ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ≥
        sourceTestRootImageNorm owner /
          (2 * ‖owner.sourceTest.test.toLp 2‖) := by
  have hraw := unitSourceTestTranslationLeakageColumn_spacing_norm_lowerBound
    owner rho hvalue
  filter_upwards [hraw] with n hrawn
  exact normalizedSelectedSourceTranslationLeakageColumn_norm_ge_of_raw
    owner rho hvalue n hrawn

/-- The squared output norms of the actual unit-scale leakage leg are not
summable on this normalized orthonormal input sequence. This is an ambient
carrier result and does not assert the G8 source-compressed diagonal identity. -/
theorem normalizedSelectedSourceTranslationLeakageColumn_energy_not_summable
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    ¬ Summable (fun n : ℕ =>
      ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ^ 2) := by
  have hsource := selectedSourceTestLp_norm_pos owner rho hvalue
  have hroot := sourceTestRootImageNorm_pos owner rho hvalue
  have hpositive : 0 < sourceTestRootImageNorm owner /
      (2 * ‖owner.sourceTest.test.toLp 2‖) := by positivity
  have hlower := normalizedSelectedSourceTranslationLeakageColumn_norm_lowerBound
    owner rho hvalue
  have hlowerSq : ∀ᶠ n in atTop,
      (sourceTestRootImageNorm owner /
        (2 * ‖owner.sourceTest.test.toLp 2‖)) ^ 2 ≤
          ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ^ 2 := by
    filter_upwards [hlower] with n hn
    nlinarith [sq_nonneg
      (‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ -
        sourceTestRootImageNorm owner /
          (2 * ‖owner.sourceTest.test.toLp 2‖))]
  intro hsum
  have hzero := hsum.tendsto_atTop_zero
  have hsmall := hzero.eventually_lt_const (sq_pos_of_pos hpositive)
  obtain ⟨n, hlarge, hsmall⟩ := (hlowerSq.and hsmall).exists
  linarith

end Dev
end ConnesWeilRH
