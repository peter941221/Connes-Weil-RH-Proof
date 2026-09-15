/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageTranslateLowerBound

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CompactLogConvolution
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open C1SameOwnerWeil
open scoped Topology

local notation "Carrier" => finiteSCarrier

/-- Integer spacing wider than the diameter of the selected compact source
test. -/
noncomputable def selectedSourceTranslationSpacing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : ℕ :=
  Nat.ceil (2 * supportRadius owner.sourceTest) + 1

/-- The center of the `n`th right translation in the separated orbit. -/
noncomputable def selectedSourceTranslationCenter
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : ℝ :=
  (n : ℝ) * (selectedSourceTranslationSpacing owner : ℝ)

/-- Right translates of the selected compact source test, spaced so their
supports are disjoint. -/
noncomputable def selectedSourceTranslationOrbit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  cc20GlobalLogTranslation (-(selectedSourceTranslationCenter owner n))
    (owner.sourceTest.test.toLp 2)

/-- Normalize the separated translation orbit in the ambient global `L2`
carrier. -/
noncomputable def normalizedSelectedSourceTranslationOrbit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  (((‖owner.sourceTest.test.toLp 2‖⁻¹ : ℝ) : ℂ) •
    selectedSourceTranslationOrbit owner n)

private theorem selectedSourceTranslationSpacing_pos
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    0 < selectedSourceTranslationSpacing owner := by
  exact Nat.succ_pos _

private theorem selectedSourceTranslationSpacing_gt_diameter
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    2 * supportRadius owner.sourceTest <
      (selectedSourceTranslationSpacing owner : ℝ) := by
  have hceil : 2 * supportRadius owner.sourceTest ≤
      (Nat.ceil (2 * supportRadius owner.sourceTest) : ℝ) := Nat.le_ceil _
  dsimp [selectedSourceTranslationSpacing]
  push_cast
  linarith

private theorem inner_compactSource_globalLogTranslation_eq_zero
    (f : SchwartzMap ℝ ℂ) (R d : ℝ)
    (hsupp : Function.support f ⊆ Set.Icc (-R) R)
    (hgap : 2 * R < d) :
    inner ℂ (f.toLp 2) (cc20GlobalLogTranslation d (f.toLp 2)) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  have hshift :=
    (measurePreserving_add_right (volume : Measure ℝ) d).quasiMeasurePreserving.ae_eq
      (SchwartzMap.coeFn_toLp f 2)
  filter_upwards [SchwartzMap.coeFn_toLp f 2,
    cc20GlobalLogTranslation_coeFn d (f.toLp 2), hshift] with x hfx htranslation hshiftx
  have hshiftx' : (f.toLp 2 : ℝ → ℂ) (x + d) = f (x + d) := by
    simpa only [Function.comp_apply] using hshiftx
  rw [hfx, htranslation, hshiftx']
  by_cases hzero : f x = 0
  · simp only [hzero, inner_zero_left, Pi.zero_apply]
  by_cases hshiftZero : f (x + d) = 0
  · simp only [hshiftZero, inner_zero_right, Pi.zero_apply]
  exfalso
  have hxmem : x ∈ Function.support f := by
    simpa only [Function.mem_support] using hzero
  have hshiftMem : x + d ∈ Function.support f := by
    simpa only [Function.mem_support] using hshiftZero
  have hx := hsupp hxmem
  have hshift := hsupp hshiftMem
  linarith [hx.1, hshift.2]

private theorem selectedSourceTranslationOrbit_inner_eq_zero_of_lt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {i j : ℕ}
    (hij : i < j) :
    inner ℂ (selectedSourceTranslationOrbit owner i)
      (selectedSourceTranslationOrbit owner j) = 0 := by
  let u : Carrier := owner.sourceTest.test.toLp 2
  let a : ℝ := selectedSourceTranslationCenter owner i
  let b : ℝ := selectedSourceTranslationCenter owner j
  let d : ℝ := b - a
  have hstep : 0 < (selectedSourceTranslationSpacing owner : ℝ) :=
    Nat.cast_pos.mpr (selectedSourceTranslationSpacing_pos owner)
  have hstepGap : 2 * supportRadius owner.sourceTest <
      (selectedSourceTranslationSpacing owner : ℝ) :=
    selectedSourceTranslationSpacing_gt_diameter owner
  have hfactor : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hij)
  have hcenters : a + (selectedSourceTranslationSpacing owner : ℝ) ≤ b := by
    dsimp [a, b, selectedSourceTranslationCenter]
    calc
      (i : ℝ) * (selectedSourceTranslationSpacing owner : ℝ) +
          (selectedSourceTranslationSpacing owner : ℝ) =
        ((i : ℝ) + 1) * (selectedSourceTranslationSpacing owner : ℝ) := by ring
      _ ≤ (j : ℝ) * (selectedSourceTranslationSpacing owner : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor hstep.le
  have hgap : 2 * supportRadius owner.sourceTest < d := by
    dsimp [d]
    exact lt_of_lt_of_le hstepGap (by linarith)
  have hshiftFirst :
      cc20GlobalLogTranslation b
          (cc20GlobalLogTranslation (-a) u) =
        cc20GlobalLogTranslation d u := by
    rw [cc20GlobalLogTranslation_add_apply]
    simpa [d, sub_eq_add_neg]
  have hshiftSecond :
      cc20GlobalLogTranslation b (cc20GlobalLogTranslation (-b) u) = u :=
    cc20GlobalLogTranslation_neg_apply b u
  have hisometry := (cc20GlobalLogTranslation b).inner_map_map
    (selectedSourceTranslationOrbit owner i)
    (selectedSourceTranslationOrbit owner j)
  calc
    inner ℂ (selectedSourceTranslationOrbit owner i)
        (selectedSourceTranslationOrbit owner j) =
      inner ℂ (cc20GlobalLogTranslation b
          (selectedSourceTranslationOrbit owner i))
        (cc20GlobalLogTranslation b
          (selectedSourceTranslationOrbit owner j)) := hisometry.symm
    _ = inner ℂ (cc20GlobalLogTranslation d u) u := by
      rw [selectedSourceTranslationOrbit, selectedSourceTranslationOrbit,
        hshiftFirst, hshiftSecond]
    _ = 0 := by
      have hzero := inner_compactSource_globalLogTranslation_eq_zero
        owner.sourceTest.test (supportRadius owner.sourceTest) d
        (support_subset_Icc owner.sourceTest) hgap
      rw [← inner_conj_symm (x := cc20GlobalLogTranslation d u)
        (y := u)]
      simpa only [u, hzero, map_zero]

/-- Nonzero Laplace detection forces the selected source test to have
positive ambient L2 norm. -/
theorem selectedSourceTestLp_norm_pos
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    0 < ‖owner.sourceTest.test.toLp 2‖ := by
  have htest := selectedOwnerSourceTest_ne_zero_of_laplaceAt_ne_zero
    owner rho hvalue
  have hLp : owner.sourceTest.test.toLp 2 ≠ 0 := by
    intro hzero
    apply htest
    apply (SchwartzMap.injective_toLp 2)
    simpa using hzero
  exact norm_pos_iff.mpr hLp

private theorem normalizedSelectedSourceTranslationOrbit_norm_eq_one
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    (n : ℕ) :
    ‖normalizedSelectedSourceTranslationOrbit owner n‖ = 1 := by
  have hu := selectedSourceTestLp_norm_pos owner rho hvalue
  rw [normalizedSelectedSourceTranslationOrbit, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu),
    selectedSourceTranslationOrbit, norm_cc20GlobalLogTranslation]
  exact inv_mul_cancel₀ hu.ne'

/-- The normalized, sufficiently separated right translations of the selected
compact source test form an orthonormal sequence in the ambient carrier. -/
theorem normalizedSelectedSourceTranslationOrbit_orthonormal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    Orthonormal ℂ (normalizedSelectedSourceTranslationOrbit owner) := by
  constructor
  · intro n
    exact normalizedSelectedSourceTranslationOrbit_norm_eq_one owner rho hvalue n
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hzero := selectedSourceTranslationOrbit_inner_eq_zero_of_lt owner hlt
      simp only [normalizedSelectedSourceTranslationOrbit,
        inner_smul_left, inner_smul_right, hzero, map_zero, mul_zero, zero_mul]
    · have hzero := selectedSourceTranslationOrbit_inner_eq_zero_of_lt owner hgt
      have hzero' : inner ℂ (selectedSourceTranslationOrbit owner i)
          (selectedSourceTranslationOrbit owner j) = 0 := by
        rw [← inner_conj_symm]
        simp [hzero]
      simp only [normalizedSelectedSourceTranslationOrbit,
        inner_smul_left, inner_smul_right, hzero', map_zero, mul_zero, zero_mul]

end Dev
end ConnesWeilRH
