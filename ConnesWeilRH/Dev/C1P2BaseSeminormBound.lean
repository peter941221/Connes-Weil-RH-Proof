/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Dev.C1HealthyYoshidaAffineCorrection
import ConnesWeilRH.Dev.C1CompactLogL2Export

/-!
# Quantitative zero-order seminorm bound for finite-window bases

This module exposes the missing quantitative interface behind the geometric
contraction route.  A compact-log pullback is bounded by the source test's
zero-order Schwartz seminorm, and a finite windowed combination is bounded by
the coefficient-weighted sum of its basis seminorms.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BaseSeminormBound

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open CCM25Concrete.SelectedYoshidaBridge
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaAffineCorrection
open C1CompactLogL2Export
open MeasureTheory

noncomputable section

theorem compactLogTestOfWindow_seminorm_zero_zero_le_source
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : Real =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b) :
    SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow g ha hb hsupport).test ≤
      SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode g) := by
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro x
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
    compactLogTestOfWindow_apply] using
    (SchwartzMap.norm_le_seminorm Complex
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g) (Real.exp x))

theorem source_combination_seminorm_zero_zero_le_coeff_weighted_sum
    {a b : Real}
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex) :
    SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode
          (windowedPositiveIntervalCompactTestCombination c)) ≤
      (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
  classical
  apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
  intro x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
  rw [show normalizedCC20ConcreteTestAlgebra.legacy.encode
      (windowedPositiveIntervalCompactTestCombination c) =
        ∑ p ∈ c.support,
          c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test by
    unfold windowedPositiveIntervalCompactTestCombination
    unfold positiveIntervalCompactTestCombination
    simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
    rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective]
    rw [Finsupp.sum]]
  calc
    ‖(∑ p ∈ c.support,
        c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ =
        ‖∑ p ∈ c.support,
          (c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ := by
      simp only [SchwartzMap.sum_apply]
    _ ≤
        ∑ p ∈ c.support,
          ‖(c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ c.support,
          ‖c p‖ *
            ‖normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test x‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [smul_eq_mul, norm_mul]
    _ ≤ ∑ p ∈ c.support,
          ‖c p‖ *
            SchwartzMap.seminorm Complex 0 0
              (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_le_seminorm Complex
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) x)
        (norm_nonneg _)

/-! A uniform coefficient and basis bound converts the exact finite budget into
an explicit cardinality product.  This is still a quantitative premise for the
selected right inverse, but it exposes the remaining obligation term by term. -/
theorem source_combination_seminorm_zero_zero_le_card_mul_uniform_budget
    {a b : Real}
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    {coeffBound basisBound : Real}
    (hcoeff_nonneg : 0 ≤ coeffBound)
    (hbasis_nonneg : 0 ≤ basisBound)
    (hcoeff : ∀ p ∈ c.support, ‖c p‖ ≤ coeffBound)
    (hbasis : ∀ p ∈ c.support,
      SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) ≤ basisBound) :
    (∑ p ∈ c.support,
      ‖c p‖ *
        SchwartzMap.seminorm Complex 0 0
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
      (c.support.card : Real) * coeffBound * basisBound := by
  calc
    (∑ p ∈ c.support,
      ‖c p‖ *
        SchwartzMap.seminorm Complex 0 0
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
        ∑ p ∈ c.support, coeffBound * basisBound := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul (hcoeff p hp) (hbasis p hp)
        (by positivity) hcoeff_nonneg
    _ = (c.support.card : Real) * coeffBound * basisBound := by
      simp [Finset.sum_const]
      ring

theorem compactLogTestOfWindow_combination_seminorm_zero_zero_le_coeff_weighted_sum
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex) :
    SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test ≤
      (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
  exact (compactLogTestOfWindow_seminorm_zero_zero_le_source
    (windowedPositiveIntervalCompactTestCombination c) ha hb
    (windowedPositiveIntervalCompactTestCombination_support_subset c)).trans
    (source_combination_seminorm_zero_zero_le_coeff_weighted_sum c)

theorem strict_base_contraction_of_coeff_weighted_budget
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    {budget : Real}
    (hbudget :
      2 *
          (∑ p ∈ c.support,
            ‖c p‖ *
              SchwartzMap.seminorm Complex 0 0
                (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) <
        budget)
    (hbudget_half : budget ≤ 1 / 2) :
    2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test <
      1 := by
  have hbound :=
    compactLogTestOfWindow_combination_seminorm_zero_zero_le_coeff_weighted_sum
      ha hb c
  have hscaled := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : Real) ≤ 2)
  have hlt :
      2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test <
        budget := by
    exact hscaled.trans_lt hbudget
  linarith

theorem strict_base_contraction_of_uniform_coeff_basis_budget
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    {coeffBound basisBound budget : Real}
    (hcoeff_nonneg : 0 ≤ coeffBound)
    (hbasis_nonneg : 0 ≤ basisBound)
    (hcoeff : ∀ p ∈ c.support, ‖c p‖ ≤ coeffBound)
    (hbasis : ∀ p ∈ c.support,
      SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) ≤ basisBound)
    (hbudget :
      2 * (c.support.card : Real) * coeffBound * basisBound < budget)
    (hbudget_half : budget ≤ 1 / 2) :
    2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination c) ha hb
          (windowedPositiveIntervalCompactTestCombination_support_subset c)).test <
      1 := by
  have hsum := source_combination_seminorm_zero_zero_le_card_mul_uniform_budget
    c hcoeff_nonneg hbasis_nonneg hcoeff hbasis
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by norm_num : (0 : Real) ≤ 2)
  have hfinite :
      2 * (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) < budget := by
    have hbudget' :
        2 * ((c.support.card : Real) * coeffBound * basisBound) < budget := by
      convert hbudget using 1 <;> ring
    exact hscaled.trans_lt hbudget'
  exact strict_base_contraction_of_coeff_weighted_budget
    ha hb c hfinite hbudget_half

theorem sparseWindowedMellinCorrection_weighted_budget_le_node_card
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex)
    {coeffBound basisBound : Real}
    (hcoeff_nonneg : 0 ≤ coeffBound)
    (hbasis_nonneg : 0 ≤ basisBound)
    (hcoeff : ∀ p ∈
        (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ ≤
          coeffBound)
    (hbasis : ∀ p ∈
        (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        SchwartzMap.seminorm Complex 0 0
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) ≤
            basisBound) :
    (∑ p ∈
        (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
      (nodes.card : Real) * coeffBound * basisBound := by
  let c := sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y
  have hsum := source_combination_seminorm_zero_zero_le_card_mul_uniform_budget
    c hcoeff_nonneg hbasis_nonneg hcoeff hbasis
  have hcard : (c.support.card : Real) ≤ (nodes.card : Real) := by
    exact_mod_cast sparseWindowedMellinCorrection_support_card
      nodes a b ha ha_one hone_b y
  have hfactor : 0 ≤ coeffBound * basisBound :=
    mul_nonneg hcoeff_nonneg hbasis_nonneg
  dsimp [c] at hsum hcard ⊢
  calc
    (∑ p ∈
        (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
        ((sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support.card : Real) *
          coeffBound * basisBound := hsum
    _ ≤ (nodes.card : Real) * coeffBound * basisBound := by
      gcongr

theorem sparse_unitBounded_correction_weighted_budget_le_node_card
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex)
    {coeffBound : Real} (hcoeff_nonneg : 0 ≤ coeffBound)
    (hcoeff : ∀ p ∈
        (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ ≤
          coeffBound) :
    (∑ p ∈
        (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
      (nodes.card : Real) * coeffBound * 1 := by
  let c := sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y
  have hsum := source_combination_seminorm_zero_zero_le_card_mul_uniform_budget
    c hcoeff_nonneg (by norm_num : (0 : Real) ≤ 1) hcoeff (by
      intro p hp
      rcases sparseUnitBoundedWindowedMellinCorrection_source_bound
        nodes a b ha ha_one hone_b y p hp with ⟨q, hqp, hqbound⟩
      apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
      intro x
      simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
      simpa [hqp] using hqbound x)
  have hcard : (c.support.card : Real) ≤ (nodes.card : Real) := by
    exact_mod_cast sparseUnitBoundedWindowedMellinCorrection_support_card
      nodes a b ha ha_one hone_b y
  calc
    (∑ p ∈ c.support,
        ‖c p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) ≤
        (c.support.card : Real) * coeffBound * 1 := hsum
    _ ≤ (nodes.card : Real) * coeffBound * 1 := by
      have hfactor : 0 ≤ coeffBound * 1 := by positivity
      gcongr

theorem strict_base_contraction_of_sparse_unitBounded_correction
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex)
    {coeffBound budget : Real} (hcoeff_nonneg : 0 ≤ coeffBound)
    (hcoeff : ∀ p ∈
        (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
        ‖(sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y) p‖ ≤
          coeffBound)
    (hbudget : 2 * (nodes.card : Real) * coeffBound < budget)
    (hbudget_half : budget ≤ 1 / 2) :
    2 * SchwartzMap.seminorm Complex 0 0
        (compactLogTestOfWindow
          (windowedPositiveIntervalCompactTestCombination
            (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y))
          ha (lt_trans (by norm_num) hone_b)
          (windowedPositiveIntervalCompactTestCombination_support_subset _)).test <
      1 := by
  let c := sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y
  have hb : 0 < b := lt_trans (by norm_num) hone_b
  have hcard : (c.support.card : Real) ≤ (nodes.card : Real) := by
    exact_mod_cast sparseUnitBoundedWindowedMellinCorrection_support_card
      nodes a b ha ha_one hone_b y
  have hbasis : ∀ p ∈ c.support,
      SchwartzMap.seminorm Complex 0 0
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test) ≤ 1 := by
    intro p hp
    rcases sparseUnitBoundedWindowedMellinCorrection_source_bound
      nodes a b ha ha_one hone_b y p hp with ⟨q, hqp, hqbound⟩
    apply SchwartzMap.seminorm_le_bound Complex 0 0 _ (by positivity)
    intro x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    simpa [hqp] using hqbound x
  have hbudget' : 2 * (c.support.card : Real) * coeffBound * 1 < budget := by
    calc
      2 * (c.support.card : Real) * coeffBound * 1 ≤
          2 * (nodes.card : Real) * coeffBound * 1 := by
        gcongr
      _ < budget := by simpa using hbudget
  dsimp [c] at hbasis hbudget' ⊢
  exact strict_base_contraction_of_uniform_coeff_basis_budget
    ha hb _ hcoeff_nonneg (by norm_num) hcoeff hbasis hbudget' hbudget_half

theorem exists_sparse_base_with_unit_targets_and_quadratic_decay
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ c : WindowedPositiveIntervalCompactTest (Real.exp lower) (Real.exp upper) →₀ Complex,
      c.support.card ≤ nodes.card ∧
      ∃ base : CompactLogTest,
        Function.support base.test ⊆ Set.Ioo lower upper ∧
        (∀ z : FiniteMellinNode nodes, laplaceAt base z.1 = 1) ∧
        ∃ C : Real, 0 ≤ C ∧
          ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
            ‖t / (2 * Real.pi)‖ ^ 2 *
                ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  let a : Real := Real.exp lower
  let b : Real := Real.exp upper
  let ha : 0 < a := Real.exp_pos lower
  let hb : 0 < b := Real.exp_pos upper
  let ha_one : a < 1 := Real.exp_lt_one_iff.mpr hlower
  let hone_b : 1 < b := Real.one_lt_exp_iff.mpr hupper
  let values : FiniteMellinNode nodes → Complex := fun _ => 1
  let c := sparseWindowedMellinCorrection nodes a b ha ha_one hone_b values
  have hcard : c.support.card ≤ nodes.card := by
    exact sparseWindowedMellinCorrection_support_card
      nodes a b ha ha_one hone_b values
  have hsource_support :
      Function.support
          (fun x : Real =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (windowedPositiveIntervalCompactTestCombination c) x) ⊆
        Set.Ioo a b := by
    exact windowedPositiveIntervalCompactTestCombination_support_subset c
  let base : CompactLogTest :=
    compactLogTestOfWindow
      (windowedPositiveIntervalCompactTestCombination c) ha hb hsource_support
  refine ⟨c, hcard, base, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := compactLogTestOfWindow_support_subset
      (windowedPositiveIntervalCompactTestCombination c) ha hb hsource_support hx
    simpa [a, b] using hx'
  · intro z
    have hmap := sparseWindowedMellinCorrection_evaluation
      nodes a b ha ha_one hone_b values
    have hmap_z := congrArg (fun q => q z) hmap
    change windowedMellinEvaluationMap nodes a b ha ha_one hone_b c z =
      values z at hmap_z
    rw [windowedMellinEvaluationMap_apply] at hmap_z
    calc
      laplaceAt base z.1 =
          normalizedCC20TestSpace.mellinAt
            (windowedPositiveIntervalCompactTestCombination c) z.1 := by
        dsimp [base]
        rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
      _ = c.sum (fun p coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b p z) :=
        windowedFiniteMellinVector_combination nodes c z
      _ = 1 := by simpa [values] using hmap_z
  · obtain ⟨C, hC, hdecay⟩ :=
      exists_uniform_laplaceAt_vertical_quadratic_decay
        (windowedPositiveIntervalCompactTestCombination c) ha hb hsource_support
    refine ⟨C, hC, ?_⟩
    intro sigma hsigma t
    exact hdecay sigma hsigma t

theorem affineResidualCorrection_seminorm_le_rightInverse_budget
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    SchwartzMap.seminorm Complex 0 0
        (affineResidualCorrection nodes hlower hupper y).test ≤
      (∑ p ∈
          (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
            (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
            (Real.one_lt_exp_iff.mpr hupper) y).support,
        ‖(windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
            (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
            (Real.one_lt_exp_iff.mpr hupper) y) p‖ *
          SchwartzMap.seminorm Complex 0 0
            (normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test)) := by
  dsimp [affineResidualCorrection]
  exact compactLogTestOfWindow_combination_seminorm_zero_zero_le_coeff_weighted_sum
    (Real.exp_pos lower) (Real.exp_pos upper)
    (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
      (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
      (Real.one_lt_exp_iff.mpr hupper) y)

theorem affineResidualCorrection_with_quadratic_decay
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt (affineResidualCorrection nodes hlower hupper y)
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  let a : Real := Real.exp lower
  let b : Real := Real.exp upper
  let ha : 0 < a := Real.exp_pos lower
  let hb : 0 < b := Real.exp_pos upper
  let ha_one : a < 1 := Real.exp_lt_one_iff.mpr hlower
  let hone_b : 1 < b := Real.one_lt_exp_iff.mpr hupper
  let coeffs := windowedMellinRightInverse nodes a b ha ha_one hone_b y
  let source := windowedPositiveIntervalCompactTestCombination coeffs
  have hsource_support :
      Function.support
          (fun x : Real =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode source x) ⊆
        Set.Ioo a b := by
    exact windowedPositiveIntervalCompactTestCombination_support_subset coeffs
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay source ha hb hsource_support
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have h := hdecay sigma hsigma t
  simpa [affineResidualCorrection, a, b, ha, hb, ha_one, hone_b, coeffs, source]
    using h

theorem exists_affine_base_with_unit_targets_and_quadratic_decay
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ base : CompactLogTest,
      Function.support base.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode nodes, laplaceAt base z.1 = 1) ∧
      ∃ C : Real, 0 ≤ C ∧
        ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
          ‖t / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  let values : FiniteMellinNode nodes → Complex := fun _ => 1
  let base := affineResidualCorrection nodes hlower hupper values
  refine ⟨base, ?_, ?_, ?_⟩
  · exact affineResidualCorrection_support_subset nodes hlower hupper values
  · intro z
    exact affineResidualCorrection_laplaceAt nodes hlower hupper values z
  · exact affineResidualCorrection_with_quadratic_decay nodes hlower hupper values

/-! The zero Mellin target imposes a sharp lower bound on the zero-order
seminorm.  In particular, a unit target on an interval of length two cannot
coexist with the strict contraction threshold used by the geometric route. -/
theorem seminorm_zero_zero_ge_half_of_laplaceAt_zero_eq_one_of_support_Ioo
    (f : CompactLogTest)
    (hsupp : Function.support f.test ⊆ Set.Ioo (-1 : Real) 1)
    (hzero : laplaceAt f 0 = 1) :
    (1 / 2 : Real) ≤ SchwartzMap.seminorm Complex 0 0 f.test := by
  have hL2 : compactLogL2sq f ≤
      (2 : Real) * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by
    have hl2 : (∫ x : Real in (-1 : Real)..1, ‖f.test x‖ ^ 2) =
        compactLogL2sq f := by
      unfold compactLogL2sq
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => ?_))
      by_cases hx : x ∈ Set.Ioc (-1 : Real) 1
      · simp [hx]
      · have hx' : x ∉ Set.Ioo (-1 : Real) 1 := by
          intro h
          exact hx ⟨h.1, le_of_lt h.2⟩
        rw [Set.indicator_of_notMem hx]
        have hz : f.test x = 0 := by
          by_contra hnz
          exact hx' (hsupp hnz)
        simp [hz]
    rw [← hl2]
    have hmono :
        (∫ x : Real in (-1 : Real)..1, ‖f.test x‖ ^ 2) ≤
          ∫ x : Real in (-1 : Real)..1,
            (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
      · have hcont : ContinuousOn
            (fun x : Real => ‖f.test x‖ ^ 2) (Set.uIcc (-1 : Real) 1) :=
            ((f.test.smooth ⊤).continuous.norm.continuousOn).pow 2
        exact hcont.intervalIntegrable
      · exact intervalIntegrable_const
      · intro x hx
        have hnorm := SchwartzMap.norm_le_seminorm Complex f.test x
        nlinarith [norm_nonneg (f.test x)]
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    norm_num at hmono
    simpa [pow_two] using hmono
  have hlap := laplaceAt_sq_le f (a := (-1 : Real)) (b := 1)
    (by norm_num) hsupp (0 : Complex)
  rw [hzero] at hlap
  have hnonneg : 0 ≤ SchwartzMap.seminorm Complex 0 0 f.test := by
    exact le_trans (norm_nonneg (f.test 0))
      (SchwartzMap.norm_le_seminorm Complex f.test 0)
  norm_num at hlap
  nlinarith [hL2]

theorem not_strict_base_contraction_of_unit_zero_target_of_support_Ioo
    (f : CompactLogTest)
    (hsupp : Function.support f.test ⊆ Set.Ioo (-1 : Real) 1)
    (hzero : laplaceAt f 0 = 1) :
    ¬ 2 * SchwartzMap.seminorm Complex 0 0 f.test < 1 := by
  intro hcontract
  have hhalf := seminorm_zero_zero_ge_half_of_laplaceAt_zero_eq_one_of_support_Ioo
    f hsupp hzero
  nlinarith

/-- Universal lower bound on the convolution contraction factor for an arbitrary
    bounded window `(a, b)`: any base test with unit Laplace target at zero
    satisfies `(b - a) * seminorm(f) ≥ 1`. -/
theorem supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one
    (f : CompactLogTest) {a b : Real} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b)
    (hzero : laplaceAt f 0 = 1) :
    1 ≤ (b - a) * SchwartzMap.seminorm Complex 0 0 f.test := by
  have hL2 : compactLogL2sq f ≤
      (b - a) * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by
    have hl2 : (∫ x : Real in a..b, ‖f.test x‖ ^ 2) =
        compactLogL2sq f := by
      unfold compactLogL2sq
      rw [intervalIntegral.integral_of_le hab.le,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => ?_))
      by_cases hx : x ∈ Set.Ioc a b
      · simp [hx]
      · have hx' : x ∉ Set.Ioo a b := by
          intro h
          exact hx ⟨h.1, le_of_lt h.2⟩
        rw [Set.indicator_of_notMem hx]
        have hz : f.test x = 0 := by
          by_contra hnz
          exact hx' (hsupp hnz)
        simp [hz]
    rw [← hl2]
    have hmono :
        (∫ x : Real in a..b, ‖f.test x‖ ^ 2) ≤
          ∫ x : Real in a..b,
            (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) hab.le
      · have hcont : ContinuousOn
            (fun x : Real => ‖f.test x‖ ^ 2) (Set.uIcc a b) :=
            ((f.test.smooth ⊤).continuous.norm.continuousOn).pow 2
        exact hcont.intervalIntegrable
      · exact intervalIntegrable_const
      · intro x hx
        have hnorm := SchwartzMap.norm_le_seminorm Complex f.test x
        nlinarith [norm_nonneg (f.test x)]
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    simpa [pow_two] using hmono
  have hlap := laplaceAt_sq_le f hab hsupp (0 : Complex)
  rw [hzero] at hlap
  have hnonneg : 0 ≤ SchwartzMap.seminorm Complex 0 0 f.test := by
    exact le_trans (norm_nonneg (f.test 0))
      (SchwartzMap.norm_le_seminorm Complex f.test 0)
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hinteg : (∫ x : Real in a..b, Real.exp (2 * (0 : Complex).re * x) ∂volume) = b - a := by
    have he : (fun x : Real => Real.exp (2 * (0 : Complex).re * x)) = fun _ => (1 : Real) := by
      funext x
      simp
    rw [he, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [hinteg] at hlap
  norm_num at hlap
  have h_sq : 1 ≤ (b - a) ^ 2 * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by
    calc
      1 ≤ (b - a) * compactLogL2sq f := hlap
      _ ≤ (b - a) * ((b - a) * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 hlen.le
      _ = (b - a) ^ 2 * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by ring
  have h_prod_sq : (b - a) ^ 2 * (SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 =
      ((b - a) * SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 := by ring
  rw [h_prod_sq] at h_sq
  have hprod_nonneg : 0 ≤ (b - a) * SchwartzMap.seminorm Complex 0 0 f.test :=
    mul_nonneg hlen.le hnonneg
  by_contra hlt
  push_neg at hlt
  have h_lt_one : ((b - a) * SchwartzMap.seminorm Complex 0 0 f.test) ^ 2 < 1 := by
    nlinarith [hprod_nonneg, hlt]
  linarith [h_sq, h_lt_one]

/-- Universal no-go for strict geometric base contraction on any bounded window:
    the contraction factor `(b - a) * seminorm(f) < 1` is mathematically impossible
    for any compactly supported base with unit Laplace target at zero. -/
theorem not_strict_base_contraction_of_arbitrary_window
    (f : CompactLogTest) {a b : Real} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b)
    (hzero : laplaceAt f 0 = 1) :
    ¬ (b - a) * SchwartzMap.seminorm Complex 0 0 f.test < 1 := by
  intro hcontract
  have hge := supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one
    f hab hsupp hzero
  linarith

end
end C1P2BaseSeminormBound
end Source
end ConnesWeilRH
