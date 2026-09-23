/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1LaneRD3Root
import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SameOwnerWeil
import Mathlib.Analysis.Complex.Basic

/-!
# Two-Point Differential Annihilator: Off-Line Zero Annihilation on Narrow Support

This module implements the two-point differential annihilator operator:
`twoPointDerivativeAnnihilator f z1 z2 = derivativeShift (derivativeShift f z1) z2`.

Under the bilateral Laplace transform, this operator multiplies by `(z2 - s) * (z1 - s)`.
Consequently:
1. It algebraically forces zeros at `s = z1` and `s = z2`;
2. It preserves critical triple vanishing at `{0, 1/2, 1}`;
3. It strictly preserves the compact support interval `[-w, w]`, preventing any
   support widening into the arithmetic prime domain;
4. For narrow tests, the convolution square remains prime-free (`finitePrimeSum = 0`).

Consumer: Two-span spectral contradiction with the pinned Yoshida detector.
-/

namespace ConnesWeilRH
namespace Source
namespace C1TwoPointDifferentialAnnihilator

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1LaneRD3Root
open C1LaneRNarrowArch
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open Set

noncomputable section

/-- The two-point differential annihilator: composing two Laplace-side derivative shifts
    at nodes `z1` and `z2`. -/
def twoPointDerivativeAnnihilator
    (f : CompactLogTest) (z1 z2 : ℂ) : CompactLogTest :=
  derivativeShift (derivativeShift f z1) z2

/-- Laplace transform representation of the two-point differential annihilator:
    multiplication by `(z2 - s) * (z1 - s)`. -/
theorem laplaceAt_twoPointDerivativeAnnihilator
    (f : CompactLogTest) (z1 z2 s : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) s =
      (z2 - s) * (z1 - s) * laplaceAt f s := by
  unfold twoPointDerivativeAnnihilator
  rw [laplaceAt_derivativeShift, laplaceAt_derivativeShift]
  ring

/-- The two-point differential annihilator vanishes identically at the first node `z1`. -/
@[simp] theorem twoPointDerivativeAnnihilator_laplaceAt_z1
    (f : CompactLogTest) (z1 z2 : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) z1 = 0 := by
  rw [laplaceAt_twoPointDerivativeAnnihilator]
  simp

/-- The two-point differential annihilator vanishes identically at the second node `z2`. -/
@[simp] theorem twoPointDerivativeAnnihilator_laplaceAt_z2
    (f : CompactLogTest) (z1 z2 : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) z2 = 0 := by
  rw [laplaceAt_twoPointDerivativeAnnihilator]
  simp

/-- The two-point differential annihilator preserves vanishing at any point `s`. -/
theorem twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
    (f : CompactLogTest) (z1 z2 s : ℂ)
    (h : laplaceAt f s = 0) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) s = 0 := by
  rw [laplaceAt_twoPointDerivativeAnnihilator, h, mul_zero]

/-- Vanishing on the CC20 critical triple `{0, 1/2, 1}` is strictly preserved
    under the two-point differential annihilator. -/
theorem twoPointDerivativeAnnihilator_vanishesOn_cc20Triple
    (f : CompactLogTest) (z1 z2 : ℂ)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet f) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (twoPointDerivativeAnnihilator f z1 z2) := by
  intro p hp
  have hzero := hvanishes p hp
  cases p with
  | zero =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero f z1 z2 0
          (by simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hzero)
  | half =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero f z1 z2 (1 / 2 : ℂ)
          (by simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hzero)
  | one =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero f z1 z2 1
          (by simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hzero)

/-- Compact support in `[-w, w]` is strictly preserved under the two-point differential annihilator. -/
theorem twoPointDerivativeAnnihilator_support_subset_Icc
    (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w) :
    Function.support ((twoPointDerivativeAnnihilator f z1 z2).test : ℝ → ℂ) ⊆ Set.Icc (-w) w := by
  unfold twoPointDerivativeAnnihilator
  exact derivativeShift_support_subset_Icc _ z2
    (derivativeShift_support_subset_Icc f z1 hsupport)

/-- For tests supported in `[-w, w]` with `w < 3/10`, the convolution square of the
    annihilated test remains strictly within the prime-free window `(-log 2, log 2)`. -/
theorem twoPointDerivativeAnnihilator_square_support_subset_open_log_two
    (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : ℝ)) :
    Function.support (twoPointDerivativeAnnihilator f z1 z2).convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
  have hsupp := twoPointDerivativeAnnihilator_support_subset_Icc f z1 z2 hsupport
  have hopen : Function.support (twoPointDerivativeAnnihilator f z1 z2).test ⊆
      Set.Ioo (-(3 / 5 : ℝ) / 2) ((3 / 5 : ℝ) / 2) := by
    intro x hx
    rcases hsupp hx with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hsquare := convolutionSquare_support_subset_symmetric
    (twoPointDerivativeAnnihilator f z1 z2) (a := (3 / 5 : ℝ)) hopen
  have hlog : (3 / 5 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Vanishing of the arithmetic prime sum for narrow annihilated tests. -/
theorem twoPointDerivativeAnnihilator_finitePrimeSum_eq_zero
    (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : ℝ)) :
    finitePrimeSum (twoPointDerivativeAnnihilator f z1 z2).convolutionSquare = 0 := by
  apply finitePrimeSum_eq_zero_of_support_subset_open_log_two
  exact twoPointDerivativeAnnihilator_square_support_subset_open_log_two f z1 z2 hsupport hw

/-- On triple-vanishing narrow tests, the same-owner Weil value of the annihilated test
    reduces identically to the negative Archimedean term. -/
theorem twoPointDerivativeAnnihilator_qw_eq_neg_archimedeanTerm
    (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet f)
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : ℝ)) :
    qw (twoPointDerivativeAnnihilator f z1 z2) =
      -archimedeanTerm (twoPointDerivativeAnnihilator f z1 z2).convolutionSquare := by
  have hvanish := twoPointDerivativeAnnihilator_vanishesOn_cc20Triple f z1 z2 hvanishes
  have hopen := twoPointDerivativeAnnihilator_square_support_subset_open_log_two f z1 z2 hsupport hw
  exact qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    (twoPointDerivativeAnnihilator f z1 z2) hvanish hopen

/-- Specialized zero-orbit annihilator: Given an off-line zero `rho`, this specializes
    the annihilator to `z1 = rho - 1/2` and `z2 = 1 - star rho - 1/2`. -/
def offlineZeroOrbitAnnihilator (f : CompactLogTest) (rho : ℂ) : CompactLogTest :=
  twoPointDerivativeAnnihilator f (rho - 1 / 2) (1 - star rho - 1 / 2)

@[simp] theorem offlineZeroOrbitAnnihilator_laplaceAt_rho_sub_half
    (f : CompactLogTest) (rho : ℂ) :
    laplaceAt (offlineZeroOrbitAnnihilator f rho) (rho - 1 / 2) = 0 :=
  twoPointDerivativeAnnihilator_laplaceAt_z1 f (rho - 1 / 2) (1 - star rho - 1 / 2)

@[simp] theorem offlineZeroOrbitAnnihilator_laplaceAt_one_sub_star_rho_sub_half
    (f : CompactLogTest) (rho : ℂ) :
    laplaceAt (offlineZeroOrbitAnnihilator f rho) (1 - star rho - 1 / 2) = 0 :=
  twoPointDerivativeAnnihilator_laplaceAt_z2 f (rho - 1 / 2) (1 - star rho - 1 / 2)

end
end C1TwoPointDifferentialAnnihilator
end Source
end ConnesWeilRH
