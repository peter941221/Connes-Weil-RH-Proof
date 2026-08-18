/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1LaneRNarrowArch

/-!
# Lane R: strictness of the explicit narrow-support root

The non-strict narrow-support estimate becomes strict once the selected D3
root is known to be nonzero.  This module supplies that missing fact without
using numerical differentiation: the positive base bump has a strictly
positive real Laplace value at `s = 2`, and the exact D3 transform law then
prevents collapse.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LaneRStrictness

open MeasureTheory
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1LaneRNarrowArch
open Dev.M2Width
open Dev.Wall14Plateau

private noncomputable def wideLaplaceRealIntegrand (w x : ℝ) : ℝ :=
  Real.exp (2 * x) * Dev.M2Width.wideBump w x

private theorem wideBump_hasCompactSupport
    (w : ℝ) (wpos : 0 < w) :
    HasCompactSupport (Dev.M2Width.wideBump w) := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-w)) (b := w))
  · exact isClosed_closure
  · have hsub :
        Function.support (Dev.M2Width.wideBump w) ⊆ Set.Icc (-w) w := by
      intro x hx
      exact Dev.M2Width.wideBump_mem_Icc w wpos x hx
    simpa [isClosed_Icc.closure_eq] using closure_mono hsub

private theorem wideLaplaceRealIntegrand_integrable
    (w : ℝ) (wpos : 0 < w) :
    Integrable (wideLaplaceRealIntegrand w) := by
  have hcont : Continuous (wideLaplaceRealIntegrand w) := by
    change Continuous (fun x : ℝ =>
      Real.exp (2 * x) * Dev.M2Width.wideBump w x)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Dev.M2Width.wideBump_contDiff w).continuous
  have hcompact : HasCompactSupport (wideLaplaceRealIntegrand w) := by
    dsimp [wideLaplaceRealIntegrand]
    exact (wideBump_hasCompactSupport w wpos).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem wideLaplaceRealIntegrand_nonneg
    (w x : ℝ) : 0 ≤ wideLaplaceRealIntegrand w x := by
  dsimp [wideLaplaceRealIntegrand]
  exact mul_nonneg (Real.exp_pos _).le (by
    unfold Dev.M2Width.wideBump
    exact Dev.Wall14Plateau.bumpEx_nonneg _)

private theorem wideLaplaceRealIntegrand_zero
    (w : ℝ) (wpos : 0 < w) :
    wideLaplaceRealIntegrand w 0 = 1 := by
  dsimp [wideLaplaceRealIntegrand]
  have hzero : Dev.M2Width.wideBump w 0 = 1 := by
    apply Dev.M2Width.wideBump_plateau w wpos 0
    rw [show Dev.Wall14Plateau.bplateau = (9 / 10 : ℝ) by rfl]
    calc
      (0 : ℝ) ^ 2 = 0 := by norm_num
      _ ≤ (9 / 10 : ℝ) ^ 2 * w ^ 2 :=
        mul_nonneg (sq_nonneg (9 / 10 : ℝ)) (sq_nonneg w)
  simp [hzero]

private theorem wideTest_laplaceAt_two_re_pos
    (w : ℝ) (wpos : 0 < w) :
    0 < (CompactLogTest.laplaceAt
      (Dev.M2Width.wideTest w wpos) (2 : ℂ)).re := by
  let q : ℝ → ℝ := wideLaplaceRealIntegrand w
  have hqint : Integrable q := by
    simpa [q] using wideLaplaceRealIntegrand_integrable w wpos
  have hqnonneg : ∀ x : ℝ, 0 ≤ q x := by
    intro x
    simpa [q] using wideLaplaceRealIntegrand_nonneg w x
  have hqcont : Continuous q := by
    simpa [q] using (show Continuous (wideLaplaceRealIntegrand w) by
      change Continuous (fun x : ℝ =>
        Real.exp (2 * x) * Dev.M2Width.wideBump w x)
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
        (Dev.M2Width.wideBump_contDiff w).continuous)
  have hqzero : q 0 ≠ 0 := by
    have hqone : q 0 = 1 := by
      simpa [q] using wideLaplaceRealIntegrand_zero w wpos
    rw [hqone]
    norm_num
  have hqpos : 0 < ∫ x : ℝ, q x := by
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (f_cont := hqcont)
      (f_int := hqint)
      (f_nonneg := hqnonneg)
      (f_x := hqzero)
  have hintegrand :
      (fun x : ℝ =>
          Complex.exp ((2 : ℂ) * (x : ℂ)) *
            (Dev.M2Width.wideTest w wpos).test x) =
        (fun x : ℝ => (q x : ℂ)) := by
    funext x
    rw [Dev.M2Width.wideTest_apply]
    have harg : (2 : ℂ) * (x : ℂ) = ((2 * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp]
    simp [q, wideLaplaceRealIntegrand]
  have hlap :
      CompactLogTest.laplaceAt
          (Dev.M2Width.wideTest w wpos) (2 : ℂ) =
        ((∫ x : ℝ, q x : ℝ) : ℂ) := by
    unfold CompactLogTest.laplaceAt
    simp only [CompactLogTest.exponentialWeight_apply]
    rw [hintegrand, integral_complex_ofReal]
  rw [hlap]
  simpa using hqpos

private theorem convolutionSquare_mass_pos_of_test_ne_zero
    (g : CompactLogTest) (hg : g.test ≠ 0) :
    0 < (g.convolutionSquare.test 0).re := by
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  have hpoint : ∃ x : ℝ, g.test x ≠ 0 := by
    by_contra! hpoint
    apply hg
    ext x
    exact hpoint x
  obtain ⟨x, hx⟩ := hpoint
  have hcont : Continuous
      (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_normSq.comp g.test.continuous
  have hcompact : HasCompactSupport
      (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      g.compactSupport.comp_left (by simp)
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (f_cont := hcont)
    (f_int := hcont.integrable_of_hasCompactSupport hcompact)
    (f_nonneg := fun y => Complex.normSq_nonneg (g.test y))
    (f_x := (Complex.normSq_pos.mpr hx).ne')

private theorem tripleVanishingRoot_square_support_of_narrow_base
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth) :
    Function.support (C1LaneRD3Root.tripleVanishingRoot h).convolutionSquare.test ⊆
      Set.Ioo (-narrowArchRadius) narrowArchRadius := by
  have hroot := C1LaneRD3Root.tripleVanishingRoot_support_subset_Icc h hsupport
  have hinput : Function.support
      (C1LaneRD3Root.tripleVanishingRoot h).test ⊆
      Set.Ioo (-(narrowArchRadius) / 2) (narrowArchRadius / 2) := by
    intro x hx
    have hx' := hroot hx
    rcases hx' with ⟨hxlow, hxhigh⟩
    dsimp [narrowArchBaseWidth] at hxlow hxhigh
    constructor <;> nlinarith [narrowArchRadius_pos]
  exact CC20YoshidaConvolution.CompactLogTest.convolutionSquare_support_subset_symmetric
    (C1LaneRD3Root.tripleVanishingRoot h) (a := narrowArchRadius) hinput

private theorem tripleVanishingRoot_square_support_open_log_two_of_narrow_base
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth) :
    Function.support (C1LaneRD3Root.tripleVanishingRoot h).convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
  have hwidth : narrowArchBaseWidth < (3 / 10 : ℝ) := by
    dsimp [narrowArchBaseWidth]
    nlinarith [narrowArchRadius_lt_one]
  exact C1LaneRD3Root.tripleVanishingRoot_square_support_subset_open_log_two_of_Icc
    h hsupport hwidth

theorem tripleVanishingRoot_archimedeanTerm_neg_of_narrow_base_of_laplaceAt_two_ne_zero
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth)
    (hlap : CompactLogTest.laplaceAt h (2 : ℂ) ≠ 0) :
    C1SameOwnerWeil.archimedeanTerm
        (C1LaneRD3Root.tripleVanishingRoot h).convolutionSquare < 0 := by
  have hroot := C1LaneRD3Root.tripleVanishingRoot_test_ne_zero_of_laplaceAt_two
    h hlap
  have hmass := convolutionSquare_mass_pos_of_test_ne_zero
    (C1LaneRD3Root.tripleVanishingRoot h) hroot
  exact archimedeanTerm_neg_of_narrow_budget
    (C1LaneRD3Root.tripleVanishingRoot h) narrowArchRadius
    narrowArchRadius_pos narrowArchRadius_lt_one
    (tripleVanishingRoot_square_support_of_narrow_base h hsupport)
    (by simpa [narrowArchCoefficient] using narrowArchRadius_budget_lt)
    hmass

theorem tripleVanishingRoot_qw_nonneg_of_narrow_base
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth) :
    0 ≤ C1SameOwnerWeil.qw (C1LaneRD3Root.tripleVanishingRoot h) := by
  have hprimefree := tripleVanishingRoot_square_support_open_log_two_of_narrow_base
    h hsupport
  have harch := archimedeanTerm_nonpos_of_narrow_budget
    (C1LaneRD3Root.tripleVanishingRoot h) narrowArchRadius
    narrowArchRadius_pos narrowArchRadius_lt_one
    (tripleVanishingRoot_square_support_of_narrow_base h hsupport)
    (by simpa [narrowArchCoefficient] using narrowArchRadius_budget)
  rw [C1LaneRD3Root.tripleVanishingRoot_qw_eq_neg_archimedeanTerm_of_primeFreeSquare
    h hprimefree]
  exact neg_nonneg.mpr harch

theorem tripleVanishingRoot_qw_pos_of_narrow_base_of_laplaceAt_two_ne_zero
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth)
    (hlap : CompactLogTest.laplaceAt h (2 : ℂ) ≠ 0) :
    0 < C1SameOwnerWeil.qw (C1LaneRD3Root.tripleVanishingRoot h) := by
  have harch := tripleVanishingRoot_archimedeanTerm_neg_of_narrow_base_of_laplaceAt_two_ne_zero
    h hsupport hlap
  have hprimefree := tripleVanishingRoot_square_support_open_log_two_of_narrow_base
    h hsupport
  rw [C1LaneRD3Root.tripleVanishingRoot_qw_eq_neg_archimedeanTerm_of_primeFreeSquare
    h hprimefree]
  exact neg_pos.mpr harch

theorem narrowArchRoot_test_ne_zero : narrowArchRoot.test ≠ 0 := by
  apply C1LaneRD3Root.tripleVanishingRoot_test_ne_zero_of_laplaceAt_two
  have hpos := wideTest_laplaceAt_two_re_pos
    narrowArchBaseWidth narrowArchBaseWidth_pos
  have hroot :
      CompactLogTest.laplaceAt
          (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos)
          (2 : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hre' :
        (CompactLogTest.laplaceAt
          (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos)
          (2 : ℂ)).re = 0 := by
      simpa using hre
    exact (ne_of_gt hpos) hre'
  exact hroot

theorem narrowArchRoot_square_mass_pos :
    0 < (narrowArchRoot.convolutionSquare.test 0).re := by
  exact convolutionSquare_mass_pos_of_test_ne_zero
    narrowArchRoot narrowArchRoot_test_ne_zero

theorem narrowArchRoot_archimedeanTerm_neg :
    C1SameOwnerWeil.archimedeanTerm narrowArchRoot.convolutionSquare < 0 := by
  apply archimedeanTerm_neg_of_narrow_budget narrowArchRoot narrowArchRadius
    narrowArchRadius_pos narrowArchRadius_lt_one narrowArchRoot_square_support
  · simpa [narrowArchCoefficient] using narrowArchRadius_budget_lt
  · exact narrowArchRoot_square_mass_pos

theorem narrowArchRoot_qw_pos :
    0 < C1SameOwnerWeil.qw narrowArchRoot := by
  rw [narrowArchRoot_qw_eq_neg_archimedeanTerm]
  exact neg_pos.mpr narrowArchRoot_archimedeanTerm_neg

end C1LaneRStrictness
end Source
end ConnesWeilRH
