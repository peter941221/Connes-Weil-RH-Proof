/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1LaneRD3Root
import ConnesWeilRH.Dev.M2WidthPlateau
import ConnesWeilRH.Dev.Wall14ArchSufficiency
import ConnesWeilRH.Dev.Wall14PlateauNear
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lane R: a narrow-support archimedean sign brick

The first theorem is the owner-preserving Cauchy--Schwarz estimate for a
Hermitian convolution square.  The later sign theorem will use this estimate
to budget the positive part of the archimedean density against the negative
tail forced by compact support.

This file contains no spectral positivity claim and no RH conclusion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LaneRNarrowArch

open MeasureTheory
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactLogConvolution.CompactLogTest
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner
open Dev.M2Width
open Set

private noncomputable def narrowDen (y : ℝ) : ℝ :=
  SelectedWeilSquareOwner.archimedeanDenominator y

private noncomputable def archimedeanRealIntegrand
    (g : CompactLogTest) (y : ℝ) : ℝ :=
  (Real.exp (y / 2) *
      (2 * (g.convolutionSquare.test y).re) -
    2 * (g.convolutionSquare.test 0).re) / narrowDen y

private theorem narrowDen_pos (y : ℝ) (hy : 0 < y) : 0 < narrowDen y := by
  unfold narrowDen SelectedWeilSquareOwner.archimedeanDenominator
  have hlt : Real.exp (-y) < Real.exp y :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

private theorem narrowDen_ge_two_mul (y : ℝ) (hy : 0 ≤ y) :
    2 * y ≤ narrowDen y := by
  have h := Dev.Wall14Plateau.deny_ge_two y hy
  simpa [narrowDen, SelectedWeilSquareOwner.archimedeanDenominator,
    Dev.Wall14Plateau.den] using h

private theorem narrowDen_le_four_mul (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    narrowDen y ≤ 4 * y := by
  have habs : |y| ≤ 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hnegabs : |-y| ≤ 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hplus := Real.abs_exp_sub_one_le habs
  have hminus := Real.abs_exp_sub_one_le hnegabs
  have hplus' : Real.exp y - 1 ≤ 2 * y := by
    have h := (abs_le.mp hplus).2
    simpa [abs_of_nonneg hy0] using h
  have hminus' : 1 - Real.exp (-y) ≤ 2 * y := by
    have h := (abs_le.mp hminus).1
    simp only [abs_neg, abs_of_nonneg hy0] at h
    linarith
  unfold narrowDen SelectedWeilSquareOwner.archimedeanDenominator
  linarith

private theorem selected_archimedeanIntegrand_re_eq
    (g : CompactLogTest) (y : ℝ) (hy : 0 < y) :
    ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re =
      archimedeanRealIntegrand g y := by
  unfold archimedeanRealIntegrand
    SelectedWeilSquareOwner.archimedeanIntegrand
  have hd0 : (narrowDen y : ℂ) ≠ 0 := by
    exact_mod_cast (narrowDen_pos y hy).ne'
  have hden_ne : narrowDen y ≠ 0 := (narrowDen_pos y hy).ne'
  have him :
      ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanNumerator y).im = 0 :=
    (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanNumerator_im_eq_zero y
  have hden :
      SelectedWeilSquareOwner.archimedeanDenominator y = narrowDen y := by
    rfl
  rw [hden, Complex.div_re]
  have hd : ((narrowDen y : ℂ)).im = 0 := by simp
  have hr : ((narrowDen y : ℂ)).re = narrowDen y := by simp
  have hnorm : Complex.normSq (narrowDen y : ℂ) = (narrowDen y) ^ 2 := by
    rw [Complex.normSq_apply, hr, hd]
    ring
  rw [him, hr, hd, hnorm]
  field_simp [hden_ne]
  unfold SelectedWeilSquareOwner.archimedeanNumerator
  rw [(SelectedWeilSquareOwner.ofCompactLogTest g).convolutionSquare_add_neg_eq_two_re]
  have hsq :
      (SelectedWeilSquareOwner.ofCompactLogTest g).convolutionSquare =
        g.convolutionSquare := by
    rfl
  rw [hsq]
  have h1 :
      (Complex.ofRealCLM (Real.exp (y / 2)) *
          ((2 * (g.convolutionSquare.test y).re : ℝ) : ℂ)).re =
        Real.exp (y / 2) * (2 * (g.convolutionSquare.test y).re) := by
    change (((Real.exp (y / 2) : ℝ) : ℂ) *
      ((2 * (g.convolutionSquare.test y).re : ℝ) : ℂ)).re = _
    rw [Complex.re_ofReal_mul]
    simp
  have h2 :
      ((2 : ℂ) * g.convolutionSquare.test 0).re =
        2 * (g.convolutionSquare.test 0).re := by
    change (((2 : ℝ) : ℂ) * g.convolutionSquare.test 0).re = _
    rw [Complex.re_ofReal_mul]
  have hnum :
      (Complex.ofRealCLM (Real.exp (y / 2)) *
          ((2 * (g.convolutionSquare.test y).re : ℝ) : ℂ) -
        (2 : ℂ) * g.convolutionSquare.test 0).re =
      Real.exp (y / 2) * (2 * (g.convolutionSquare.test y).re) -
        2 * (g.convolutionSquare.test 0).re := by
    rw [Complex.sub_re, h1, h2]
  rw [hnum]
  ring

private theorem archimedeanRealIntegrand_le_mass
    (g : CompactLogTest) (R y : ℝ)
    (hy0 : 0 < y) (hyR : y ≤ R) (hR1 : R ≤ 1)
    (hnorm : ‖g.convolutionSquare.test y‖ ≤
      (g.convolutionSquare.test 0).re) :
    archimedeanRealIntegrand g y ≤
      (g.convolutionSquare.test 0).re := by
  let A : ℝ := (g.convolutionSquare.test 0).re
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have hF : (g.convolutionSquare.test y).re ≤ A := by
    exact (Complex.re_le_norm _).trans hnorm
  have ht0 : 0 ≤ y / 2 := by positivity
  have ht1 : |y / 2| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    nlinarith [hyR, hR1]
  have hexp : Real.exp (y / 2) - 1 ≤ y := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_le ht1)).2
    rw [abs_of_nonneg ht0] at h
    nlinarith
  have hden : 0 < narrowDen y := narrowDen_pos y hy0
  have hden_lower : 2 * y ≤ narrowDen y :=
    narrowDen_ge_two_mul y hy0.le
  have hmul : Real.exp (y / 2) * (g.convolutionSquare.test y).re ≤
      Real.exp (y / 2) * A :=
    mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
  have hnum :
      Real.exp (y / 2) * (2 * (g.convolutionSquare.test y).re) - 2 * A ≤
        2 * A * y := by
    calc
      Real.exp (y / 2) * (2 * (g.convolutionSquare.test y).re) - 2 * A ≤
          2 * (Real.exp (y / 2) * A) - 2 * A := by
        nlinarith
      _ = 2 * A * (Real.exp (y / 2) - 1) := by ring
      _ ≤ 2 * A * y := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hmass_den : 2 * A * y ≤ A * narrowDen y := by
    have h := mul_le_mul_of_nonneg_left hden_lower hA
    nlinarith
  unfold archimedeanRealIntegrand
  apply (div_le_iff₀ hden).2
  calc
    Real.exp (y / 2) * (2 * (g.convolutionSquare.test y).re) -
        2 * (g.convolutionSquare.test 0).re ≤ 2 * A * y := by
      simpa [A] using hnum
    _ ≤ A * narrowDen y := hmass_den

private theorem archimedeanRealIntegrand_eq_tail
    (g : CompactLogTest) (R y : ℝ)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R)
    (hyR : R ≤ y) :
    archimedeanRealIntegrand g y =
      -2 * (g.convolutionSquare.test 0).re / narrowDen y := by
  have hyzero : g.convolutionSquare.test y = 0 := by
    by_contra hne
    have hmem : y ∈ Function.support g.convolutionSquare.test := hne
    exact (not_lt_of_ge hyR) (hsupport hmem).2
  unfold archimedeanRealIntegrand
  simp [hyzero]

theorem convolutionSquare_norm_le_mass
    (g : CompactLogTest) (y : ℝ) :
    ‖g.convolutionSquare.test y‖ ≤
      (g.convolutionSquare.test 0).re := by
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hbase : MemLp (g.test : ℝ → ℂ) (ENNReal.ofReal (2 : ℝ)) :=
    SchwartzMap.memLp g.test (ENNReal.ofReal (2 : ℝ))
  have hneg : MeasurePreserving (fun t : ℝ => -t) volume volume := by
    exact Measure.measurePreserving_neg volume
  have hsub : MeasurePreserving (fun t : ℝ => y - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).add_left volume y
  have hleft : MemLp (fun t : ℝ => g.test (-t))
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [Function.comp_apply] using hbase.comp_measurePreserving hneg
  have hright : MemLp (fun t : ℝ => g.test (y - t))
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [Function.comp_apply] using hbase.comp_measurePreserving hsub
  have hbound :
      ‖∫ t : ℝ, star (g.test (-t)) * g.test (y - t)‖ ≤
        ∫ t : ℝ, ‖star (g.test (-t)) * g.test (y - t)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have hneg_norm_integral :
      (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, ‖g.test t‖ ^ (2 : ℝ) := by
    simpa only [Function.comp_apply] using
      hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
        (fun t : ℝ => ‖g.test t‖ ^ (2 : ℝ))
  have hsub_norm_integral :
      (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, ‖g.test t‖ ^ (2 : ℝ) := by
    simpa only [Function.comp_apply] using
      hsub.integral_comp (Homeomorph.subLeft y).measurableEmbedding
        (fun t : ℝ => ‖g.test t‖ ^ (2 : ℝ))
  have hmass : 0 ≤ ∫ t : ℝ, Complex.normSq (g.test t) := by
    exact integral_nonneg fun t => Complex.normSq_nonneg (g.test t)
  have hneg_normSq_integral :
      (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, Complex.normSq (g.test t) := by
    rw [hneg_norm_integral]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, Complex.normSq_eq_norm_sq]
  have hsub_normSq_integral :
      (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, Complex.normSq (g.test t) := by
    rw [hsub_norm_integral]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, Complex.normSq_eq_norm_sq]
  have hholder_bound :
      (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
        (∫ t : ℝ, Complex.normSq (g.test t)) := by
    have hraw :
        (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
          (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        hholder hleft hright
    rw [hneg_normSq_integral, hsub_normSq_integral] at hraw
    calc
      (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
          (∫ t : ℝ, Complex.normSq (g.test t)) ^ (1 / (2 : ℝ)) *
            (∫ t : ℝ, Complex.normSq (g.test t)) ^ (1 / (2 : ℝ)) := hraw
      _ = ∫ t : ℝ, Complex.normSq (g.test t) := by
        rw [← Real.sqrt_eq_rpow]
        simpa only [pow_two] using Real.sq_sqrt hmass
  calc
    ‖∫ t : ℝ, star (g.test (-t)) * g.test (y - t)‖ ≤
        ∫ t : ℝ, ‖star (g.test (-t)) * g.test (y - t)‖ := hbound
    _ = ∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [norm_mul, norm_star]
    _ ≤ ∫ t : ℝ, Complex.normSq (g.test t) := hholder_bound
    _ = (g.convolutionSquare.test 0).re := by
      rw [g.convolutionSquare_zero_eq_integral_normSq]
      simp

private theorem archimedeanRealIntegrand_integrableOn_Ioi
    (g : CompactLogTest) :
    IntegrableOn (archimedeanRealIntegrand g) (Ioi (0 : ℝ)) := by
  have hcomplex : IntegrableOn
      ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand)
      (Ioi (0 : ℝ)) :=
    (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand_integrableOn_Ioi
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hcomplex.re
  intro y hy
  exact (selected_archimedeanIntegrand_re_eq g y hy).symm

private theorem archimedeanRealIntegrand_integral_eq_selected_re
    (g : CompactLogTest) :
    (∫ y in Ioi (0 : ℝ), archimedeanRealIntegrand g y) =
      (∫ y in Ioi (0 : ℝ),
        (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re := by
  have hcomplex : IntegrableOn
      ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand)
      (Ioi (0 : ℝ)) :=
    (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand_integrableOn_Ioi
  calc
    (∫ y in Ioi (0 : ℝ), archimedeanRealIntegrand g y) =
        ∫ y in Ioi (0 : ℝ),
          ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re := by
      apply integral_congr_ae
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact (selected_archimedeanIntegrand_re_eq g y hy).symm
    _ = (∫ y in Ioi (0 : ℝ),
        (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re :=
      integral_re hcomplex

private theorem archimedeanRealIntegrand_le_neg_mass_div
    (g : CompactLogTest) (R y : ℝ)
    (hRpos : 0 < R) (hyR : R ≤ y) (hy1 : y ≤ 1)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R) :
    archimedeanRealIntegrand g y ≤
      -(g.convolutionSquare.test 0).re / (2 * y) := by
  let A : ℝ := (g.convolutionSquare.test 0).re
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have hy0 : 0 < y := lt_of_lt_of_le hRpos hyR
  have hden : 0 < narrowDen y := narrowDen_pos y hy0
  have hden_upper : narrowDen y ≤ 4 * y :=
    narrowDen_le_four_mul y hy0.le hy1
  have hcoef : -(A / (2 * y)) ≤ 0 := by
    exact neg_nonpos.mpr (div_nonneg hA (by positivity))
  have hmul : (-(A / (2 * y))) * (4 * y) ≤
      (-(A / (2 * y))) * narrowDen y :=
    mul_le_mul_of_nonpos_left hden_upper hcoef
  rw [archimedeanRealIntegrand_eq_tail g R y hsupport hyR]
  apply (div_le_iff₀ hden).2
  calc
    -2 * (g.convolutionSquare.test 0).re =
        (-(A / (2 * y))) * (4 * y) := by
      dsimp [A]
      field_simp
      ring
    _ ≤ (-(g.convolutionSquare.test 0).re / (2 * y)) * narrowDen y := by
      calc
        (-(A / (2 * y))) * (4 * y) ≤
            (-(A / (2 * y))) * narrowDen y := hmul
        _ = (-(g.convolutionSquare.test 0).re / (2 * y)) * narrowDen y := by
          dsimp [A]
          ring

private theorem archimedeanRealIntegrand_le_zero_of_ge_one
    (g : CompactLogTest) (R y : ℝ)
    (hRpos : 0 < R) (hyR : R ≤ y)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R) :
    archimedeanRealIntegrand g y ≤ 0 := by
  have hA : 0 ≤ (g.convolutionSquare.test 0).re :=
    g.convolutionSquare_zero_re_nonnegative
  rw [archimedeanRealIntegrand_eq_tail g R y hsupport hyR]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (narrowDen_pos y (lt_of_lt_of_le hRpos hyR)).le

private theorem archimedeanRealIntegrand_integral_le_narrow_budget
    (g : CompactLogTest) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R) :
    (∫ y in Ioi (0 : ℝ), archimedeanRealIntegrand g y) ≤
      (R - (1 / 2 : ℝ) * Real.log (1 / R)) *
        (g.convolutionSquare.test 0).re := by
  let A : ℝ := (g.convolutionSquare.test 0).re
  let f : ℝ → ℝ := archimedeanRealIntegrand g
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    simpa [f] using archimedeanRealIntegrand_integrableOn_Ioi g
  have hAint : IntegrableOn f (Ioc (0 : ℝ) R) := by
    apply hf.mono_set
    intro y hy
    exact hy.1
  have hBint : IntegrableOn f (Ioc R 1) := by
    apply hf.mono_set
    intro y hy
    exact lt_trans hRpos hy.1
  have hCint : IntegrableOn f (Ioi (1 : ℝ)) := by
    apply hf.mono_set
    intro y hy
    exact lt_trans hRpos (lt_trans hRlt hy)
  have hABdisj : Disjoint (Ioc (0 : ℝ) R) (Ioc R 1) := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact (not_lt_of_ge hyA.2) hyB.1
  have hBCdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hyB hyC
    exact (not_lt_of_ge hyB.2) hyC
  have hABset : Ioc (0 : ℝ) R ∪ Ioc R 1 = Ioc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioc, Set.mem_Ioc]
    constructor
    · rintro (hy | hy)
      · exact ⟨hy.1, hy.2.trans hRlt.le⟩
      · exact ⟨lt_trans hRpos hy.1, hy.2⟩
    · intro hy
      by_cases hle : y ≤ R
      · exact Or.inl ⟨hy.1, hle⟩
      · exact Or.inr ⟨lt_of_not_ge hle, hy.2⟩
  have hBCset : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by
    ext y
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi, Set.mem_Ioi]
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact lt_trans (by norm_num) hy
    · intro hy
      by_cases hle : y ≤ 1
      · exact Or.inl ⟨hy, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
  have hABint : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    apply hf.mono_set
    intro y hy
    exact hy.1
  have hsplitAB :
      (∫ y in Ioc (0 : ℝ) 1, f y) =
        (∫ y in Ioc (0 : ℝ) R, f y) +
          (∫ y in Ioc R 1, f y) := by
    rw [← hABset]
    exact MeasureTheory.setIntegral_union hABdisj measurableSet_Ioc hAint hBint
  have hsplitBC :
      (∫ y in Ioi (0 : ℝ), f y) =
        (∫ y in Ioc (0 : ℝ) 1, f y) +
          (∫ y in Ioi (1 : ℝ), f y) := by
    rw [← hBCset]
    exact MeasureTheory.setIntegral_union hBCdisj measurableSet_Ioi hABint hCint
  have hconstAint : IntegrableOn (fun _ : ℝ => A) (Ioc (0 : ℝ) R) := by
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
  have hnear_mono :
      (∫ y in Ioc (0 : ℝ) R, f y) ≤
        ∫ y in Ioc (0 : ℝ) R, A := by
    apply MeasureTheory.setIntegral_mono_on hAint hconstAint measurableSet_Ioc
    intro y hy
    exact archimedeanRealIntegrand_le_mass g R y hy.1 hy.2 hRlt.le
      (convolutionSquare_norm_le_mass g y)
  have hnear_const :
      (∫ y in Ioc (0 : ℝ) R, A) = A * R := by
    rw [MeasureTheory.setIntegral_const]
    simp [hRpos.le]
    ring
  have hnear : (∫ y in Ioc (0 : ℝ) R, f y) ≤ A * R := by
    exact hnear_mono.trans_eq hnear_const
  let q : ℝ → ℝ := fun y => (-A / 2) * (1 / y)
  have hqcont : ContinuousOn q (Icc R 1) := by
    dsimp [q]
    apply ContinuousOn.const_mul
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact (ne_of_gt (lt_of_lt_of_le hRpos hy.1))
  have hqint : IntegrableOn q (Ioc R 1) := by
    exact hqcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmid_mono :
      (∫ y in Ioc R 1, f y) ≤ ∫ y in Ioc R 1, q y := by
    apply MeasureTheory.setIntegral_mono_on hBint hqint measurableSet_Ioc
    intro y hy
    calc
      f y ≤ -(g.convolutionSquare.test 0).re / (2 * y) :=
        archimedeanRealIntegrand_le_neg_mass_div g R y hRpos
          (le_of_lt hy.1) hy.2 hsupport
      _ = q y := by
        dsimp [q, A]
        ring
  have hzero : (0 : ℝ) ∉ Set.uIcc R 1 :=
    notMem_uIcc_of_lt hRpos (by linarith)
  have hmid_exact :
      (∫ y in Ioc R 1, q y) =
        (-A / 2) * Real.log (1 / R) := by
    calc
      (∫ y in Ioc R 1, q y) = ∫ y in R..(1 : ℝ), q y := by
        rw [intervalIntegral.integral_of_le hRlt.le]
      _ = ∫ y in R..(1 : ℝ), (-A / 2) * (1 / y) := by rfl
      _ = (-A / 2) * (∫ y in R..(1 : ℝ), 1 / y) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (-A / 2) * Real.log (1 / R) := by
        simp only [one_div, integral_inv hzero]
  have hmid :
      (∫ y in Ioc R 1, f y) ≤ (-A / 2) * Real.log (1 / R) := by
    exact hmid_mono.trans_eq hmid_exact
  have hzeroCint : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_zero
  have htail : (∫ y in Ioi (1 : ℝ), f y) ≤ 0 := by
    have htail_mono :
        (∫ y in Ioi (1 : ℝ), f y) ≤
          ∫ y in Ioi (1 : ℝ), (0 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on hCint hzeroCint measurableSet_Ioi
      intro y hy
      exact archimedeanRealIntegrand_le_zero_of_ge_one g R y hRpos
        (hRlt.le.trans hy.le) hsupport
    simpa using htail_mono
  rw [show (∫ y in Ioi (0 : ℝ), f y) =
      (∫ y in Ioc (0 : ℝ) R, f y) +
        (∫ y in Ioc R 1, f y) +
        (∫ y in Ioi (1 : ℝ), f y) by rw [hsplitBC, hsplitAB]]
  have hsum :
      (∫ y in Ioc (0 : ℝ) R, f y) +
          (∫ y in Ioc R 1, f y) +
          (∫ y in Ioi (1 : ℝ), f y) ≤
        A * R + (-A / 2) * Real.log (1 / R) + 0 := by
    nlinarith [hnear, hmid, htail]
  calc
    (∫ y in Ioc (0 : ℝ) R, f y) +
          (∫ y in Ioc R 1, f y) +
          (∫ y in Ioi (1 : ℝ), f y) ≤
        A * R + (-A / 2) * Real.log (1 / R) + 0 := hsum
    _ = (R - (1 / 2 : ℝ) * Real.log (1 / R)) *
        (g.convolutionSquare.test 0).re := by
      dsimp [A]
      ring

private theorem archimedeanTerm_nonpos_of_narrow_budget
    (g : CompactLogTest) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R)
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0 := by
  rw [C1SameOwnerWeil.archimedeanTerm_square_eq_selected]
  rw [ConnesWeilRH.Source.CCM25Concrete.archimedeanTerm_re_eq_lead_add_integral]
  let C : ℝ := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant
  let A : ℝ := (g.convolutionSquare.test 0).re
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have hI :
      (∫ y in Ioi (0 : ℝ),
        (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re ≤
        (R - (1 / 2 : ℝ) * Real.log (1 / R)) * A := by
    calc
      (∫ y in Ioi (0 : ℝ),
          (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re =
          ∫ y in Ioi (0 : ℝ), archimedeanRealIntegrand g y := by
        exact (archimedeanRealIntegrand_integral_eq_selected_re g).symm
      _ ≤ (R - (1 / 2 : ℝ) * Real.log (1 / R)) * A := by
        simpa [A] using
          (archimedeanRealIntegrand_integral_le_narrow_budget g R hRpos hRlt hsupport)
  have hbudget' : C + R - (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0 := by
    simpa [C, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbudget
  have hmul : (C + R - (1 / 2 : ℝ) * Real.log (1 / R)) * A ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hbudget' hA
  calc
    C * A +
          (∫ y in Ioi (0 : ℝ),
            (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y).re ≤
        C * A + (R - (1 / 2 : ℝ) * Real.log (1 / R)) * A :=
      by simpa [add_comm] using add_le_add_left hI (C * A)
    _ = (C + R - (1 / 2 : ℝ) * Real.log (1 / R)) * A := by ring
    _ ≤ 0 := hmul

/-- The exact archimedean coefficient used by the narrow-support budget. -/
noncomputable def narrowArchCoefficient : ℝ :=
  Real.log (4 * Real.pi) + Real.eulerMascheroniConstant

theorem narrowArchCoefficient_pos : 0 < narrowArchCoefficient := by
  exact CCM25Concrete.archimedeanCoefficient_pos

/-- Choosing the support radius from the coefficient makes the budget algebraic. -/
noncomputable def narrowArchRadius : ℝ :=
  Real.exp (-4 * (narrowArchCoefficient + 1))

theorem narrowArchRadius_pos : 0 < narrowArchRadius := by
  exact Real.exp_pos _

theorem narrowArchRadius_lt_one : narrowArchRadius < 1 := by
  rw [narrowArchRadius, Real.exp_lt_one_iff]
  nlinarith [narrowArchCoefficient_pos]

theorem narrowArchRadius_log_inv :
    Real.log (1 / narrowArchRadius) = 4 * (narrowArchCoefficient + 1) := by
  rw [narrowArchRadius, one_div, Real.log_inv, Real.log_exp]
  ring

theorem narrowArchRadius_budget :
    narrowArchCoefficient + narrowArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / narrowArchRadius) ≤ 0 := by
  rw [narrowArchRadius_log_inv]
  have hR : narrowArchRadius ≤ 1 := narrowArchRadius_lt_one.le
  nlinarith [narrowArchCoefficient_pos]

noncomputable def narrowArchBaseWidth : ℝ := narrowArchRadius / 4

theorem narrowArchBaseWidth_pos : 0 < narrowArchBaseWidth := by
  exact div_pos narrowArchRadius_pos (by norm_num)

private theorem wideTest_support_subset_Icc
    (w : ℝ) (hw : 0 < w) :
    Function.support (Dev.M2Width.wideTest w hw).test ⊆ Icc (-w) w := by
  intro x hx
  have hne : Dev.M2Width.wideBump w x ≠ 0 := by
    intro hzero
    apply hx
    rw [Dev.M2Width.wideTest_apply]
    simp [hzero]
  exact Dev.M2Width.wideBump_mem_Icc w hw x hne

noncomputable def narrowArchRoot : CompactLogTest :=
  C1LaneRD3Root.tripleVanishingRoot
    (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos)

theorem narrowArchRoot_square_support :
    Function.support narrowArchRoot.convolutionSquare.test ⊆
      Ioo (-narrowArchRadius) narrowArchRadius := by
  have hbase := wideTest_support_subset_Icc
    narrowArchBaseWidth narrowArchBaseWidth_pos
  have hroot := C1LaneRD3Root.tripleVanishingRoot_support_subset_Icc
    (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos) hbase
  have hinput : Function.support narrowArchRoot.test ⊆
      Ioo (-(narrowArchRadius) / 2) (narrowArchRadius / 2) := by
    intro x hx
    have hx' := hroot hx
    rcases hx' with ⟨hxlow, hxhigh⟩
    dsimp [narrowArchBaseWidth] at hxlow hxhigh
    constructor <;> nlinarith [narrowArchRadius_pos]
  exact CC20YoshidaConvolution.CompactLogTest.convolutionSquare_support_subset_symmetric
    narrowArchRoot (a := narrowArchRadius) hinput

theorem narrowArchRoot_archimedeanTerm_nonpos :
    C1SameOwnerWeil.archimedeanTerm narrowArchRoot.convolutionSquare ≤ 0 := by
  apply archimedeanTerm_nonpos_of_narrow_budget narrowArchRoot narrowArchRadius
    narrowArchRadius_pos narrowArchRadius_lt_one narrowArchRoot_square_support
  simpa [narrowArchCoefficient] using narrowArchRadius_budget

theorem narrowArchRoot_square_support_subset_open_log_two :
    Function.support narrowArchRoot.convolutionSquare.test ⊆
      Ioo (-Real.log 2) (Real.log 2) := by
  have hbase := wideTest_support_subset_Icc
    narrowArchBaseWidth narrowArchBaseWidth_pos
  have hwidth : narrowArchBaseWidth < (3 / 10 : ℝ) := by
    dsimp [narrowArchBaseWidth]
    nlinarith [narrowArchRadius_lt_one]
  have hwide := C1LaneRD3Root.tripleVanishingRoot_square_support_subset_open_log_two_of_Icc
    (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos) hbase hwidth
  simpa [narrowArchRoot] using hwide

theorem narrowArchRoot_qw_eq_neg_archimedeanTerm :
    C1SameOwnerWeil.qw narrowArchRoot =
      -C1SameOwnerWeil.archimedeanTerm narrowArchRoot.convolutionSquare := by
  have hroot := C1LaneRD3Root.tripleVanishingRoot_qw_eq_neg_archimedeanTerm_of_primeFreeSquare
    (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos)
    (by simpa [narrowArchRoot] using narrowArchRoot_square_support_subset_open_log_two)
  simpa [narrowArchRoot] using hroot

theorem narrowArchRoot_qw_nonneg : 0 ≤ C1SameOwnerWeil.qw narrowArchRoot := by
  rw [narrowArchRoot_qw_eq_neg_archimedeanTerm]
  exact neg_nonneg.mpr narrowArchRoot_archimedeanTerm_nonpos

end C1LaneRNarrowArch
end Source
end ConnesWeilRH
