/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CC20YoshidaFullProduct
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Lane R: differential construction of a triple-vanishing root

The bilateral Laplace transform turns the compactly supported differential
operator `D_a f = f' + a f` into multiplication by `a - s`.  Composing the
three shifts with `a = 1`, `1 / 2`, and `0` therefore forces zeros at the
three healthy criterion nodes.  This file records the owner-preserving
construction and the single-shift transform law; it does not assert the
remaining archimedean sign inequality.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LaneRD3Root

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open scoped ContDiff

private theorem contDiff_deriv_compactLogTest (f : CompactLogTest) :
    ContDiff ℝ ∞ (deriv (f.test : ℝ → ℂ)) := by
  simpa [Function.iterate_succ_apply] using
    (ContDiff.iterate_deriv 1 (f.test.smooth ⊤))

private theorem hasCompactSupport_deriv_compactLogTest (f : CompactLogTest) :
    HasCompactSupport (deriv (f.test : ℝ → ℂ)) := by
  exact f.compactSupport.deriv

/-- One Laplace-side differential shift, with its own compact-log owner. -/
noncomputable def derivativeShift (f : CompactLogTest) (a : ℂ) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => deriv (f.test : ℝ → ℂ) x + a * f.test x
  have hcompact : HasCompactSupport raw := by
    exact (hasCompactSupport_deriv_compactLogTest f).add
      (f.compactSupport.mul_left)
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    exact (contDiff_deriv_compactLogTest f).add
      (contDiff_const.mul (f.test.smooth ⊤))
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem derivativeShift_apply
    (f : CompactLogTest) (a : ℂ) (x : ℝ) :
    (derivativeShift f a).test x =
      deriv (f.test : ℝ → ℂ) x + a * f.test x :=
  rfl

private theorem derivativeShift_integrand_integrable
    (f : CompactLogTest) (a s : ℂ) :
    Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) *
        (deriv (f.test : ℝ → ℂ) x + a * f.test x)) := by
  have hcont : Continuous (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) *
        (deriv (f.test : ℝ → ℂ) x + a * f.test x)) := by
    exact
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
        ((contDiff_deriv_compactLogTest f).continuous.add
          (continuous_const.mul (f.test.smooth ⊤).continuous))
  have hcompact : HasCompactSupport (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) *
        (deriv (f.test : ℝ → ℂ) x + a * f.test x)) := by
    exact (hasCompactSupport_deriv_compactLogTest f).add
      (f.compactSupport.mul_left) |>.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem laplaceAt_derivativeShift
    (f : CompactLogTest) (a s : ℂ) :
    laplaceAt (derivativeShift f a) s =
      (a - s) * laplaceAt f s := by
  let u : ℝ → ℂ := fun x =>
    Complex.exp (s * (x : ℂ)) * f.test x
  let u' : ℝ → ℂ := fun x =>
    Complex.exp (s * (x : ℂ)) *
      (s * f.test x + deriv (f.test : ℝ → ℂ) x)
  have hu_cont : Continuous u := by
    dsimp [u]
    exact
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
        (f.test.smooth ⊤).continuous
  have hu_compact : HasCompactSupport u := by
    dsimp [u]
    exact f.compactSupport.mul_left
  have hu : Integrable u := hu_cont.integrable_of_hasCompactSupport hu_compact
  have hscaled : HasCompactSupport (fun x : ℝ => s * f.test x) := by
    have hscaledRaw : HasCompactSupport
        ((fun _ : ℝ => s) * (f.test : ℝ → ℂ)) :=
      f.compactSupport.mul_left
    simpa only [Pi.mul_apply] using hscaledRaw
  have hexpScaled : HasCompactSupport (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * (s * f.test x)) := by
    have hraw : HasCompactSupport
        ((fun x : ℝ => Complex.exp (s * (x : ℂ))) *
          (fun x : ℝ => s * f.test x)) :=
      hscaled.mul_left
    simpa only [Pi.mul_apply] using hraw
  have hexpDeriv : HasCompactSupport (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) := by
    have hraw : HasCompactSupport
        ((fun x : ℝ => Complex.exp (s * (x : ℂ))) *
          deriv (f.test : ℝ → ℂ)) :=
      (hasCompactSupport_deriv_compactLogTest f).mul_left
    simpa only [Pi.mul_apply] using hraw
  have hu'_cont : Continuous u' := by
    dsimp [u']
    exact
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).mul
        ((continuous_const.mul (f.test.smooth ⊤).continuous).add
          (contDiff_deriv_compactLogTest f).continuous)
  have hu'_compact : HasCompactSupport u' := by
    dsimp [u']
    simpa only [mul_add] using hexpScaled.add hexpDeriv
  have hu' : Integrable u' :=
    hu'_cont.integrable_of_hasCompactSupport hu'_compact
  have hderiv : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => s * (y : ℂ)) s x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul s).comp_ofReal
    have hexp : HasDerivAt
        (fun y : ℝ => Complex.exp (s * (y : ℂ)))
        (s * Complex.exp (s * (x : ℂ))) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
    have hf : HasDerivAt (fun y : ℝ => f.test y)
        (deriv (f.test : ℝ → ℂ) x) x :=
      ((f.test.smooth ⊤).differentiable (by simp) x).hasDerivAt
    have hprod := hexp.mul hf
    convert hprod using 1
    simp only [u']
    ring
  have hzero : (∫ x : ℝ, u' x) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderiv hu' hu
  have hderiv_integrable : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) := by
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) := by
      exact
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).mul
          (contDiff_deriv_compactLogTest f).continuous
    have hcompact : HasCompactSupport (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) :=
      hexpDeriv
    exact hcont.integrable_of_hasCompactSupport hcompact
  have hmul_integrable : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * (s * f.test x)) := by
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (s * f.test x)) := by
      exact
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.mul (f.test.smooth ⊤).continuous)
    have hcompact : HasCompactSupport (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (s * f.test x)) :=
      hexpScaled
    exact hcont.integrable_of_hasCompactSupport hcompact
  have ha_integrable : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * (a * f.test x)) := by
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (a * f.test x)) := by
      exact
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.mul (f.test.smooth ⊤).continuous)
    have hcompact : HasCompactSupport (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (a * f.test x)) := by
      have hscaledA : HasCompactSupport (fun x : ℝ => a * f.test x) := by
        have hraw : HasCompactSupport
            ((fun _ : ℝ => a) * (f.test : ℝ → ℂ)) :=
          f.compactSupport.mul_left
        simpa only [Pi.mul_apply] using hraw
      have hraw : HasCompactSupport
          ((fun x : ℝ => Complex.exp (s * (x : ℂ))) *
            (fun x : ℝ => a * f.test x)) :=
        hscaledA.mul_left
      simpa only [Pi.mul_apply] using hraw
    exact hcont.integrable_of_hasCompactSupport hcompact
  have hzero' : (∫ x : ℝ,
      Complex.exp (s * (x : ℂ)) * (s * f.test x) +
        Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) = 0 := by
    calc
      (∫ x : ℝ,
          Complex.exp (s * (x : ℂ)) * (s * f.test x) +
            Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) =
          ∫ x : ℝ, u' x := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [u']
            ring
      _ = 0 := hzero
  rw [integral_add hmul_integrable hderiv_integrable] at hzero'
  have hmul : (∫ x : ℝ,
      Complex.exp (s * (x : ℂ)) * (s * f.test x)) =
      s * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x) := by
    calc
      (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * (s * f.test x)) =
          ∫ x : ℝ, s * (Complex.exp (s * (x : ℂ)) * f.test x) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = s * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x) := by
        rw [integral_const_mul]
  have ha : (∫ x : ℝ,
      Complex.exp (s * (x : ℂ)) * (a * f.test x)) =
      a * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x) := by
    calc
      (∫ x : ℝ,
          Complex.exp (s * (x : ℂ)) * (a * f.test x)) =
          ∫ x : ℝ, a * (Complex.exp (s * (x : ℂ)) * f.test x) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = a * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x) := by
        rw [integral_const_mul]
  have hfull : (∫ x : ℝ,
      Complex.exp (s * (x : ℂ)) *
        (deriv (f.test : ℝ → ℂ) x + a * f.test x)) =
      (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) +
        (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * (a * f.test x)) := by
    calc
      (∫ x : ℝ,
          Complex.exp (s * (x : ℂ)) *
            (deriv (f.test : ℝ → ℂ) x + a * f.test x)) =
          ∫ x : ℝ,
            (Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) +
              (Complex.exp (s * (x : ℂ)) * (a * f.test x)) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x : ℝ,
          Complex.exp (s * (x : ℂ)) * deriv (f.test : ℝ → ℂ) x) +
          (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * (a * f.test x)) :=
        integral_add hderiv_integrable ha_integrable
  rw [hmul] at hzero'
  have hformula : (∫ x : ℝ,
      Complex.exp (s * (x : ℂ)) *
        (deriv (f.test : ℝ → ℂ) x + a * f.test x)) =
      (a - s) * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x) := by
    rw [hfull, ha]
    linear_combination hzero'
  unfold laplaceAt
  simp only [exponentialWeight_apply, derivativeShift_apply]
  exact hformula

/-- A differential root that vanishes at the three healthy criterion nodes. -/
noncomputable def tripleVanishingRoot (h : CompactLogTest) : CompactLogTest :=
  derivativeShift
    (derivativeShift
      (derivativeShift h 1)
      (1 / 2 : ℂ))
    0

theorem laplaceAt_tripleVanishingRoot
    (h : CompactLogTest) (s : ℂ) :
    laplaceAt (tripleVanishingRoot h) s =
      (0 - s) * ((1 / 2 : ℂ) - s) * (1 - s) * laplaceAt h s := by
  simp [tripleVanishingRoot, laplaceAt_derivativeShift, mul_assoc]

/-- A nonzero Laplace value away from the three differential roots prevents
the D3 construction from collapsing to the zero test. -/
theorem tripleVanishingRoot_test_ne_zero_of_laplaceAt_two
    (h : CompactLogTest)
    (hlap : laplaceAt h (2 : ℂ) ≠ 0) :
    (tripleVanishingRoot h).test ≠ 0 := by
  intro hzero
  have hrootLap : laplaceAt (tripleVanishingRoot h) (2 : ℂ) = 0 := by
    unfold laplaceAt
    simp only [exponentialWeight_apply]
    rw [hzero]
    simp
  have hprod :
      ((0 - (2 : ℂ)) * ((1 / 2 : ℂ) - 2) * (1 - 2)) *
          laplaceAt h (2 : ℂ) = 0 := by
    rw [← laplaceAt_tripleVanishingRoot h (2 : ℂ)]
    exact hrootLap
  rcases mul_eq_zero.mp hprod with hfactor | hbase
  · norm_num at hfactor
  · exact hlap hbase

@[simp] theorem tripleVanishingRoot_laplaceAt_zero
    (h : CompactLogTest) :
    laplaceAt (tripleVanishingRoot h) 0 = 0 := by
  rw [laplaceAt_tripleVanishingRoot]
  norm_num

@[simp] theorem tripleVanishingRoot_laplaceAt_half
    (h : CompactLogTest) :
    laplaceAt (tripleVanishingRoot h) (1 / 2 : ℂ) = 0 := by
  rw [laplaceAt_tripleVanishingRoot]
  norm_num

@[simp] theorem tripleVanishingRoot_laplaceAt_one
    (h : CompactLogTest) :
    laplaceAt (tripleVanishingRoot h) 1 = 0 := by
  rw [laplaceAt_tripleVanishingRoot]
  norm_num

theorem tripleVanishingRoot_vanishesOn_cc20Triple
    (h : CompactLogTest) :
    CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (tripleVanishingRoot h) := by
  intro p _hp
  cases p with
  | zero =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        tripleVanishingRoot_laplaceAt_zero h
  | half =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        tripleVanishingRoot_laplaceAt_half h
  | one =>
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
        tripleVanishingRoot_laplaceAt_one h

theorem tripleVanishingRoot_poleTerm_eq_zero
    (h : CompactLogTest) :
    C1SameOwnerWeil.poleTerm (tripleVanishingRoot h).convolutionSquare = 0 :=
  C1HealthyYoshidaDetector.poleTerm_convolutionSquare_of_vanishesOn_cc20Triple
    (tripleVanishingRoot h) (tripleVanishingRoot_vanishesOn_cc20Triple h)

theorem tripleVanishingRoot_qw_eq_neg_archimedeanTerm_of_primeFreeSquare
    (h : CompactLogTest)
    (hsupport :
      Function.support (tripleVanishingRoot h).convolutionSquare.test ⊆
        Set.Ioo (-Real.log 2) (Real.log 2)) :
    C1SameOwnerWeil.qw (tripleVanishingRoot h) =
      -C1SameOwnerWeil.archimedeanTerm
        (tripleVanishingRoot h).convolutionSquare :=
  C1HealthyYoshidaDetector.qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    (tripleVanishingRoot h) (tripleVanishingRoot_vanishesOn_cc20Triple h) hsupport

theorem derivativeShift_support_subset_Icc
    (f : CompactLogTest) (a : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w) :
    Function.support ((derivativeShift f a).test : ℝ → ℂ) ⊆ Set.Icc (-w) w := by
  intro x hx
  have htsupport : tsupport (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w := by
    simpa [isClosed_Icc.closure_eq] using closure_mono hsupport
  by_contra hnot
  have hxnot_tsupport : x ∉ tsupport (f.test : ℝ → ℂ) := by
    intro hxmem
    exact hnot (htsupport hxmem)
  have hderivzero : deriv (f.test : ℝ → ℂ) x = 0 :=
    deriv_of_notMem_tsupport hxnot_tsupport
  have hxnot_support : x ∉ Function.support (f.test : ℝ → ℂ) := by
    intro hxmem
    exact hnot (hsupport hxmem)
  have hfzero : f.test x = 0 := by
    by_contra hne
    exact hxnot_support hne
  rw [Function.mem_support] at hx
  exact hx (by simp [derivativeShift_apply, hderivzero, hfzero])

theorem tripleVanishingRoot_support_subset_Icc
    (f : CompactLogTest) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w) :
    Function.support ((tripleVanishingRoot f).test : ℝ → ℂ) ⊆ Set.Icc (-w) w := by
  unfold tripleVanishingRoot
  exact derivativeShift_support_subset_Icc _ _
    (derivativeShift_support_subset_Icc _ _
      (derivativeShift_support_subset_Icc f 1 hsupport))

theorem tripleVanishingRoot_square_support_subset_open_log_two_of_Icc
    (f : CompactLogTest) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : ℝ)) :
    Function.support (tripleVanishingRoot f).convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
  have hroot := tripleVanishingRoot_support_subset_Icc f hsupport
  have hopen : Function.support (tripleVanishingRoot f).test ⊆
      Set.Ioo (-(3 / 5 : ℝ) / 2) ((3 / 5 : ℝ) / 2) := by
    intro x hx
    rcases hroot hx with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hsquare := convolutionSquare_support_subset_symmetric
    (tripleVanishingRoot f) (a := (3 / 5 : ℝ)) hopen
  have hlog : (3 / 5 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

end C1LaneRD3Root
end Source
end ConnesWeilRH
