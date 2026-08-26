/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Compact log-coordinate convolution tests

CCM25 uses additive convolution after passing from the multiplicative variable
to its logarithm. This module packages the compact smooth tests on which that
convolution remains a Schwartz function.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CompactLogConvolution

open MeasureTheory
open scoped ContDiff

/-- A Schwartz test with compact support in the additive log coordinate. -/
structure CompactLogTest where
  test : TestFunction
  compactSupport : HasCompactSupport test

namespace CompactLogTest

/-- Compact logarithmic tests are determined by their underlying Schwartz
functions; the compact-support field is proof data. -/
@[ext] theorem ext {f g : CompactLogTest} (h : f.test = g.test) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          dsimp only at h
          subst g
          rfl

/-- Reflection in the additive log coordinate, without complex conjugation. -/
noncomputable def reflection (f : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => f.test (-x)
  have hcompact : HasCompactSupport raw := by
    simpa [raw] using f.compactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have hsmooth : ContDiff ℝ ∞ raw := by
    fun_prop
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem reflection_apply (f : CompactLogTest) (x : ℝ) :
    f.reflection.test x = f.test (-x) :=
  rfl

/-- Reflection sends a support interval `[a,c]` to `[-c,-a]`. -/
theorem reflection_support_subset_Icc
    (f : CompactLogTest) (a c : ℝ)
    (hsupp : Function.support f.test ⊆ Set.Icc a c) :
    Function.support f.reflection.test ⊆ Set.Icc (-c) (-a) := by
  intro x hx
  have hreflected : f.test (-x) ≠ 0 := by
    simpa only [reflection_apply] using hx
  rcases hsupp hreflected with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- The CCM25 involution `f*(x) = conj (f(-x))`. -/
noncomputable def involution (f : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => star (f.test (-x))
  have hreflected : HasCompactSupport (fun x : ℝ => f.test (-x)) := by
    simpa using f.compactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have hcompact : HasCompactSupport raw :=
    hreflected.comp_left (by simp)
  have hsmooth : ContDiff ℝ ∞ raw := by
    have hinner : ContDiff ℝ ∞ (fun x : ℝ => f.test (-x)) := by
      fun_prop
    simpa [raw, Complex.star_def] using
      Complex.conjCLE.contDiff.comp hinner
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem involution_apply (f : CompactLogTest) (x : ℝ) :
    f.involution.test x = star (f.test (-x)) :=
  rfl

/-- Additive convolution in the log coordinate. -/
noncomputable def convolution (f g : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ :=
    MeasureTheory.convolution f.test g.test
      (ContinuousLinearMap.mul ℝ ℂ) volume
  have hcompact : HasCompactSupport raw := by
    exact f.compactSupport.convolution
      (ContinuousLinearMap.mul ℝ ℂ) g.compactSupport
  have hsmooth : ContDiff ℝ ∞ raw := by
    exact g.compactSupport.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) f.test.integrable.locallyIntegrable
      (g.test.smooth ⊤)
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem convolution_apply (f g : CompactLogTest) (x : ℝ) :
    (f.convolution g).test x =
      ∫ t : ℝ, f.test t * g.test (x - t) :=
  rfl

/-- The selected CCM25 half-density square `g* * g`. -/
noncomputable def convolutionSquare (g : CompactLogTest) : CompactLogTest :=
  g.involution.convolution g

@[simp] theorem convolutionSquare_apply (g : CompactLogTest) (x : ℝ) :
    g.convolutionSquare.test x =
      ∫ t : ℝ, star (g.test (-t)) * g.test (x - t) := by
  rfl

/-- The genuine convolution square is Hermitian: `F(-x) = conj (F x)`. -/
theorem convolutionSquare_neg (g : CompactLogTest) (x : ℝ) :
    g.convolutionSquare.test (-x) = star (g.convolutionSquare.test x) := by
  rw [convolutionSquare_apply, convolutionSquare_apply]
  simp only [Complex.star_def]
  rw [← integral_conj]
  let reflected : ℝ → ℂ := fun t =>
    g.test (-t) * star (g.test (x - t))
  calc
    (∫ t : ℝ, star (g.test (-t)) * g.test (-x - t)) =
        ∫ t : ℝ, reflected (t + x) := by
      apply integral_congr_ae
      filter_upwards with t
      have hleft : -(t + x) = -x - t := by ring
      have hright : x - (t + x) = -t := by ring
      simp only [reflected, hleft, hright, mul_comm]
    _ = ∫ t : ℝ, reflected t := integral_add_right_eq_self reflected x
    _ = ∫ t : ℝ, star (star (g.test (-t)) * g.test (x - t)) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [reflected, star_mul, star_star]
      exact mul_comm _ _

/-- Reflecting the root reflects its convolution square. -/
theorem reflection_convolutionSquare_apply
    (g : CompactLogTest) (x : ℝ) :
    g.reflection.convolutionSquare.test x =
      g.convolutionSquare.test (-x) := by
  rw [convolutionSquare_apply, convolutionSquare_apply]
  simp only [reflection_apply, neg_neg]
  let reflected : ℝ → ℂ := fun t =>
    star (g.test (-t)) * g.test (-x - t)
  calc
    (∫ t : ℝ, star (g.test t) * g.test (-(x - t))) =
        ∫ t : ℝ, reflected (-t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [reflected, neg_neg]
      congr 2 <;> ring
    _ = ∫ t : ℝ, reflected t :=
      integral_neg_eq_self reflected (volume : Measure ℝ)

/-- At zero the convolution square is the integral of the pointwise norm square. -/
theorem convolutionSquare_zero_eq_integral_normSq (g : CompactLogTest) :
    g.convolutionSquare.test 0 =
      ((∫ t : ℝ, Complex.normSq (g.test t) : ℝ) : ℂ) := by
  rw [convolutionSquare_apply]
  calc
    (∫ t : ℝ, star (g.test (-t)) * g.test (0 - t)) =
        ∫ t : ℝ, (Complex.normSq (g.test (-t)) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      simp [Complex.normSq_eq_conj_mul_self]
    _ = ∫ t : ℝ, (Complex.normSq (g.test t) : ℂ) := by
      simpa using (integral_neg_eq_self
        (fun t : ℝ => (Complex.normSq (g.test t) : ℂ))
        (volume : Measure ℝ))
    _ = ((∫ t : ℝ, Complex.normSq (g.test t) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]

theorem convolutionSquare_zero_im (g : CompactLogTest) :
    (g.convolutionSquare.test 0).im = 0 := by
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  simp

theorem convolutionSquare_zero_re_nonnegative (g : CompactLogTest) :
    0 ≤ (g.convolutionSquare.test 0).re := by
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  simp only [Complex.ofReal_re]
  exact integral_nonneg fun t => Complex.normSq_nonneg (g.test t)

/-- The symmetric evaluation used by the finite-prime term is real. -/
theorem convolutionSquare_add_neg_eq_two_re (g : CompactLogTest) (x : ℝ) :
    g.convolutionSquare.test x + g.convolutionSquare.test (-x) =
      ((2 * (g.convolutionSquare.test x).re : ℝ) : ℂ) := by
  rw [g.convolutionSquare_neg]
  apply Complex.ext
  · simp
    ring
  · simp

/-- A root supported in a symmetric interval has its Hermitian convolution
square supported in the doubled interval: a nonzero value at `x` needs both
convolution factors nonzero at points whose difference is `x`. -/
theorem convolutionSquare_support_subset_two_mul
    (g : CompactLogTest) {a : ℝ}
    (hsupport : Function.support g.test ⊆ Set.Icc (-a) a) :
    Function.support g.convolutionSquare.test ⊆ Set.Icc (-(2 * a)) (2 * a) := by
  intro x hx
  by_contra hout
  have hxne : g.convolutionSquare.test x ≠ 0 := Function.mem_support.mp hx
  have hint : (fun t : ℝ => star (g.test (-t)) * g.test (x - t)) = 0 := by
    funext t
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have hu := hsupport (star_ne_zero.mp h1)
    have hv := hsupport h2
    exact hout ⟨by linarith [hu.1, hu.2, hv.1, hv.2],
      by linarith [hu.1, hu.2, hv.1, hv.2]⟩
  rw [convolutionSquare_apply, hint] at hxne
  simp at hxne

/-- At the doubled endpoint the Hermitian convolution square vanishes: the two
root-support windows then overlap in at most one point, and the continuous
integrand with support inside a singleton is identically zero. -/
theorem convolutionSquare_two_mul_eq_zero
    (g : CompactLogTest) {a : ℝ}
    (hsupport : Function.support g.test ⊆ Set.Icc (-a) a) :
    g.convolutionSquare.test (2 * a) = 0 := by
  have hpoint : ∀ t : ℝ,
      star (g.test (-t)) * g.test (2 * a - t) ≠ 0 → t = a := by
    intro t ht
    have h1 := left_ne_zero_of_mul ht
    have h2 := right_ne_zero_of_mul ht
    have hu := hsupport (star_ne_zero.mp h1)
    have hv := hsupport h2
    linarith [hu.1, hu.2, hv.1, hv.2]
  have hint : (fun t : ℝ => star (g.test (-t)) * g.test (2 * a - t)) = 0 := by
    funext t
    by_contra hne
    have hta : a = t := (hpoint t hne).symm
    subst hta
    have hctest := SchwartzMap.continuous g.test
    have hcont : Continuous fun t : ℝ => star (g.test (-t)) * g.test (2 * a - t) :=
      (hctest.comp continuous_neg).star.mul
        (hctest.comp (continuous_const.sub continuous_id))
    have hnonzero : a ∈
        (fun t : ℝ => star (g.test (-t)) * g.test (2 * a - t)) ⁻¹'
          {z : ℂ | z ≠ 0} := hne
    have hopen : IsOpen
        ((fun t : ℝ => star (g.test (-t)) * g.test (2 * a - t)) ⁻¹'
          {z : ℂ | z ≠ 0}) :=
      hcont.isOpen_preimage _ isOpen_ne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a hnonzero
    have hmem : a - ε / 2 ∈
        (fun t : ℝ => star (g.test (-t)) * g.test (2 * a - t)) ⁻¹'
          {z : ℂ | z ≠ 0} := by
      refine hball ?_
      simp only [Metric.mem_ball, Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith
    have heq : a - ε / 2 = a := hpoint _ hmem
    linarith
  rw [convolutionSquare_apply, hint]
  simp

/-- The Hermitian convolution square of a root supported in a symmetric
interval is supported in the OPEN doubled interval: both endpoints carry no
mass because the root-support windows only touch there. -/
theorem convolutionSquare_support_subset_two_mul_Ioo
    (g : CompactLogTest) {a : ℝ}
    (hsupport : Function.support g.test ⊆ Set.Icc (-a) a) :
    Function.support g.convolutionSquare.test ⊆ Set.Ioo (-(2 * a)) (2 * a) := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := convolutionSquare_support_subset_two_mul g hsupport hx
  have hright : g.convolutionSquare.test (2 * a) = 0 :=
    convolutionSquare_two_mul_eq_zero g hsupport
  have hleft : g.convolutionSquare.test (-(2 * a)) = 0 := by
    rw [g.convolutionSquare_neg, hright]
    simp
  have hxne : g.convolutionSquare.test x ≠ 0 := Function.mem_support.mp hx
  constructor
  · by_contra hle
    have hxeq : x = -(2 * a) := by linarith
    rw [hxeq] at hxne
    exact hxne hleft
  · by_contra hle
    have hxeq : x = 2 * a := by linarith
    rw [hxeq] at hxne
    exact hxne hright

end CompactLogTest
end CompactLogConvolution
end CCM25Concrete
end Source
end ConnesWeilRH
