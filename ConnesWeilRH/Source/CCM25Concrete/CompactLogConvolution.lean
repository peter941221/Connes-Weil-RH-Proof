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

end CompactLogTest
end CompactLogConvolution
end CCM25Concrete
end Source
end ConnesWeilRH
