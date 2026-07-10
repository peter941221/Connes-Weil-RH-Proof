/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-!
# Genuine convolution for the source Yoshida construction

Yoshida's approximation uses additive convolution after passing to the
logarithmic coordinate. This module records the support addition law and the
bilateral Laplace product law for the existing compact log tests.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaConvolution

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open scoped ContDiff

namespace CompactLogTest

/-- Multiplication by the exponential character used in a bilateral Laplace
evaluation. -/
noncomputable def exponentialWeight (f : CompactLogTest) (s : ℂ) :
    CompactLogTest := by
  let raw : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ)) * f.test x
  have hcompact : HasCompactSupport raw := f.compactSupport.mul_left
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    have hlinear : ContDiff ℝ ∞ (fun x : ℝ => s * (x : ℂ)) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    exact hlinear.cexp.mul (f.test.smooth ⊤)
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem exponentialWeight_apply
    (f : CompactLogTest) (s : ℂ) (x : ℝ) :
    (exponentialWeight f s).test x =
      Complex.exp (s * (x : ℂ)) * f.test x :=
  rfl

/-- Bilateral Laplace evaluation of a compact log test. -/
noncomputable def laplaceAt (f : CompactLogTest) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (exponentialWeight f s).test x

theorem convolution_support_subset_add_Ioo
    (f g : CompactLogTest) {fLower fUpper gLower gUpper : ℝ}
    (hf : Function.support f.test ⊆ Set.Ioo fLower fUpper)
    (hg : Function.support g.test ⊆ Set.Ioo gLower gUpper) :
    Function.support (f.convolution g).test ⊆
      Set.Ioo (fLower + gLower) (fUpper + gUpper) := by
  intro x hx
  have hxconv : x ∈ Function.support
      (MeasureTheory.convolution f.test g.test
        (ContinuousLinearMap.mul ℝ ℂ) volume) := by
    simpa [CompactLogTest.convolution_apply] using hx
  have hxadd := MeasureTheory.support_convolution_subset
    (ContinuousLinearMap.mul ℝ ℂ) hxconv
  rcases Set.mem_add.mp hxadd with ⟨y, hy, z, hz, hyz⟩
  have hyBounds := hf hy
  have hzBounds := hg hz
  constructor
  · rw [← hyz]
    exact add_lt_add hyBounds.1 hzBounds.1
  · rw [← hyz]
    exact add_lt_add hyBounds.2 hzBounds.2

theorem exponentialWeight_convolution_apply
    (f g : CompactLogTest) (s : ℂ) (x : ℝ) :
    (exponentialWeight (f.convolution g) s).test x =
      ((exponentialWeight f s).convolution
        (exponentialWeight g s)).test x := by
  simp only [exponentialWeight_apply, CompactLogTest.convolution_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hexp :
      Complex.exp (s * (x : ℂ)) =
        Complex.exp (s * (t : ℂ)) *
          Complex.exp (s * ((x - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Additive log convolution becomes multiplication under the bilateral
Laplace transform. This is the source convolution law used in Yoshida's
convolution-power tail argument. -/
theorem laplaceAt_convolution
    (f g : CompactLogTest) (s : ℂ) :
    laplaceAt (f.convolution g) s = laplaceAt f s * laplaceAt g s := by
  unfold laplaceAt
  have hfun :
      (fun x : ℝ => (exponentialWeight (f.convolution g) s).test x) =
        fun x : ℝ =>
          ((exponentialWeight f s).convolution
            (exponentialWeight g s)).test x := by
    funext x
    exact exponentialWeight_convolution_apply f g s x
  rw [hfun]
  simpa only [CompactLogTest.convolution_apply,
    ContinuousLinearMap.mul_apply'] using
    (MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℂ)
      (exponentialWeight f s).test.integrable
      (exponentialWeight g s).test.integrable)

/-- A nonempty convolution iterate. Index `n` represents `n + 1` copies of
the same compact test, avoiding a distributional convolution unit. -/
noncomputable def convolutionIterate (f : CompactLogTest) : ℕ → CompactLogTest
  | 0 => f
  | n + 1 => (convolutionIterate f n).convolution f

@[simp] theorem convolutionIterate_zero (f : CompactLogTest) :
    convolutionIterate f 0 = f :=
  rfl

@[simp] theorem convolutionIterate_succ (f : CompactLogTest) (n : ℕ) :
    convolutionIterate f (n + 1) =
      (convolutionIterate f n).convolution f :=
  rfl

theorem laplaceAt_convolutionIterate
    (f : CompactLogTest) (s : ℂ) (n : ℕ) :
    laplaceAt (convolutionIterate f n) s = laplaceAt f s ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convolutionIterate_succ, laplaceAt_convolution, ih]
      exact (pow_succ _ (n + 1)).symm

theorem convolutionIterate_support_subset_Ioo
    (f : CompactLogTest) {lower upper : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper)
    (n : ℕ) :
    Function.support (convolutionIterate f n).test ⊆
      Set.Ioo ((n + 1 : ℕ) * lower) ((n + 1 : ℕ) * upper) := by
  induction n with
  | zero =>
      simpa using hsupport
  | succ n ih =>
      have hadd := convolution_support_subset_add_Ioo
        (convolutionIterate f n) f ih hsupport
      convert hadd using 1 <;> norm_num <;> ring_nf

end CompactLogTest
end CC20YoshidaConvolution
end Source
end ConnesWeilRH
