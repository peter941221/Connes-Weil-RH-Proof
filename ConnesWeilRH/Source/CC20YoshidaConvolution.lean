/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Source.CC20YoshidaTail
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedYoshidaBridge

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
open CCM25Concrete.SelectedYoshidaBridge
open scoped ContDiff
open scoped FourierTransform

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

/-- The selected positive-variable Mellin transform is the bilateral Laplace
transform of its compact log pullback. -/
theorem laplaceAt_compactLogTestOfWindow_eq_mellin
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b)
    (s : ℂ) :
    laplaceAt (compactLogTestOfWindow g ha hb hsupport) s =
      mellin
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) s := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  unfold laplaceAt
  simp only [exponentialWeight_apply, compactLogTestOfWindow_apply]
  rw [← integral_neg_eq_self
    (fun u : ℝ =>
      Complex.exp (s * (u : ℂ)) *
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp u))
    volume]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Complex.ofReal_neg, mul_neg, smul_eq_mul, Complex.real_smul]
  rw [Real.inner_apply, ← mul_assoc]
  change
    Complex.exp (-(s * (u : ℂ))) *
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp (-u)) =
      (Complex.exp
          (((-2 * Real.pi *
              (u * (s.im / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-s.re * u) : ℂ)) *
          normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp (-u))
  congr 1
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  have hphase :
      -2 * Real.pi * (u * (s.im / (2 * Real.pi))) = -(u * s.im) := by
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  apply Complex.ext <;>
    simp <;>
    ring

/-- The Mellin strip estimate is the same uniform quadratic estimate for the
bilateral Laplace transform of the compact log pullback. -/
theorem exists_uniform_laplaceAt_vertical_quadratic_decay
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt (compactLogTestOfWindow g ha hb hsupport)
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    CC20YoshidaTail.exists_uniform_mellin_vertical_quadratic_decay
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g)
      ha hb hsupport
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
  exact hbound sigma hsigma t

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

/-- A uniform strict contraction on a set becomes an arbitrarily small
uniform bound after enough genuine convolution factors. -/
theorem exists_convolutionIterate_laplaceAt_norm_le_of_uniform_contraction
    (f : CompactLogTest) (U : Set ℂ) (q epsilon : ℝ)
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (hepsilon : 0 < epsilon)
    (hcontraction : ∀ s ∈ U, ‖laplaceAt f s‖ ≤ q) :
    ∃ n : ℕ, ∀ s ∈ U,
      ‖laplaceAt (convolutionIterate f n) s‖ ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hepsilon hq_lt_one
  refine ⟨n, ?_⟩
  intro s hs
  rw [laplaceAt_convolutionIterate, norm_pow]
  calc
    ‖laplaceAt f s‖ ^ (n + 1) ≤ q ^ (n + 1) := by
      gcongr
      exact hcontraction s hs
    _ ≤ q ^ n :=
      pow_le_pow_of_le_one hq_nonneg hq_lt_one.le (Nat.le_succ n)
    _ ≤ epsilon := hn.le

/-- A bounded finite correction factor preserves the convolution-power tail
estimate after increasing the convolution count. -/
theorem exists_convolutionIterate_convolution_laplaceAt_norm_le
    (f correction : CompactLogTest) (U : Set ℂ) (q B epsilon : ℝ)
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (hB_nonneg : 0 ≤ B)
    (hepsilon : 0 < epsilon)
    (hcontraction : ∀ s ∈ U, ‖laplaceAt f s‖ ≤ q)
    (hcorrection : ∀ s ∈ U, ‖laplaceAt correction s‖ ≤ B) :
    ∃ n : ℕ, ∀ s ∈ U,
      ‖laplaceAt ((convolutionIterate f n).convolution correction) s‖ ≤ epsilon := by
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (by positivity : 0 < epsilon / (B + 1)) hq_lt_one
  refine ⟨n, ?_⟩
  intro s hs
  rw [laplaceAt_convolution, laplaceAt_convolutionIterate, norm_mul, norm_pow]
  apply le_of_lt
  calc
    ‖laplaceAt f s‖ ^ (n + 1) * ‖laplaceAt correction s‖ ≤ q ^ (n + 1) * B := by
      gcongr
      exact hcontraction s hs
      exact hcorrection s hs
    _ ≤ q ^ n * B := by
      apply mul_le_mul_of_nonneg_right _ hB_nonneg
      simpa [Nat.succ_eq_add_one] using
        pow_le_pow_of_le_one hq_nonneg hq_lt_one.le (Nat.le_succ n)
    _ < epsilon := by
      calc
        q ^ n * B ≤ q ^ n * (B + 1) := by
          gcongr
          linarith
        _ < (epsilon / (B + 1)) * (B + 1) :=
          mul_lt_mul_of_pos_right hn (by linarith)
        _ = epsilon := by
          field_simp

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

/-- The support budget for one finite correction factor adds its log-window to
the `(n + 1)` copies consumed by the convolution power. -/
theorem convolutionIterate_convolution_support_subset_Ioo
    (f correction : CompactLogTest) {lower upper correctionLower correctionUpper : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper)
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo correctionLower correctionUpper)
    (n : ℕ) :
    Function.support ((convolutionIterate f n).convolution correction).test ⊆
      Set.Ioo ((n + 1 : ℕ) * lower + correctionLower)
        ((n + 1 : ℕ) * upper + correctionUpper) := by
  exact convolution_support_subset_add_Ioo
    (convolutionIterate f n) correction
    (convolutionIterate_support_subset_Ioo f hsupport n)
    hcorrection

end CompactLogTest
end CC20YoshidaConvolution
end Source
end ConnesWeilRH
