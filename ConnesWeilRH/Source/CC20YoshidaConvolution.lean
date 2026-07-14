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
open CC20YoshidaNearZeros
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

/-- The uniform quadratic strip bound gives a strict uniform contraction away
from a finite vertical region. -/
theorem exists_uniform_laplaceAt_vertical_half_contraction
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
        ‖laplaceAt (compactLogTestOfWindow g ha hb hsupport)
          ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay g ha hb hsupport
  refine ⟨2 * Real.pi * Real.sqrt (2 * C + 1), by positivity, ?_⟩
  intro sigma hsigma t hT
  have hpi : 0 < 2 * Real.pi := by positivity
  have hroot : 0 ≤ Real.sqrt (2 * C + 1) := Real.sqrt_nonneg _
  have hroot_sq : Real.sqrt (2 * C + 1) ^ 2 = 2 * C + 1 := by
    rw [Real.sq_sqrt]
    linarith
  have hquotient : Real.sqrt (2 * C + 1) ≤ |t| / (2 * Real.pi) :=
    (le_div_iff₀ hpi).2 (by simpa [mul_comm] using hT)
  have hfrequency : 2 * C + 1 ≤ ‖t / (2 * Real.pi)‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hpi.le]
    rw [← hroot_sq]
    exact (sq_le_sq₀ hroot (by positivity)).2 hquotient
  have hdecay := hbound sigma hsigma t
  by_contra hnot
  have hstrict : 1 / 2 <
      ‖laplaceAt (compactLogTestOfWindow g ha hb hsupport)
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ :=
    lt_of_not_ge hnot
  have hfrequency_pos : 0 < ‖t / (2 * Real.pi)‖ ^ 2 := by
    linarith
  have hproduct :
      (2 * C + 1) * (1 / 2 : ℝ) <
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt (compactLogTestOfWindow g ha hb hsupport)
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ := by
    calc
      (2 * C + 1) * (1 / 2 : ℝ) ≤
          ‖t / (2 * Real.pi)‖ ^ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hfrequency (by norm_num)
      _ < ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt (compactLogTestOfWindow g ha hb hsupport)
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_lt_mul_of_pos_left hstrict hfrequency_pos
  linarith

/-- Compress a compact log test by a positive factor while preserving its
integral normalization. Yoshida's convolution powers use a factor depending
on the number of copies so their total support stays in one fixed window. -/
noncomputable def rescale (f : CompactLogTest) (r : ℝ) (hr : 0 < r) :
    CompactLogTest := by
  let raw : ℝ → ℂ := fun x => ((r : ℂ)⁻¹) * f.test (x / r)
  have hcompactComp : HasCompactSupport (fun x : ℝ => f.test (x / r)) := by
    simpa [div_eq_inv_mul] using
      f.compactSupport.comp_smul (inv_ne_zero hr.ne')
  have hcompact : HasCompactSupport raw := hcompactComp.mul_left
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    fun_prop
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem rescale_apply
    (f : CompactLogTest) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    (rescale f r hr).test x = ((r : ℂ)⁻¹) * f.test (x / r) :=
  rfl

/-- Rescaling by `r` multiplies both log-support endpoints by `r`. -/
theorem rescale_support_subset_Ioo
    (f : CompactLogTest) {lower upper r : ℝ} (hr : 0 < r)
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper) :
    Function.support (rescale f r hr).test ⊆
      Set.Ioo (r * lower) (r * upper) := by
  intro x hx
  have hvalue : f.test (x / r) ≠ 0 := by
    intro hzero
    apply hx
    simp [rescale_apply, hzero]
  have hbounds := hsupport hvalue
  constructor
  · have h := mul_lt_mul_of_pos_left hbounds.1 hr
    convert h using 1 <;> field_simp [hr.ne']
  · have h := mul_lt_mul_of_pos_left hbounds.2 hr
    convert h using 1 <;> field_simp [hr.ne']

/-- The normalized compression has bilateral Laplace transform `s ↦ Phi(r s)`.
This is the change-of-variables identity needed before taking convolution
powers in a fixed support window. -/
theorem laplaceAt_rescale
    (f : CompactLogTest) (r : ℝ) (hr : 0 < r) (s : ℂ) :
    laplaceAt (rescale f r hr) s = laplaceAt f ((r : ℂ) * s) := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, rescale_apply]
  let weighted : ℝ → ℂ := fun y =>
    Complex.exp (((r : ℂ) * s) * (y : ℂ)) * f.test y
  have hintegrand :
      (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (((r : ℂ)⁻¹) * f.test (x / r))) =
      fun x : ℝ => ((r : ℂ)⁻¹) * weighted (x / r) := by
    funext x
    dsimp [weighted]
    have harg : s * (x : ℂ) = ((r : ℂ) * s) * ((x / r : ℝ) : ℂ) := by
      push_cast
      field_simp [hr.ne']
    rw [harg]
    ring
  rw [hintegrand, integral_const_mul, Measure.integral_comp_div]
  simp only [abs_of_pos hr, weighted]
  have hrComplex : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  change (r : ℂ)⁻¹ * ((r : ℂ) * ∫ y : ℝ,
      Complex.exp (((r : ℂ) * s) * (y : ℂ)) * f.test y) =
    ∫ x : ℝ, Complex.exp (((r : ℂ) * s) * (x : ℂ)) * f.test x
  rw [← mul_assoc, inv_mul_cancel₀ hrComplex, one_mul]

/-- Arbitrary values on finitely many Laplace nodes can be realized by one
compact log test in any prescribed residual window around zero. This is the
finite correction factor used by the support-preserving Yoshida product. -/
theorem exists_residualWindow_correction
    (nodes : Finset ℂ) {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → ℂ) :
    ∃ correction : CompactLogTest,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      ∀ z : FiniteMellinNode nodes, laplaceAt correction z.1 = y z := by
  have ha : 0 < Real.exp lower := Real.exp_pos lower
  have hb : 0 < Real.exp upper := Real.exp_pos upper
  have ha_one : Real.exp lower < 1 := Real.exp_lt_one_iff.mpr hlower
  have hone_b : 1 < Real.exp upper := Real.one_lt_exp_iff.mpr hupper
  rcases fixed_window_finite_mellin_surjective
      nodes ha ha_one hone_b y with
    ⟨g, _hcompact, hsupport, hvalues⟩
  let correction := compactLogTestOfWindow g ha hb hsupport
  refine ⟨correction, ?_, ?_⟩
  · simpa [correction] using
      compactLogTestOfWindow_support_subset g ha hb hsupport
  · intro z
    dsimp [correction]
    rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
    simpa only [normalizedCC20TestSpace_mellinAt_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin] using
      hvalues z

/-- The residual correction can retain the uniform quadratic strip bound from
the same positive-variable source test. This keeps the far-tail constant
available for the later product estimate. -/
theorem exists_residualWindow_correction_with_quadratic_decay
    (nodes : Finset ℂ) {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → ℂ) :
    ∃ correction : CompactLogTest, ∃ C : ℝ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode nodes, laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have ha : 0 < Real.exp lower := Real.exp_pos lower
  have hb : 0 < Real.exp upper := Real.exp_pos upper
  have ha_one : Real.exp lower < 1 := Real.exp_lt_one_iff.mpr hlower
  have hone_b : 1 < Real.exp upper := Real.one_lt_exp_iff.mpr hupper
  rcases fixed_window_finite_mellin_surjective
      nodes ha ha_one hone_b y with
    ⟨g, _hcompact, hsupport, hvalues⟩
  let correction := compactLogTestOfWindow g ha hb hsupport
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay g ha hb hsupport
  refine ⟨correction, C, ?_, ?_, hC, ?_⟩
  · simpa [correction] using
      compactLogTestOfWindow_support_subset g ha hb hsupport
  · intro z
    dsimp [correction]
    rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
    simpa only [normalizedCC20TestSpace_mellinAt_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin] using
      hvalues z
  · intro sigma hsigma t
    simpa [correction] using hdecay sigma hsigma t

/-- Nearby source zeros and route nodes have one finite correction factor in
the same arbitrarily small residual log window. -/
theorem exists_residualWindow_nearbyZero_correction
    (rho : ℂ) (R : ℝ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ) :
    ∃ correction : CompactLogTest,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      ∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        laplaceAt correction z.1 = y z :=
  exists_residualWindow_correction _ hlower hupper y

theorem exists_residualWindow_nearbyZero_correction_with_quadratic_decay
    (rho : ℂ) (R : ℝ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ) :
    ∃ correction : CompactLogTest, ∃ C : ℝ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C :=
  exists_residualWindow_correction_with_quadratic_decay _ hlower hupper y

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
      · exact hcontraction s hs
      · exact hcorrection s hs
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

/-- Compressing a test by `1 / (n + 1)` before taking `n + 1` convolution
copies exactly cancels support growth. -/
theorem convolutionIterate_rescale_inv_natCast_support_subset_Ioo
    (f : CompactLogTest) {lower upper : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper)
    (n : ℕ) :
    Function.support
        (convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).test ⊆
      Set.Ioo lower upper := by
  have hscaled := rescale_support_subset_Ioo f
    (r := (((n + 1 : ℕ) : ℝ)⁻¹)) (by positivity) hsupport
  have hiterated := convolutionIterate_support_subset_Ioo
    (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) hscaled n
  convert hiterated using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one] <;>
    field_simp

/-- The support-preserving convolution power has the expected Yoshida
transform `Phi(s / (n + 1))^(n + 1)`. -/
theorem laplaceAt_convolutionIterate_rescale_inv_natCast
    (f : CompactLogTest) (s : ℂ) (n : ℕ) :
    laplaceAt
        (convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n) s =
      laplaceAt f (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * s) ^ (n + 1) := by
  rw [laplaceAt_convolutionIterate, laplaceAt_rescale]

/-- The complete Yoshida product consists of the support-preserving power and
one finite correction factor. -/
theorem laplaceAt_convolutionIterate_rescale_inv_natCast_convolution
    (f correction : CompactLogTest) (s : ℂ) (n : ℕ) :
    laplaceAt
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction) s =
      laplaceAt f (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * s) ^ (n + 1) *
        laplaceAt correction s := by
  rw [laplaceAt_convolution,
    laplaceAt_convolutionIterate_rescale_inv_natCast]

/-- Interpolating the correction to value one at `rho` does not make the
assembled Yoshida product detect `rho`. If the rescaled base factor vanishes
there, the complete product still vanishes. This is the rejection guard for
treating correction-node interpolation as assembled-test interpolation. -/
theorem laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_zero_of_base
    (f correction : CompactLogTest) (rho : ℂ) (n : ℕ)
    (hbase :
      laplaceAt f (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * rho) = 0)
    (hcorrection : laplaceAt correction rho = 1) :
    laplaceAt
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction) rho = 0 := by
  rw [laplaceAt_convolutionIterate_rescale_inv_natCast_convolution,
    hbase, hcorrection]
  simp

/-- A contraction for the base factor and quadratic decay for the finite
correction give a quadratic far-vertical bound for the assembled Yoshida
product. Rescaling enlarges the height threshold by exactly `n + 1`. -/
theorem convolutionIterate_rescale_convolution_vertical_quadratic_bound
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) :
    ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ((n + 1 : ℕ) : ℝ) * T ≤ |t| →
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt
              ((convolutionIterate
                (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
                  correction)
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          q ^ (n + 1) * C := by
  intro sigma hsigma t ht
  let k : ℝ := ((n + 1 : ℕ) : ℝ)
  let r : ℝ := k⁻¹
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hk_one : 1 ≤ k := by
    dsimp [k]
    norm_num
  have hr : 0 < r := inv_pos.mpr hk
  have hr_one : r ≤ 1 := inv_le_one_of_one_le₀ hk_one
  have hsigmaScaled : r * sigma ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hr.le hsigma.1
    · calc
        r * sigma ≤ 1 * sigma :=
          mul_le_mul_of_nonneg_right hr_one hsigma.1
        _ ≤ 1 := by simpa using hsigma.2
  have htDiv : T ≤ |t| / k :=
    (le_div_iff₀ hk).2 (by simpa [k, mul_comm] using ht)
  have htScaled : T ≤ |r * t| := by
    rw [abs_mul, abs_of_pos hr]
    simpa [r, div_eq_inv_mul] using htDiv
  have hscalePoint :
      (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          ((sigma : ℂ) + (t : ℂ) * Complex.I)) =
        (((r * sigma : ℝ) : ℂ) + ((r * t : ℝ) : ℂ) * Complex.I) := by
    dsimp [r, k]
    push_cast
    ring
  have hbaseScaled :
      ‖laplaceAt f
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          ((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤ q := by
    rw [hscalePoint]
    exact hbase (r * sigma) hsigmaScaled (r * t) htScaled
  have hbasePower :
      ‖laplaceAt f
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          ((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ^ (n + 1) ≤
        q ^ (n + 1) := by
    gcongr
  have hcorrectionAt := hcorrection sigma hsigma t
  rw [laplaceAt_convolutionIterate_rescale_inv_natCast_convolution,
    norm_mul, norm_pow]
  calc
    ‖t / (2 * Real.pi)‖ ^ 2 *
          (‖laplaceAt f
              (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
                ((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ^ (n + 1) *
            ‖laplaceAt correction
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖) =
        ‖laplaceAt f
            (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
              ((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ^ (n + 1) *
          (‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖) := by ring
    _ ≤ q ^ (n + 1) * C := by
      exact mul_le_mul hbasePower hcorrectionAt
        (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (pow_nonneg hq _)

theorem convolutionIterate_rescale_convolution_quadratic_bound_at_complex
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hheight : ((n + 1 : ℕ) : ℝ) * T ≤ |z.im|) :
    ‖z.im / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt
          ((convolutionIterate
            (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
              correction) z‖ ≤
      q ^ (n + 1) * C := by
  have hbound :=
    convolutionIterate_rescale_convolution_vertical_quadratic_bound
      f correction q C T n hq hbase hcorrection
      z.re hz z.im hheight
  simpa only [Complex.re_add_im] using hbound

/-- On the closed critical strip, sufficiently large vertical height controls
distance from a fixed center. The conservative constant `6 * pi` keeps the
result in a division-free form for later dyadic-shell estimates. -/
theorem norm_sub_sq_mul_laplaceAt_le_of_vertical_quadratic_bound
    (f : CompactLogTest) (rho z : ℂ) (A : ℝ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hone : 1 ≤ |z.im|)
    (hrhoHeight : 2 * |rho.im| ≤ |z.im|)
    (hvertical :
      ‖z.im / (2 * Real.pi)‖ ^ 2 * ‖laplaceAt f z‖ ≤ A) :
    ‖z - rho‖ ^ 2 * ‖laplaceAt f z‖ ≤ (6 * Real.pi) ^ 2 * A := by
  have hre : |z.re - rho.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hrho.1, hrho.2, hz.1, hz.2]
  have him : |z.im - rho.im| ≤ |z.im| + |rho.im| :=
    abs_sub z.im rho.im
  have hrhoIm : |rho.im| ≤ |z.im| := by linarith
  have hnorm : ‖z - rho‖ ≤ 3 * |z.im| := by
    calc
      ‖z - rho‖ ≤ |(z - rho).re| + |(z - rho).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re - rho.re| + |z.im - rho.im| := by simp
      _ ≤ 1 + (|z.im| + |rho.im|) := add_le_add hre him
      _ ≤ 3 * |z.im| := by linarith
  have hnormSq : ‖z - rho‖ ^ 2 ≤ (3 * |z.im|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖z - rho‖ ^ 2 * ‖laplaceAt f z‖ ≤
        (3 * |z.im|) ^ 2 * ‖laplaceAt f z‖ :=
      mul_le_mul_of_nonneg_right hnormSq (norm_nonneg _)
    _ = (6 * Real.pi) ^ 2 *
        (‖z.im / (2 * Real.pi)‖ ^ 2 * ‖laplaceAt f z‖) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ (6 * Real.pi) ^ 2 * A :=
      mul_le_mul_of_nonneg_left hvertical (sq_nonneg _)

theorem convolutionIterate_rescale_convolution_distance_quadratic_bound
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (rho z : ℂ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hcontractHeight : ((n + 1 : ℕ) : ℝ) * T ≤ |z.im|)
    (hone : 1 ≤ |z.im|)
    (hrhoHeight : 2 * |rho.im| ≤ |z.im|) :
    ‖z - rho‖ ^ 2 *
        ‖laplaceAt
          ((convolutionIterate
            (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
              correction) z‖ ≤
      (6 * Real.pi) ^ 2 * (q ^ (n + 1) * C) := by
  apply norm_sub_sq_mul_laplaceAt_le_of_vertical_quadratic_bound
    _ rho z (q ^ (n + 1) * C) hrho hz hone hrhoHeight
  exact convolutionIterate_rescale_convolution_quadratic_bound_at_complex
    f correction q C T n hq hbase hcorrection hz hcontractHeight

/-- Enough support-preserving base copies make the distance-weighted far tail
smaller than any prescribed positive epsilon. -/
theorem exists_convolutionIterate_rescale_convolution_distance_bound_lt
    (f correction : CompactLogTest) (C T : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / 2)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      ((n + 1 : ℕ) : ℝ) * T ≤ |z.im| →
      1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt
              ((convolutionIterate
                (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
                  correction) z‖ < epsilon := by
  let D : ℝ := (6 * Real.pi) ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hCplus : 0 < C + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hepsilon (mul_pos hD hCplus))
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  intro z hz hcontractHeight hone hrhoHeight
  have hdistance :=
    convolutionIterate_rescale_convolution_distance_quadratic_bound
      f correction (1 / 2) C T n (by norm_num) hbase hcorrection
      rho z hrho hz hcontractHeight hone hrhoHeight
  apply lt_of_le_of_lt hdistance
  calc
    D * ((1 / 2 : ℝ) ^ (n + 1) * C) ≤
        D * ((1 / 2 : ℝ) ^ n * C) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      apply mul_le_mul_of_nonneg_right _ hC
      simpa [Nat.succ_eq_add_one] using
        pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.le_succ n)
    _ ≤ D * ((1 / 2 : ℝ) ^ n * (C + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by norm_num) _)
    _ < D * ((epsilon / (D * (C + 1))) * (C + 1)) := by
      gcongr
    _ = epsilon := by
      field_simp [ne_of_gt hD, ne_of_gt hCplus]

/-- Without support-preserving rescaling, the base contraction is evaluated at
the original spectral point. Hence the far-vertical threshold stays equal to
`T`, independently of the convolution count. -/
theorem convolutionIterate_convolution_vertical_quadratic_bound
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) :
    ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt ((convolutionIterate f n).convolution correction)
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        q ^ (n + 1) * C := by
  intro sigma hsigma t ht
  have hbaseAt := hbase sigma hsigma t ht
  have hbasePower :
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1) ≤
        q ^ (n + 1) := by
    gcongr
  have hcorrectionAt := hcorrection sigma hsigma t
  rw [laplaceAt_convolution, laplaceAt_convolutionIterate, norm_mul, norm_pow]
  calc
    ‖t / (2 * Real.pi)‖ ^ 2 *
          (‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1) *
            ‖laplaceAt correction
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖) =
        ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1) *
          (‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖) := by ring
    _ ≤ q ^ (n + 1) * C := by
      exact mul_le_mul hbasePower hcorrectionAt
        (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (pow_nonneg hq _)

theorem convolutionIterate_convolution_quadratic_bound_at_complex
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hheight : T ≤ |z.im|) :
    ‖z.im / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt ((convolutionIterate f n).convolution correction) z‖ ≤
      q ^ (n + 1) * C := by
  have hbound := convolutionIterate_convolution_vertical_quadratic_bound
    f correction q C T n hq hbase hcorrection z.re hz z.im hheight
  simpa only [Complex.re_add_im] using hbound

theorem convolutionIterate_convolution_distance_quadratic_bound
    (f correction : CompactLogTest) (q C T : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (rho z : ℂ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hcontractHeight : T ≤ |z.im|)
    (hone : 1 ≤ |z.im|)
    (hrhoHeight : 2 * |rho.im| ≤ |z.im|) :
    ‖z - rho‖ ^ 2 *
        ‖laplaceAt ((convolutionIterate f n).convolution correction) z‖ ≤
      (6 * Real.pi) ^ 2 * (q ^ (n + 1) * C) := by
  apply norm_sub_sq_mul_laplaceAt_le_of_vertical_quadratic_bound
    _ rho z (q ^ (n + 1) * C) hrho hz hone hrhoHeight
  exact convolutionIterate_convolution_quadratic_bound_at_complex
    f correction q C T n hq hbase hcorrection hz hcontractHeight

/-- Once the correction and its quadratic constant are fixed, enough unscaled
base copies make the distance-weighted tail arbitrarily small without moving
the far-vertical threshold. -/
theorem exists_convolutionIterate_convolution_distance_bound_lt
    (f correction : CompactLogTest) (C T : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / 2)
    (hcorrection : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt ((convolutionIterate f n).convolution correction) z‖ <
          epsilon := by
  let D : ℝ := (6 * Real.pi) ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hCplus : 0 < C + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hepsilon (mul_pos hD hCplus))
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  intro z hz hcontractHeight hone hrhoHeight
  have hdistance := convolutionIterate_convolution_distance_quadratic_bound
    f correction (1 / 2) C T n (by norm_num) hbase hcorrection
    rho z hrho hz hcontractHeight hone hrhoHeight
  apply lt_of_le_of_lt hdistance
  calc
    D * ((1 / 2 : ℝ) ^ (n + 1) * C) ≤
        D * ((1 / 2 : ℝ) ^ n * C) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      apply mul_le_mul_of_nonneg_right _ hC
      simpa [Nat.succ_eq_add_one] using
        pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.le_succ n)
    _ ≤ D * ((1 / 2 : ℝ) ^ n * (C + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by norm_num) _)
    _ < D * ((epsilon / (D * (C + 1))) * (C + 1)) := by
      gcongr
    _ = epsilon := by
      field_simp [ne_of_gt hD, ne_of_gt hCplus]

/-- The nearby-zero correction and the unscaled convolution power can be
assembled with one fixed base threshold. The support is allowed to grow with
the number of copies; this is the deliberate escape from the rescaled
radius--count feedback loop. -/
theorem exists_residualWindow_nearbyZero_unscaled_assembled_distance_bound_lt
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b)
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (R : ℝ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ correction : CompactLogTest, ∃ C T : ℝ, ∃ n : ℕ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      Function.support
          ((convolutionIterate
            (compactLogTestOfWindow g ha hb hsupport) n).convolution
              correction).test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * Real.log a + lower)
          (((n + 1 : ℕ) : ℝ) * Real.log b + upper) ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧ 0 ≤ T ∧
      ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
        T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
          ‖z - rho‖ ^ 2 *
              ‖laplaceAt
                ((convolutionIterate
                  (compactLogTestOfWindow g ha hb hsupport) n).convolution
                    correction) z‖ < epsilon := by
  obtain ⟨correction, C, hcorrectionSupport, hvalues, hC, hcorrectionDecay⟩ :=
    exists_residualWindow_nearbyZero_correction_with_quadratic_decay
      rho R routeNodes hlower hupper y
  obtain ⟨T, hT, hbase⟩ :=
    exists_uniform_laplaceAt_vertical_half_contraction g ha hb hsupport
  obtain ⟨n, hdistance⟩ :=
    exists_convolutionIterate_convolution_distance_bound_lt
      (compactLogTestOfWindow g ha hb hsupport) correction C T hC
      hbase hcorrectionDecay rho hrho epsilon hepsilon
  have hbaseSupport := compactLogTestOfWindow_support_subset
    g ha hb hsupport
  have hassembledSupport := convolution_support_subset_add_Ioo
    (convolutionIterate (compactLogTestOfWindow g ha hb hsupport) n)
    correction
    (convolutionIterate_support_subset_Ioo
      (compactLogTestOfWindow g ha hb hsupport) hbaseSupport n)
    hcorrectionSupport
  exact ⟨correction, C, T, n, hcorrectionSupport, hassembledSupport,
    hvalues, hC, hT, hdistance⟩

/-- A normalized unscaled Yoshida product. The base is normalized at `rho`; a
single finite correction kills every other selected node, while the power is
chosen only after the correction constant is known. The existential threshold
is outside the radius quantifier, so the theorem exposes the absence of the
old `(n + 1) * T` radius cycle. -/
theorem exists_fixedThreshold_nearbyZero_unscaled_normalized_assembly
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b)
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hbaseNormalize :
      laplaceAt (compactLogTestOfWindow g ha hb hsupport) rho = 1)
    (routeNodes : Finset ℂ) (hrhoNode : rho ∈ routeNodes)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ R : ℝ, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : ℝ, ∃ n : ℕ,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support
              ((convolutionIterate
                (compactLogTestOfWindow g ha hb hsupport) n).convolution
                  correction).test ⊆
            Set.Ioo (((n + 1 : ℕ) : ℝ) * Real.log a + lower)
              (((n + 1 : ℕ) : ℝ) * Real.log b + upper) ∧
          laplaceAt
              ((convolutionIterate
                (compactLogTestOfWindow g ha hb hsupport) n).convolution
                  correction) rho = 1 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ≠ rho →
              laplaceAt
                ((convolutionIterate
                  (compactLogTestOfWindow g ha hb hsupport) n).convolution
                    correction) z.1 = 0) ∧
          0 ≤ C ∧
          ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt
                    ((convolutionIterate
                      (compactLogTestOfWindow g ha hb hsupport) n).convolution
                        correction) z‖ < epsilon := by
  obtain ⟨T, hT, hbase⟩ :=
    exists_uniform_laplaceAt_vertical_half_contraction g ha hb hsupport
  refine ⟨T, hT, ?_⟩
  intro R hR
  let nodes : Finset ℂ :=
    sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes
  let y : FiniteMellinNode nodes → ℂ := fun z =>
    if z.1 = rho then 1 else 0
  have hrhoNodes : rho ∈ nodes := by
    exact Finset.mem_union_right _ hrhoNode
  obtain ⟨correction, C, hcorrectionSupport, hvalues, hC,
      hcorrectionDecay⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      nodes hlower hupper y
  obtain ⟨n, hdistance⟩ :=
    exists_convolutionIterate_convolution_distance_bound_lt
      (compactLogTestOfWindow g ha hb hsupport) correction C T hC
      hbase hcorrectionDecay rho hrho epsilon hepsilon
  have hbaseSupport := compactLogTestOfWindow_support_subset
    g ha hb hsupport
  have hassembledSupport := convolution_support_subset_add_Ioo
    (convolutionIterate (compactLogTestOfWindow g ha hb hsupport) n)
    correction
    (convolutionIterate_support_subset_Ioo
      (compactLogTestOfWindow g ha hb hsupport) hbaseSupport n)
    hcorrectionSupport
  have hcorrectionRho := hvalues
    (⟨rho, hrhoNodes⟩ : FiniteMellinNode nodes)
  dsimp [y] at hcorrectionRho
  simp at hcorrectionRho
  have hassembledRho :
      laplaceAt
          ((convolutionIterate
            (compactLogTestOfWindow g ha hb hsupport) n).convolution
              correction) rho = 1 := by
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate,
      hbaseNormalize, hcorrectionRho]
    simp
  have hassembledZeros :
      ∀ z : FiniteMellinNode nodes, z.1 ≠ rho →
        laplaceAt
          ((convolutionIterate
            (compactLogTestOfWindow g ha hb hsupport) n).convolution
              correction) z.1 = 0 := by
    intro z hz
    have hcorrection := hvalues z
    dsimp [y] at hcorrection
    have hzero : (if z.1 = rho then (1 : ℂ) else 0) = 0 := by
      simp [hz]
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate,
      hcorrection, hzero]
    simp
  exact ⟨correction, C, n, hcorrectionSupport, hassembledSupport,
    hassembledRho, hassembledZeros, hC, hdistance⟩

/-- The nearby-zero correction producer and the base contraction assemble into
the epsilon-small distance majorant required for the far strip zeros. -/
theorem exists_residualWindow_nearbyZero_assembled_distance_bound_lt
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b)
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (R : ℝ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ correction : CompactLogTest, ∃ C T : ℝ, ∃ n : ℕ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧ 0 ≤ T ∧
      ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
        ((n + 1 : ℕ) : ℝ) * T ≤ |z.im| →
        1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
          ‖z - rho‖ ^ 2 *
              ‖laplaceAt
                ((convolutionIterate
                  (rescale (compactLogTestOfWindow g ha hb hsupport)
                    (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
                    correction) z‖ < epsilon := by
  obtain ⟨correction, C, hcorrectionSupport, hvalues, hC, hcorrectionDecay⟩ :=
    exists_residualWindow_nearbyZero_correction_with_quadratic_decay
      rho R routeNodes hlower hupper y
  obtain ⟨T, hT, hbase⟩ :=
    exists_uniform_laplaceAt_vertical_half_contraction g ha hb hsupport
  obtain ⟨n, hdistance⟩ :=
    exists_convolutionIterate_rescale_convolution_distance_bound_lt
      (compactLogTestOfWindow g ha hb hsupport) correction C T hC
      hbase hcorrectionDecay rho hrho epsilon hepsilon
  exact ⟨correction, C, T, n, hcorrectionSupport, hvalues, hC, hT, hdistance⟩

/-- One residual-window correction, its decay constant, and the base-factor
threshold produce an assembled Yoshida test with a quadratic bound at every
far point of the closed critical strip. -/
theorem exists_residualWindow_nearbyZero_assembled_quadratic_bound
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo a b)
    (rho : ℂ) (R : ℝ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes) → ℂ)
    (n : ℕ) :
    ∃ correction : CompactLogTest, ∃ C T : ℝ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧ 0 ≤ T ∧
      ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
        ((n + 1 : ℕ) : ℝ) * T ≤ |z.im| →
          ‖z.im / (2 * Real.pi)‖ ^ 2 *
              ‖laplaceAt
                ((convolutionIterate
                  (rescale (compactLogTestOfWindow g ha hb hsupport)
                    (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
                    correction) z‖ ≤
            (1 / 2 : ℝ) ^ (n + 1) * C := by
  obtain ⟨correction, C, hcorrectionSupport, hvalues, hC, hcorrectionDecay⟩ :=
    exists_residualWindow_nearbyZero_correction_with_quadratic_decay
      rho R routeNodes hlower hupper y
  obtain ⟨T, hT, hbase⟩ :=
    exists_uniform_laplaceAt_vertical_half_contraction g ha hb hsupport
  refine ⟨correction, C, T, hcorrectionSupport, hvalues, hC, hT, ?_⟩
  intro z hz hheight
  exact convolutionIterate_rescale_convolution_quadratic_bound_at_complex
    (compactLogTestOfWindow g ha hb hsupport) correction
    (1 / 2) C T n (by norm_num) hbase hcorrectionDecay hz hheight

/-- After normalized rescaling, the power consumes exactly the base support
budget, independently of the convolution count; the correction consumes only
its own fixed residual budget. -/
theorem convolutionIterate_rescale_inv_natCast_convolution_support_subset_Ioo
    (f correction : CompactLogTest)
    {lower upper correctionLower correctionUpper : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper)
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo correctionLower correctionUpper)
    (n : ℕ) :
    Function.support
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction).test ⊆
      Set.Ioo (lower + correctionLower) (upper + correctionUpper) := by
  exact convolution_support_subset_add_Ioo _ _
    (convolutionIterate_rescale_inv_natCast_support_subset_Ioo f hsupport n)
    hcorrection

/-- A concrete allocation of base and correction windows keeps the assembled
Yoshida test inside a prescribed outer window. -/
theorem convolutionIterate_rescale_inv_natCast_convolution_support_subset_of_budget
    (f correction : CompactLogTest)
    {outerLower outerUpper lower upper correctionLower correctionUpper : ℝ}
    (hsupport : Function.support f.test ⊆ Set.Ioo lower upper)
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo correctionLower correctionUpper)
    (hlower : outerLower ≤ lower + correctionLower)
    (hupper : upper + correctionUpper ≤ outerUpper)
    (n : ℕ) :
    Function.support
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction).test ⊆
      Set.Ioo outerLower outerUpper := by
  intro x hx
  have hbounds :=
    convolutionIterate_rescale_inv_natCast_convolution_support_subset_Ioo
      f correction hsupport hcorrection n hx
  exact ⟨lt_of_le_of_lt hlower hbounds.1,
    lt_of_lt_of_le hbounds.2 hupper⟩

/-- Splitting any prescribed log-support window equally between the normalized
base power and the finite correction keeps the assembled Yoshida test in that
same outer window. In particular, increasing the convolution count creates no
minimum support width. -/
theorem convolutionIterate_rescale_inv_natCast_convolution_support_subset_half_budget
    (f correction : CompactLogTest) {outerLower outerUpper : ℝ}
    (hsupport : Function.support f.test ⊆
      Set.Ioo (outerLower / 2) (outerUpper / 2))
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo (outerLower / 2) (outerUpper / 2))
    (n : ℕ) :
    Function.support
        ((convolutionIterate
          (rescale f (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity)) n).convolution
            correction).test ⊆
      Set.Ioo outerLower outerUpper := by
  apply convolutionIterate_rescale_inv_natCast_convolution_support_subset_of_budget
    f correction hsupport hcorrection
  · convert le_rfl using 1 <;> ring
  · convert le_rfl using 1 <;> ring

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
