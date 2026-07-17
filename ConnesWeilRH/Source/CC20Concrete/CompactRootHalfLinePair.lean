/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CC20Concrete.GlobalLogSoninProjection
import ConnesWeilRH.Source.CC20Concrete.SelfAdjointBoundaryCommutator
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Compact-root Hilbert--Schmidt pair at a half-line boundary

If a convolution root is supported in `[a,c]`, the overlap between its
positive- and negative-half-line outputs is contained in `[-c,-a]`.  The two
input legs are likewise confined to `[a-c,0]` and `[0,c-a]`.  This module
constructs the resulting pair on the actual whole-line `L2` carrier from
continuous kernels on those compact intervals.

The identification of its trace product with the global half-line crossing
is kept separate.  No trace estimate or Gate 3U bound is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace CompactRootHalfLinePair

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProduct InnerProductSpace
open CCM25Concrete
open CCM25Concrete.SelectedCrossingKernel
open CCM25Concrete.SelectedCrossingOperatorBridge

abbrev BoundaryOutputInterval (a c : ℝ) := KernelInterval (-c) (-a) 0

abbrev BoundaryNegativeInputInterval (a c : ℝ) :=
  KernelInterval (a - c) 0 0

abbrev BoundaryPositiveInputInterval (a c : ℝ) :=
  KernelInterval 0 (c - a) 0

/-- The complete input window seen from the reflected output interval. -/
abbrev BoundaryFullInputInterval (a c : ℝ) :=
  KernelInterval (a - c) (c - a) 0

/-- A nonzero negative-half-line kernel value is forced into the compact
input window `[a-c,0]` once the output lies in `[-c,-a]`. -/
theorem negativeInput_mem_of_kernel_ne_zero
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) {x : ℝ}
    (hx : x ≤ 0) (hkernel : g.test (x - t.1) ≠ 0) :
    x ∈ Set.Icc (a - c) 0 := by
  have hz : x - t.1 ∈ Set.Icc a c := by
    exact hsupp (by simpa [Function.mem_support] using hkernel)
  constructor
  · linarith [hz.1, t.2.1]
  · exact hx

/-- A nonzero positive-half-line kernel value is forced into the compact
input window `[0,c-a]` on the same output window. -/
theorem positiveInput_mem_of_kernel_ne_zero
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) {x : ℝ}
    (hx : 0 ≤ x) (hkernel : g.test (x - t.1) ≠ 0) :
    x ∈ Set.Icc 0 (c - a) := by
  have hz : x - t.1 ∈ Set.Icc a c := by
    exact hsupp (by simpa [Function.mem_support] using hkernel)
  constructor
  · exact hx
  · linarith [hz.2, t.2.2]

/-- Compact support alone forces every contributing input into the complete
window `[a-c,c-a]`. -/
theorem fullInput_mem_of_kernel_ne_zero
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) {x : ℝ}
    (hkernel : g.test (x - t.1) ≠ 0) :
    x ∈ Set.Icc (a - c) (c - a) := by
  have hz : x - t.1 ∈ Set.Icc a c := by
    exact hsupp (by simpa [Function.mem_support] using hkernel)
  constructor
  · linarith [hz.1, t.2.1]
  · linarith [hz.2, t.2.2]

/-- If both half-line legs contribute at one output point, that point must be
inside the reflected support window `[-c,-a]`. -/
theorem output_mem_of_two_halfLine_kernel_ne_zero
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {t xNegative xPositive : ℝ}
    (hxNegative : xNegative ≤ 0) (hxPositive : 0 ≤ xPositive)
    (hnegative : g.test (xNegative - t) ≠ 0)
    (hpositive : g.test (xPositive - t) ≠ 0) :
    t ∈ Set.Icc (-c) (-a) := by
  have hzNegative : xNegative - t ∈ Set.Icc a c := by
    exact hsupp (by simpa [Function.mem_support] using hnegative)
  have hzPositive : xPositive - t ∈ Set.Icc a c := by
    exact hsupp (by simpa [Function.mem_support] using hpositive)
  constructor
  · linarith [hzPositive.2]
  · linarith [hzNegative.1]

/-- The compact kernel for the negative-half-line input leg.  The kernel is
written in the convention of `ContinuousKernelHilbertSchmidt`, whose
coefficient operator conjugates the displayed section. -/
noncomputable def negativeBoundaryRootKernel
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    ContinuousMap
      ((BoundaryOutputInterval a c) ×
        (BoundaryNegativeInputInterval a c)) ℂ where
  toFun z := g.test (z.2.1 - z.1.1)
  continuous_toFun := g.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

/-- The compact kernel for the positive-half-line input leg. -/
noncomputable def positiveBoundaryRootKernel
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    ContinuousMap
      ((BoundaryOutputInterval a c) ×
        (BoundaryPositiveInputInterval a c)) ℂ where
  toFun z := g.test (z.2.1 - z.1.1)
  continuous_toFun := g.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

/-- The same root kernel on the complete input window. -/
noncomputable def fullBoundaryRootKernel
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    ContinuousMap
      ((BoundaryOutputInterval a c) ×
        (BoundaryFullInputInterval a c)) ℂ where
  toFun z := g.test (z.2.1 - z.1.1)
  continuous_toFun := g.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

/-- On a restricted Schwartz input, the negative kernel coefficient is its
literal compact-window convolution integral. -/
theorem negativeBoundaryCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (negativeBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
          (kernelRestriction u (a - c) 0 0)) t =
      ∫ x in Set.Icc (a - c - 0) (0 + 0),
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (negativeBoundaryRootKernel g a c) t))
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
        (kernelRestriction u (a - c) 0 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : BoundaryNegativeInputInterval a c,
      u x.1 * star (g.test (x.1 - t.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Set.Icc (a - c - 0) (0 + 0)) measurableSet_Icc
    (fun x : ℝ => u x * star (g.test (x - t.1)))

/-- On a restricted Schwartz input, the positive kernel coefficient is its
literal compact-window convolution integral. -/
theorem positiveBoundaryCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (positiveBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (kernelRestriction u 0 (c - a) 0)) t =
      ∫ x in Set.Icc (0 - 0) (c - a + 0),
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (positiveBoundaryRootKernel g a c) t))
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
        (kernelRestriction u 0 (c - a) 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : BoundaryPositiveInputInterval a c,
      u x.1 * star (g.test (x.1 - t.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Set.Icc (0 - 0) (c - a + 0)) measurableSet_Icc
    (fun x : ℝ => u x * star (g.test (x - t.1)))

/-- On a restricted Schwartz input, the complete kernel coefficient is its
literal compact-window convolution integral. -/
theorem fullBoundaryCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryFullInputInterval a c))
        (fullBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryFullInputInterval a c)) ℂ
          (kernelRestriction u (a - c) (c - a) 0)) t =
      ∫ x in Set.Icc (a - c - 0) (c - a + 0),
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryFullInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (fullBoundaryRootKernel g a c) t))
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryFullInputInterval a c)) ℂ
        (kernelRestriction u (a - c) (c - a) 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : BoundaryFullInputInterval a c,
      u x.1 * star (g.test (x.1 - t.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Set.Icc (a - c - 0) (c - a + 0)) measurableSet_Icc
    (fun x : ℝ => u x * star (g.test (x - t.1)))

/-- Compact support of the root and negative-half-line support of the input
remove the complement of `[a-c,0]` from the convolution integral. -/
theorem negativeBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Iic 0)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (negativeBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
          (kernelRestriction u (a - c) 0 0)) t =
      ∫ x : ℝ, u x * star (g.test (x - t.1)) := by
  rw [negativeBoundaryCoefficient_kernelRestriction_eq_setIntegral]
  simp only [sub_zero, add_zero]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (a - c) (0 : ℝ)
  · rw [Set.indicator_of_mem hx]
  · have hzero : u x = 0 ∨ g.test (x - t.1) = 0 := by
      by_contra hnonzero
      push Not at hnonzero
      have hxNegative : x ≤ 0 :=
        hu (by simpa [Function.mem_support] using hnonzero.1)
      exact hx (negativeInput_mem_of_kernel_ne_zero
        g a c hsupp t hxNegative hnonzero.2)
    rcases hzero with hzero | hzero
    · simp [Set.indicator, hx, hzero]
    · simp [Set.indicator, hx, hzero]

/-- Compact support of the root and positive-half-line support of the input
remove the complement of `[0,c-a]` from the convolution integral. -/
theorem positiveBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Ici 0)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (positiveBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (kernelRestriction u 0 (c - a) 0)) t =
      ∫ x : ℝ, u x * star (g.test (x - t.1)) := by
  rw [positiveBoundaryCoefficient_kernelRestriction_eq_setIntegral]
  simp only [sub_zero, add_zero]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) (c - a)
  · rw [Set.indicator_of_mem hx]
  · have hzero : u x = 0 ∨ g.test (x - t.1) = 0 := by
      by_contra hnonzero
      push Not at hnonzero
      have hxPositive : 0 ≤ x :=
        hu (by simpa [Function.mem_support] using hnonzero.1)
      exact hx (positiveInput_mem_of_kernel_ne_zero
        g a c hsupp t hxPositive hnonzero.2)
    rcases hzero with hzero | hzero
    · simp [Set.indicator, hx, hzero]
    · simp [Set.indicator, hx, hzero]

/-- On the complete input window, compact root support removes the complement
without any half-line support assumption on the input. -/
theorem fullBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryFullInputInterval a c))
        (fullBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryFullInputInterval a c)) ℂ
          (kernelRestriction u (a - c) (c - a) 0)) t =
      ∫ x : ℝ, u x * star (g.test (x - t.1)) := by
  rw [fullBoundaryCoefficient_kernelRestriction_eq_setIntegral]
  simp only [sub_zero, add_zero]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (a - c) (c - a)
  · rw [Set.indicator_of_mem hx]
  · have hzero : g.test (x - t.1) = 0 := by
      by_contra hnonzero
      exact hx (fullInput_mem_of_kernel_ne_zero
        g a c hsupp t hnonzero)
    simp [Set.indicator, hx, hzero]

/-- The full coefficient integral is the genuine Schwartz convolution core
used by `cc20GlobalLogConvolution`. -/
theorem fullBoundaryIntegral_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (t : ℝ) :
    (∫ x : ℝ, u x * star (g.test (x - t))) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  calc
    (∫ x : ℝ, u x * star (g.test (x - t))) =
        (u ⋆[B] g.involution.test) t := by
      rw [MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards with x
      rw [CompactLogConvolution.CompactLogTest.involution_apply]
      simp only [B, ContinuousLinearMap.mul_apply']
      congr 2
      ring
    _ = SchwartzMap.convolution B u g.involution.test t :=
      (SchwartzMap.convolution_apply B u g.involution.test t).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        u g.involution.test t := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f t)
        (schwartzConvolution_mul_real_eq_complex
          u g.involution.test).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f t)
        (schwartzConvolution_mul_real_comm u g.involution.test)

/-- The bundled compact convolution square is the Schwartz convolution of
the involuted root with the root. -/
theorem convolutionSquare_test_eq_schwartzConvolution
    (g : CompactLogConvolution.CompactLogTest) :
    g.convolutionSquare.test =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test g.test := by
  ext x
  rw [CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  let B := ContinuousLinearMap.mul ℂ ℂ
  calc
    (∫ t : ℝ, star (g.test (-t)) * g.test (x - t)) =
        (g.involution.test ⋆[B] g.test) x := by
      rfl
    _ = SchwartzMap.convolution B g.involution.test g.test x :=
      (SchwartzMap.convolution_apply B
        g.involution.test g.test x).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test g.test x := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f x)
        (schwartzConvolution_mul_real_eq_complex
          g.involution.test g.test).symm

/-- Associativity for the concrete scalar Schwartz convolution, stated in the
orientation needed by the positive detector. -/
theorem schwartzConvolution_root_assoc
    (g : CompactLogConvolution.CompactLogTest) (u : SchwartzMap ℝ ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) g.test
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.convolutionSquare.test u := by
  rw [convolutionSquare_test_eq_schwartzConvolution]
  apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) g.test
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u)) =
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test g.test) u)
  rw [SchwartzMap.fourier_convolution, SchwartzMap.fourier_convolution,
    SchwartzMap.fourier_convolution, SchwartzMap.fourier_convolution]
  ext x
  change (𝓕 g.test) x * ((𝓕 g.involution.test) x * (𝓕 u) x) =
    ((𝓕 g.involution.test) x * (𝓕 g.test) x) * (𝓕 u) x
  ring

/-- The selected positive root detector is exactly convolution by the compact
convolution-square kernel. -/
theorem globalConvolutionPositive_eq_convolutionSquare
    (g : CompactLogConvolution.CompactLogTest) :
    cc20GlobalConvolutionPositive g.involution.test =
      cc20GlobalLogConvolution g.convolutionSquare.test := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (cc20GlobalConvolutionPositive g.involution.test :
        cc20GlobalLogCrossingL2 → cc20GlobalLogCrossingL2) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (cc20GlobalLogConvolution g.convolutionSquare.test :
        cc20GlobalLogCrossingL2 → cc20GlobalLogCrossingL2) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    rw [Function.comp_apply, Function.comp_apply]
    unfold cc20GlobalConvolutionPositive
    simp only [ContinuousLinearMap.comp_apply]
    rw [adjoint_globalLogConvolution_involution]
    rw [cc20GlobalLogConvolution_toLp]
    rw [cc20GlobalLogConvolution_toLp]
    rw [cc20GlobalLogConvolution_toLp]
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f.toLp 2)
      (schwartzConvolution_root_assoc g u)
  have hfun := DenseRange.equalizer hdense
    (cc20GlobalConvolutionPositive g.involution.test).continuous
    (cc20GlobalLogConvolution g.convolutionSquare.test).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- A compact root supported in `[a,c]` has convolution square supported in
the difference interval `[a-c,c-a]`. -/
theorem convolutionSquare_support_subset
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    Function.support g.convolutionSquare.test ⊆
      Set.Icc (a - c) (c - a) := by
  intro x hx
  by_contra houtside
  have hintegrand : ∀ t : ℝ,
      star (g.test (-t)) * g.test (x - t) = 0 := by
    intro t
    by_cases hleft : g.test (-t) = 0
    · simp [hleft]
    by_cases hright : g.test (x - t) = 0
    · simp [hright]
    exfalso
    apply houtside
    have ht := hsupp (by simpa [Function.mem_support] using hleft)
    have hxt := hsupp (by simpa [Function.mem_support] using hright)
    constructor
    · linarith [ht.2, hxt.1]
    · linarith [ht.1, hxt.2]
  have hzero : g.convolutionSquare.test x = 0 := by
    rw [CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
    simp only [hintegrand, integral_zero]
  exact hx hzero

/-- The compact convolution square is fixed by the CCM25 involution. -/
theorem convolutionSquare_involution_test_eq
    (g : CompactLogConvolution.CompactLogTest) :
    g.convolutionSquare.involution.test = g.convolutionSquare.test := by
  ext x
  rw [CompactLogConvolution.CompactLogTest.involution_apply]
  rw [CompactLogConvolution.CompactLogTest.convolutionSquare_neg]
  simp only [star_star]

theorem negativeBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Iic 0)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (negativeBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
          (kernelRestriction u (a - c) 0 0)) t =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t.1 := by
  rw [negativeBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    g u a c hsupp hu t]
  exact fullBoundaryIntegral_eq_globalConvolutionCore g u t.1

theorem positiveBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Ici 0)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (positiveBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (kernelRestriction u 0 (c - a) 0)) t =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t.1 := by
  rw [positiveBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    g u a c hsupp hu t]
  exact fullBoundaryIntegral_eq_globalConvolutionCore g u t.1

theorem fullBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryFullInputInterval a c))
        (fullBoundaryRootKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryFullInputInterval a c)) ℂ
          (kernelRestriction u (a - c) (c - a) 0)) t =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t.1 := by
  rw [fullBoundaryCoefficient_kernelRestriction_eq_fullIntegral
    g u a c hsupp t]
  exact fullBoundaryIntegral_eq_globalConvolutionCore g u t.1

/-- The complete compact kernel factor before the half-line input is split. -/
noncomputable def fullBoundaryRootFactor
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryFullInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (fullBoundaryRootKernel g a c) ∘L
    globalL2ToKernelInterval (a - c) (c - a) 0

/-- On the global Schwartz core, the complete factor is the reflected-window
restriction of the genuine global root convolution. -/
theorem fullBoundaryRootFactor_apply_schwartzToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    fullBoundaryRootFactor g a c (u.toLp 2) =
      globalL2ToKernelInterval (-c) (-a) 0
        (cc20GlobalLogConvolution g.involution.test (u.toLp 2)) := by
  unfold fullBoundaryRootFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [cc20GlobalLogConvolution_toLp]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  apply congrArg
    (ContinuousMap.toLp 2
      (volume : Measure (BoundaryOutputInterval a c)) ℂ)
  ext t
  exact fullBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c hsupp t

/-- The complete factor is the bounded `L2` extension of the genuine global
root convolution followed by reflected-window restriction. -/
theorem fullBoundaryRootFactor_eq_globalConvolution
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    fullBoundaryRootFactor g a c =
      globalL2ToKernelInterval (-c) (-a) 0 ∘L
        cc20GlobalLogConvolution g.involution.test := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (fullBoundaryRootFactor g a c : cc20GlobalLogCrossingL2 →
        Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (globalL2ToKernelInterval (-c) (-a) 0 ∘L
        cc20GlobalLogConvolution g.involution.test :
          cc20GlobalLogCrossingL2 →
            Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply] using
      fullBoundaryRootFactor_apply_schwartzToLp g u a c hsupp
  have hfun := DenseRange.equalizer hdense
    (fullBoundaryRootFactor g a c).continuous
    (globalL2ToKernelInterval (-c) (-a) 0 ∘L
      cc20GlobalLogConvolution g.involution.test).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The complete coefficient restricted by the negative compact-window
projection is exactly the negative-window coefficient integral. -/
theorem fullBoundaryCoefficient_negativeWindowProjection_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ) (hac : a ≤ c)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryFullInputInterval a c))
        (fullBoundaryRootKernel g a c)
        (globalL2ToKernelInterval (a - c) (c - a) 0
          (kernelIntervalProjection (a - c) 0 0 (u.toLp 2))) t =
      ∫ x in Set.Icc (a - c) 0,
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (_ : Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)))
      (_ : Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))) = _
  rw [MeasureTheory.L2.inner_def]
  let fullSet := Set.Icc (a - c - 0) (c - a + 0)
  let negativeSet := Set.Icc (a - c) (0 : ℝ)
  let projected := kernelIntervalProjection (a - c) 0 0 (u.toLp 2)
  have hrestricted := globalL2ToKernelInterval_coeFn
    (a - c) (c - a) 0 projected
  have hprojected :=
    (measurePreserving_kernelIntervalSubtypeVal
      (a - c) (c - a) 0).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := fullSet)
        (kernelIntervalProjection_coeFn (a - c) 0 0 (u.toLp 2)))
  have hschwartz :=
    (measurePreserving_kernelIntervalSubtypeVal
      (a - c) (c - a) 0).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := fullSet)
        (u.coeFn_toLp 2 (volume : Measure ℝ)))
  have hsection := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal))
    (volume : Measure (BoundaryFullInputInterval a c)) (𝕜 := ℂ)
    (ContinuousKernelHilbertSchmidt.kernelSection
      (fullBoundaryRootKernel g a c) t)
  calc
    (∫ x : BoundaryFullInputInterval a c,
        inner ℂ
          ((ContinuousMap.toLp 2
            (volume : Measure (BoundaryFullInputInterval a c)) ℂ)
            (ContinuousKernelHilbertSchmidt.kernelSection
              (fullBoundaryRootKernel g a c) t) x)
          (globalL2ToKernelInterval (a - c) (c - a) 0 projected x)) =
        ∫ x : BoundaryFullInputInterval a c,
          negativeSet.indicator
            (fun y => u y * star (g.test (y - t.1))) x.1 := by
      apply integral_congr_ae
      filter_upwards [hrestricted, hprojected, hschwartz, hsection] with
        x hr hp hu hs
      rw [hr, hs]
      simp only [RCLike.inner_apply]
      change projected x.1 * star (g.test (x.1 - t.1)) = _
      have hp' : projected x.1 =
          negativeSet.indicator (fun y => (u.toLp 2 : ℝ → ℂ) y) x.1 := by
        simpa only [Function.comp_apply, negativeSet, projected,
          sub_zero, add_zero] using hp
      have hu' : (u.toLp 2 : ℝ → ℂ) x.1 = u x.1 := by
        simpa only [Function.comp_apply] using hu
      rw [hp']
      by_cases hx : x.1 ∈ negativeSet
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hu']
      · simp only [Set.indicator_of_notMem hx, zero_mul]
    _ = ∫ x in fullSet,
        negativeSet.indicator
          (fun y => u y * star (g.test (y - t.1))) x := by
      exact integral_subtype_comap (μ := (volume : Measure ℝ))
        (s := fullSet) measurableSet_Icc _
    _ = ∫ x in negativeSet,
        u x * star (g.test (x - t.1)) := by
      rw [← integral_indicator measurableSet_Icc]
      rw [Set.indicator_indicator]
      have hsubset : negativeSet ⊆ fullSet := by
        intro x hx
        constructor
        · simpa only [sub_zero] using hx.1
        · linarith [hx.2, hac]
      rw [Set.inter_eq_right.mpr hsubset]
      rw [integral_indicator measurableSet_Icc]

/-- The complete coefficient restricted by the positive compact-window
projection is exactly the positive-window coefficient integral. -/
theorem fullBoundaryCoefficient_positiveWindowProjection_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ) (hac : a ≤ c)
    (t : BoundaryOutputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryFullInputInterval a c))
        (fullBoundaryRootKernel g a c)
        (globalL2ToKernelInterval (a - c) (c - a) 0
          (kernelIntervalProjection 0 (c - a) 0 (u.toLp 2))) t =
      ∫ x in Set.Icc 0 (c - a),
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (_ : Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)))
      (_ : Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))) = _
  rw [MeasureTheory.L2.inner_def]
  let fullSet := Set.Icc (a - c - 0) (c - a + 0)
  let positiveSet := Set.Icc (0 : ℝ) (c - a)
  let projected := kernelIntervalProjection 0 (c - a) 0 (u.toLp 2)
  have hrestricted := globalL2ToKernelInterval_coeFn
    (a - c) (c - a) 0 projected
  have hprojected :=
    (measurePreserving_kernelIntervalSubtypeVal
      (a - c) (c - a) 0).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := fullSet)
        (kernelIntervalProjection_coeFn 0 (c - a) 0 (u.toLp 2)))
  have hschwartz :=
    (measurePreserving_kernelIntervalSubtypeVal
      (a - c) (c - a) 0).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := fullSet)
        (u.coeFn_toLp 2 (volume : Measure ℝ)))
  have hsection := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal))
    (volume : Measure (BoundaryFullInputInterval a c)) (𝕜 := ℂ)
    (ContinuousKernelHilbertSchmidt.kernelSection
      (fullBoundaryRootKernel g a c) t)
  calc
    (∫ x : BoundaryFullInputInterval a c,
        inner ℂ
          ((ContinuousMap.toLp 2
            (volume : Measure (BoundaryFullInputInterval a c)) ℂ)
            (ContinuousKernelHilbertSchmidt.kernelSection
              (fullBoundaryRootKernel g a c) t) x)
          (globalL2ToKernelInterval (a - c) (c - a) 0 projected x)) =
        ∫ x : BoundaryFullInputInterval a c,
          positiveSet.indicator
            (fun y => u y * star (g.test (y - t.1))) x.1 := by
      apply integral_congr_ae
      filter_upwards [hrestricted, hprojected, hschwartz, hsection] with
        x hr hp hu hs
      rw [hr, hs]
      simp only [RCLike.inner_apply]
      change projected x.1 * star (g.test (x.1 - t.1)) = _
      have hp' : projected x.1 =
          positiveSet.indicator (fun y => (u.toLp 2 : ℝ → ℂ) y) x.1 := by
        simpa only [Function.comp_apply, positiveSet, projected,
          sub_zero, add_zero] using hp
      have hu' : (u.toLp 2 : ℝ → ℂ) x.1 = u x.1 := by
        simpa only [Function.comp_apply] using hu
      rw [hp']
      by_cases hx : x.1 ∈ positiveSet
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hu']
      · simp only [Set.indicator_of_notMem hx, zero_mul]
    _ = ∫ x in fullSet,
        positiveSet.indicator
          (fun y => u y * star (g.test (y - t.1))) x := by
      exact integral_subtype_comap (μ := (volume : Measure ℝ))
        (s := fullSet) measurableSet_Icc _
    _ = ∫ x in positiveSet,
        u x * star (g.test (x - t.1)) := by
      rw [← integral_indicator measurableSet_Icc]
      rw [Set.indicator_indicator]
      have hsubset : positiveSet ⊆ fullSet := by
        intro x hx
        constructor
        · linarith [hx.1, hac]
        · simpa only [add_zero] using hx.2
      rw [Set.inter_eq_right.mpr hsubset]
      rw [integral_indicator measurableSet_Icc]

/-- The whole-line negative input is restricted to its support-forced compact
window before applying the continuous root kernel. -/
noncomputable def negativeBoundaryRootFactor
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryNegativeInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (negativeBoundaryRootKernel g a c) ∘L
    globalL2ToKernelInterval (a - c) 0 0

/-- The whole-line positive input is restricted to its support-forced compact
window before applying the continuous root kernel. -/
noncomputable def positiveBoundaryRootFactor
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryPositiveInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (positiveBoundaryRootKernel g a c) ∘L
    globalL2ToKernelInterval 0 (c - a) 0

/-- On a negative-half-line Schwartz core, the compact factor is exactly the
reflected-window restriction of the genuine global root convolution. -/
theorem negativeBoundaryRootFactor_apply_schwartzToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Iic 0) :
    negativeBoundaryRootFactor g a c (u.toLp 2) =
      globalL2ToKernelInterval (-c) (-a) 0
        (cc20GlobalLogConvolution g.involution.test (u.toLp 2)) := by
  unfold negativeBoundaryRootFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [cc20GlobalLogConvolution_toLp]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  apply congrArg
    (ContinuousMap.toLp 2
      (volume : Measure (BoundaryOutputInterval a c)) ℂ)
  ext t
  exact negativeBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c hsupp hu t

/-- On a positive-half-line Schwartz core, the compact factor is exactly the
same reflected-window restriction of the genuine global root convolution. -/
theorem positiveBoundaryRootFactor_apply_schwartzToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hu : Function.support u ⊆ Set.Ici 0) :
    positiveBoundaryRootFactor g a c (u.toLp 2) =
      globalL2ToKernelInterval (-c) (-a) 0
        (cc20GlobalLogConvolution g.involution.test (u.toLp 2)) := by
  unfold positiveBoundaryRootFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [cc20GlobalLogConvolution_toLp]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  apply congrArg
    (ContinuousMap.toLp 2
      (volume : Measure (BoundaryOutputInterval a c)) ℂ)
  ext t
  exact positiveBoundaryCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c hsupp hu t

/-- The negative compact factor is the complete factor after the negative
compact-window projection. -/
theorem fullBoundaryRootFactor_comp_negativeWindowProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c) :
    fullBoundaryRootFactor g a c ∘L
        kernelIntervalProjection (a - c) 0 0 =
      negativeBoundaryRootFactor g a c := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (fullBoundaryRootFactor g a c ∘L
          kernelIntervalProjection (a - c) 0 0 :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (negativeBoundaryRootFactor g a c :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    unfold fullBoundaryRootFactor negativeBoundaryRootFactor
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousKernelHilbertSchmidt.operator_apply,
      ContinuousKernelHilbertSchmidt.operator_apply]
    apply congrArg
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryOutputInterval a c)) ℂ)
    ext t
    rw [fullBoundaryCoefficient_negativeWindowProjection_eq_setIntegral
      g u a c hac t]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [negativeBoundaryCoefficient_kernelRestriction_eq_setIntegral]
    simp only [sub_zero, add_zero]
  have hfun := DenseRange.equalizer hdense
    (fullBoundaryRootFactor g a c ∘L
      kernelIntervalProjection (a - c) 0 0).continuous
    (negativeBoundaryRootFactor g a c).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The positive compact factor is the complete factor after the positive
compact-window projection. -/
theorem fullBoundaryRootFactor_comp_positiveWindowProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c) :
    fullBoundaryRootFactor g a c ∘L
        kernelIntervalProjection 0 (c - a) 0 =
      positiveBoundaryRootFactor g a c := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (fullBoundaryRootFactor g a c ∘L
          kernelIntervalProjection 0 (c - a) 0 :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (positiveBoundaryRootFactor g a c :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    unfold fullBoundaryRootFactor positiveBoundaryRootFactor
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousKernelHilbertSchmidt.operator_apply,
      ContinuousKernelHilbertSchmidt.operator_apply]
    apply congrArg
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryOutputInterval a c)) ℂ)
    ext t
    rw [fullBoundaryCoefficient_positiveWindowProjection_eq_setIntegral
      g u a c hac t]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [positiveBoundaryCoefficient_kernelRestriction_eq_setIntegral]
    simp only [sub_zero, add_zero]
  have hfun := DenseRange.equalizer hdense
    (fullBoundaryRootFactor g a c ∘L
      kernelIntervalProjection 0 (c - a) 0).continuous
    (positiveBoundaryRootFactor g a c).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- Zero extension from the compact negative input window. -/
noncomputable def negativeBoundaryZeroExtension (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension (a - c) 0 0

/-- Zero extension from the compact positive input window. -/
noncomputable def positiveBoundaryZeroExtension (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension 0 (c - a) 0

/-- Zero extension from the complete boundary input window. -/
noncomputable def fullBoundaryZeroExtension (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension (a - c) (c - a) 0

/-- Inclusion of the negative compact input window into the complete one. -/
noncomputable def negativeBoundaryInputEmbedding (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)) :=
  globalL2ToKernelInterval (a - c) (c - a) 0 ∘L
    negativeBoundaryZeroExtension a c

/-- Inclusion of the positive compact input window into the complete one. -/
noncomputable def positiveBoundaryInputEmbedding (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)) :=
  globalL2ToKernelInterval (a - c) (c - a) 0 ∘L
    positiveBoundaryZeroExtension a c

theorem negativeBoundaryInputEmbedding_adjoint (a c : ℝ) :
    (negativeBoundaryInputEmbedding a c).adjoint =
      globalL2ToKernelInterval (a - c) 0 0 ∘L
        fullBoundaryZeroExtension a c := by
  rw [negativeBoundaryInputEmbedding,
    ContinuousLinearMap.adjoint_comp]
  have hnegative : (negativeBoundaryZeroExtension a c).adjoint =
      globalL2ToKernelInterval (a - c) 0 0 := by
    unfold negativeBoundaryZeroExtension
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint]
  have hfull :
      (globalL2ToKernelInterval (a - c) (c - a) 0).adjoint =
        fullBoundaryZeroExtension a c := by
    unfold fullBoundaryZeroExtension
    exact (kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval
      (a - c) (c - a) 0).symm
  rw [hnegative, hfull]

theorem positiveBoundaryInputEmbedding_adjoint (a c : ℝ) :
    (positiveBoundaryInputEmbedding a c).adjoint =
      globalL2ToKernelInterval 0 (c - a) 0 ∘L
        fullBoundaryZeroExtension a c := by
  rw [positiveBoundaryInputEmbedding,
    ContinuousLinearMap.adjoint_comp]
  have hpositive : (positiveBoundaryZeroExtension a c).adjoint =
      globalL2ToKernelInterval 0 (c - a) 0 := by
    unfold positiveBoundaryZeroExtension
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint]
  have hfull :
      (globalL2ToKernelInterval (a - c) (c - a) 0).adjoint =
        fullBoundaryZeroExtension a c := by
    unfold fullBoundaryZeroExtension
    exact (kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval
      (a - c) (c - a) 0).symm
  rw [hpositive, hfull]

/-- The complete factor only reads the complete compact input window. -/
theorem fullBoundaryRootFactor_comp_fullWindowProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    fullBoundaryRootFactor g a c ∘L
        kernelIntervalProjection (a - c) (c - a) 0 =
      fullBoundaryRootFactor g a c := by
  unfold fullBoundaryRootFactor
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hadj :
      (kernelIntervalL2ZeroExtension (a - c) (c - a) 0).adjoint =
        globalL2ToKernelInterval (a - c) (c - a) 0 := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [kernelIntervalProjection, ContinuousLinearMap.comp_apply, hadj]
  rw [globalL2ToKernelInterval_zeroExtension]

/-- On the complete compact window, the negative half-line is exactly the
negative compact input window, up to the null boundary point. -/
theorem fullWindowProjection_comp_negativeHalfLineProjection
    (a c : ℝ) (hac : a ≤ c) :
    kernelIntervalProjection (a - c) (c - a) 0 ∘L
        cc20NegativeHalfLineProjection =
      kernelIntervalProjection (a - c) 0 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  have hfull := kernelIntervalProjection_coeFn
    (a - c) (c - a) 0 (cc20NegativeHalfLineProjection u)
  have hhalf := cc20NegativeHalfLineProjection_coeFn u
  have hnegative := kernelIntervalProjection_coeFn (a - c) 0 0 u
  have hzero := MeasureTheory.volume.ae_ne (0 : ℝ)
  filter_upwards [hfull, hhalf, hnegative, hzero] with x hf hh hn hxzero
  simp only [ContinuousLinearMap.comp_apply]
  simp only [sub_zero, add_zero] at hf hn
  rw [hf, hn]
  let fullSet := Set.Icc (a - c) (c - a)
  let negativeSet := Set.Icc (a - c) (0 : ℝ)
  by_cases hxnegative : x ∈ negativeSet
  · have hxlt : x < 0 := lt_of_le_of_ne hxnegative.2 hxzero
    have hxhalf : x ∈ Set.Iio (0 : ℝ) := hxlt
    have hxfull : x ∈ fullSet := by
      constructor
      · exact hxnegative.1
      · linarith [hac]
    rw [Set.indicator_of_mem hxfull, Set.indicator_of_mem hxnegative,
      hh, Set.indicator_of_mem hxhalf]
  · rw [Set.indicator_of_notMem hxnegative]
    by_cases hxfull : x ∈ fullSet
    · rw [Set.indicator_of_mem hxfull]
      have hxnotlt : x ∉ Set.Iio (0 : ℝ) := by
        intro hxlt
        apply hxnegative
        exact ⟨hxfull.1, le_of_lt hxlt⟩
      rw [hh, Set.indicator_of_notMem hxnotlt]
    · rw [Set.indicator_of_notMem hxfull]

/-- On the complete compact window, the positive half-line is exactly the
positive compact input window. -/
theorem fullWindowProjection_comp_positiveHalfLineProjection
    (a c : ℝ) (hac : a ≤ c) :
    kernelIntervalProjection (a - c) (c - a) 0 ∘L
        cc20PositiveHalfLineProjection =
      kernelIntervalProjection 0 (c - a) 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  have hfull := kernelIntervalProjection_coeFn
    (a - c) (c - a) 0 (cc20PositiveHalfLineProjection u)
  have hhalf := cc20PositiveHalfLineProjection_coeFn u
  have hpositive := kernelIntervalProjection_coeFn 0 (c - a) 0 u
  filter_upwards [hfull, hhalf, hpositive] with x hf hh hp
  simp only [ContinuousLinearMap.comp_apply]
  simp only [sub_zero, add_zero] at hf hp
  rw [hf, hp]
  let fullSet := Set.Icc (a - c) (c - a)
  let positiveSet := Set.Icc (0 : ℝ) (c - a)
  by_cases hxpositive : x ∈ positiveSet
  · have hxhalf : x ∈ cc20PositiveHalfLine := hxpositive.1
    have hxfull : x ∈ fullSet := by
      constructor
      · linarith [hac, hxpositive.1]
      · exact hxpositive.2
    rw [Set.indicator_of_mem hxfull, Set.indicator_of_mem hxpositive,
      hh, Set.indicator_of_mem hxhalf]
  · rw [Set.indicator_of_notMem hxpositive]
    by_cases hxfull : x ∈ fullSet
    · rw [Set.indicator_of_mem hxfull]
      have hxnotpositive : x ∉ cc20PositiveHalfLine := by
        intro hx
        apply hxpositive
        exact ⟨hx, hxfull.2⟩
      rw [hh, Set.indicator_of_notMem hxnotpositive]
    · rw [Set.indicator_of_notMem hxfull]

/-- The negative compact factor is the complete factor on the actual
negative half-line. -/
theorem fullBoundaryRootFactor_comp_negativeHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c) :
    fullBoundaryRootFactor g a c ∘L cc20NegativeHalfLineProjection =
      negativeBoundaryRootFactor g a c := by
  calc
    fullBoundaryRootFactor g a c ∘L cc20NegativeHalfLineProjection =
        (fullBoundaryRootFactor g a c ∘L
          kernelIntervalProjection (a - c) (c - a) 0) ∘L
            cc20NegativeHalfLineProjection := by
      rw [fullBoundaryRootFactor_comp_fullWindowProjection]
    _ = fullBoundaryRootFactor g a c ∘L
        (kernelIntervalProjection (a - c) (c - a) 0 ∘L
          cc20NegativeHalfLineProjection) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = fullBoundaryRootFactor g a c ∘L
        kernelIntervalProjection (a - c) 0 0 := by
      rw [fullWindowProjection_comp_negativeHalfLineProjection a c hac]
    _ = negativeBoundaryRootFactor g a c :=
      fullBoundaryRootFactor_comp_negativeWindowProjection g a c hac

/-- The positive compact factor is the complete factor on the actual
positive half-line. -/
theorem fullBoundaryRootFactor_comp_positiveHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c) :
    fullBoundaryRootFactor g a c ∘L cc20PositiveHalfLineProjection =
      positiveBoundaryRootFactor g a c := by
  calc
    fullBoundaryRootFactor g a c ∘L cc20PositiveHalfLineProjection =
        (fullBoundaryRootFactor g a c ∘L
          kernelIntervalProjection (a - c) (c - a) 0) ∘L
            cc20PositiveHalfLineProjection := by
      rw [fullBoundaryRootFactor_comp_fullWindowProjection]
    _ = fullBoundaryRootFactor g a c ∘L
        (kernelIntervalProjection (a - c) (c - a) 0 ∘L
          cc20PositiveHalfLineProjection) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = fullBoundaryRootFactor g a c ∘L
        kernelIntervalProjection 0 (c - a) 0 := by
      rw [fullWindowProjection_comp_positiveHalfLineProjection a c hac]
    _ = positiveBoundaryRootFactor g a c :=
      fullBoundaryRootFactor_comp_positiveWindowProjection g a c hac

/-- The negative factor is the reflected-window restriction of the genuine
global convolution on negative-half-line input. -/
theorem negativeBoundaryRootFactor_eq_globalConvolution_negativeHalfLine
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    negativeBoundaryRootFactor g a c =
      globalL2ToKernelInterval (-c) (-a) 0 ∘L
        cc20GlobalLogConvolution g.involution.test ∘L
          cc20NegativeHalfLineProjection := by
  rw [← fullBoundaryRootFactor_comp_negativeHalfLineProjection
    g a c hac]
  rw [fullBoundaryRootFactor_eq_globalConvolution g a c hsupp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The positive factor is the same reflected-window restriction of the
genuine global convolution on positive-half-line input. -/
theorem positiveBoundaryRootFactor_eq_globalConvolution_positiveHalfLine
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    positiveBoundaryRootFactor g a c =
      globalL2ToKernelInterval (-c) (-a) 0 ∘L
        cc20GlobalLogConvolution g.involution.test ∘L
          cc20PositiveHalfLineProjection := by
  rw [← fullBoundaryRootFactor_comp_positiveHalfLineProjection
    g a c hac]
  rw [fullBoundaryRootFactor_eq_globalConvolution g a c hsupp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Positive-window zero extension lands in the fixed positive half-line. -/
theorem positiveHalfLineProjection_comp_positiveBoundaryZeroExtension
    (a c : ℝ) :
    cc20PositiveHalfLineProjection ∘L
        positiveBoundaryZeroExtension a c =
      positiveBoundaryZeroExtension a c := by
  apply ContinuousLinearMap.ext
  intro u
  unfold positiveBoundaryZeroExtension kernelIntervalL2ZeroExtension
  simp only [ContinuousLinearMap.comp_apply]
  let v := (kernelIntervalSubtypeRestrictedL2IsometryEquiv
    0 (c - a) 0).symm u
  rw [Lp.ext_iff]
  have hprojection := cc20PositiveHalfLineProjection_coeFn
    (kernelIntervalRestrictedZeroExtension 0 (c - a) 0 v)
  have hextension := kernelIntervalRestrictedZeroExtension_coeFn
    0 (c - a) 0 v
  filter_upwards [hprojection, hextension] with t hp he
  simp only [sub_zero, add_zero] at he
  change (cc20PositiveHalfLineProjection
      (kernelIntervalRestrictedZeroExtension 0 (c - a) 0 v) : ℝ → ℂ) t =
    (kernelIntervalRestrictedZeroExtension 0 (c - a) 0 v : ℝ → ℂ) t
  rw [hp]
  by_cases ht : t ∈ Set.Icc (0 : ℝ) (c - a)
  · have htPositive : t ∈ cc20PositiveHalfLine := by
      simpa only [cc20PositiveHalfLine, Set.mem_Ici] using ht.1
    rw [Set.indicator_of_mem htPositive, he,
      Set.indicator_of_mem ht]
  · by_cases htPositive : t ∈ cc20PositiveHalfLine
    · rw [Set.indicator_of_mem htPositive, he,
        Set.indicator_of_notMem ht]
    · rw [Set.indicator_of_notMem htPositive, he,
        Set.indicator_of_notMem ht]

/-- Negative-window zero extension is killed by the fixed positive-half-line
projection.  The shared endpoint is null and is removed explicitly. -/
theorem positiveHalfLineProjection_comp_negativeBoundaryZeroExtension
    (a c : ℝ) :
    cc20PositiveHalfLineProjection ∘L
      negativeBoundaryZeroExtension a c = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  unfold negativeBoundaryZeroExtension kernelIntervalL2ZeroExtension
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply]
  let v := (kernelIntervalSubtypeRestrictedL2IsometryEquiv
    (a - c) 0 0).symm u
  change cc20PositiveHalfLineProjection
      (kernelIntervalRestrictedZeroExtension (a - c) 0 0 v) =
    (0 : cc20GlobalLogCrossingL2)
  rw [Lp.ext_iff]
  have hprojection := cc20PositiveHalfLineProjection_coeFn
    (kernelIntervalRestrictedZeroExtension (a - c) 0 0 v)
  have hextension := kernelIntervalRestrictedZeroExtension_coeFn
    (a - c) 0 0 v
  filter_upwards [hprojection, hextension,
    MeasureTheory.volume.ae_ne (0 : ℝ),
    Lp.coeFn_zero ℂ 2 volume] with t hp he htZero hzeroAt
  simp only [sub_zero, add_zero] at he
  rw [hp]
  rw [hzeroAt]
  by_cases htPositive : t ∈ cc20PositiveHalfLine
  · have htInterval : t ∉ Set.Icc (a - c) (0 : ℝ) := by
      intro ht
      have htNonpositive : t ≤ 0 := ht.2
      have htNonnegative : 0 ≤ t := htPositive
      exact htZero (le_antisymm htNonpositive htNonnegative)
    rw [Set.indicator_of_mem htPositive, he,
      Set.indicator_of_notMem htInterval]
    simp only [Pi.zero_apply]
  · rw [Set.indicator_of_notMem htPositive]
    simp only [Pi.zero_apply]

/-- Restriction to the positive compact input window already absorbs the
positive-half-line projection. -/
theorem positiveBoundaryRestriction_comp_positiveHalfLineProjection
    (a c : ℝ) :
    globalL2ToKernelInterval 0 (c - a) 0 ∘L
        cc20PositiveHalfLineProjection =
      globalL2ToKernelInterval 0 (c - a) 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (positiveHalfLineProjection_comp_positiveBoundaryZeroExtension a c)
  rw [ContinuousLinearMap.adjoint_comp] at h
  have hselfWitness := cc20PositiveHalfLineProjection_isSelfAdjoint
  have hself : cc20PositiveHalfLineProjection.adjoint =
      cc20PositiveHalfLineProjection :=
    hselfWitness.adjoint_eq
  have hextension : (positiveBoundaryZeroExtension a c).adjoint =
      globalL2ToKernelInterval 0 (c - a) 0 := by
    unfold positiveBoundaryZeroExtension
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint]
  rw [hself, hextension] at h
  exact h

/-- Restriction to the negative compact input window kills the positive
half-line projection. -/
theorem negativeBoundaryRestriction_comp_positiveHalfLineProjection
    (a c : ℝ) :
    globalL2ToKernelInterval (a - c) 0 0 ∘L
        cc20PositiveHalfLineProjection = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (positiveHalfLineProjection_comp_negativeBoundaryZeroExtension a c)
  rw [ContinuousLinearMap.adjoint_comp] at h
  simp only [map_zero] at h
  have hselfWitness := cc20PositiveHalfLineProjection_isSelfAdjoint
  have hself : cc20PositiveHalfLineProjection.adjoint =
      cc20PositiveHalfLineProjection :=
    hselfWitness.adjoint_eq
  have hextension : (negativeBoundaryZeroExtension a c).adjoint =
      globalL2ToKernelInterval (a - c) 0 0 := by
    unfold negativeBoundaryZeroExtension
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint]
  rw [hself, hextension] at h
  exact h

/-- The positive compact kernel factor ignores an additional positive
half-line projection on its input. -/
theorem positiveBoundaryRootFactor_comp_positiveHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    positiveBoundaryRootFactor g a c ∘L
        cc20PositiveHalfLineProjection =
      positiveBoundaryRootFactor g a c := by
  unfold positiveBoundaryRootFactor
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) =>
        map u)
    (positiveBoundaryRestriction_comp_positiveHalfLineProjection a c)
  simpa only [ContinuousLinearMap.comp_apply] using congrArg
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryPositiveInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (positiveBoundaryRootKernel g a c)) h

/-- The negative compact kernel factor ignores an additional negative
half-line projection on its input. -/
theorem negativeBoundaryRootFactor_comp_negativeHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    negativeBoundaryRootFactor g a c ∘L
        (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
          cc20PositiveHalfLineProjection) =
      negativeBoundaryRootFactor g a c := by
  unfold negativeBoundaryRootFactor
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have hzero := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) =>
        map u)
    (negativeBoundaryRestriction_comp_positiveHalfLineProjection a c)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero
  rw [hzero, map_zero, sub_zero]

/-- The negative compact factor vanishes on positive-half-line input. -/
theorem negativeBoundaryRootFactor_comp_positiveHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    negativeBoundaryRootFactor g a c ∘L
        cc20PositiveHalfLineProjection = 0 := by
  unfold negativeBoundaryRootFactor
  apply ContinuousLinearMap.ext
  intro u
  have hzero := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) =>
        map u)
    (negativeBoundaryRestriction_comp_positiveHalfLineProjection a c)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  rw [hzero, map_zero]

/-- The positive compact factor vanishes on negative-half-line input. -/
theorem positiveBoundaryRootFactor_comp_negativeHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    positiveBoundaryRootFactor g a c ∘L
        (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
          cc20PositiveHalfLineProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hfixed := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) => map u)
    (positiveBoundaryRootFactor_comp_positiveHalfLineProjection g a c)
  simp only [ContinuousLinearMap.comp_apply] at hfixed
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply, map_sub]
  rw [hfixed, sub_self]

/-- The positive detector formed from the complete compact boundary factor. -/
noncomputable def windowedBoundaryDetector
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (fullBoundaryRootFactor g a c)† ∘L fullBoundaryRootFactor g a c

theorem windowedBoundaryDetector_isSelfAdjoint
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    IsSelfAdjoint (windowedBoundaryDetector g a c) := by
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (fullBoundaryRootFactor g a c)).isSelfAdjoint

/-- The two actual whole-line factors form one `A^dagger B` owner. -/
noncomputable def pairData
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))
      globalBasis where
  left := negativeBoundaryRootFactor g a c
  right := positiveBoundaryRootFactor g a c
  left_summable_normSq :=
    PositiveTrace.summable_normSq_precomp
      negativeBasis outputBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (negativeBoundaryRootKernel g a c))
      (globalL2ToKernelInterval (a - c) 0 0)
      (ContinuousKernelHilbertSchmidt.basis_normSq_summable
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (negativeBoundaryRootKernel g a c) negativeBasis)
  right_summable_normSq :=
    PositiveTrace.summable_normSq_precomp
      positiveBasis outputBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (positiveBoundaryRootKernel g a c))
      (globalL2ToKernelInterval 0 (c - a) 0)
      (ContinuousKernelHilbertSchmidt.basis_normSq_summable
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (positiveBoundaryRootKernel g a c) positiveBasis)

theorem pairData_traceProduct_eq
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (pairData g a c negativeBasis positiveBasis outputBasis
      globalBasis).traceProduct =
      (negativeBoundaryRootFactor g a c)† ∘L
        positiveBoundaryRootFactor g a c := by
  rfl

/-- The compact pair product is the actual oriented half-line crossing of the
single windowed positive detector. -/
theorem pairData_traceProduct_eq_orientedBoundaryCrossing
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct =
      cc20OrientedBoundaryCrossing cc20PositiveHalfLineProjection
        (windowedBoundaryDetector g a c) := by
  rw [pairData_traceProduct_eq]
  rw [← fullBoundaryRootFactor_comp_negativeHalfLineProjection
    g a c hac]
  rw [← fullBoundaryRootFactor_comp_positiveHalfLineProjection
    g a c hac]
  have hnegativeAdjoint : cc20NegativeHalfLineProjection.adjoint =
      cc20NegativeHalfLineProjection := by
    unfold cc20NegativeHalfLineProjection
    rw [map_sub, ContinuousLinearMap.adjoint_id,
      cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq]
  rw [ContinuousLinearMap.adjoint_comp, hnegativeAdjoint]
  unfold cc20OrientedBoundaryCrossing windowedBoundaryDetector
  unfold cc20NegativeHalfLineProjection
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The pair product only reads positive-half-line input. -/
theorem pairData_traceProduct_comp_positiveHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct ∘L cc20PositiveHalfLineProjection =
      (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct := by
  rw [pairData_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  have hfixed := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) => map u)
    (positiveBoundaryRootFactor_comp_positiveHalfLineProjection g a c)
  simpa only [ContinuousLinearMap.comp_apply] using congrArg
    (negativeBoundaryRootFactor g a c).adjoint hfixed

/-- The pair product kills negative-half-line input. -/
theorem pairData_traceProduct_comp_negativeHalfLineProjection
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct ∘L
        (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
          cc20PositiveHalfLineProjection) = 0 := by
  rw [pairData_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  have hzero := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) => map u)
    (positiveBoundaryRootFactor_comp_negativeHalfLineProjection g a c)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  rw [hzero, map_zero]

/-- The range of the pair product lies in the negative half-line. -/
theorem positiveHalfLineProjection_comp_pairData_traceProduct
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    cc20PositiveHalfLineProjection ∘L
        (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (negativeBoundaryRootFactor_comp_positiveHalfLineProjection g a c)
  rw [ContinuousLinearMap.adjoint_comp] at h
  simp only [map_zero] at h
  have hselfWitness := cc20PositiveHalfLineProjection_isSelfAdjoint
  rw [hselfWitness.adjoint_eq] at h
  rw [pairData_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply]
  have hzero := congrArg
    (fun map : Lp ℂ 2
      (volume : Measure (BoundaryOutputInterval a c)) →L[ℂ]
        cc20GlobalLogCrossingL2 =>
      map (positiveBoundaryRootFactor g a c u)) h
  simpa only [ContinuousLinearMap.comp_apply] using hzero

/-- Equivalently, the negative-half-line projection fixes the pair product. -/
theorem negativeHalfLineProjection_comp_pairData_traceProduct
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
        cc20PositiveHalfLineProjection) ∘L
        (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct =
      (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero := congrArg
    (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
      cc20GlobalLogCrossingL2 => map u)
    (positiveHalfLineProjection_comp_pairData_traceProduct g a c
      negativeBasis positiveBasis outputBasis globalBasis)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  change (pairData g a c negativeBasis positiveBasis outputBasis
      globalBasis).traceProduct u -
        cc20PositiveHalfLineProjection
          ((pairData g a c negativeBasis positiveBasis outputBasis
            globalBasis).traceProduct u) =
      (pairData g a c negativeBasis positiveBasis outputBasis
        globalBasis).traceProduct u
  rw [hzero, sub_zero]

theorem pairData_isTraceClassAlong
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      ((negativeBoundaryRootFactor g a c)† ∘L
        positiveBoundaryRootFactor g a c) := by
  rw [← pairData_traceProduct_eq g a c negativeBasis positiveBasis
    outputBasis globalBasis]
  exact (pairData g a c negativeBasis positiveBasis outputBasis globalBasis)
    |>.traceProduct_isTraceClassAlong

/-- The forward and reverse boundary orientations are recombined as one
signed operator before any scalar estimate. -/
noncomputable def signedBoundaryOperator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (pairData g a c negativeBasis positiveBasis outputBasis
      globalBasis).swap.traceProduct -
    (pairData g a c negativeBasis positiveBasis outputBasis
      globalBasis).traceProduct

theorem signedBoundaryOperator_eq_adjoint_sub
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    signedBoundaryOperator g a c negativeBasis positiveBasis outputBasis
        globalBasis =
      (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct.adjoint -
        (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct := by
  rw [signedBoundaryOperator,
    PositiveTrace.BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint]

/-- The signed compact pair is the genuine commutator of the positive
windowed boundary detector with the actual half-line projection. -/
theorem signedBoundaryOperator_eq_commutator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    signedBoundaryOperator g a c negativeBasis positiveBasis outputBasis
        globalBasis =
      cc20Commutator cc20PositiveHalfLineProjection
        (windowedBoundaryDetector g a c) := by
  rw [signedBoundaryOperator_eq_adjoint_sub]
  rw [pairData_traceProduct_eq_orientedBoundaryCrossing
    g a c hac negativeBasis positiveBasis outputBasis globalBasis]
  exact (cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    cc20PositiveHalfLineProjection (windowedBoundaryDetector g a c)
    cc20PositiveHalfLineProjection_isSelfAdjoint
    (windowedBoundaryDetector_isSelfAdjoint g a c)).symm

theorem signedBoundaryOperator_isTraceClassAlong
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (signedBoundaryOperator g a c negativeBasis positiveBasis outputBasis
        globalBasis) := by
  rw [signedBoundaryOperator_eq_adjoint_sub]
  apply PositiveTrace.isTraceClassAlong_sub
  · exact PositiveTrace.isTraceClassAlong_adjoint globalBasis _
      ((pairData g a c negativeBasis positiveBasis outputBasis globalBasis)
        |>.traceProduct_isTraceClassAlong)
  · exact (pairData g a c negativeBasis positiveBasis outputBasis globalBasis)
      |>.traceProduct_isTraceClassAlong

/-- The signed scalar is the conjugate of the forward trace minus the
forward trace.  The two orientations remain coupled in this identity. -/
theorem ordinaryTraceAlong_signedBoundaryOperator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (signedBoundaryOperator g a c negativeBasis positiveBasis
          outputBasis globalBasis) =
      star (PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct) -
      PositiveTrace.ordinaryTraceAlong globalBasis
        (pairData g a c negativeBasis positiveBasis outputBasis
          globalBasis).traceProduct := by
  rw [signedBoundaryOperator_eq_adjoint_sub]
  rw [PositiveTrace.ordinaryTraceAlong_sub]
  · rw [PositiveTrace.ordinaryTraceAlong_adjoint]
  · exact PositiveTrace.isTraceClassAlong_adjoint globalBasis _
      ((pairData g a c negativeBasis positiveBasis outputBasis globalBasis)
        |>.traceProduct_isTraceClassAlong)
  · exact (pairData g a c negativeBasis positiveBasis outputBasis globalBasis)
      |>.traceProduct_isTraceClassAlong

end CompactRootHalfLinePair
end CC20Concrete
end Source
end ConnesWeilRH
