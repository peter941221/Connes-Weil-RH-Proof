/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingKernel

/-!
# Identify the compact crossing coefficient with Schwartz convolution

The finite kernel operator is first identified on restricted Schwartz inputs.
This is the dense-core equality needed before transporting `pairData` to the
whole-line convolution/crossing composition.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedCrossingOperatorBridge

open MeasureTheory
open scoped Convolution FourierTransform
open ConnesWeilRH.Source.CC20Concrete
open SelectedCrossingKernel

noncomputable def kernelRestriction
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ) :
    ContinuousMap (KernelInterval a c b) ℂ where
  toFun t := u t.1
  continuous_toFun := u.continuous.comp continuous_subtype_val

noncomputable def sourceRestriction
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    ContinuousMap (SourceInterval b) ℂ where
  toFun s := u s.1
  continuous_toFun := u.continuous.comp continuous_subtype_val

noncomputable def shiftedSourceRestriction
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    ContinuousMap (SourceInterval b) ℂ where
  toFun s := u (s.1 - b)
  continuous_toFun := u.continuous.comp
    (continuous_subtype_val.sub continuous_const)

theorem rightCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t in Set.Icc (a - b) (c + b),
        u t * star (g.test (t - s.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (rightKernel g.test g.test.continuous a c b) s))
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ t : KernelInterval a c b,
      u t.1 * star (g.test (t.1 - s.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc (fun t : ℝ => u t * star (g.test (t - s.1)))

theorem rightCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b))
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t : ℝ, u t * star (g.test (t - s.1)) := by
  rw [rightCoefficient_kernelRestriction_eq_setIntegral]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [Set.indicator_of_mem ht]
  · have hut : u t = 0 := by
      by_contra hne
      exact ht (hu (by simpa [Function.mem_support] using hne))
    simp [Set.indicator, ht, hut]

theorem rightCoefficient_kernelRestriction_eq_schwartzConvolution
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b))
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        u g.involution.test s.1 := by
  rw [rightCoefficient_kernelRestriction_eq_fullIntegral g u a c b hu s]
  let B := ContinuousLinearMap.mul ℂ ℂ
  calc
    (∫ t : ℝ, u t * star (g.test (t - s.1))) =
        (u ⋆[B] g.involution.test) s.1 := by
      rw [MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      rw [CompactLogConvolution.CompactLogTest.involution_apply]
      congr 2
      ring
    _ = SchwartzMap.convolution B
        u g.involution.test s.1 :=
      (SchwartzMap.convolution_apply
        B u g.involution.test s.1).symm

theorem schwartzConvolution_mul_real_eq_complex
    (u v : SchwartzMap ℝ ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v := by
  apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v) =
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v)
  rw [SchwartzMap.fourier_convolution, SchwartzMap.fourier_convolution]
  ext x
  rfl

theorem schwartzConvolution_mul_real_comm
    (u v : SchwartzMap ℝ ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) v u := by
  have hflip : (ContinuousLinearMap.mul ℝ ℂ).flip =
      ContinuousLinearMap.mul ℝ ℂ := by
    ext x y
    exact mul_comm y x
  calc
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ).flip v u :=
      (SchwartzMap.convolution_flip
        (ContinuousLinearMap.mul ℝ ℂ) u v).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) v u := by
      rw [hflip]

theorem rightCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b))
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u s.1 := by
  rw [rightCoefficient_kernelRestriction_eq_schwartzConvolution
    g u a c b hu s]
  rw [← schwartzConvolution_mul_real_eq_complex]
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
    (schwartzConvolution_mul_real_comm u g.involution.test)

theorem rightCoefficient_kernelRestriction_eq_sourceRestriction
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b)) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      sourceRestriction
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u) b := by
  ext s
  exact rightCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c b hu s

theorem rightOperator_kernelRestriction_eq_sourceConvolutionToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b)) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (sourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  rw [rightCoefficient_kernelRestriction_eq_sourceRestriction g u a c b hu]

theorem leftCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t in Set.Icc (a - b) (c + b),
        u t * star (g.test (t - s.1 + b)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (leftKernel g.test g.test.continuous a c b) s))
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ t : KernelInterval a c b,
      u t.1 * star (g.test (t.1 - s.1 + b))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc
    (fun t : ℝ => u t * star (g.test (t - s.1 + b)))

theorem leftCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b))
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t : ℝ, u t * star (g.test (t - s.1 + b)) := by
  rw [leftCoefficient_kernelRestriction_eq_setIntegral]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [Set.indicator_of_mem ht]
  · have hut : u t = 0 := by
      by_contra hne
      exact ht (hu (by simpa [Function.mem_support] using hne))
    simp [Set.indicator, ht, hut]

theorem leftCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b))
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u (s.1 - b) := by
  rw [leftCoefficient_kernelRestriction_eq_fullIntegral g u a c b hu s]
  have hcomplex :
      (∫ t : ℝ, u t * star (g.test (t - s.1 + b))) =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
          u g.involution.test (s.1 - b) := by
    let B := ContinuousLinearMap.mul ℂ ℂ
    calc
      (∫ t : ℝ, u t * star (g.test (t - s.1 + b))) =
          (u ⋆[B] g.involution.test) (s.1 - b) := by
        rw [MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with t
        rw [CompactLogConvolution.CompactLogTest.involution_apply]
        congr 2
        ring
      _ = SchwartzMap.convolution B u g.involution.test (s.1 - b) :=
        (SchwartzMap.convolution_apply
          B u g.involution.test (s.1 - b)).symm
  rw [hcomplex]
  rw [← schwartzConvolution_mul_real_eq_complex]
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (s.1 - b))
    (schwartzConvolution_mul_real_comm u g.involution.test)

theorem leftCoefficient_kernelRestriction_eq_shiftedSourceRestriction
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b)) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      shiftedSourceRestriction
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u) b := by
  ext s
  exact leftCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c b hu s

theorem leftOperator_kernelRestriction_eq_shiftedSourceConvolutionToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hu : Function.support u ⊆ Set.Icc (a - b) (c + b)) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (shiftedSourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  rw [leftCoefficient_kernelRestriction_eq_shiftedSourceRestriction
    g u a c b hu]

end SelectedCrossingOperatorBridge
end CCM25Concrete
end Source
end ConnesWeilRH
