/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compact output restrictions for compactly supported convolution kernels

For a kernel supported in `[A,C]` and an output interval `[d,e]`, only the
input interval `[d+A,e+C]` contributes.  This module identifies the resulting
continuous-kernel operator with the restriction of the genuine Fourier-defined
global convolution on all of `L2`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace CompactConvolutionSupport

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProduct InnerProductSpace
open CCM25Concrete
open CCM25Concrete.SelectedCrossingKernel
open CCM25Concrete.SelectedCrossingOperatorBridge
open CompactRootHalfLinePair

abbrev CompactOutputInterval (d e : ℝ) := KernelInterval d e 0

abbrev CompactInputInterval (A C d e : ℝ) :=
  KernelInterval (d + A) (e + C) 0

theorem input_mem_of_kernel_ne_zero
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc A C)
    (t : CompactOutputInterval d e) {x : ℝ}
    (hkernel : g.test (x - t.1) ≠ 0) :
    x ∈ Set.Icc (d + A) (e + C) := by
  have hz : x - t.1 ∈ Set.Icc A C := by
    exact hsupp (by simpa [Function.mem_support] using hkernel)
  constructor
  · linarith [hz.1, t.2.1]
  · linarith [hz.2, t.2.2]

noncomputable def compactOutputRootKernel
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ) :
    ContinuousMap
      ((CompactOutputInterval d e) ×
        (CompactInputInterval A C d e)) ℂ where
  toFun z := g.test (z.2.1 - z.1.1)
  continuous_toFun := g.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

theorem coefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (A C d e : ℝ)
    (t : CompactOutputInterval d e) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (CompactInputInterval A C d e))
        (compactOutputRootKernel g A C d e)
        (ContinuousMap.toLp 2
          (volume : Measure (CompactInputInterval A C d e)) ℂ
          (kernelRestriction u (d + A) (e + C) 0)) t =
      ∫ x in Set.Icc (d + A - 0) (e + C + 0),
        u x * star (g.test (x - t.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (CompactInputInterval A C d e)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (compactOutputRootKernel g A C d e) t))
      (ContinuousMap.toLp 2
        (volume : Measure (CompactInputInterval A C d e)) ℂ
        (kernelRestriction u (d + A) (e + C) 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : CompactInputInterval A C d e,
      u x.1 * star (g.test (x.1 - t.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Set.Icc (d + A - 0) (e + C + 0)) measurableSet_Icc
    (fun x : ℝ => u x * star (g.test (x - t.1)))

theorem coefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (A C d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc A C)
    (t : CompactOutputInterval d e) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (CompactInputInterval A C d e))
        (compactOutputRootKernel g A C d e)
        (ContinuousMap.toLp 2
          (volume : Measure (CompactInputInterval A C d e)) ℂ
          (kernelRestriction u (d + A) (e + C) 0)) t =
      ∫ x : ℝ, u x * star (g.test (x - t.1)) := by
  rw [coefficient_kernelRestriction_eq_setIntegral]
  simp only [sub_zero, add_zero]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (d + A) (e + C)
  · rw [Set.indicator_of_mem hx]
  · have hzero : g.test (x - t.1) = 0 := by
      by_contra hnonzero
      exact hx (input_mem_of_kernel_ne_zero
        g A C d e hsupp t hnonzero)
    simp [Set.indicator, hx, hzero]

theorem coefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (A C d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc A C)
    (t : CompactOutputInterval d e) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (CompactInputInterval A C d e))
        (compactOutputRootKernel g A C d e)
        (ContinuousMap.toLp 2
          (volume : Measure (CompactInputInterval A C d e)) ℂ
          (kernelRestriction u (d + A) (e + C) 0)) t =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u t.1 := by
  rw [coefficient_kernelRestriction_eq_fullIntegral
    g u A C d e hsupp t]
  exact fullBoundaryIntegral_eq_globalConvolutionCore g u t.1

noncomputable def compactOutputRootFactor
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (CompactOutputInterval d e)) :=
  ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (CompactInputInterval A C d e))
      (volume : Measure (CompactOutputInterval d e))
      (compactOutputRootKernel g A C d e) ∘L
    globalL2ToKernelInterval (d + A) (e + C) 0

theorem compactOutputRootFactor_apply_schwartzToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (A C d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc A C) :
    compactOutputRootFactor g A C d e (u.toLp 2) =
      globalL2ToKernelInterval d e 0
        (cc20GlobalLogConvolution g.involution.test (u.toLp 2)) := by
  unfold compactOutputRootFactor
  simp only [ContinuousLinearMap.comp_apply]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [cc20GlobalLogConvolution_toLp]
  rw [globalL2ToKernelInterval_apply_schwartzToLp]
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  apply congrArg
    (ContinuousMap.toLp 2
      (volume : Measure (CompactOutputInterval d e)) ℂ)
  ext t
  exact coefficient_kernelRestriction_eq_globalConvolutionCore
    g u A C d e hsupp t

theorem compactOutputRootFactor_eq_globalConvolution
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc A C) :
    compactOutputRootFactor g A C d e =
      globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.involution.test := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (compactOutputRootFactor g A C d e :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (CompactOutputInterval d e))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.involution.test :
          cc20GlobalLogCrossingL2 →
            Lp ℂ 2 (volume : Measure (CompactOutputInterval d e))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply] using
      compactOutputRootFactor_apply_schwartzToLp
        g u A C d e hsupp
  have hfun := DenseRange.equalizer hdense
    (compactOutputRootFactor g A C d e).continuous
    (globalL2ToKernelInterval d e 0 ∘L
      cc20GlobalLogConvolution g.involution.test).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The compact-output factor only reads its support-forced compact input
window. -/
theorem compactOutputRootFactor_comp_inputProjection
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ) :
    compactOutputRootFactor g A C d e ∘L
        kernelIntervalProjection (d + A) (e + C) 0 =
      compactOutputRootFactor g A C d e := by
  unfold compactOutputRootFactor
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hadj :
      (kernelIntervalL2ZeroExtension (d + A) (e + C) 0).adjoint =
        globalL2ToKernelInterval (d + A) (e + C) 0 := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [kernelIntervalProjection, ContinuousLinearMap.comp_apply, hadj]
  rw [globalL2ToKernelInterval_zeroExtension]

/-- A compact interval whose upper endpoint is nonpositive has zero overlap
with the positive half-line, up to the null endpoint. -/
theorem inputProjection_comp_positiveHalfLine_eq_zero
    (A C d e : ℝ) (hupper : e + C ≤ 0) :
    kernelIntervalProjection (d + A) (e + C) 0 ∘L
        cc20PositiveHalfLineProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  have hprojection := kernelIntervalProjection_coeFn
    (d + A) (e + C) 0 (cc20PositiveHalfLineProjection u)
  have hhalf := cc20PositiveHalfLineProjection_coeFn u
  have hzeroValue := Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  have hzeroPoint := MeasureTheory.volume.ae_ne (0 : ℝ)
  filter_upwards [hprojection, hhalf, hzeroValue, hzeroPoint] with
    x hp hh hz hxzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  simp only [sub_zero, add_zero] at hp
  rw [hp, hz]
  let inputSet := Set.Icc (d + A) (e + C)
  by_cases hx : x ∈ inputSet
  · rw [Set.indicator_of_mem hx, hh]
    have hxnot : x ∉ cc20PositiveHalfLine := by
      intro hxpositive
      have hxle : x ≤ 0 := hx.2.trans hupper
      exact hxzero (le_antisymm hxle hxpositive)
    rw [Set.indicator_of_notMem hxnot]
    simp only [Pi.zero_apply]
  · rw [Set.indicator_of_notMem hx]
    simp only [Pi.zero_apply]

/-- If the forced input window is nonpositive, the compact-output factor
kills positive-half-line input. -/
theorem compactOutputRootFactor_comp_positiveHalfLine_eq_zero
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ) (hupper : e + C ≤ 0) :
    compactOutputRootFactor g A C d e ∘L
        cc20PositiveHalfLineProjection = 0 := by
  calc
    compactOutputRootFactor g A C d e ∘L
        cc20PositiveHalfLineProjection =
      (compactOutputRootFactor g A C d e ∘L
        kernelIntervalProjection (d + A) (e + C) 0) ∘L
          cc20PositiveHalfLineProjection := by
      rw [compactOutputRootFactor_comp_inputProjection]
    _ = compactOutputRootFactor g A C d e ∘L
        (kernelIntervalProjection (d + A) (e + C) 0 ∘L
          cc20PositiveHalfLineProjection) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = 0 := by
      rw [inputProjection_comp_positiveHalfLine_eq_zero
        A C d e hupper]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply, map_zero]

/-- A compact interval whose lower endpoint is nonnegative has zero overlap
with the negative half-line, up to the null endpoint. -/
theorem inputProjection_comp_negativeHalfLine_eq_zero
    (A C d e : ℝ) (hlower : 0 ≤ d + A) :
    kernelIntervalProjection (d + A) (e + C) 0 ∘L
        cc20NegativeHalfLineProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  have hprojection := kernelIntervalProjection_coeFn
    (d + A) (e + C) 0 (cc20NegativeHalfLineProjection u)
  have hhalf := cc20NegativeHalfLineProjection_coeFn u
  have hzeroValue := Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  have hzeroPoint := MeasureTheory.volume.ae_ne (0 : ℝ)
  filter_upwards [hprojection, hhalf, hzeroValue, hzeroPoint] with
    x hp hh hz hxzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  simp only [sub_zero, add_zero] at hp
  rw [hp, hz]
  let inputSet := Set.Icc (d + A) (e + C)
  by_cases hx : x ∈ inputSet
  · rw [Set.indicator_of_mem hx, hh]
    have hxnot : x ∉ Set.Iio (0 : ℝ) := by
      intro hxnegative
      have hxge : 0 ≤ x := hlower.trans hx.1
      exact hxzero (le_antisymm (le_of_lt hxnegative) hxge)
    rw [Set.indicator_of_notMem hxnot]
    simp only [Pi.zero_apply]
  · rw [Set.indicator_of_notMem hx]
    simp only [Pi.zero_apply]

/-- If the forced input window is nonnegative, the compact-output factor
kills negative-half-line input. -/
theorem compactOutputRootFactor_comp_negativeHalfLine_eq_zero
    (g : CompactLogConvolution.CompactLogTest)
    (A C d e : ℝ) (hlower : 0 ≤ d + A) :
    compactOutputRootFactor g A C d e ∘L
        cc20NegativeHalfLineProjection = 0 := by
  calc
    compactOutputRootFactor g A C d e ∘L
        cc20NegativeHalfLineProjection =
      (compactOutputRootFactor g A C d e ∘L
        kernelIntervalProjection (d + A) (e + C) 0) ∘L
          cc20NegativeHalfLineProjection := by
      rw [compactOutputRootFactor_comp_inputProjection]
    _ = compactOutputRootFactor g A C d e ∘L
        (kernelIntervalProjection (d + A) (e + C) 0 ∘L
          cc20NegativeHalfLineProjection) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = 0 := by
      rw [inputProjection_comp_negativeHalfLine_eq_zero
        A C d e hlower]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply, map_zero]

/-- A compact restriction of the convolution-square detector is represented
by the generic compact-output factor. -/
theorem convolutionSquare_compactOutputRootFactor_eq
    (g : CompactLogConvolution.CompactLogTest)
    (a c d e : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    compactOutputRootFactor g.convolutionSquare
        (a - c) (c - a) d e =
      globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test := by
  have hsquare := convolutionSquare_support_subset g a c hsupp
  rw [compactOutputRootFactor_eq_globalConvolution
    g.convolutionSquare (a - c) (c - a) d e hsquare]
  rw [convolutionSquare_involution_test_eq]

/-- Below the lower difference endpoint, every compact output restriction of
the convolution-square detector vanishes on positive-half-line input. -/
theorem convolutionSquare_restrict_below_eq_zero
    (g : CompactLogConvolution.CompactLogTest)
    (a c d e : ℝ) (he : e ≤ a - c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20PositiveHalfLineProjection = 0 := by
  calc
    globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20PositiveHalfLineProjection =
      (globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test) ∘L
          cc20PositiveHalfLineProjection := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = compactOutputRootFactor g.convolutionSquare
        (a - c) (c - a) d e ∘L
          cc20PositiveHalfLineProjection := by
      rw [convolutionSquare_compactOutputRootFactor_eq
        g a c d e hsupp]
    _ = 0 := by
      apply compactOutputRootFactor_comp_positiveHalfLine_eq_zero
      linarith

/-- Above the upper difference endpoint, every compact output restriction of
the convolution-square detector vanishes on negative-half-line input. -/
theorem convolutionSquare_restrict_above_eq_zero
    (g : CompactLogConvolution.CompactLogTest)
    (a c d e : ℝ) (hd : c - a ≤ d)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20NegativeHalfLineProjection = 0 := by
  calc
    globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20NegativeHalfLineProjection =
      (globalL2ToKernelInterval d e 0 ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test) ∘L
          cc20NegativeHalfLineProjection := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = compactOutputRootFactor g.convolutionSquare
        (a - c) (c - a) d e ∘L
          cc20NegativeHalfLineProjection := by
      rw [convolutionSquare_compactOutputRootFactor_eq
        g a c d e hsupp]
    _ = 0 := by
      apply compactOutputRootFactor_comp_negativeHalfLine_eq_zero
      linarith

/-- A zero compact restriction means that the global `L2` representative
vanishes almost everywhere on that interval. -/
theorem ae_eq_zero_on_compactInterval_of_restriction_eq_zero
    (u : cc20GlobalLogCrossingL2) (d e : ℝ)
    (hzero : globalL2ToKernelInterval d e 0 u = 0) :
    ∀ᵐ x : ℝ ∂volume, x ∈ Set.Icc d e → (u : ℝ → ℂ) x = 0 := by
  have hrestricted :
      LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Icc (d - 0) (e + 0)) u = 0 := by
    apply (kernelIntervalSubtypeRestrictedL2IsometryEquiv d e 0).injective
    simpa only [globalL2ToKernelInterval,
      ContinuousLinearMap.comp_apply, map_zero] using hzero
  rw [Lp.ext_iff] at hrestricted
  have hcoe := LpToLpRestrictCLM_coeFn ℂ
    (Set.Icc (d - 0) (e + 0)) u
  have hzeroCoe := Lp.coeFn_zero ℂ 2
    (volume.restrict (Set.Icc (d - 0) (e + 0)))
  have hrestrictedAe :
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc (d - 0) (e + 0))),
        (u : ℝ → ℂ) x = 0 := by
    filter_upwards [hcoe, hrestricted, hzeroCoe] with x hc hr hz
    rw [← hc, hr, hz]
    rfl
  have hglobal := (ae_restrict_iff' measurableSet_Icc).mp hrestrictedAe
  filter_upwards [hglobal] with x hx
  simpa only [sub_zero, add_zero] using hx

/-- Convolution by the compact square sends positive-half-line input to a
function vanishing below the lower difference endpoint. -/
theorem convolutionSquare_positiveHalfLine_vanishes_below
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (u : cc20GlobalLogCrossingL2) :
    ∀ᵐ x : ℝ ∂volume, x < a - c →
      (cc20GlobalLogConvolution g.convolutionSquare.test
        (cc20PositiveHalfLineProjection u) : ℝ → ℂ) x = 0 := by
  let v := cc20GlobalLogConvolution g.convolutionSquare.test
    (cc20PositiveHalfLineProjection u)
  have hcompact (n : ℕ) :
      globalL2ToKernelInterval (-(n : ℝ)) (a - c) 0 v = 0 := by
    have hop := convolutionSquare_restrict_below_eq_zero
      g a c (-(n : ℝ)) (a - c) le_rfl hsupp
    have happ := congrArg
      (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
        Lp ℂ 2 (volume : Measure (CompactOutputInterval (-(n : ℝ)) (a - c))) =>
          T u) hop
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, v] using happ
  have hcompactAe (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume, x ∈ Set.Icc (-(n : ℝ)) (a - c) →
        (v : ℝ → ℂ) x = 0 :=
    ae_eq_zero_on_compactInterval_of_restriction_eq_zero
      v (-(n : ℝ)) (a - c) (hcompact n)
  have hall : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x ∈ Set.Icc (-(n : ℝ)) (a - c) → (v : ℝ → ℂ) x = 0 :=
    ae_all_iff.mpr hcompactAe
  filter_upwards [hall] with x hx
  intro hxlower
  obtain ⟨n, hn⟩ := exists_nat_ge (-x)
  apply hx n
  constructor
  · linarith
  · exact le_of_lt hxlower

/-- Convolution by the compact square sends negative-half-line input to a
function vanishing above the upper difference endpoint. -/
theorem convolutionSquare_negativeHalfLine_vanishes_above
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (u : cc20GlobalLogCrossingL2) :
    ∀ᵐ x : ℝ ∂volume, c - a < x →
      (cc20GlobalLogConvolution g.convolutionSquare.test
        (cc20NegativeHalfLineProjection u) : ℝ → ℂ) x = 0 := by
  let v := cc20GlobalLogConvolution g.convolutionSquare.test
    (cc20NegativeHalfLineProjection u)
  have hcompact (n : ℕ) :
      globalL2ToKernelInterval (c - a) (n : ℝ) 0 v = 0 := by
    have hop := convolutionSquare_restrict_above_eq_zero
      g a c (c - a) (n : ℝ) le_rfl hsupp
    have happ := congrArg
      (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
        Lp ℂ 2 (volume : Measure (CompactOutputInterval (c - a) (n : ℝ))) =>
          T u) hop
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, v] using happ
  have hcompactAe (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume, x ∈ Set.Icc (c - a) (n : ℝ) →
        (v : ℝ → ℂ) x = 0 :=
    ae_eq_zero_on_compactInterval_of_restriction_eq_zero
      v (c - a) (n : ℝ) (hcompact n)
  have hall : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x ∈ Set.Icc (c - a) (n : ℝ) → (v : ℝ → ℂ) x = 0 :=
    ae_all_iff.mpr hcompactAe
  filter_upwards [hall] with x hx
  intro hxupper
  obtain ⟨n, hn⟩ := exists_nat_ge x
  apply hx n
  constructor
  · exact le_of_lt hxupper
  · exact hn

theorem kernelIntervalProjection_isSelfAdjoint
    (d e : ℝ) :
    IsSelfAdjoint (kernelIntervalProjection d e 0) := by
  unfold kernelIntervalProjection
  have h := (ContinuousLinearMap.isPositive_adjoint_comp_self
    (kernelIntervalL2ZeroExtension d e 0).adjoint).isSelfAdjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

theorem convolutionSquareOperator_isSelfAdjoint
    (g : CompactLogConvolution.CompactLogTest) :
    IsSelfAdjoint
      (cc20GlobalLogConvolution g.convolutionSquare.test) := by
  rw [← globalConvolutionPositive_eq_convolutionSquare]
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (cc20GlobalLogConvolution g.involution.test)).isSelfAdjoint

/-- The compact negative output window fixes the positive-to-negative
convolution-square crossing. -/
theorem negativeCompactProjection_fixes_squareCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    kernelIntervalProjection (a - c) 0 0 ∘L
        cc20NegativeHalfLineProjection ∘L
          cc20GlobalLogConvolution g.convolutionSquare.test ∘L
            cc20PositiveHalfLineProjection =
      cc20NegativeHalfLineProjection ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20PositiveHalfLineProjection := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  let f := cc20GlobalLogConvolution g.convolutionSquare.test
    (cc20PositiveHalfLineProjection u)
  let v := cc20NegativeHalfLineProjection f
  have hprojection := kernelIntervalProjection_coeFn (a - c) 0 0 v
  have hnegative := cc20NegativeHalfLineProjection_coeFn f
  have hbelow := convolutionSquare_positiveHalfLine_vanishes_below
    g a c hsupp u
  filter_upwards [hprojection, hnegative, hbelow] with x hp hn hb
  simp only [ContinuousLinearMap.comp_apply, f, v] at hp hn ⊢
  simp only [sub_zero, add_zero] at hp
  rw [hp]
  let outputSet := Set.Icc (a - c) (0 : ℝ)
  by_cases hxoutput : x ∈ outputSet
  · rw [Set.indicator_of_mem hxoutput]
  · rw [Set.indicator_of_notMem hxoutput, hn]
    by_cases hxnegative : x ∈ Set.Iio (0 : ℝ)
    · rw [Set.indicator_of_mem hxnegative]
      have hxbelow : x < a - c := by
        by_contra hxnot
        apply hxoutput
        exact ⟨le_of_not_gt hxnot, le_of_lt hxnegative⟩
      exact (hb hxbelow).symm
    · rw [Set.indicator_of_notMem hxnegative]

/-- The compact positive output window fixes the negative-to-positive adjoint
crossing. -/
theorem positiveCompactProjection_fixes_reverseSquareCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    kernelIntervalProjection 0 (c - a) 0 ∘L
        cc20PositiveHalfLineProjection ∘L
          cc20GlobalLogConvolution g.convolutionSquare.test ∘L
            cc20NegativeHalfLineProjection =
      cc20PositiveHalfLineProjection ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20NegativeHalfLineProjection := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  let f := cc20GlobalLogConvolution g.convolutionSquare.test
    (cc20NegativeHalfLineProjection u)
  let v := cc20PositiveHalfLineProjection f
  have hprojection := kernelIntervalProjection_coeFn 0 (c - a) 0 v
  have hpositive := cc20PositiveHalfLineProjection_coeFn f
  have habove := convolutionSquare_negativeHalfLine_vanishes_above
    g a c hsupp u
  filter_upwards [hprojection, hpositive, habove] with x hp he ha
  simp only [ContinuousLinearMap.comp_apply, f, v] at hp he ⊢
  simp only [sub_zero, add_zero] at hp
  rw [hp]
  let outputSet := Set.Icc (0 : ℝ) (c - a)
  by_cases hxoutput : x ∈ outputSet
  · rw [Set.indicator_of_mem hxoutput]
  · rw [Set.indicator_of_notMem hxoutput, he]
    by_cases hxpositive : x ∈ cc20PositiveHalfLine
    · rw [Set.indicator_of_mem hxpositive]
      have hxabove : c - a < x := by
        by_contra hxnot
        apply hxoutput
        exact ⟨hxpositive, le_of_not_gt hxnot⟩
      exact (ha hxabove).symm
    · rw [Set.indicator_of_notMem hxpositive]

/-- The compact positive input window fixes the positive-to-negative
convolution-square crossing. -/
theorem squareCrossing_comp_positiveCompactProjection
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    (cc20NegativeHalfLineProjection ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20PositiveHalfLineProjection) ∘L
        kernelIntervalProjection 0 (c - a) 0 =
      cc20NegativeHalfLineProjection ∘L
        cc20GlobalLogConvolution g.convolutionSquare.test ∘L
          cc20PositiveHalfLineProjection := by
  have hreverse := positiveCompactProjection_fixes_reverseSquareCrossing
    g a c hsupp
  have hadj := congrArg ContinuousLinearMap.adjoint hreverse
  have hnegativeAdjoint : cc20NegativeHalfLineProjection.adjoint =
      cc20NegativeHalfLineProjection := by
    unfold cc20NegativeHalfLineProjection
    rw [map_sub, ContinuousLinearMap.adjoint_id,
      cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq]
  simp only [ContinuousLinearMap.adjoint_comp,
    (kernelIntervalProjection_isSelfAdjoint 0 (c - a)).adjoint_eq,
    cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq,
    (convolutionSquareOperator_isSelfAdjoint g).adjoint_eq,
    hnegativeAdjoint] at hadj
  exact hadj

/-- A column of the negative compact root kernel, viewed on the common output
window. -/
noncomputable def negativeBoundaryColumn
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (x : BoundaryNegativeInputInterval a c) :
    ContinuousMap (BoundaryOutputInterval a c) ℂ where
  toFun t := g.test (x.1 - t.1)
  continuous_toFun := g.test.continuous.comp
    (continuous_const.sub continuous_subtype_val)

/-- A column of the positive compact root kernel on the same output window. -/
noncomputable def positiveBoundaryColumn
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (y : BoundaryPositiveInputInterval a c) :
    ContinuousMap (BoundaryOutputInterval a c) ℂ where
  toFun t := g.test (y.1 - t.1)
  continuous_toFun := g.test.continuous.comp
    (continuous_const.sub continuous_subtype_val)

/-- The inner product of one negative and one positive root column is the
literal convolution-square kernel at their displacement. -/
theorem inner_negative_positiveBoundaryColumn_eq_convolutionSquare
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (x : BoundaryNegativeInputInterval a c)
    (y : BoundaryPositiveInputInterval a c) :
    inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryOutputInterval a c)) ℂ
          (negativeBoundaryColumn g a c x))
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryOutputInterval a c)) ℂ
          (positiveBoundaryColumn g a c y)) =
      g.convolutionSquare.test (y.1 - x.1) := by
  rw [ContinuousMap.inner_toLp]
  change (∫ t : BoundaryOutputInterval a c,
      g.test (y.1 - t.1) * star (g.test (x.1 - t.1))
        ∂Measure.comap Subtype.val volume) = _
  have hsubtype :
      (∫ t : BoundaryOutputInterval a c,
        g.test (y.1 - t.1) * star (g.test (x.1 - t.1))
          ∂Measure.comap Subtype.val volume) =
        ∫ t in Set.Icc (-c) (-a),
          g.test (y.1 - t) * star (g.test (x.1 - t)) := by
    simpa only [sub_zero, add_zero] using
      (integral_subtype_comap (μ := (volume : Measure ℝ))
        (s := Set.Icc (-c - 0) (-a + 0)) measurableSet_Icc
        (fun t : ℝ => g.test (y.1 - t) * star (g.test (x.1 - t))))
  rw [hsubtype]
  rw [← integral_indicator measurableSet_Icc]
  have hfull :
      (∫ t : ℝ,
        (Set.Icc (-c) (-a)).indicator
          (fun s => g.test (y.1 - s) * star (g.test (x.1 - s))) t) =
      ∫ t : ℝ, g.test (y.1 - t) * star (g.test (x.1 - t)) := by
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Icc (-c) (-a)
    · rw [Set.indicator_of_mem ht]
    · have hzero : g.test (x.1 - t) = 0 ∨ g.test (y.1 - t) = 0 := by
        by_contra hnonzero
        push Not at hnonzero
        exact ht (output_mem_of_two_halfLine_kernel_ne_zero
          g a c hsupp
            (by simpa only [sub_zero, add_zero] using x.2.2)
            (by simpa only [sub_zero, add_zero] using y.2.1)
            hnonzero.1 hnonzero.2)
      rcases hzero with hzero | hzero
      · simp [Set.indicator, ht, hzero]
      · simp [Set.indicator, ht, hzero]
  rw [hfull]
  rw [CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  let integrand : ℝ → ℂ := fun s =>
    star (g.test (-s)) * g.test (y.1 - x.1 - s)
  calc
    (∫ t : ℝ, g.test (y.1 - t) * star (g.test (x.1 - t))) =
        ∫ t : ℝ, integrand (t + (-x.1)) := by
      apply integral_congr_ae
      filter_upwards with t
      have hleft : -(t + -x.1) = x.1 - t := by ring
      have hright : y.1 - x.1 - (t + -x.1) = y.1 - t := by ring
      simp only [integrand, hleft, hright, mul_comm]
    _ = ∫ s : ℝ, integrand s := integral_add_right_eq_self integrand (-x.1)

/-- The finite convolution-square kernel from the positive compact input
window to the negative compact output window. -/
noncomputable def squareBoundaryKernel
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    ContinuousMap
      ((BoundaryNegativeInputInterval a c) ×
        (BoundaryPositiveInputInterval a c)) ℂ where
  toFun z := g.convolutionSquare.test (z.2.1 - z.1.1)
  continuous_toFun := g.convolutionSquare.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

/-- The continuous-kernel operator carried by the finite square crossing. -/
noncomputable def squareBoundaryKernelOperator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryPositiveInputInterval a c))
    (volume : Measure (BoundaryNegativeInputInterval a c))
    (squareBoundaryKernel g a c)

theorem squareBoundaryKernel_apply
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (x : BoundaryNegativeInputInterval a c)
    (y : BoundaryPositiveInputInterval a c) :
    squareBoundaryKernel g a c (x, y) =
      inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryOutputInterval a c)) ℂ
          (negativeBoundaryColumn g a c x))
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryOutputInterval a c)) ℂ
          (positiveBoundaryColumn g a c y)) := by
  exact (inner_negative_positiveBoundaryColumn_eq_convolutionSquare
    g a c hsupp x y).symm

/-- The finite negative root leg before the whole-line input restriction. -/
noncomputable def finiteNegativeBoundaryRootOperator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryNegativeInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (negativeBoundaryRootKernel g a c)

/-- The finite positive root leg before the whole-line input restriction. -/
noncomputable def finitePositiveBoundaryRootOperator
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryPositiveInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (positiveBoundaryRootKernel g a c)

/-- On continuous compact inputs, the two finite root legs pair through the
single convolution-square kernel. -/
theorem finiteBoundaryRootOperators_inner_continuous
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (v : ContinuousMap (BoundaryNegativeInputInterval a c) ℂ)
    (u : ContinuousMap (BoundaryPositiveInputInterval a c) ℂ) :
    inner ℂ
        (finiteNegativeBoundaryRootOperator g a c
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v))
        (finitePositiveBoundaryRootOperator g a c
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u)) =
      inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v)
        (squareBoundaryKernelOperator g a c
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u)) := by
  unfold finiteNegativeBoundaryRootOperator finitePositiveBoundaryRootOperator
    squareBoundaryKernelOperator
  rw [ContinuousKernelHilbertSchmidt.operator_apply,
    ContinuousKernelHilbertSchmidt.operator_apply,
    ContinuousKernelHilbertSchmidt.operator_apply]
  rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  have hnegative (t : BoundaryOutputInterval a c) :
      ContinuousKernelHilbertSchmidt.coefficient
          (volume : Measure (BoundaryNegativeInputInterval a c))
          (negativeBoundaryRootKernel g a c)
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v) t =
        ∫ x : BoundaryNegativeInputInterval a c,
          v x * star (g.test (x.1 - t.1)) := by
    change inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ
          (ContinuousKernelHilbertSchmidt.kernelSection
            (negativeBoundaryRootKernel g a c) t))
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v) = _
    rw [ContinuousMap.inner_toLp]
    rfl
  have hpositive (t : BoundaryOutputInterval a c) :
      ContinuousKernelHilbertSchmidt.coefficient
          (volume : Measure (BoundaryPositiveInputInterval a c))
          (positiveBoundaryRootKernel g a c)
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t =
        ∫ y : BoundaryPositiveInputInterval a c,
          u y * star (g.test (y.1 - t.1)) := by
    change inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (ContinuousKernelHilbertSchmidt.kernelSection
            (positiveBoundaryRootKernel g a c) t))
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) = _
    rw [ContinuousMap.inner_toLp]
    rfl
  have hsquare (x : BoundaryNegativeInputInterval a c) :
      ContinuousKernelHilbertSchmidt.coefficient
          (volume : Measure (BoundaryPositiveInputInterval a c))
          (squareBoundaryKernel g a c)
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) x =
        ∫ y : BoundaryPositiveInputInterval a c,
          u y * star (squareBoundaryKernel g a c (x, y)) := by
    change inner ℂ
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (ContinuousKernelHilbertSchmidt.kernelSection
            (squareBoundaryKernel g a c) x))
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) = _
    rw [ContinuousMap.inner_toLp]
    rfl
  have houter : Integrable
      (fun p : (BoundaryOutputInterval a c) ×
          (BoundaryNegativeInputInterval a c) =>
        star (v p.2) * g.test (p.2.1 - p.1.1) *
          ContinuousKernelHilbertSchmidt.coefficient
            (volume : Measure (BoundaryPositiveInputInterval a c))
            (positiveBoundaryRootKernel g a c)
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) p.1)
      ((volume : Measure (BoundaryOutputInterval a c)).prod
        (volume : Measure (BoundaryNegativeInputInterval a c))) := by
    have hc : Continuous
        (fun p : (BoundaryOutputInterval a c) ×
            (BoundaryNegativeInputInterval a c) =>
          star (v p.2) * g.test (p.2.1 - p.1.1) *
            ContinuousKernelHilbertSchmidt.coefficient
              (volume : Measure (BoundaryPositiveInputInterval a c))
              (positiveBoundaryRootKernel g a c)
              (ContinuousMap.toLp 2
                (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) p.1) := by
      fun_prop
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure (BoundaryOutputInterval a c)).prod
          (volume : Measure (BoundaryNegativeInputInterval a c)))
        isCompact_univ).integrable
  have hcolumn (x : BoundaryNegativeInputInterval a c) :
      (∫ t : BoundaryOutputInterval a c,
          g.test (x.1 - t.1) *
            ContinuousKernelHilbertSchmidt.coefficient
              (volume : Measure (BoundaryPositiveInputInterval a c))
              (positiveBoundaryRootKernel g a c)
              (ContinuousMap.toLp 2
                (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t) =
        ∫ y : BoundaryPositiveInputInterval a c,
          u y * star (squareBoundaryKernel g a c (x, y)) := by
    have hinner : Integrable
        (fun p : (BoundaryOutputInterval a c) ×
            (BoundaryPositiveInputInterval a c) =>
          g.test (x.1 - p.1.1) *
            (u p.2 * star (g.test (p.2.1 - p.1.1))))
        ((volume : Measure (BoundaryOutputInterval a c)).prod
          (volume : Measure (BoundaryPositiveInputInterval a c))) := by
      have hc : Continuous
          (fun p : (BoundaryOutputInterval a c) ×
              (BoundaryPositiveInputInterval a c) =>
            g.test (x.1 - p.1.1) *
              (u p.2 * star (g.test (p.2.1 - p.1.1)))) := by
        fun_prop
      simpa only [Measure.restrict_univ] using
        (hc.continuousOn.integrableOn_compact
          (μ := (volume : Measure (BoundaryOutputInterval a c)).prod
            (volume : Measure (BoundaryPositiveInputInterval a c)))
          isCompact_univ).integrable
    calc
      (∫ t : BoundaryOutputInterval a c,
          g.test (x.1 - t.1) *
            ContinuousKernelHilbertSchmidt.coefficient
              (volume : Measure (BoundaryPositiveInputInterval a c))
              (positiveBoundaryRootKernel g a c)
              (ContinuousMap.toLp 2
                (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t) =
          ∫ t : BoundaryOutputInterval a c,
            ∫ y : BoundaryPositiveInputInterval a c,
              g.test (x.1 - t.1) *
                (u y * star (g.test (y.1 - t.1))) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hpositive, ← integral_const_mul]
      _ = ∫ y : BoundaryPositiveInputInterval a c,
            ∫ t : BoundaryOutputInterval a c,
              g.test (x.1 - t.1) *
                (u y * star (g.test (y.1 - t.1))) :=
        integral_integral_swap hinner
      _ = ∫ y : BoundaryPositiveInputInterval a c,
          u y * star (squareBoundaryKernel g a c (x, y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [squareBoundaryKernel_apply g a c hsupp x y,
          ContinuousMap.inner_toLp]
        change (∫ t : BoundaryOutputInterval a c,
            g.test (x.1 - t.1) *
              (u y * star (g.test (y.1 - t.1)))) =
          u y * conj (∫ t : BoundaryOutputInterval a c,
            g.test (y.1 - t.1) * star (g.test (x.1 - t.1)))
        rw [← integral_conj, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        simp only [RCLike.star_def, map_mul, RCLike.conj_conj]
        ring
  simp_rw [hsquare]
  calc
    (∫ t : BoundaryOutputInterval a c,
        ContinuousKernelHilbertSchmidt.coefficient
            (volume : Measure (BoundaryPositiveInputInterval a c))
            (positiveBoundaryRootKernel g a c)
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t *
          star (ContinuousKernelHilbertSchmidt.coefficient
            (volume : Measure (BoundaryNegativeInputInterval a c))
            (negativeBoundaryRootKernel g a c)
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v) t)) =
        ∫ t : BoundaryOutputInterval a c,
          ∫ x : BoundaryNegativeInputInterval a c,
            star (v x) * g.test (x.1 - t.1) *
              ContinuousKernelHilbertSchmidt.coefficient
                (volume : Measure (BoundaryPositiveInputInterval a c))
                (positiveBoundaryRootKernel g a c)
                (ContinuousMap.toLp 2
                  (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hnegative]
      change _ * conj (∫ x : BoundaryNegativeInputInterval a c,
        v x * star (g.test (x.1 - t.1))) = _
      rw [← integral_conj]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.star_def, map_mul, RCLike.conj_conj]
      ring
    _ = ∫ x : BoundaryNegativeInputInterval a c,
          ∫ t : BoundaryOutputInterval a c,
            star (v x) * g.test (x.1 - t.1) *
              ContinuousKernelHilbertSchmidt.coefficient
                (volume : Measure (BoundaryPositiveInputInterval a c))
                (positiveBoundaryRootKernel g a c)
                (ContinuousMap.toLp 2
                  (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t :=
      integral_integral_swap houter
    _ = ∫ x : BoundaryNegativeInputInterval a c,
          (∫ y : BoundaryPositiveInputInterval a c,
            u y * star (squareBoundaryKernel g a c (x, y))) * star (v x) := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        (∫ t : BoundaryOutputInterval a c,
            star (v x) * g.test (x.1 - t.1) *
              ContinuousKernelHilbertSchmidt.coefficient
                (volume : Measure (BoundaryPositiveInputInterval a c))
                (positiveBoundaryRootKernel g a c)
                (ContinuousMap.toLp 2
                  (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t) =
            star (v x) *
              (∫ t : BoundaryOutputInterval a c,
                g.test (x.1 - t.1) *
                  ContinuousKernelHilbertSchmidt.coefficient
                    (volume : Measure (BoundaryPositiveInputInterval a c))
                    (positiveBoundaryRootKernel g a c)
                    (ContinuousMap.toLp 2
                      (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) t) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          ring
        _ = star (v x) *
            (∫ y : BoundaryPositiveInputInterval a c,
              u y * star (squareBoundaryKernel g a c (x, y))) := by
          rw [hcolumn]
        _ = (∫ y : BoundaryPositiveInputInterval a c,
              u y * star (squareBoundaryKernel g a c (x, y))) * star (v x) :=
          mul_comm _ _

/-- The finite `A^dagger B` product of the two root legs is exactly the
continuous convolution-square kernel operator. -/
theorem finiteBoundaryRootOperator_adjoint_comp
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    (finiteNegativeBoundaryRootOperator g a c)† ∘L
        finitePositiveBoundaryRootOperator g a c =
      squareBoundaryKernelOperator g a c := by
  have hdenseNegative : DenseRange
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal))
      (μ := (volume : Measure (BoundaryNegativeInputInterval a c)))
      (by norm_num)
  have hdensePositive : DenseRange
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal))
      (μ := (volume : Measure (BoundaryPositiveInputInterval a c)))
      (by norm_num)
  have hcore (u : ContinuousMap (BoundaryPositiveInputInterval a c) ℂ) :
      ((finiteNegativeBoundaryRootOperator g a c)† ∘L
          finitePositiveBoundaryRootOperator g a c)
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) =
        squareBoundaryKernelOperator g a c
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u) := by
    apply ext_inner_left ℂ
    intro v
    let leftVector :=
      ((finiteNegativeBoundaryRootOperator g a c)† ∘L
        finitePositiveBoundaryRootOperator g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u)
    let rightVector := squareBoundaryKernelOperator g a c
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u)
    have hcontinuous :
        (fun w : Lp ℂ 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) =>
          inner ℂ w leftVector) ∘
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ) =
          (fun w : Lp ℂ 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) =>
          inner ℂ w rightVector) ∘
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ) := by
      funext v0
      change inner ℂ
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v0)
          (((finiteNegativeBoundaryRootOperator g a c)† ∘L
            finitePositiveBoundaryRootOperator g a c)
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u)) =
        inner ℂ
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ v0)
          (squareBoundaryKernelOperator g a c
            (ContinuousMap.toLp 2
              (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ u))
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
      exact finiteBoundaryRootOperators_inner_continuous
        g a c hsupp v0 u
    have hequal := DenseRange.equalizer hdenseNegative
      (by fun_prop) (by fun_prop) hcontinuous
    exact congrFun hequal v
  have hcontinuous :
      (((finiteNegativeBoundaryRootOperator g a c)† ∘L
          finitePositiveBoundaryRootOperator g a c) :
        Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →
          Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))) ∘
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ) =
        (squareBoundaryKernelOperator g a c :
          Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →
            Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))) ∘
          (ContinuousMap.toLp 2
            (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ) := by
    funext u
    exact hcore u
  have hequal := DenseRange.equalizer hdensePositive
    ((finiteNegativeBoundaryRootOperator g a c)† ∘L
      finitePositiveBoundaryRootOperator g a c).continuous
    (squareBoundaryKernelOperator g a c).continuous hcontinuous
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hequal u

theorem squareBoundaryCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ)
    (x : BoundaryNegativeInputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (squareBoundaryKernel g a c)
        (ContinuousMap.toLp 2
          (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
          (kernelRestriction u 0 (c - a) 0)) x =
      ∫ y in Set.Icc 0 (c - a),
        u y * star (g.convolutionSquare.test (y - x.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (squareBoundaryKernel g a c) x))
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) ℂ
        (kernelRestriction u 0 (c - a) 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ y : BoundaryPositiveInputInterval a c,
      u y.1 * star (g.convolutionSquare.test (y.1 - x.1))
        ∂Measure.comap Subtype.val volume) = _
  simpa only [sub_zero, add_zero] using
    (integral_subtype_comap (μ := (volume : Measure ℝ))
      (s := Set.Icc (0 - 0) (c - a + 0)) measurableSet_Icc
      (fun y : ℝ =>
        u y * star (g.convolutionSquare.test (y - x.1))))

theorem squareFullCoefficient_positiveProjection_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c : ℝ) (hac : a ≤ c)
    (x : BoundaryNegativeInputInterval a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure
          (CompactInputInterval (a - c) (c - a) (a - c) 0))
        (compactOutputRootKernel g.convolutionSquare
          (a - c) (c - a) (a - c) 0)
        (globalL2ToKernelInterval
          ((a - c) + (a - c)) (0 + (c - a)) 0
          (kernelIntervalProjection 0 (c - a) 0 (u.toLp 2))) x =
      ∫ y in Set.Icc 0 (c - a),
        u y * star (g.convolutionSquare.test (y - x.1)) := by
  change inner ℂ
      (_ : Lp ℂ 2 (volume : Measure
        (CompactInputInterval (a - c) (c - a) (a - c) 0)))
      (_ : Lp ℂ 2 (volume : Measure
        (CompactInputInterval (a - c) (c - a) (a - c) 0))) = _
  rw [MeasureTheory.L2.inner_def]
  let fullSet := Set.Icc
    ((a - c) + (a - c) - 0) (0 + (c - a) + 0)
  let positiveSet := Set.Icc (0 : ℝ) (c - a)
  let projected := kernelIntervalProjection 0 (c - a) 0 (u.toLp 2)
  have hrestricted := globalL2ToKernelInterval_coeFn
    ((a - c) + (a - c)) (0 + (c - a)) 0 projected
  have hprojected :=
    (measurePreserving_kernelIntervalSubtypeVal
      ((a - c) + (a - c)) (0 + (c - a)) 0)
      |>.quasiMeasurePreserving.ae_eq_comp
        (ae_restrict_of_ae (s := fullSet)
          (kernelIntervalProjection_coeFn 0 (c - a) 0 (u.toLp 2)))
  have hschwartz :=
    (measurePreserving_kernelIntervalSubtypeVal
      ((a - c) + (a - c)) (0 + (c - a)) 0)
      |>.quasiMeasurePreserving.ae_eq_comp
        (ae_restrict_of_ae (s := fullSet)
          (u.coeFn_toLp 2 (volume : Measure ℝ)))
  have hsection := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal))
    (volume : Measure
      (CompactInputInterval (a - c) (c - a) (a - c) 0)) (𝕜 := ℂ)
    (ContinuousKernelHilbertSchmidt.kernelSection
      (compactOutputRootKernel g.convolutionSquare
        (a - c) (c - a) (a - c) 0) x)
  calc
    (∫ y : CompactInputInterval (a - c) (c - a) (a - c) 0,
        inner ℂ
          ((ContinuousMap.toLp 2
            (volume : Measure
              (CompactInputInterval (a - c) (c - a) (a - c) 0)) ℂ)
            (ContinuousKernelHilbertSchmidt.kernelSection
              (compactOutputRootKernel g.convolutionSquare
                (a - c) (c - a) (a - c) 0) x) y)
          (globalL2ToKernelInterval
            ((a - c) + (a - c)) (0 + (c - a)) 0 projected y)) =
        ∫ y : CompactInputInterval (a - c) (c - a) (a - c) 0,
          positiveSet.indicator
            (fun z => u z *
              star (g.convolutionSquare.test (z - x.1))) y.1 := by
      apply integral_congr_ae
      filter_upwards [hrestricted, hprojected, hschwartz, hsection] with
        y hr hp hu hk
      rw [hr, hk]
      simp only [RCLike.inner_apply]
      change projected y.1 *
        star (g.convolutionSquare.test (y.1 - x.1)) = _
      have hp' : projected y.1 =
          positiveSet.indicator (fun z => (u.toLp 2 : ℝ → ℂ) z) y.1 := by
        simpa only [Function.comp_apply, positiveSet, projected,
          sub_zero, add_zero] using hp
      have hu' : (u.toLp 2 : ℝ → ℂ) y.1 = u y.1 := by
        simpa only [Function.comp_apply] using hu
      rw [hp']
      by_cases hy : y.1 ∈ positiveSet
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hu']
      · simp only [Set.indicator_of_notMem hy, zero_mul]
    _ = ∫ y in fullSet,
        positiveSet.indicator
          (fun z => u z * star (g.convolutionSquare.test (z - x.1))) y := by
      exact integral_subtype_comap (μ := (volume : Measure ℝ))
        (s := fullSet) measurableSet_Icc _
    _ = ∫ y in positiveSet,
        u y * star (g.convolutionSquare.test (y - x.1)) := by
      rw [← integral_indicator measurableSet_Icc]
      rw [Set.indicator_indicator]
      have hsubset : positiveSet ⊆ fullSet := by
        intro y hy
        constructor
        · linarith [hy.1, hac]
        · simpa only [zero_add, add_zero] using hy.2
      rw [Set.inter_eq_right.mpr hsubset]
      rw [integral_indicator measurableSet_Icc]

theorem squareFullFactor_comp_positiveProjection_eq_kernelOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hac : a ≤ c) :
    compactOutputRootFactor g.convolutionSquare
        (a - c) (c - a) (a - c) 0 ∘L
          kernelIntervalProjection 0 (c - a) 0 =
      squareBoundaryKernelOperator g a c ∘L
        globalL2ToKernelInterval 0 (c - a) 0 := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (compactOutputRootFactor g.convolutionSquare
          (a - c) (c - a) (a - c) 0 ∘L
            kernelIntervalProjection 0 (c - a) 0 :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
      (squareBoundaryKernelOperator g a c ∘L
          globalL2ToKernelInterval 0 (c - a) 0 :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    unfold compactOutputRootFactor squareBoundaryKernelOperator
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousKernelHilbertSchmidt.operator_apply,
      ContinuousKernelHilbertSchmidt.operator_apply]
    apply congrArg
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryNegativeInputInterval a c)) ℂ)
    ext x
    rw [squareFullCoefficient_positiveProjection_eq_setIntegral
      g u a c hac x]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [squareBoundaryCoefficient_kernelRestriction_eq_setIntegral]
  have hfun := DenseRange.equalizer hdense
    (compactOutputRootFactor g.convolutionSquare
      (a - c) (c - a) (a - c) 0 ∘L
        kernelIntervalProjection 0 (c - a) 0).continuous
    (squareBoundaryKernelOperator g a c ∘L
      globalL2ToKernelInterval 0 (c - a) 0).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The actual convolution-square crossing before compact carrier
factorization. -/
noncomputable def globalSquareHalfLineCrossing
    (g : CompactLogConvolution.CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20NegativeHalfLineProjection ∘L
    cc20GlobalLogConvolution g.convolutionSquare.test ∘L
      cc20PositiveHalfLineProjection

/-- The finite carrier of the actual square crossing. -/
noncomputable def finiteSquareHalfLineCrossing
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) :=
  globalL2ToKernelInterval (a - c) 0 0 ∘L
    cc20GlobalLogConvolution g.convolutionSquare.test ∘L
      positiveBoundaryZeroExtension a c

/-- The finite carrier extracted from the genuine global detector is the
continuous convolution-square kernel operator. -/
theorem finiteSquareHalfLineCrossing_eq_kernelOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    finiteSquareHalfLineCrossing g a c =
      squareBoundaryKernelOperator g a c := by
  have hfactor := convolutionSquare_compactOutputRootFactor_eq
    g a c (a - c) 0 hsupp
  have hglobal := squareFullFactor_comp_positiveProjection_eq_kernelOperator
    g a c hac
  apply ContinuousLinearMap.ext
  intro u
  let z := positiveBoundaryZeroExtension a c u
  have hprojection : kernelIntervalProjection 0 (c - a) 0 z = z := by
    exact kernelIntervalProjection_zeroExtension 0 (c - a) 0 u
  have hrestriction : globalL2ToKernelInterval 0 (c - a) 0 z = u := by
    exact globalL2ToKernelInterval_zeroExtension 0 (c - a) 0 u
  have hglobalAt := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) => T z)
    hglobal
  simp only [ContinuousLinearMap.comp_apply] at hglobalAt
  rw [hprojection, hrestriction] at hglobalAt
  rw [finiteSquareHalfLineCrossing]
  have hfactorAt := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) => T z)
    hfactor
  simp only [ContinuousLinearMap.comp_apply] at hfactorAt
  simp only [ContinuousLinearMap.comp_apply]
  rw [← hfactorAt]
  exact hglobalAt

/-- Zero-extend the finite square crossing back to the global carrier. -/
noncomputable def finiteSquareHalfLineCrossingExtension
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  negativeBoundaryZeroExtension a c ∘L
    finiteSquareHalfLineCrossing g a c ∘L
      globalL2ToKernelInterval 0 (c - a) 0

theorem negativeBoundaryWindowProjection_eq
    (a c : ℝ) :
    negativeBoundaryZeroExtension a c ∘L
        globalL2ToKernelInterval (a - c) 0 0 =
      kernelIntervalProjection (a - c) 0 0 := by
  unfold negativeBoundaryZeroExtension kernelIntervalProjection
  have hadj :
      (kernelIntervalL2ZeroExtension (a - c) 0 0).adjoint =
        globalL2ToKernelInterval (a - c) 0 0 := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [hadj]

theorem positiveBoundaryWindowProjection_eq
    (a c : ℝ) :
    positiveBoundaryZeroExtension a c ∘L
        globalL2ToKernelInterval 0 (c - a) 0 =
      kernelIntervalProjection 0 (c - a) 0 := by
  unfold positiveBoundaryZeroExtension kernelIntervalProjection
  have hadj :
      (kernelIntervalL2ZeroExtension 0 (c - a) 0).adjoint =
        globalL2ToKernelInterval 0 (c - a) 0 := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [hadj]

/-- The genuine global square crossing is exactly the zero extension of its
finite positive-to-negative carrier. -/
theorem globalSquareHalfLineCrossing_eq_finiteExtension
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    globalSquareHalfLineCrossing g =
      finiteSquareHalfLineCrossingExtension g a c := by
  have hleft := negativeCompactProjection_fixes_squareCrossing
    g a c hsupp
  have hright := squareCrossing_comp_positiveCompactProjection
    g a c hsupp
  have hleft' :
      kernelIntervalProjection (a - c) 0 0 ∘L
          globalSquareHalfLineCrossing g =
        globalSquareHalfLineCrossing g := by
    simpa only [globalSquareHalfLineCrossing] using hleft
  have hright' :
      globalSquareHalfLineCrossing g ∘L
          kernelIntervalProjection 0 (c - a) 0 =
        globalSquareHalfLineCrossing g := by
    simpa only [globalSquareHalfLineCrossing] using hright
  have hcompact :
      (kernelIntervalProjection (a - c) 0 0 ∘L
        globalSquareHalfLineCrossing g) ∘L
          kernelIntervalProjection 0 (c - a) 0 =
        globalSquareHalfLineCrossing g := by
    rw [hleft']
    exact hright'
  rw [← hcompact]
  rw [finiteSquareHalfLineCrossingExtension,
    finiteSquareHalfLineCrossing, globalSquareHalfLineCrossing]
  rw [← negativeBoundaryWindowProjection_eq a c]
  rw [← positiveBoundaryWindowProjection_eq a c]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  let z := positiveBoundaryZeroExtension a c
    (globalL2ToKernelInterval 0 (c - a) 0 u)
  have hz : cc20PositiveHalfLineProjection z = z := by
    have h := congrArg
      (fun T : Lp ℂ 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
          cc20GlobalLogCrossingL2 =>
        T (globalL2ToKernelInterval 0 (c - a) 0 u))
      (positiveHalfLineProjection_comp_positiveBoundaryZeroExtension a c)
    simpa only [ContinuousLinearMap.comp_apply, z] using h
  let w := cc20GlobalLogConvolution g.convolutionSquare.test z
  have hr : globalL2ToKernelInterval (a - c) 0 0
      (cc20NegativeHalfLineProjection w) =
        globalL2ToKernelInterval (a - c) 0 0 w := by
    unfold cc20NegativeHalfLineProjection
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub]
    have hzero := congrArg
      (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
        Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) =>
          T w)
      (negativeBoundaryRestriction_comp_positiveHalfLineProjection a c)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hzero
    rw [hzero, sub_zero]
  rw [hz, hr]

/-- The square-kernel crossing is the route's actual oriented crossing for
the positive convolution detector. -/
theorem globalSquareHalfLineCrossing_eq_orientedBoundaryCrossing
    (g : CompactLogConvolution.CompactLogTest) :
    globalSquareHalfLineCrossing g =
      cc20OrientedBoundaryCrossing cc20PositiveHalfLineProjection
        (cc20GlobalConvolutionPositive g.involution.test) := by
  rw [globalConvolutionPositive_eq_convolutionSquare]
  unfold globalSquareHalfLineCrossing cc20OrientedBoundaryCrossing
  unfold cc20NegativeHalfLineProjection
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The route's genuine oriented boundary crossing is exactly the zero
extension of the finite convolution-square carrier. -/
theorem orientedBoundaryCrossing_eq_finiteSquareExtension
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    cc20OrientedBoundaryCrossing cc20PositiveHalfLineProjection
        (cc20GlobalConvolutionPositive g.involution.test) =
      finiteSquareHalfLineCrossingExtension g a c := by
  rw [← globalSquareHalfLineCrossing_eq_orientedBoundaryCrossing]
  exact globalSquareHalfLineCrossing_eq_finiteExtension g a c hsupp

/-- The compact Hilbert--Schmidt pair product is the zero extension of the
finite convolution-square kernel. -/
theorem pairData_traceProduct_eq_finiteSquareExtension
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
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
      finiteSquareHalfLineCrossingExtension g a c := by
  rw [pairData_traceProduct_eq]
  unfold negativeBoundaryRootFactor positiveBoundaryRootFactor
  change
    (finiteNegativeBoundaryRootOperator g a c ∘L
        globalL2ToKernelInterval (a - c) 0 0)† ∘L
      (finitePositiveBoundaryRootOperator g a c ∘L
        globalL2ToKernelInterval 0 (c - a) 0) = _
  rw [ContinuousLinearMap.adjoint_comp]
  have hnegativeAdjoint :
      (globalL2ToKernelInterval (a - c) 0 0)† =
        negativeBoundaryZeroExtension a c := by
    exact (kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval
      (a - c) 0 0).symm
  rw [hnegativeAdjoint]
  have hfinite := finiteBoundaryRootOperator_adjoint_comp
    g a c hsupp
  have hsquare := finiteSquareHalfLineCrossing_eq_kernelOperator
    g a c hac hsupp
  rw [finiteSquareHalfLineCrossingExtension]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsquare]
  apply congrArg (negativeBoundaryZeroExtension a c)
  have hfiniteAt := congrArg
    (fun T : Lp ℂ 2
        (volume : Measure (BoundaryPositiveInputInterval a c)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)) =>
      T (globalL2ToKernelInterval 0 (c - a) 0 u)) hfinite
  simpa only [ContinuousLinearMap.comp_apply] using hfiniteAt

/-- The compact pair product is the route's genuine oriented half-line
crossing of the actual positive convolution detector. -/
theorem pairData_traceProduct_eq_genuineOrientedBoundaryCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
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
        (cc20GlobalConvolutionPositive g.involution.test) := by
  rw [pairData_traceProduct_eq_finiteSquareExtension
    g a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis]
  exact (orientedBoundaryCrossing_eq_finiteSquareExtension
    g a c hsupp).symm

/-- The signed compact pair is the genuine commutator of the actual positive
convolution detector with the half-line projection. -/
theorem signedBoundaryOperator_eq_genuineCommutator
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
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
        (cc20GlobalConvolutionPositive g.involution.test) := by
  rw [signedBoundaryOperator_eq_adjoint_sub]
  rw [pairData_traceProduct_eq_genuineOrientedBoundaryCrossing
    g a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis]
  have hdetector : IsSelfAdjoint
      (cc20GlobalConvolutionPositive g.involution.test) := by
    exact (ContinuousLinearMap.isPositive_adjoint_comp_self
      (cc20GlobalLogConvolution g.involution.test)).isSelfAdjoint
  exact (cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    cc20PositiveHalfLineProjection
    (cc20GlobalConvolutionPositive g.involution.test)
    cc20PositiveHalfLineProjection_isSelfAdjoint hdetector).symm


end CompactConvolutionSupport
end CC20Concrete
end Source
end ConnesWeilRH
