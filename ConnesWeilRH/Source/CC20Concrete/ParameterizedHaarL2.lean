/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarMeasure
import ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarL2

/-!
# Parameterized CC20 regular-kernel operators on the source Haar spaces

For every `lambda > 1`, this module places the same ordinary CC20 regular
kernel on `L2([1/lambda,lambda], d rho/rho)`.  The diagonal Dirac distribution
is not included.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

noncomputable def cc20WindowPositiveCoordinate
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) : PositiveCoordinate :=
  ⟨rho.1, lt_of_lt_of_le
    (one_div_pos.mpr (lt_trans (by norm_num) hlambda)) rho.2.1⟩

theorem continuous_cc20WindowPositiveCoordinate
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Continuous (cc20WindowPositiveCoordinate lambda hlambda) :=
  continuous_subtype_val.subtype_mk _

noncomputable def cc20WindowComplexRegularKernel
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ContinuousMap (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ where
  toFun p := (cc20RegularKernel
    (cc20WindowPositiveCoordinate lambda hlambda p.1,
      cc20WindowPositiveCoordinate lambda hlambda p.2) : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (continuous_cc20RegularKernel.comp
        (((continuous_cc20WindowPositiveCoordinate lambda hlambda).comp
          continuous_fst).prodMk
        ((continuous_cc20WindowPositiveCoordinate lambda hlambda).comp
          continuous_snd)))

noncomputable def cc20WindowComplexKernelSection
    (lambda : ℝ) (hlambda : 1 < lambda)
    (x : CC20WindowPoint lambda) :
    ContinuousMap (CC20WindowPoint lambda) ℂ :=
  (cc20WindowComplexRegularKernel lambda hlambda).curry x

noncomputable def cc20WindowHaarComplexKernelSectionToLp
    (lambda : ℝ) (hlambda : 1 < lambda)
    (x : CC20WindowPoint lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
  ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
    (cc20WindowComplexKernelSection lambda hlambda x)

theorem continuous_cc20WindowHaarComplexKernelSectionToLp
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Continuous (cc20WindowHaarComplexKernelSectionToLp lambda hlambda) := by
  exact
    (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ).continuous.comp
      (cc20WindowComplexRegularKernel lambda hlambda).curry.continuous

theorem cc20WindowHaarComplex_l2Factor_eq_lpNorm
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20WindowHaarMeasure lambda hlambda) ^
        (1 / (2 : ℝ)) =
      lpNorm f 2 (cc20WindowHaarMeasure lambda hlambda) := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := fun y => f y)
    (μ := cc20WindowHaarMeasure lambda hlambda)
    (p := (2 : ENNReal)) (by norm_num) (by norm_num)
    f.continuous.aestronglyMeasurable
  norm_num at h ⊢
  exact h.symm

theorem norm_cc20WindowHaarComplex_toLp_eq_lpNorm
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ f‖ =
      lpNorm f 2 (cc20WindowHaarMeasure lambda hlambda) := by
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae
    (ContinuousMap.coeFn_toLp
      (μ := cc20WindowHaarMeasure lambda hlambda) (𝕜 := ℂ) f)]
  exact toReal_eLpNorm f.continuous.aestronglyMeasurable

noncomputable def cc20WindowHaarComplexKernelCoefficient
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    ContinuousMap (CC20WindowPoint lambda) ℂ where
  toFun x := inner ℂ
    (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x) u
  continuous_toFun :=
    (continuous_cc20WindowHaarComplexKernelSectionToLp lambda hlambda).inner
      continuous_const

theorem cc20WindowHaarComplexKernelCoefficient_add
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u v : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    cc20WindowHaarComplexKernelCoefficient lambda hlambda (u + v) =
      cc20WindowHaarComplexKernelCoefficient lambda hlambda u +
        cc20WindowHaarComplexKernelCoefficient lambda hlambda v := by
  ext x
  simp [cc20WindowHaarComplexKernelCoefficient, inner_add_right]

theorem cc20WindowHaarComplexKernelCoefficient_smul
    (lambda : ℝ) (hlambda : 1 < lambda)
    (c : ℂ) (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    cc20WindowHaarComplexKernelCoefficient lambda hlambda (c • u) =
      c • cc20WindowHaarComplexKernelCoefficient lambda hlambda u := by
  ext x
  simp [cc20WindowHaarComplexKernelCoefficient, inner_smul_right]

noncomputable def cc20WindowHaarComplexKernelCoefficientLinearMap
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) →ₗ[ℂ]
      ContinuousMap (CC20WindowPoint lambda) ℂ where
  toFun := cc20WindowHaarComplexKernelCoefficient lambda hlambda
  map_add' := cc20WindowHaarComplexKernelCoefficient_add lambda hlambda
  map_smul' := cc20WindowHaarComplexKernelCoefficient_smul lambda hlambda

theorem norm_cc20WindowHaarComplexKernelSectionToLp_le
    (lambda : ℝ) (hlambda : 1 < lambda)
    (x : CC20WindowPoint lambda) :
    ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ ≤
      lpNorm (fun _ : CC20WindowPoint lambda =>
        ‖cc20WindowComplexRegularKernel lambda hlambda‖)
        2 (cc20WindowHaarMeasure lambda hlambda) := by
  rw [cc20WindowHaarComplexKernelSectionToLp]
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae
    (ContinuousMap.coeFn_toLp
      (μ := cc20WindowHaarMeasure lambda hlambda)
      (𝕜 := ℂ) (cc20WindowComplexKernelSection lambda hlambda x))]
  rw [toReal_eLpNorm
    (cc20WindowComplexKernelSection
      lambda hlambda x).continuous.aestronglyMeasurable]
  apply lpNorm_mono_real (p := (2 : ENNReal))
    (memLp_const ‖cc20WindowComplexRegularKernel lambda hlambda‖)
  intro y
  exact (cc20WindowComplexRegularKernel
    lambda hlambda).norm_coe_le_norm (x, y)

theorem norm_cc20WindowHaarComplexKernelCoefficient_le
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    ‖cc20WindowHaarComplexKernelCoefficient lambda hlambda u‖ ≤
      lpNorm (fun _ : CC20WindowPoint lambda =>
        ‖cc20WindowComplexRegularKernel lambda hlambda‖)
          2 (cc20WindowHaarMeasure lambda hlambda) * ‖u‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg lpNorm_nonneg (norm_nonneg _))).2
  intro x
  calc
    ‖cc20WindowHaarComplexKernelCoefficient lambda hlambda u x‖ =
        ‖inner ℂ
          (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x) u‖ := rfl
    _ ≤ ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ lpNorm (fun _ : CC20WindowPoint lambda =>
          ‖cc20WindowComplexRegularKernel lambda hlambda‖)
          2 (cc20WindowHaarMeasure lambda hlambda) * ‖u‖ := by
      gcongr
      exact norm_cc20WindowHaarComplexKernelSectionToLp_le lambda hlambda x

noncomputable def cc20WindowHaarComplexKernelCoefficientContinuousLinearMap
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) →L[ℂ]
      ContinuousMap (CC20WindowPoint lambda) ℂ :=
  LinearMap.mkContinuous
    (cc20WindowHaarComplexKernelCoefficientLinearMap lambda hlambda)
    (lpNorm (fun _ : CC20WindowPoint lambda =>
      ‖cc20WindowComplexRegularKernel lambda hlambda‖)
      2 (cc20WindowHaarMeasure lambda hlambda))
    (norm_cc20WindowHaarComplexKernelCoefficient_le lambda hlambda)

noncomputable def cc20WindowHaarComplexL2Operator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) →L[ℂ]
      Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
  (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ).comp
    (cc20WindowHaarComplexKernelCoefficientContinuousLinearMap lambda hlambda)

theorem cc20WindowHaarComplexL2Operator_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    cc20WindowHaarComplexL2Operator lambda hlambda u =
      ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowHaarComplexKernelCoefficient lambda hlambda u) := rfl

noncomputable def cc20WindowSourceHaarAction
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (x : CC20WindowPoint lambda) : ℂ :=
  ∫ y, cc20WindowComplexRegularKernel lambda hlambda (x, y) * f y
    ∂cc20WindowHaarMeasure lambda hlambda

theorem cc20WindowHaarComplexKernelCoefficient_continuous_input
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (x : CC20WindowPoint lambda) :
    cc20WindowHaarComplexKernelCoefficient lambda hlambda
        (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ f) x =
      cc20WindowSourceHaarAction lambda hlambda f x := by
  change inner ℂ
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowComplexKernelSection lambda hlambda x))
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ f) = _
  rw [ContinuousMap.inner_toLp]
  simp [cc20WindowSourceHaarAction, cc20WindowComplexKernelSection,
    cc20WindowComplexRegularKernel, mul_comm]

theorem norm_cc20WindowHaarComplex_toLp_continuous_sq
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    ‖ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂cc20WindowHaarMeasure lambda hlambda := by
  rw [norm_cc20WindowHaarComplex_toLp_eq_lpNorm,
    ← cc20WindowHaarComplex_l2Factor_eq_lpNorm]
  simp_rw [Real.rpow_two]
  have hnonneg :
      0 ≤ ∫ x, ‖f x‖ ^ 2 ∂cc20WindowHaarMeasure lambda hlambda :=
    integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow]
  simpa only [] using Real.sq_sqrt hnonneg

theorem integrable_cc20WindowHaarComplexKernelSectionToLp_norm_sq
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Integrable (fun x : CC20WindowPoint lambda =>
      ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ ^ 2)
        (cc20WindowHaarMeasure lambda hlambda) := by
  have hc : Continuous (fun x : CC20WindowPoint lambda =>
      ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ ^ 2) :=
    (continuous_cc20WindowHaarComplexKernelSectionToLp lambda hlambda).norm.pow 2
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := cc20WindowHaarMeasure lambda hlambda) isCompact_univ).integrable

theorem cc20WindowHaarComplexL2Operator_finite_basis_sum_le_kernel_energy
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)))
    (s : Finset ι) :
    ∑ i ∈ s,
        ‖cc20WindowHaarComplexL2Operator lambda hlambda (basis i)‖ ^ 2 ≤
      ∫ x,
        ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ ^ 2
          ∂cc20WindowHaarMeasure lambda hlambda := by
  have hcoeff (i : ι) :
      ‖cc20WindowHaarComplexL2Operator lambda hlambda (basis i)‖ ^ 2 =
        ∫ x,
          ‖cc20WindowHaarComplexKernelCoefficient
            lambda hlambda (basis i) x‖ ^ 2
            ∂cc20WindowHaarMeasure lambda hlambda := by
    rw [cc20WindowHaarComplexL2Operator_apply,
      norm_cc20WindowHaarComplex_toLp_continuous_sq]
  have hint (i : ι) : Integrable
      (fun x => ‖cc20WindowHaarComplexKernelCoefficient
        lambda hlambda (basis i) x‖ ^ 2)
      (cc20WindowHaarMeasure lambda hlambda) := by
    have hc : Continuous
        (fun x => ‖cc20WindowHaarComplexKernelCoefficient
          lambda hlambda (basis i) x‖ ^ 2) :=
      (cc20WindowHaarComplexKernelCoefficient
        lambda hlambda (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := cc20WindowHaarMeasure lambda hlambda) isCompact_univ).integrable
  simp_rw [hcoeff]
  have hsum : ∫ x, ∑ i ∈ s,
      ‖cc20WindowHaarComplexKernelCoefficient
        lambda hlambda (basis i) x‖ ^ 2
        ∂cc20WindowHaarMeasure lambda hlambda =
      ∑ i ∈ s, ∫ x,
        ‖cc20WindowHaarComplexKernelCoefficient
          lambda hlambda (basis i) x‖ ^ 2
          ∂cc20WindowHaarMeasure lambda hlambda :=
    integral_finsetSum s (fun i _hi => hint i)
  rw [← hsum]
  apply integral_mono_ae
  · exact integrable_finsetSum s (fun i _hi => hint i)
  · exact integrable_cc20WindowHaarComplexKernelSectionToLp_norm_sq
      lambda hlambda
  · filter_upwards with x
    simpa only [cc20WindowHaarComplexKernelCoefficient, norm_inner_symm] using
      basis.orthonormal.sum_inner_products_le
        (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x)

theorem cc20WindowHaarComplexL2Operator_basis_normSq_summable
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))) :
    Summable (fun i =>
      ‖cc20WindowHaarComplexL2Operator lambda hlambda (basis i)‖ ^ 2) := by
  refine summable_of_sum_le
    (c := ∫ x,
      ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x‖ ^ 2
        ∂cc20WindowHaarMeasure lambda hlambda)
    (fun i => sq_nonneg _) ?_
  intro s
  exact cc20WindowHaarComplexL2Operator_finite_basis_sum_le_kernel_energy
    lambda hlambda basis s

noncomputable def cc20WindowHaarComplexBasisHilbertSchmidtData
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))) :
    PositiveTrace.BasisHilbertSchmidtData basis where
  operator := cc20WindowHaarComplexL2Operator lambda hlambda
  summable_normSq :=
    cc20WindowHaarComplexL2Operator_basis_normSq_summable
      lambda hlambda basis

theorem cc20WindowHaarComplexPositiveTrace_re_nonnegative
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))) :
    0 ≤ (PositiveTrace.ordinaryTraceAlong basis
      (cc20WindowHaarComplexBasisHilbertSchmidtData
        lambda hlambda basis).positiveComposition).re :=
  PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
    (cc20WindowHaarComplexBasisHilbertSchmidtData lambda hlambda basis)

end CC20Concrete
end Source
end ConnesWeilRH
