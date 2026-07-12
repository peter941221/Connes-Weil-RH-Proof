/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CC20Concrete.RegularKernelHilbertSchmidt

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- The ordinary real regular kernel, regarded as a complex-valued kernel. -/
noncomputable def cc20CompactComplexRegularKernel :
    ContinuousMap (CC20CompactInterval × CC20CompactInterval) ℂ where
  toFun p := (cc20CompactRegularKernel p : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp cc20CompactRegularKernel.continuous

noncomputable def cc20CompactComplexKernelSection
    (x : CC20CompactInterval) : ContinuousMap CC20CompactInterval ℂ :=
  cc20CompactComplexRegularKernel.curry x

noncomputable def cc20CompactComplexKernelSectionToLp
    (x : CC20CompactInterval) : Lp ℂ 2 cc20CompactMeasure :=
  ContinuousMap.toLp 2 cc20CompactMeasure ℂ
    (cc20CompactComplexKernelSection x)

theorem continuous_cc20CompactComplexKernelSectionToLp :
    Continuous cc20CompactComplexKernelSectionToLp := by
  exact (ContinuousMap.toLp 2 cc20CompactMeasure ℂ).continuous.comp
    cc20CompactComplexRegularKernel.curry.continuous

theorem cc20CompactComplex_l2Factor_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℂ) :
    (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) =
      lpNorm f 2 cc20CompactMeasure := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := fun y => f y) (μ := cc20CompactMeasure) (p := (2 : ENNReal))
    (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable
  norm_num at h ⊢
  exact h.symm

theorem norm_cc20CompactComplex_toLp_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℂ) :
    ‖ContinuousMap.toLp 2 cc20CompactMeasure ℂ f‖ =
      lpNorm f 2 cc20CompactMeasure := by
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae
    (ContinuousMap.coeFn_toLp (μ := cc20CompactMeasure) (𝕜 := ℂ) f)]
  exact toReal_eLpNorm f.continuous.aestronglyMeasurable

theorem norm_cc20CompactComplexKernelSectionToLp_le
    (x : CC20CompactInterval) :
    ‖cc20CompactComplexKernelSectionToLp x‖ ≤
      lpNorm (fun _ : CC20CompactInterval =>
        ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactMeasure := by
  rw [cc20CompactComplexKernelSectionToLp,
    norm_cc20CompactComplex_toLp_eq_lpNorm]
  apply lpNorm_mono_real (p := (2 : ENNReal))
    (memLp_const ‖cc20CompactComplexRegularKernel‖)
  intro y
  exact cc20CompactComplexRegularKernel.norm_coe_le_norm (x, y)

/-- The complex-linear kernel action. The kernel section is the first inner
product argument because Mathlib's complex inner product is linear in its
second argument. -/
noncomputable def cc20CompactComplexKernelCoefficient
    (u : Lp ℂ 2 cc20CompactMeasure) :
    ContinuousMap CC20CompactInterval ℂ where
  toFun x := inner ℂ (cc20CompactComplexKernelSectionToLp x) u
  continuous_toFun := by
    exact continuous_cc20CompactComplexKernelSectionToLp.inner continuous_const

theorem cc20CompactComplexKernelCoefficient_add
    (u v : Lp ℂ 2 cc20CompactMeasure) :
    cc20CompactComplexKernelCoefficient (u + v) =
      cc20CompactComplexKernelCoefficient u +
        cc20CompactComplexKernelCoefficient v := by
  ext x
  simp [cc20CompactComplexKernelCoefficient, inner_add_right]

theorem cc20CompactComplexKernelCoefficient_smul
    (c : ℂ) (u : Lp ℂ 2 cc20CompactMeasure) :
    cc20CompactComplexKernelCoefficient (c • u) =
      c • cc20CompactComplexKernelCoefficient u := by
  ext x
  simp [cc20CompactComplexKernelCoefficient, inner_smul_right]

noncomputable def cc20CompactComplexKernelCoefficientLinearMap :
    Lp ℂ 2 cc20CompactMeasure →ₗ[ℂ]
      ContinuousMap CC20CompactInterval ℂ where
  toFun := cc20CompactComplexKernelCoefficient
  map_add' := cc20CompactComplexKernelCoefficient_add
  map_smul' := cc20CompactComplexKernelCoefficient_smul

theorem norm_cc20CompactComplexKernelCoefficient_le
    (u : Lp ℂ 2 cc20CompactMeasure) :
    ‖cc20CompactComplexKernelCoefficient u‖ ≤
      lpNorm (fun _ : CC20CompactInterval =>
          ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactMeasure * ‖u‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg lpNorm_nonneg (norm_nonneg _))).2
  intro x
  calc
    ‖cc20CompactComplexKernelCoefficient u x‖ =
        ‖inner ℂ (cc20CompactComplexKernelSectionToLp x) u‖ := rfl
    _ ≤ ‖cc20CompactComplexKernelSectionToLp x‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ lpNorm (fun _ : CC20CompactInterval =>
          ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactMeasure * ‖u‖ := by
      gcongr
      exact norm_cc20CompactComplexKernelSectionToLp_le x

noncomputable def cc20CompactComplexKernelCoefficientContinuousLinearMap :
    Lp ℂ 2 cc20CompactMeasure →L[ℂ]
      ContinuousMap CC20CompactInterval ℂ :=
  LinearMap.mkContinuous cc20CompactComplexKernelCoefficientLinearMap
    (lpNorm (fun _ : CC20CompactInterval =>
      ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactMeasure)
    norm_cc20CompactComplexKernelCoefficient_le

/-- The genuine complex-linear `L²` operator defined by the same ordinary
regular kernel as the real operator. -/
noncomputable def cc20CompactComplexL2Operator :
    Lp ℂ 2 cc20CompactMeasure →L[ℂ] Lp ℂ 2 cc20CompactMeasure :=
  (ContinuousMap.toLp 2 cc20CompactMeasure ℂ).comp
    cc20CompactComplexKernelCoefficientContinuousLinearMap

theorem norm_toLp_complex_continuous_sq
    (f : ContinuousMap CC20CompactInterval ℂ) :
    ‖ContinuousMap.toLp 2 cc20CompactMeasure ℂ f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂cc20CompactMeasure := by
  rw [norm_cc20CompactComplex_toLp_eq_lpNorm,
    ← cc20CompactComplex_l2Factor_eq_lpNorm]
  simp_rw [Real.rpow_two]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂cc20CompactMeasure := by
    exact integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow]
  simpa only [] using Real.sq_sqrt hnonneg

theorem cc20CompactComplexL2Operator_apply
    (u : Lp ℂ 2 cc20CompactMeasure) :
    cc20CompactComplexL2Operator u =
      ContinuousMap.toLp 2 cc20CompactMeasure ℂ
        (cc20CompactComplexKernelCoefficient u) := rfl

theorem cc20CompactComplexKernelCoefficient_continuous_input
    (f : ContinuousMap CC20CompactInterval ℂ)
    (x : CC20CompactInterval) :
    cc20CompactComplexKernelCoefficient
        (ContinuousMap.toLp 2 cc20CompactMeasure ℂ f) x =
      ∫ y, (cc20CompactRegularKernel (x, y) : ℂ) * f y
        ∂cc20CompactMeasure := by
  change inner ℂ
      (ContinuousMap.toLp 2 cc20CompactMeasure ℂ
        (cc20CompactComplexKernelSection x))
      (ContinuousMap.toLp 2 cc20CompactMeasure ℂ f) = _
  rw [ContinuousMap.inner_toLp]
  simp [cc20CompactComplexKernelSection,
    cc20CompactComplexRegularKernel, mul_comm]

theorem integrable_cc20CompactComplexKernelSectionToLp_norm_sq :
    Integrable (fun x : CC20CompactInterval =>
      ‖cc20CompactComplexKernelSectionToLp x‖ ^ 2) cc20CompactMeasure := by
  have hc : Continuous (fun x : CC20CompactInterval =>
      ‖cc20CompactComplexKernelSectionToLp x‖ ^ 2) :=
    continuous_cc20CompactComplexKernelSectionToLp.norm.pow 2
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := cc20CompactMeasure) isCompact_univ).integrable

theorem cc20CompactComplexL2Operator_finite_basis_sum_le_kernel_energy
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 cc20CompactMeasure))
    (s : Finset ι) :
    ∑ i ∈ s, ‖cc20CompactComplexL2Operator (basis i)‖ ^ 2 ≤
      ∫ x, ‖cc20CompactComplexKernelSectionToLp x‖ ^ 2
        ∂cc20CompactMeasure := by
  have hcoeff (i : ι) :
      ‖cc20CompactComplexL2Operator (basis i)‖ ^ 2 =
        ∫ x, ‖cc20CompactComplexKernelCoefficient (basis i) x‖ ^ 2
          ∂cc20CompactMeasure := by
    rw [cc20CompactComplexL2Operator_apply,
      norm_toLp_complex_continuous_sq]
  have hint (i : ι) : Integrable
      (fun x => ‖cc20CompactComplexKernelCoefficient (basis i) x‖ ^ 2)
        cc20CompactMeasure := by
    have hc : Continuous
        (fun x => ‖cc20CompactComplexKernelCoefficient (basis i) x‖ ^ 2) :=
      (cc20CompactComplexKernelCoefficient (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := cc20CompactMeasure) isCompact_univ).integrable
  simp_rw [hcoeff]
  have hsum : ∫ x, ∑ i ∈ s,
      ‖cc20CompactComplexKernelCoefficient (basis i) x‖ ^ 2
        ∂cc20CompactMeasure =
      ∑ i ∈ s, ∫ x,
        ‖cc20CompactComplexKernelCoefficient (basis i) x‖ ^ 2
          ∂cc20CompactMeasure :=
    integral_finsetSum s (fun i hi => hint i)
  rw [← hsum]
  apply integral_mono_ae
  · exact integrable_finsetSum s (fun i hi => hint i)
  · exact integrable_cc20CompactComplexKernelSectionToLp_norm_sq
  · filter_upwards with x
    simpa only [cc20CompactComplexKernelCoefficient, norm_inner_symm] using
      basis.orthonormal.sum_inner_products_le
        (cc20CompactComplexKernelSectionToLp x)

theorem cc20CompactComplexL2Operator_basis_normSq_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 cc20CompactMeasure)) :
    Summable (fun i => ‖cc20CompactComplexL2Operator (basis i)‖ ^ 2) := by
  refine summable_of_sum_le
    (c := ∫ x, ‖cc20CompactComplexKernelSectionToLp x‖ ^ 2
      ∂cc20CompactMeasure) (fun i => sq_nonneg _) ?_
  intro s
  exact cc20CompactComplexL2Operator_finite_basis_sum_le_kernel_energy basis s

/-- The complex same-kernel operator packaged for the project's ordinary
positive-trace consumer. -/
noncomputable def cc20CompactComplexBasisHilbertSchmidtData
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 cc20CompactMeasure)) :
    PositiveTrace.BasisHilbertSchmidtData basis where
  operator := cc20CompactComplexL2Operator
  summable_normSq := cc20CompactComplexL2Operator_basis_normSq_summable basis

theorem cc20CompactComplexPositiveTrace_re_nonnegative
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 cc20CompactMeasure)) :
    0 ≤ (PositiveTrace.ordinaryTraceAlong basis
      (cc20CompactComplexBasisHilbertSchmidtData basis).positiveComposition).re :=
  PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
    (cc20CompactComplexBasisHilbertSchmidtData basis)

end CC20Concrete
end Source
end ConnesWeilRH
