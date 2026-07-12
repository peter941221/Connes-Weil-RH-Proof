/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelL2Prelude
import ConnesWeilRH.Source.CC20Concrete.RegularKernelL2Symmetry
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.CompactOpen

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

/-- The section `K(x, ·)` of the compact regular kernel, represented in the
same real `L²` space on which `cc20CompactL2Operator` acts. -/
noncomputable def cc20CompactKernelSectionToLp
    (x : CC20CompactInterval) : Lp ℝ 2 cc20CompactMeasure :=
  ContinuousMap.toLp 2 cc20CompactMeasure ℝ (cc20CompactKernelSection x)

theorem continuous_cc20CompactKernelSectionToLp :
    Continuous cc20CompactKernelSectionToLp := by
  change Continuous (fun x =>
    ContinuousMap.toLp 2 cc20CompactMeasure ℝ
      (cc20CompactRegularKernel.curry x))
  exact (ContinuousMap.toLp 2 cc20CompactMeasure ℝ).continuous.comp
    cc20CompactRegularKernel.curry.continuous

/-- The continuous coefficient representative `x ↦ ⟪u, K(x, ·)⟫`. -/
noncomputable def cc20CompactKernelCoefficient
    (u : Lp ℝ 2 cc20CompactMeasure) :
    ContinuousMap CC20CompactInterval ℝ where
  toFun x := inner ℝ u (cc20CompactKernelSectionToLp x)
  continuous_toFun := by
    exact continuous_const.inner continuous_cc20CompactKernelSectionToLp

theorem cc20CompactKernelCoefficient_add
    (u v : Lp ℝ 2 cc20CompactMeasure) :
    cc20CompactKernelCoefficient (u + v) =
      cc20CompactKernelCoefficient u + cc20CompactKernelCoefficient v := by
  ext x
  simp [cc20CompactKernelCoefficient, inner_add_left]

theorem cc20CompactKernelCoefficient_smul
    (c : ℝ) (u : Lp ℝ 2 cc20CompactMeasure) :
    cc20CompactKernelCoefficient (c • u) =
      c • cc20CompactKernelCoefficient u := by
  ext x
  simp [cc20CompactKernelCoefficient, real_inner_smul_left]

noncomputable def cc20CompactKernelCoefficientLinearMap :
    Lp ℝ 2 cc20CompactMeasure →ₗ[ℝ]
      ContinuousMap CC20CompactInterval ℝ where
  toFun := cc20CompactKernelCoefficient
  map_add' := cc20CompactKernelCoefficient_add
  map_smul' := cc20CompactKernelCoefficient_smul

theorem norm_cc20CompactKernelSectionToLp_le
    (x : CC20CompactInterval) :
    ‖cc20CompactKernelSectionToLp x‖ ≤
      lpNorm (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
        2 cc20CompactMeasure := by
  rw [cc20CompactKernelSectionToLp,
    norm_cc20Compact_toLp_eq_lpNorm,
    ← cc20Compact_l2Factor_eq_lpNorm]
  exact cc20CompactKernelSection_l2Factor_le_sup x

theorem norm_cc20CompactKernelCoefficient_le
    (u : Lp ℝ 2 cc20CompactMeasure) :
    ‖cc20CompactKernelCoefficient u‖ ≤
      lpNorm (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
          2 cc20CompactMeasure * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg lpNorm_nonneg (norm_nonneg _))).2
  intro x
  calc
    ‖cc20CompactKernelCoefficient u x‖ =
        ‖inner ℝ u (cc20CompactKernelSectionToLp x)‖ := rfl
    _ ≤ ‖u‖ * ‖cc20CompactKernelSectionToLp x‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ * lpNorm
        (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
          2 cc20CompactMeasure := by
      gcongr
      exact norm_cc20CompactKernelSectionToLp_le x
    _ = lpNorm
        (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
          2 cc20CompactMeasure * ‖u‖ := mul_comm _ _

noncomputable def cc20CompactKernelCoefficientContinuousLinearMap :
    Lp ℝ 2 cc20CompactMeasure →L[ℝ]
      ContinuousMap CC20CompactInterval ℝ :=
  LinearMap.mkContinuous cc20CompactKernelCoefficientLinearMap
    (lpNorm (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
      2 cc20CompactMeasure)
    norm_cc20CompactKernelCoefficient_le

noncomputable def cc20CompactKernelCoefficientToLpOperator :
    Lp ℝ 2 cc20CompactMeasure →L[ℝ] Lp ℝ 2 cc20CompactMeasure :=
  (ContinuousMap.toLp 2 cc20CompactMeasure ℝ).comp
    cc20CompactKernelCoefficientContinuousLinearMap

theorem cc20CompactKernelCoefficient_continuous_input
    (f : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactKernelCoefficient
        (ContinuousMap.toLp 2 cc20CompactMeasure ℝ f) =
      cc20CompactMeasureContinuousOperator f := by
  ext x
  change inner ℝ (ContinuousMap.toLp 2 cc20CompactMeasure ℝ f)
      (ContinuousMap.toLp 2 cc20CompactMeasure ℝ (cc20CompactKernelSection x)) = _
  rw [ContinuousMap.inner_toLp]
  rfl

theorem cc20CompactKernelCoefficientToLpOperator_agrees_on_continuous
    (f : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactKernelCoefficientToLpOperator
        (ContinuousMap.toLp 2 cc20CompactMeasure ℝ f) =
      cc20CompactMeasureToLpLinearMap f := by
  change ContinuousMap.toLp 2 cc20CompactMeasure ℝ
      (cc20CompactKernelCoefficient
        (ContinuousMap.toLp 2 cc20CompactMeasure ℝ f)) = _
  rw [cc20CompactKernelCoefficient_continuous_input]
  rfl

theorem cc20CompactKernelCoefficientToLpOperator_eq :
    cc20CompactKernelCoefficientToLpOperator = cc20CompactL2Operator := by
  apply ContinuousLinearMap.ext
  intro u
  have hdense : DenseRange
      (ContinuousMap.toLp 2 cc20CompactMeasure ℝ) :=
    ContinuousMap.toLp_denseRange (E := ℝ) (𝕜 := ℝ)
      (p := (2 : ENNReal)) (μ := cc20CompactMeasure) (by norm_num)
  refine DenseRange.induction_on hdense u (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [cc20CompactKernelCoefficientToLpOperator_agrees_on_continuous,
    cc20CompactL2Operator_agrees_on_continuous]

theorem cc20CompactL2Operator_eq_kernelCoefficient
    (u : Lp ℝ 2 cc20CompactMeasure) :
    cc20CompactL2Operator u =
      ContinuousMap.toLp 2 cc20CompactMeasure ℝ
        (cc20CompactKernelCoefficient u) := by
  rw [← cc20CompactKernelCoefficientToLpOperator_eq]
  rfl

theorem norm_toLp_continuous_sq
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂cc20CompactMeasure := by
  rw [norm_cc20Compact_toLp_eq_lpNorm,
    ← cc20Compact_l2Factor_eq_lpNorm]
  simp_rw [Real.rpow_two]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂cc20CompactMeasure := by
    exact integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow]
  simpa only [] using Real.sq_sqrt hnonneg

theorem integrable_cc20CompactKernelSectionToLp_norm_sq :
    Integrable
      (fun x : CC20CompactInterval =>
        ‖cc20CompactKernelSectionToLp x‖ ^ 2) cc20CompactMeasure := by
  have hc : Continuous (fun x : CC20CompactInterval =>
      ‖cc20CompactKernelSectionToLp x‖ ^ 2) := by
    exact (continuous_cc20CompactKernelSectionToLp.norm.pow 2)
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := cc20CompactMeasure) isCompact_univ).integrable

theorem cc20CompactL2Operator_finite_basis_sum_le_kernel_energy
    {ι : Type*} (basis : HilbertBasis ι ℝ (Lp ℝ 2 cc20CompactMeasure))
    (s : Finset ι) :
    ∑ i ∈ s, ‖cc20CompactL2Operator (basis i)‖ ^ 2 ≤
      ∫ x, ‖cc20CompactKernelSectionToLp x‖ ^ 2 ∂cc20CompactMeasure := by
  have hcoeff (i : ι) :
      ‖cc20CompactL2Operator (basis i)‖ ^ 2 =
        ∫ x, ‖cc20CompactKernelCoefficient (basis i) x‖ ^ 2
          ∂cc20CompactMeasure := by
    rw [cc20CompactL2Operator_eq_kernelCoefficient,
      norm_toLp_continuous_sq]
  have hint (i : ι) : Integrable
      (fun x => ‖cc20CompactKernelCoefficient (basis i) x‖ ^ 2)
        cc20CompactMeasure := by
    have hc : Continuous
        (fun x => ‖cc20CompactKernelCoefficient (basis i) x‖ ^ 2) :=
      (cc20CompactKernelCoefficient (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := cc20CompactMeasure) isCompact_univ).integrable
  simp_rw [hcoeff]
  have hsum : ∫ x, ∑ i ∈ s,
      ‖cc20CompactKernelCoefficient (basis i) x‖ ^ 2 ∂cc20CompactMeasure =
      ∑ i ∈ s, ∫ x, ‖cc20CompactKernelCoefficient (basis i) x‖ ^ 2
        ∂cc20CompactMeasure := by
    exact integral_finsetSum s (fun i hi => hint i)
  rw [← hsum]
  apply integral_mono_ae
  · exact integrable_finsetSum s (fun i hi => hint i)
  · exact integrable_cc20CompactKernelSectionToLp_norm_sq
  · filter_upwards with x
    exact basis.orthonormal.sum_inner_products_le
      (cc20CompactKernelSectionToLp x)

theorem cc20CompactL2Operator_basis_normSq_summable
    {ι : Type*} (basis : HilbertBasis ι ℝ (Lp ℝ 2 cc20CompactMeasure)) :
    Summable (fun i => ‖cc20CompactL2Operator (basis i)‖ ^ 2) := by
  refine summable_of_sum_le
    (c := ∫ x, ‖cc20CompactKernelSectionToLp x‖ ^ 2 ∂cc20CompactMeasure)
    (fun i => sq_nonneg _) ?_
  intro s
  exact cc20CompactL2Operator_finite_basis_sum_le_kernel_energy basis s

end CC20Concrete
end Source
end ConnesWeilRH
