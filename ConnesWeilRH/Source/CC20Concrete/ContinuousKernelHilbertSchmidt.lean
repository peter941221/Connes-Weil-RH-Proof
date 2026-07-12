/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Hilbert-Schmidt operators from continuous kernels on compact spaces

This module supplies the reusable operator layer needed by the two crossing
kernels.  It constructs the actual `L2` operator from a continuous kernel and
proves basis-square summability from the kernel sections.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ContinuousKernelHilbertSchmidt

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

variable {X Y : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y]

noncomputable def kernelSection
    (kernel : ContinuousMap (Y × X) ℂ) (y : Y) : ContinuousMap X ℂ :=
  kernel.curry y

noncomputable def sectionToLp
  (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) (y : Y) : Lp ℂ 2 μX :=
  ContinuousMap.toLp 2 μX ℂ (kernelSection kernel y)

theorem continuous_sectionToLp
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Continuous (sectionToLp μX kernel) := by
  exact (ContinuousMap.toLp 2 μX ℂ).continuous.comp kernel.curry.continuous

noncomputable def sectionToLpMap
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    ContinuousMap Y (Lp ℂ 2 μX) where
  toFun := sectionToLp μX kernel
  continuous_toFun := continuous_sectionToLp μX kernel

noncomputable def coefficient
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u : Lp ℂ 2 μX) : ContinuousMap Y ℂ where
  toFun y := inner ℂ (sectionToLp μX kernel y) u
  continuous_toFun :=
    (continuous_sectionToLp μX kernel).inner continuous_const

theorem coefficient_add
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u v : Lp ℂ 2 μX) :
    coefficient μX kernel (u + v) =
      coefficient μX kernel u + coefficient μX kernel v := by
  ext y
  simp [coefficient, inner_add_right]

theorem coefficient_smul
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (c : ℂ) (u : Lp ℂ 2 μX) :
    coefficient μX kernel (c • u) = c • coefficient μX kernel u := by
  ext y
  simp [coefficient, inner_smul_right]

noncomputable def coefficientLinearMap
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Lp ℂ 2 μX →ₗ[ℂ] ContinuousMap Y ℂ where
  toFun := coefficient μX kernel
  map_add' := coefficient_add μX kernel
  map_smul' := coefficient_smul μX kernel

theorem norm_coefficient_le
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u : Lp ℂ 2 μX) :
    ‖coefficient μX kernel u‖ ≤
      ‖sectionToLpMap μX kernel‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro y
  calc
    ‖coefficient μX kernel u y‖ =
        ‖inner ℂ (sectionToLp μX kernel y) u‖ := rfl
    _ ≤ ‖sectionToLp μX kernel y‖ * ‖u‖ := norm_inner_le_norm _ _
    _ ≤ ‖sectionToLpMap μX kernel‖ * ‖u‖ := by
      gcongr
      exact (sectionToLpMap μX kernel).norm_coe_le_norm y

noncomputable def coefficientContinuousLinearMap
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Lp ℂ 2 μX →L[ℂ] ContinuousMap Y ℂ :=
  LinearMap.mkContinuous (coefficientLinearMap μX kernel)
    ‖sectionToLpMap μX kernel‖ (norm_coefficient_le μX kernel)

noncomputable def operator
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Lp ℂ 2 μX →L[ℂ] Lp ℂ 2 μY :=
  (ContinuousMap.toLp 2 μY ℂ).comp
    (coefficientContinuousLinearMap μX kernel)

theorem operator_apply
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ) (u : Lp ℂ 2 μX) :
    operator μX μY kernel u =
      ContinuousMap.toLp 2 μY ℂ (coefficient μX kernel u) := rfl

theorem norm_continuousMap_toLp_sq
    (μY : Measure Y) [IsFiniteMeasure μY]
    (f : ContinuousMap Y ℂ) :
    ‖ContinuousMap.toLp 2 μY ℂ f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂μY := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := fun y => f y) (μ := μY) (p := (2 : ENNReal))
    (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable
  norm_num at h ⊢
  rw [show ‖ContinuousMap.toLp 2 μY ℂ f‖ = lpNorm f 2 μY by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae
      (ContinuousMap.coeFn_toLp (μ := μY) (𝕜 := ℂ) f)]
    exact toReal_eLpNorm f.continuous.aestronglyMeasurable]
  rw [h]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (by positivity)

theorem section_normSq_integrable
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Integrable (fun y => ‖sectionToLp μX kernel y‖ ^ 2) μY := by
  have hc : Continuous (fun y => ‖sectionToLp μX kernel y‖ ^ 2) :=
    (continuous_sectionToLp μX kernel).norm.pow 2
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := μY) isCompact_univ).integrable

theorem finite_basis_sum_le_section_energy
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX))
    (s : Finset ι) :
    ∑ i ∈ s, ‖operator μX μY kernel (basis i)‖ ^ 2 ≤
      ∫ y, ‖sectionToLp μX kernel y‖ ^ 2 ∂μY := by
  have hcoeff (i : ι) :
      ‖operator μX μY kernel (basis i)‖ ^ 2 =
        ∫ y, ‖coefficient μX kernel (basis i) y‖ ^ 2 ∂μY := by
    rw [operator_apply, norm_continuousMap_toLp_sq]
  have hint (i : ι) : Integrable
      (fun y => ‖coefficient μX kernel (basis i) y‖ ^ 2) μY := by
    have hc : Continuous
        (fun y => ‖coefficient μX kernel (basis i) y‖ ^ 2) :=
      (coefficient μX kernel (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := μY) isCompact_univ).integrable
  simp_rw [hcoeff]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  apply integral_mono_ae
  · exact integrable_finsetSum s (fun i _ => hint i)
  · exact section_normSq_integrable μX μY kernel
  · filter_upwards with y
    simpa only [coefficient, norm_inner_symm] using
      basis.orthonormal.sum_inner_products_le (sectionToLp μX kernel y)

theorem basis_normSq_summable
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX)) :
    Summable (fun i => ‖operator μX μY kernel (basis i)‖ ^ 2) := by
  refine summable_of_sum_le
    (c := ∫ y, ‖sectionToLp μX kernel y‖ ^ 2 ∂μY)
    (fun i => sq_nonneg _) ?_
  intro s
  exact finite_basis_sum_le_section_energy μX μY kernel basis s

theorem coefficient_inner_integrable
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (leftKernel rightKernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX)) (i : ι) :
    Integrable (fun y => inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)) μY := by
  have hc : Continuous (fun y => inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)) := by
    fun_prop
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := μY) isCompact_univ).integrable

theorem coefficient_inner_integral_norm_le
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (leftKernel rightKernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX)) (i : ι) :
    (∫ y, ‖inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)‖ ∂μY) ≤
      (1 / 2 : ℝ) *
        (‖operator μX μY leftKernel (basis i)‖ ^ 2 +
          ‖operator μX μY rightKernel (basis i)‖ ^ 2) := by
  have hpoint : ∀ y, ‖inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)‖ ≤
      (1 / 2 : ℝ) *
        (‖coefficient μX leftKernel (basis i) y‖ ^ 2 +
          ‖coefficient μX rightKernel (basis i) y‖ ^ 2) := by
    intro y
    calc
      ‖inner ℂ
          (coefficient μX leftKernel (basis i) y)
          (coefficient μX rightKernel (basis i) y)‖ ≤
          ‖coefficient μX leftKernel (basis i) y‖ *
            ‖coefficient μX rightKernel (basis i) y‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖coefficient μX leftKernel (basis i) y‖ ^ 2 +
            ‖coefficient μX rightKernel (basis i) y‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖coefficient μX leftKernel (basis i) y‖ -
            ‖coefficient μX rightKernel (basis i) y‖)]
  have hleft : Integrable
      (fun y => ‖coefficient μX leftKernel (basis i) y‖ ^ 2) μY := by
    have hc : Continuous
        (fun y => ‖coefficient μX leftKernel (basis i) y‖ ^ 2) :=
      (coefficient μX leftKernel (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := μY) isCompact_univ).integrable
  have hright : Integrable
      (fun y => ‖coefficient μX rightKernel (basis i) y‖ ^ 2) μY := by
    have hc : Continuous
        (fun y => ‖coefficient μX rightKernel (basis i) y‖ ^ 2) :=
      (coefficient μX rightKernel (basis i)).continuous.norm.pow 2
    simpa only [Measure.restrict_univ] using
      (hc.continuousOn.integrableOn_compact
        (μ := μY) isCompact_univ).integrable
  calc
    (∫ y, ‖inner ℂ
        (coefficient μX leftKernel (basis i) y)
        (coefficient μX rightKernel (basis i) y)‖ ∂μY) ≤
      ∫ y, (1 / 2 : ℝ) *
        (‖coefficient μX leftKernel (basis i) y‖ ^ 2 +
          ‖coefficient μX rightKernel (basis i) y‖ ^ 2) ∂μY := by
      apply integral_mono_ae
      · exact (coefficient_inner_integrable
          μX μY leftKernel rightKernel basis i).norm
      · refine ((hleft.const_mul (1 / 2 : ℝ)).add
          (hright.const_mul (1 / 2 : ℝ))).congr ?_
        filter_upwards with y
        simp only [Pi.add_apply]
        ring
      · filter_upwards with y
        exact hpoint y
    _ = (1 / 2 : ℝ) *
        (‖operator μX μY leftKernel (basis i)‖ ^ 2 +
          ‖operator μX μY rightKernel (basis i)‖ ^ 2) := by
      rw [integral_const_mul,
        integral_add hleft hright,
        ← norm_continuousMap_toLp_sq μY
          (coefficient μX leftKernel (basis i)),
        ← norm_continuousMap_toLp_sq μY
          (coefficient μX rightKernel (basis i))]
      rfl

theorem coefficient_inner_integral_norm_summable
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (leftKernel rightKernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX)) :
    Summable (fun i => ∫ y, ‖inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)‖ ∂μY) := by
  apply Summable.of_norm_bounded
    (((basis_normSq_summable μX μY leftKernel basis).add
      (basis_normSq_summable μX μY rightKernel basis)).mul_left
        (1 / 2 : ℝ))
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact coefficient_inner_integral_norm_le μX μY leftKernel rightKernel basis i
  · exact integral_nonneg fun _ => norm_nonneg _

noncomputable def pairData
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (leftKernel rightKernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX)) :
    PositiveTrace.BasisHilbertSchmidtPairData (G := Lp ℂ 2 μY) basis where
  left := operator μX μY leftKernel
  right := operator μX μY rightKernel
  left_summable_normSq := basis_normSq_summable μX μY leftKernel basis
  right_summable_normSq := basis_normSq_summable μX μY rightKernel basis

theorem pairData_trace_eq_kernel_inner
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (leftKernel rightKernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 μX))
    (hF_int : ∀ i, Integrable
      (fun y => inner ℂ
        (coefficient μX leftKernel (basis i) y)
        (coefficient μX rightKernel (basis i) y)) μY)
    (hF_sum : Summable (fun i => ∫ y, ‖inner ℂ
        (coefficient μX leftKernel (basis i) y)
        (coefficient μX rightKernel (basis i) y)‖ ∂μY)) :
    PositiveTrace.ordinaryTraceAlong basis
        (pairData μX μY leftKernel rightKernel basis).traceProduct =
      ∫ y, inner ℂ
        (sectionToLp μX rightKernel y)
        (sectionToLp μX leftKernel y) ∂μY := by
  rw [PositiveTrace.ordinaryTraceAlong]
  have hdiag (i : ι) :
      ⟪basis i,
          (pairData μX μY leftKernel rightKernel basis).traceProduct (basis i)⟫_ℂ =
        ∫ y, inner ℂ
          (coefficient μX leftKernel (basis i) y)
          (coefficient μX rightKernel (basis i) y) ∂μY := by
    rw [PositiveTrace.BasisHilbertSchmidtPairData.traceProduct_diagonal]
    change inner ℂ
      (operator μX μY leftKernel (basis i))
      (operator μX μY rightKernel (basis i)) = _
    rw [operator_apply, operator_apply]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards
      [ContinuousMap.coeFn_toLp
        (p := (2 : ENNReal))
        (μ := μY) (𝕜 := ℂ) (coefficient μX leftKernel (basis i)),
       ContinuousMap.coeFn_toLp
        (p := (2 : ENNReal))
        (μ := μY) (𝕜 := ℂ) (coefficient μX rightKernel (basis i))] with y hleft hright
    rw [hleft, hright]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun i y => inner ℂ
      (coefficient μX leftKernel (basis i) y)
      (coefficient μX rightKernel (basis i) y)) hF_int hF_sum
  calc
    ∑' i, ⟪basis i,
        (pairData μX μY leftKernel rightKernel basis).traceProduct (basis i)⟫_ℂ =
      ∑' i, ∫ y, inner ℂ
        (coefficient μX leftKernel (basis i) y)
        (coefficient μX rightKernel (basis i) y) ∂μY :=
      tsum_congr hdiag
    _ = ∫ y, ∑' i, inner ℂ
        (coefficient μX leftKernel (basis i) y)
        (coefficient μX rightKernel (basis i) y) ∂μY := hswap
    _ = ∫ y, inner ℂ
        (sectionToLp μX rightKernel y)
        (sectionToLp μX leftKernel y) ∂μY := by
      apply integral_congr_ae
      filter_upwards with y
      simp [coefficient, inner_conj_symm]
      rw [← basis.tsum_inner_mul_inner
        (sectionToLp μX rightKernel y) (sectionToLp μX leftKernel y)]

end ContinuousKernelHilbertSchmidt
end CC20Concrete
end Source
end ConnesWeilRH
