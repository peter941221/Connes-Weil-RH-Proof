/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelComplexHilbertSchmidt
import ConnesWeilRH.Source.CC20Concrete.RegularKernelSourceBridge

/-!
# Complex L2 operator for the CC20 Haar measure

This module reconstructs the same complex regular-kernel operator on the
source Hilbert space measure `d*rho = d rho / rho`. It does not identify the
result with the full distributional statement `-2 Id + K_I`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

noncomputable def cc20CompactHaarComplexKernelSectionToLp
    (x : CC20CompactInterval) : Lp ℂ 2 cc20CompactHaarMeasure :=
  ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ
    (cc20CompactComplexKernelSection x)

theorem continuous_cc20CompactHaarComplexKernelSectionToLp :
    Continuous cc20CompactHaarComplexKernelSectionToLp := by
  exact (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ).continuous.comp
    cc20CompactComplexRegularKernel.curry.continuous

theorem cc20CompactHaarComplex_l2Factor_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℂ) :
    (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20CompactHaarMeasure) ^ (1 / (2 : ℝ)) =
      lpNorm f 2 cc20CompactHaarMeasure := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := fun y => f y) (μ := cc20CompactHaarMeasure) (p := (2 : ENNReal))
    (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable
  norm_num at h ⊢
  exact h.symm

theorem norm_cc20CompactHaarComplex_toLp_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℂ) :
    ‖ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ f‖ =
      lpNorm f 2 cc20CompactHaarMeasure := by
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae
    (ContinuousMap.coeFn_toLp (μ := cc20CompactHaarMeasure) (𝕜 := ℂ) f)]
  exact toReal_eLpNorm f.continuous.aestronglyMeasurable

theorem norm_cc20CompactHaarComplexKernelSectionToLp_le
    (x : CC20CompactInterval) :
    ‖cc20CompactHaarComplexKernelSectionToLp x‖ ≤
      lpNorm (fun _ : CC20CompactInterval =>
        ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactHaarMeasure := by
  rw [cc20CompactHaarComplexKernelSectionToLp,
    norm_cc20CompactHaarComplex_toLp_eq_lpNorm]
  apply lpNorm_mono_real (p := (2 : ENNReal))
    (memLp_const ‖cc20CompactComplexRegularKernel‖)
  intro y
  exact cc20CompactComplexRegularKernel.norm_coe_le_norm (x, y)

/-- The complex-linear Haar kernel coefficient. The kernel section is the
first inner-product argument because the second argument is complex-linear. -/
noncomputable def cc20CompactHaarComplexKernelCoefficient
    (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    ContinuousMap CC20CompactInterval ℂ where
  toFun x := inner ℂ (cc20CompactHaarComplexKernelSectionToLp x) u
  continuous_toFun :=
    continuous_cc20CompactHaarComplexKernelSectionToLp.inner continuous_const

theorem cc20CompactHaarComplexKernelCoefficient_add
    (u v : Lp ℂ 2 cc20CompactHaarMeasure) :
    cc20CompactHaarComplexKernelCoefficient (u + v) =
      cc20CompactHaarComplexKernelCoefficient u +
        cc20CompactHaarComplexKernelCoefficient v := by
  ext x
  simp [cc20CompactHaarComplexKernelCoefficient, inner_add_right]

theorem cc20CompactHaarComplexKernelCoefficient_smul
    (c : ℂ) (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    cc20CompactHaarComplexKernelCoefficient (c • u) =
      c • cc20CompactHaarComplexKernelCoefficient u := by
  ext x
  simp [cc20CompactHaarComplexKernelCoefficient, inner_smul_right]

noncomputable def cc20CompactHaarComplexKernelCoefficientLinearMap :
    Lp ℂ 2 cc20CompactHaarMeasure →ₗ[ℂ]
      ContinuousMap CC20CompactInterval ℂ where
  toFun := cc20CompactHaarComplexKernelCoefficient
  map_add' := cc20CompactHaarComplexKernelCoefficient_add
  map_smul' := cc20CompactHaarComplexKernelCoefficient_smul

theorem norm_cc20CompactHaarComplexKernelCoefficient_le
    (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    ‖cc20CompactHaarComplexKernelCoefficient u‖ ≤
      lpNorm (fun _ : CC20CompactInterval =>
          ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactHaarMeasure * ‖u‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg lpNorm_nonneg (norm_nonneg _))).2
  intro x
  calc
    ‖cc20CompactHaarComplexKernelCoefficient u x‖ =
        ‖inner ℂ (cc20CompactHaarComplexKernelSectionToLp x) u‖ := rfl
    _ ≤ ‖cc20CompactHaarComplexKernelSectionToLp x‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ lpNorm (fun _ : CC20CompactInterval =>
          ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactHaarMeasure * ‖u‖ := by
      gcongr
      exact norm_cc20CompactHaarComplexKernelSectionToLp_le x

noncomputable def cc20CompactHaarComplexKernelCoefficientContinuousLinearMap :
    Lp ℂ 2 cc20CompactHaarMeasure →L[ℂ]
      ContinuousMap CC20CompactInterval ℂ :=
  LinearMap.mkContinuous cc20CompactHaarComplexKernelCoefficientLinearMap
    (lpNorm (fun _ : CC20CompactInterval =>
      ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactHaarMeasure)
    norm_cc20CompactHaarComplexKernelCoefficient_le

/-- The same ordinary regular kernel as a complex-linear operator on the
source Hilbert space `L2(sqrt I, d*rho)`. -/
noncomputable def cc20CompactHaarComplexL2Operator :
    Lp ℂ 2 cc20CompactHaarMeasure →L[ℂ]
      Lp ℂ 2 cc20CompactHaarMeasure :=
  (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ).comp
    cc20CompactHaarComplexKernelCoefficientContinuousLinearMap

theorem cc20CompactHaarComplexL2Operator_apply
    (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    cc20CompactHaarComplexL2Operator u =
      ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ
        (cc20CompactHaarComplexKernelCoefficient u) := rfl

/-- On continuous inputs, the Haar `L2` operator is exactly the source Haar
integral action defined by the literal regular kernel. -/
theorem cc20CompactHaarComplexKernelCoefficient_continuous_input
    (f : ContinuousMap CC20CompactInterval ℂ)
    (x : CC20CompactInterval) :
    cc20CompactHaarComplexKernelCoefficient
        (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ f) x =
      cc20CompactSourceHaarAction f x := by
  change inner ℂ
      (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ
        (cc20CompactComplexKernelSection x))
      (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ f) = _
  rw [ContinuousMap.inner_toLp]
  simp [cc20CompactSourceHaarAction, cc20CompactComplexKernelSection,
    cc20CompactComplexRegularKernel, mul_comm]

end CC20Concrete
end Source
end ConnesWeilRH
