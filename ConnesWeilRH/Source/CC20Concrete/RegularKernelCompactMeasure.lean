/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelCompactOperator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

noncomputable def cc20CompactMeasure : Measure CC20CompactInterval :=
  Measure.comap Subtype.val volume

theorem cc20CompactMeasure_univ :
    cc20CompactMeasure Set.univ = ENNReal.ofReal (3 / 2 : ℝ) := by
  rw [cc20CompactMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume Set.univ,
    Set.image_univ, Subtype.range_coe_subtype]
  change volume (Set.Icc (1 / 2 : ℝ) 2) = ENNReal.ofReal (3 / 2 : ℝ)
  rw [Real.volume_Icc]
  norm_num

instance : IsFiniteMeasure cc20CompactMeasure where
  measure_univ_lt_top := by
    rw [cc20CompactMeasure_univ]
    exact ENNReal.ofReal_lt_top

/-- The multiplicative Haar density `1 / rho` on the fixed compact interval. -/
noncomputable def cc20CompactHaarDensity (rho : CC20CompactInterval) : NNReal :=
  ⟨1 / (rho : ℝ), one_div_nonneg.mpr (le_of_lt (lt_of_lt_of_le (by norm_num) rho.property.1))⟩

theorem cc20CompactHaarDensity_coe (rho : CC20CompactInterval) :
    (cc20CompactHaarDensity rho : ℝ) = 1 / (rho : ℝ) := rfl

theorem cc20CompactHaarDensity_le_two (rho : CC20CompactInterval) :
    cc20CompactHaarDensity rho ≤ 2 := by
  apply NNReal.coe_le_coe.mp
  rw [cc20CompactHaarDensity_coe, NNReal.coe_ofNat]
  have hrho : 0 < (rho : ℝ) :=
    lt_of_lt_of_le (by norm_num) rho.property.1
  exact (div_le_iff₀ hrho).2 (by nlinarith [rho.property.1])

/-- The source measure `d*rho = d rho / rho` on `sqrt I = [1/2, 2]`. -/
noncomputable def cc20CompactHaarMeasure : Measure CC20CompactInterval :=
  cc20CompactMeasure.withDensity fun rho => cc20CompactHaarDensity rho

theorem continuous_cc20CompactHaarDensity :
    Continuous cc20CompactHaarDensity := by
  unfold cc20CompactHaarDensity
  apply Continuous.subtype_mk
  exact continuous_const.div continuous_subtype_val fun rho =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) rho.property.1)

theorem measurable_cc20CompactHaarDensity :
    Measurable cc20CompactHaarDensity :=
  continuous_cc20CompactHaarDensity.measurable

theorem cc20CompactHaarMeasure_univ_lt_top :
    cc20CompactHaarMeasure Set.univ < ⊤ := by
  rw [cc20CompactHaarMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    ∫⁻ rho, (cc20CompactHaarDensity rho : ENNReal) ∂cc20CompactMeasure ≤
        ∫⁻ _rho, (2 : ENNReal) ∂cc20CompactMeasure := by
      apply lintegral_mono
      intro rho
      change (cc20CompactHaarDensity rho : ENNReal) ≤ ((2 : NNReal) : ENNReal)
      exact ENNReal.coe_le_coe.2 (cc20CompactHaarDensity_le_two rho)
    _ < ⊤ := by
      simp only [lintegral_const]
      exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)

instance : IsFiniteMeasure cc20CompactHaarMeasure where
  measure_univ_lt_top := cc20CompactHaarMeasure_univ_lt_top

/-- Integration against the source Haar measure is ordinary integration with
the exact density `1 / rho`. -/
theorem integral_cc20CompactHaarMeasure_eq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CC20CompactInterval → E) :
    ∫ rho, f rho ∂cc20CompactHaarMeasure =
      ∫ rho, (1 / (rho : ℝ)) • f rho ∂cc20CompactMeasure := by
  rw [cc20CompactHaarMeasure,
    integral_withDensity_eq_integral_smul measurable_cc20CompactHaarDensity]
  apply integral_congr_ae
  filter_upwards with rho
  rw [NNReal.smul_def, cc20CompactHaarDensity_coe]

end CC20Concrete
end Source
end ConnesWeilRH
