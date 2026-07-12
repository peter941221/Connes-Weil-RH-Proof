/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.WindowContainment

/-!
# The parameterized source Haar measures

For every `lambda > 1`, this module defines the source measure `d rho / rho`
on `[1/lambda, lambda]`.  It is the measure-level foundation for a genuine
parameterized CC20 regular-kernel operator family.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

abbrev CC20WindowPoint (lambda : ℝ) :=
  {x : ℝ // x ∈ cc20WindowInterval lambda}

noncomputable def cc20WindowBaseMeasure (lambda : ℝ) :
    Measure (CC20WindowPoint lambda) :=
  Measure.comap Subtype.val volume

theorem cc20WindowBaseMeasure_univ
    (lambda : ℝ) :
    cc20WindowBaseMeasure lambda Set.univ =
      ENNReal.ofReal (lambda - 1 / lambda) := by
  unfold cc20WindowBaseMeasure cc20WindowInterval
  change (Measure.comap Subtype.val volume) Set.univ =
    ENNReal.ofReal (lambda - 1 / lambda)
  rw [
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume
      Set.univ,
    Set.image_univ, Subtype.range_coe_subtype]
  change volume (Set.Icc (1 / lambda) lambda) =
    ENNReal.ofReal (lambda - 1 / lambda)
  rw [Real.volume_Icc]

instance cc20WindowBaseMeasure_isFinite
    (lambda : ℝ) :
    IsFiniteMeasure (cc20WindowBaseMeasure lambda) where
  measure_univ_lt_top := by
    rw [cc20WindowBaseMeasure_univ lambda]
    exact ENNReal.ofReal_lt_top

noncomputable def cc20WindowHaarDensity
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) : NNReal :=
  ⟨1 / rho.1, one_div_nonneg.mpr (by
    exact le_of_lt (lt_of_lt_of_le
      (div_pos (by norm_num) (by linarith)) rho.2.1))⟩

theorem cc20WindowHaarDensity_coe
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) :
    (cc20WindowHaarDensity lambda hlambda rho : ℝ) = 1 / rho.1 := rfl

theorem cc20WindowHaarDensity_le_lambda
    (lambda : ℝ) (hlambda : 1 < lambda)
    (rho : CC20WindowPoint lambda) :
    cc20WindowHaarDensity lambda hlambda rho ≤ lambda := by
  change 1 / rho.1 ≤ lambda
  have hrho : 0 < rho.1 :=
    lt_of_lt_of_le (div_pos (by norm_num) (by linarith)) rho.2.1
  apply (div_le_iff₀ hrho).2
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  simpa [mul_comm] using (div_le_iff₀ hlambda_pos).mp rho.2.1

theorem measurable_cc20WindowHaarDensity
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Measurable (cc20WindowHaarDensity lambda hlambda) := by
  unfold cc20WindowHaarDensity
  apply Measurable.subtype_mk
  exact (continuous_const.div continuous_subtype_val
    (fun rho => ne_of_gt (lt_of_lt_of_le
      (div_pos (by norm_num) (by linarith)) rho.2.1))).measurable

noncomputable def cc20WindowHaarMeasure
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Measure (CC20WindowPoint lambda) :=
  (cc20WindowBaseMeasure lambda).withDensity
    (fun rho => cc20WindowHaarDensity lambda hlambda rho)

theorem cc20WindowHaarMeasure_univ_lt_top
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20WindowHaarMeasure lambda hlambda Set.univ < ⊤ := by
  letI := cc20WindowBaseMeasure_isFinite lambda
  rw [cc20WindowHaarMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    ∫⁻ rho, (cc20WindowHaarDensity lambda hlambda rho : ENNReal)
        ∂cc20WindowBaseMeasure lambda ≤
      ∫⁻ _rho, ENNReal.ofReal lambda ∂cc20WindowBaseMeasure lambda := by
        apply lintegral_mono
        intro rho
        rw [ENNReal.ofReal_eq_coe_nnreal (by linarith)]
        apply ENNReal.coe_le_coe.2
        apply NNReal.coe_le_coe.mp
        simpa using
          (cc20WindowHaarDensity_le_lambda lambda hlambda rho)
    _ < ⊤ := by
      simp only [lintegral_const]
      exact ENNReal.mul_lt_top (by
        exact ENNReal.ofReal_lt_top) (measure_lt_top _ _)

instance cc20WindowHaarMeasure_isFinite
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsFiniteMeasure (cc20WindowHaarMeasure lambda hlambda) where
  measure_univ_lt_top := cc20WindowHaarMeasure_univ_lt_top lambda hlambda

theorem integral_cc20WindowHaarMeasure_eq_smul
    (lambda : ℝ) (hlambda : 1 < lambda)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CC20WindowPoint lambda → E) :
    ∫ rho, f rho ∂cc20WindowHaarMeasure lambda hlambda =
      ∫ rho, (1 / rho.1) • f rho ∂cc20WindowBaseMeasure lambda := by
  rw [cc20WindowHaarMeasure,
    integral_withDensity_eq_integral_smul
      (measurable_cc20WindowHaarDensity lambda hlambda)]
  apply integral_congr_ae
  filter_upwards with rho
  rw [NNReal.smul_def, cc20WindowHaarDensity_coe]

end CC20Concrete
end Source
end ConnesWeilRH
