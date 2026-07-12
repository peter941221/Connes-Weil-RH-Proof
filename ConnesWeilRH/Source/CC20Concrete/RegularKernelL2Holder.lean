/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelL2Prelude
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Normed.Operator.Extend

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

noncomputable def cc20CompactMeasureOperator
    (f : ContinuousMap CC20CompactInterval ℝ) (x : CC20CompactInterval) : ℝ :=
  ∫ y, cc20CompactKernelSection x y * f y ∂cc20CompactMeasure

theorem integrable_cc20CompactKernelSection_mul
    (x : CC20CompactInterval) (f : ContinuousMap CC20CompactInterval ℝ) :
    Integrable (fun y => cc20CompactKernelSection x y * f y)
      cc20CompactMeasure := by
  exact (cc20CompactKernelSection_memLp x).integrable_mul
    (cc20CompactContinuousFunction_memLp f)

theorem norm_cc20CompactMeasureOperator_le_holder
    (x : CC20CompactInterval) (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖cc20CompactMeasureOperator f x‖ ≤
      (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
          ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) := by
  calc
    ‖cc20CompactMeasureOperator f x‖ ≤
        ∫ y, ‖cc20CompactKernelSection x y * f y‖ ∂cc20CompactMeasure := by
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ‖cc20CompactKernelSection x y‖ * ‖f y‖
          ∂cc20CompactMeasure := by
      congr 1
      funext y
      exact norm_mul _ _
    _ ≤ (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
          ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using cc20CompactKernelSection_memLp x)
        (by simpa using cc20CompactContinuousFunction_memLp f)

theorem cc20Compact_l2Factor_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℝ) :
    (∫ y, ‖f y‖ ^ (2 : ℝ) ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) =
      lpNorm f 2 cc20CompactMeasure := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := fun y => f y) (μ := cc20CompactMeasure) (p := (2 : ENNReal))
    (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable
  norm_num at h ⊢
  exact h.symm

theorem norm_cc20Compact_toLp_eq_lpNorm
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖ =
      lpNorm f 2 cc20CompactMeasure := by
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae
    (ContinuousMap.coeFn_toLp (μ := cc20CompactMeasure) (𝕜 := ℝ) f)]
  exact toReal_eLpNorm f.continuous.aestronglyMeasurable

theorem norm_cc20CompactMeasureOperator_le_kernelFactor_mul_toLp
    (x : CC20CompactInterval) (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖cc20CompactMeasureOperator f x‖ ≤
      (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
          ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) *
        ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖ := by
  calc
    ‖cc20CompactMeasureOperator f x‖ ≤
        (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
            ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) *
          (∫ y, ‖f y‖ ^ (2 : ℝ)
            ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) :=
      norm_cc20CompactMeasureOperator_le_holder x f
    _ = (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
            ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) *
          ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖ := by
      rw [cc20Compact_l2Factor_eq_lpNorm f,
        ← norm_cc20Compact_toLp_eq_lpNorm f]

theorem cc20CompactKernelSection_l2Factor_le_sup
    (x : CC20CompactInterval) :
    (∫ y, ‖cc20CompactKernelSection x y‖ ^ (2 : ℝ)
        ∂cc20CompactMeasure) ^ (1 / (2 : ℝ)) ≤
      lpNorm (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
        2 cc20CompactMeasure := by
  rw [cc20Compact_l2Factor_eq_lpNorm]
  apply lpNorm_mono_real (p := (2 : ENNReal))
    (memLp_const ‖cc20CompactRegularKernel‖)
  intro y
  exact cc20CompactRegularKernel.norm_coe_le_norm (x, y)

theorem cc20CompactMeasure_ne_zero : cc20CompactMeasure ≠ 0 := by
  apply (Measure.measure_univ_ne_zero).mp
  rw [cc20CompactMeasure_univ]
  norm_num

theorem continuous_cc20CompactMeasureOperator
    (f : ContinuousMap CC20CompactInterval ℝ) :
    Continuous (cc20CompactMeasureOperator f) := by
  have hintegrand : Continuous (Function.uncurry
      (fun x : CC20CompactInterval => fun y : CC20CompactInterval =>
        cc20CompactKernelSection x y * f y)) := by
    have hkernel : Continuous (fun p : CC20CompactInterval × CC20CompactInterval =>
        cc20CompactKernelSection p.1 p.2) :=
      cc20CompactRegularKernel.continuous
    simpa [Function.uncurry] using
      hkernel.mul (f.continuous.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous
    (μ := cc20CompactMeasure) hintegrand
    (s := Set.univ) isCompact_univ
  simpa [cc20CompactMeasureOperator] using h

noncomputable def cc20CompactMeasureContinuousOperator
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ContinuousMap CC20CompactInterval ℝ where
  toFun := cc20CompactMeasureOperator f
  continuous_toFun := continuous_cc20CompactMeasureOperator f

theorem cc20CompactMeasureContinuousOperator_add
    (f g : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactMeasureContinuousOperator (f + g) =
      cc20CompactMeasureContinuousOperator f +
        cc20CompactMeasureContinuousOperator g := by
  ext x
  simpa [cc20CompactMeasureContinuousOperator, cc20CompactMeasureOperator,
    mul_add] using integral_add
      (integrable_cc20CompactKernelSection_mul x f)
      (integrable_cc20CompactKernelSection_mul x g)

theorem cc20CompactMeasureContinuousOperator_smul
    (c : ℝ) (f : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactMeasureContinuousOperator (c • f) =
      c • cc20CompactMeasureContinuousOperator f := by
  ext x
  simpa [cc20CompactMeasureContinuousOperator, cc20CompactMeasureOperator,
    mul_comm, mul_left_comm, mul_assoc] using
    (integral_const_mul (μ := cc20CompactMeasure) c
      (fun y => cc20CompactKernelSection x y * f y)
    )

noncomputable def cc20CompactMeasureContinuousLinearMap :
    ContinuousMap CC20CompactInterval ℝ →ₗ[ℝ]
      ContinuousMap CC20CompactInterval ℝ where
  toFun := cc20CompactMeasureContinuousOperator
  map_add' := cc20CompactMeasureContinuousOperator_add
  map_smul' := cc20CompactMeasureContinuousOperator_smul

noncomputable def cc20CompactMeasureToLpLinearMap :
    ContinuousMap CC20CompactInterval ℝ →ₗ[ℝ]
      Lp ℝ 2 cc20CompactMeasure :=
  (ContinuousMap.toLp 2 cc20CompactMeasure ℝ).toLinearMap.comp
    cc20CompactMeasureContinuousLinearMap

set_option maxHeartbeats 800000 in
-- The global output norm proof expands several nested `lpNorm` and rpow identities.
theorem norm_cc20CompactMeasureContinuousOperator_toLp_le
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ
        (cc20CompactMeasureContinuousOperator f)‖ ≤
      (‖cc20CompactRegularKernel‖ *
        (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ))) *
        (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ)) *
        ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖ := by
  rw [norm_cc20Compact_toLp_eq_lpNorm]
  let C : ℝ := ‖cc20CompactRegularKernel‖ *
    (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ)) *
      ‖ContinuousMap.toLp 2 cc20CompactMeasure ℝ f‖
  have hpoint : ∀ x : CC20CompactInterval,
      ‖cc20CompactMeasureContinuousOperator f x‖ ≤ C := by
    intro x
    have hfactor := cc20CompactKernelSection_l2Factor_le_sup x
    have hholder := norm_cc20CompactMeasureOperator_le_kernelFactor_mul_toLp x f
    have hconst :
        lpNorm (fun _ : CC20CompactInterval => ‖cc20CompactRegularKernel‖)
            2 cc20CompactMeasure =
          ‖cc20CompactRegularKernel‖ *
            (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ)) := by
      simp [lpNorm_const' (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        ‖cc20CompactRegularKernel‖]
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (norm_nonneg (ContinuousMap.toLp 2 cc20CompactMeasure ℝ f))
    exact hholder.trans (hmul.trans_eq (by simp [C, hconst]))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine (lpNorm_mono_real (p := (2 : ENNReal)) (f :=
      (cc20CompactMeasureContinuousOperator f : CC20CompactInterval → ℝ))
      (g := fun _ : CC20CompactInterval => C) (memLp_const C) hpoint).trans_eq ?_
  rw [lpNorm_const' (p := (2 : ENNReal)) (by norm_num) (by norm_num)]
  norm_num
  rw [abs_of_nonneg hC]
  dsimp [C]
  ring

theorem cc20CompactMeasureToLpLinearMap_norm_bound
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖cc20CompactMeasureToLpLinearMap f‖ ≤
      (‖cc20CompactRegularKernel‖ *
        (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ))) *
        (cc20CompactMeasure.real Set.univ) ^ (1 / (2 : ℝ)) *
        ‖(ContinuousMap.toLp 2 cc20CompactMeasure ℝ) f‖ := by
  exact norm_cc20CompactMeasureContinuousOperator_toLp_le f

noncomputable def cc20CompactL2Operator :
    Lp ℝ 2 cc20CompactMeasure →L[ℝ] Lp ℝ 2 cc20CompactMeasure :=
  LinearMap.extendOfNorm cc20CompactMeasureToLpLinearMap
    (ContinuousMap.toLp 2 cc20CompactMeasure ℝ).toLinearMap

theorem cc20CompactL2Operator_agrees_on_continuous
    (f : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactL2Operator
        ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) f) =
      cc20CompactMeasureToLpLinearMap f := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℝ) (𝕜 := ℝ)
      (p := (2 : ENNReal)) (μ := cc20CompactMeasure) (by norm_num)
  · exact ⟨_, cc20CompactMeasureToLpLinearMap_norm_bound⟩

end CC20Concrete
end Source
end ConnesWeilRH
