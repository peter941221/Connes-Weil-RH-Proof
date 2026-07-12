/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelOperator
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Bounded compact-interval regular-kernel operator

The operator is now restricted to the genuine compact interval `[1/2,2]`.
The continuous kernel has a finite supremum norm there, giving an explicit
operator bound and hence a continuous linear map on continuous functions.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

abbrev CC20CompactInterval := Set.Icc (1 / 2 : ℝ) 2

noncomputable def cc20CompactClamp (x : ℝ) : CC20CompactInterval :=
  ⟨min (max x (1 / 2)) 2, by
    constructor
    · exact le_min (le_max_right _ _) (by norm_num)
    · exact min_le_right _ _⟩

theorem continuous_cc20CompactClamp : Continuous cc20CompactClamp := by
  exact ((continuous_id.max continuous_const).min continuous_const).subtype_mk _

noncomputable def cc20CompactRegularKernel :
    ContinuousMap (CC20CompactInterval × CC20CompactInterval) ℝ where
  toFun p := cc20RegularKernelReal (p.1.1, p.2.1)
  continuous_toFun := continuous_cc20RegularKernelReal.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

noncomputable def cc20CompactIntervalOperator
    (f : ContinuousMap CC20CompactInterval ℝ) (x : CC20CompactInterval) : ℝ :=
  ∫ y in (1 / 2 : ℝ)..2,
    cc20RegularKernelReal (x.1, y) * f (cc20CompactClamp y)

theorem continuous_cc20CompactIntervalOperator
    (f : ContinuousMap CC20CompactInterval ℝ) :
    Continuous (cc20CompactIntervalOperator f) := by
  have hintegrand : Continuous (Function.uncurry
      (fun x : CC20CompactInterval => fun y : ℝ =>
        cc20RegularKernelReal (x.1, y) * f (cc20CompactClamp y))) := by
    have hkernel : Continuous (fun p : CC20CompactInterval × ℝ =>
        cc20RegularKernelReal (p.1.1, p.2)) :=
      continuous_cc20RegularKernelReal.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hf : Continuous (fun p : CC20CompactInterval × ℝ =>
        f (cc20CompactClamp p.2)) :=
      f.continuous.comp (continuous_cc20CompactClamp.comp continuous_snd)
    simpa [Function.uncurry] using hkernel.mul hf
  unfold cc20CompactIntervalOperator
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hintegrand (1 / 2 : ℝ) 2

noncomputable def cc20CompactContinuousOperator
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ContinuousMap CC20CompactInterval ℝ where
  toFun := cc20CompactIntervalOperator f
  continuous_toFun := continuous_cc20CompactIntervalOperator f

theorem cc20CompactContinuousOperator_add
    (f g : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactContinuousOperator (f + g) =
      cc20CompactContinuousOperator f + cc20CompactContinuousOperator g := by
  ext x
  have hf : IntervalIntegrable
      (fun y : ℝ => cc20RegularKernelReal (x.1, y) * f (cc20CompactClamp y))
      volume (1 / 2 : ℝ) 2 :=
    ((continuous_cc20RegularKernelReal.comp
      (continuous_const.prodMk continuous_id)).mul
        (f.continuous.comp continuous_cc20CompactClamp)).intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun y : ℝ => cc20RegularKernelReal (x.1, y) * g (cc20CompactClamp y))
      volume (1 / 2 : ℝ) 2 :=
    ((continuous_cc20RegularKernelReal.comp
      (continuous_const.prodMk continuous_id)).mul
        (g.continuous.comp continuous_cc20CompactClamp)).intervalIntegrable _ _
  simpa [cc20CompactContinuousOperator, cc20CompactIntervalOperator, mul_add]
    using intervalIntegral.integral_add hf hg

theorem cc20CompactContinuousOperator_smul
    (c : ℝ) (f : ContinuousMap CC20CompactInterval ℝ) :
    cc20CompactContinuousOperator (c • f) =
      c • cc20CompactContinuousOperator f := by
  ext x
  simp [cc20CompactContinuousOperator, cc20CompactIntervalOperator,
    mul_left_comm]

noncomputable def cc20CompactContinuousLinearMap :
    ContinuousMap CC20CompactInterval ℝ →ₗ[ℝ]
      ContinuousMap CC20CompactInterval ℝ where
  toFun := cc20CompactContinuousOperator
  map_add' := cc20CompactContinuousOperator_add
  map_smul' := cc20CompactContinuousOperator_smul

theorem norm_cc20CompactContinuousOperator_le
    (f : ContinuousMap CC20CompactInterval ℝ) :
    ‖cc20CompactContinuousOperator f‖ ≤
      ((3 / 2 : ℝ) * ‖cc20CompactRegularKernel‖) * ‖f‖ := by
  apply (ContinuousMap.norm_le (cc20CompactContinuousOperator f) (mul_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))).2
  intro x
  have hpoint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := 2)
    (C := ‖cc20CompactRegularKernel‖ * ‖f‖)
    (f := fun y : ℝ =>
      cc20RegularKernelReal (x.1, y) * f (cc20CompactClamp y))
    (fun y hy => by
      rw [Set.uIoc_of_le (by norm_num)] at hy
      have hyIcc : y ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨le_of_lt hy.1, hy.2⟩
      have hclamp : (cc20CompactClamp y).1 = y := by
        change min (max y (1 / 2 : ℝ)) 2 = y
        rw [max_eq_left hyIcc.1, min_eq_left hyIcc.2]
      have hkernel := cc20CompactRegularKernel.norm_coe_le_norm
        (x, cc20CompactClamp y)
      have hkernel' : ‖cc20RegularKernelReal (x.1, y)‖ ≤
          ‖cc20CompactRegularKernel‖ := by
        simpa [cc20CompactRegularKernel, hclamp] using hkernel
      rw [norm_mul]
      exact mul_le_mul
        hkernel'
        (f.norm_coe_le_norm (cc20CompactClamp y))
        (norm_nonneg _) (norm_nonneg _))
  simpa [cc20CompactContinuousOperator, cc20CompactIntervalOperator] using
    hpoint.trans_eq (by ring)

noncomputable def cc20CompactContinuousLinearOperator :
    ContinuousMap CC20CompactInterval ℝ →L[ℝ]
      ContinuousMap CC20CompactInterval ℝ :=
  cc20CompactContinuousLinearMap.mkContinuous
    ((3 / 2 : ℝ) * ‖cc20CompactRegularKernel‖)
    norm_cc20CompactContinuousOperator_le

end CC20Concrete
end Source
end ConnesWeilRH
