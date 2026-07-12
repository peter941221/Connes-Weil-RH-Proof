/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact-interval operator of the ordinary CC20 regular kernel candidate

This module constructs the integral operator carried by the same concrete
kernel used in `RegularKernelL2`.  Its domain and codomain are continuous real
functions.  No identification with the source CC20 operator or
Hilbert--Schmidt extension is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped Interval

theorem continuous_cc20SqrtIMap : Continuous cc20SqrtIMap := by
  exact (continuous_id.max continuous_const).subtype_mk _

theorem continuous_cc20RegularKernelReal : Continuous cc20RegularKernelReal := by
  have hpair : Continuous
      (fun p : ℝ × ℝ => (cc20SqrtIMap p.1, cc20SqrtIMap p.2)) :=
    (continuous_cc20SqrtIMap.comp continuous_fst).prodMk
      (continuous_cc20SqrtIMap.comp continuous_snd)
  exact Continuous.comp continuous_cc20RegularKernel hpair

noncomputable def cc20RegularKernelIntervalOperator
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (1 / 2 : ℝ)..2, cc20RegularKernelReal (x, y) * f y

theorem continuous_cc20RegularKernelIntervalIntegrand
    {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (Function.uncurry
      (fun x y : ℝ => cc20RegularKernelReal (x, y) * f y)) := by
  simpa [Function.uncurry] using
    continuous_cc20RegularKernelReal.mul (hf.comp continuous_snd)

theorem continuous_cc20RegularKernelIntervalOperator
    {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cc20RegularKernelIntervalOperator f) := by
  unfold cc20RegularKernelIntervalOperator
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_cc20RegularKernelIntervalIntegrand hf) (1 / 2 : ℝ) 2

noncomputable def cc20RegularKernelContinuousOperator
    (f : ContinuousMap ℝ ℝ) : ContinuousMap ℝ ℝ where
  toFun := cc20RegularKernelIntervalOperator f
  continuous_toFun := continuous_cc20RegularKernelIntervalOperator f.continuous

theorem cc20RegularKernelContinuousOperator_zero :
    cc20RegularKernelContinuousOperator 0 = 0 := by
  ext x
  simp [cc20RegularKernelContinuousOperator,
    cc20RegularKernelIntervalOperator]

theorem cc20RegularKernelContinuousOperator_add
    (f g : ContinuousMap ℝ ℝ) :
    cc20RegularKernelContinuousOperator (f + g) =
      cc20RegularKernelContinuousOperator f +
        cc20RegularKernelContinuousOperator g := by
  ext x
  have hf : IntervalIntegrable
      (fun y : ℝ => cc20RegularKernelReal (x, y) * f y) volume
      (1 / 2 : ℝ) 2 :=
    ((continuous_cc20RegularKernelReal.comp
      (continuous_const.prodMk continuous_id)).mul f.continuous).intervalIntegrable
        (1 / 2 : ℝ) 2
  have hg : IntervalIntegrable
      (fun y : ℝ => cc20RegularKernelReal (x, y) * g y) volume
      (1 / 2 : ℝ) 2 :=
    ((continuous_cc20RegularKernelReal.comp
      (continuous_const.prodMk continuous_id)).mul g.continuous).intervalIntegrable
        (1 / 2 : ℝ) 2
  simpa [cc20RegularKernelContinuousOperator,
    cc20RegularKernelIntervalOperator, mul_add] using
    intervalIntegral.integral_add hf hg

theorem cc20RegularKernelContinuousOperator_smul
    (c : ℝ) (f : ContinuousMap ℝ ℝ) :
    cc20RegularKernelContinuousOperator (c • f) =
      c • cc20RegularKernelContinuousOperator f := by
  ext x
  simp [cc20RegularKernelContinuousOperator,
    cc20RegularKernelIntervalOperator, intervalIntegral.integral_smul,
    mul_assoc, mul_left_comm]

noncomputable def cc20RegularKernelContinuousLinearMap :
    ContinuousMap ℝ ℝ →ₗ[ℝ] ContinuousMap ℝ ℝ where
  toFun := cc20RegularKernelContinuousOperator
  map_add' := cc20RegularKernelContinuousOperator_add
  map_smul' := cc20RegularKernelContinuousOperator_smul

end CC20Concrete
end Source
end ConnesWeilRH
