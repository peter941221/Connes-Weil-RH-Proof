/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelCompactMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Prod

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

noncomputable def cc20CompactKernelSection
    (x : CC20CompactInterval) : ContinuousMap CC20CompactInterval ℝ where
  toFun y := cc20RegularKernelReal (x.1, y.1)
  continuous_toFun := continuous_cc20RegularKernelReal.comp
    ((continuous_const.comp continuous_subtype_val).prodMk continuous_subtype_val)

theorem cc20SqrtIMap_subtype_val (x : CC20CompactInterval) :
    cc20SqrtIMap x.1 = ⟨x.1, lt_of_lt_of_le (by norm_num) x.2.1⟩ := by
  apply Subtype.ext
  change max x.1 (1 / 2 : ℝ) = x.1
  exact max_eq_left x.2.1

theorem cc20CompactRegularKernel_swap
    (p : CC20CompactInterval × CC20CompactInterval) :
    cc20CompactRegularKernel (p.2, p.1) = cc20CompactRegularKernel p := by
  unfold cc20CompactRegularKernel cc20RegularKernelReal
  change cc20RegularKernel (cc20SqrtIMap p.2.1, cc20SqrtIMap p.1.1) =
    cc20RegularKernel (cc20SqrtIMap p.1.1, cc20SqrtIMap p.2.1)
  rw [cc20SqrtIMap_subtype_val p.1, cc20SqrtIMap_subtype_val p.2]
  exact cc20RegularKernel_swap
    (⟨p.1.1, lt_of_lt_of_le (by norm_num) p.1.2.1⟩,
      ⟨p.2.1, lt_of_lt_of_le (by norm_num) p.2.2.1⟩)

theorem cc20CompactKernelSection_memLp
    (x : CC20CompactInterval) :
    MemLp (cc20CompactKernelSection x) 2 cc20CompactMeasure := by
  exact ContinuousMap.memLp cc20CompactMeasure ℝ (cc20CompactKernelSection x)

theorem cc20CompactContinuousFunction_memLp
    (f : ContinuousMap CC20CompactInterval ℝ) :
    MemLp f 2 cc20CompactMeasure := by
  exact ContinuousMap.memLp cc20CompactMeasure ℝ f

theorem cc20CompactKernelSection_norm_bound
    (x : CC20CompactInterval) :
    ‖cc20CompactKernelSection x‖ ≤ ‖cc20CompactRegularKernel‖ := by
  apply (ContinuousMap.norm_le (cc20CompactKernelSection x) (norm_nonneg _)).2
  intro y
  exact cc20CompactRegularKernel.norm_coe_le_norm (x, y)

theorem cc20CompactRegularKernel_memLp_two :
    MemLp cc20CompactRegularKernel 2
      (cc20CompactMeasure.prod cc20CompactMeasure) := by
  exact ContinuousMap.memLp (cc20CompactMeasure.prod cc20CompactMeasure) ℝ
    cc20CompactRegularKernel

theorem integrable_cc20CompactRegularKernel_norm_sq :
    Integrable (fun p => ‖cc20CompactRegularKernel p‖ ^ 2)
      (cc20CompactMeasure.prod cc20CompactMeasure) := by
  have hmem := cc20CompactRegularKernel_memLp_two
  simpa [Real.norm_eq_abs] using hmem.integrable_norm_rpow (by norm_num)

theorem cc20CompactRegularKernel_norm_sq_fubini :
    (∫ x, ∫ y, ‖cc20CompactRegularKernel (x, y)‖ ^ 2
        ∂cc20CompactMeasure ∂cc20CompactMeasure) =
      ∫ p, ‖cc20CompactRegularKernel p‖ ^ 2
        ∂(cc20CompactMeasure.prod cc20CompactMeasure) := by
  exact integral_integral integrable_cc20CompactRegularKernel_norm_sq

end CC20Concrete
end Source
end ConnesWeilRH
