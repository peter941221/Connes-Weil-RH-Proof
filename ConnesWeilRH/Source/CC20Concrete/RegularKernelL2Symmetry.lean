/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelL2Holder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

theorem integrable_cc20CompactKernel_bilinear
    (f g : ContinuousMap CC20CompactInterval ℝ) :
    Integrable
      (fun p : CC20CompactInterval × CC20CompactInterval =>
        g p.1 * cc20CompactRegularKernel p * f p.2)
      (cc20CompactMeasure.prod cc20CompactMeasure) := by
  have hc : Continuous
      (fun p : CC20CompactInterval × CC20CompactInterval =>
        g p.1 * cc20CompactRegularKernel p * f p.2) := by
    exact (g.continuous.comp continuous_fst).mul
      cc20CompactRegularKernel.continuous |>.mul
      (f.continuous.comp continuous_snd)
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := cc20CompactMeasure.prod cc20CompactMeasure) isCompact_univ).integrable

theorem cc20CompactMeasure_inner_symmetry_continuous
    (f g : ContinuousMap CC20CompactInterval ℝ) :
    ∫ x, cc20CompactMeasureOperator f x * g x ∂cc20CompactMeasure =
      ∫ x, f x * cc20CompactMeasureOperator g x ∂cc20CompactMeasure := by
  have hbil := integrable_cc20CompactKernel_bilinear f g
  calc
    ∫ x, cc20CompactMeasureOperator f x * g x ∂cc20CompactMeasure =
        ∫ x, ∫ y, g x * cc20CompactRegularKernel (x, y) * f y
          ∂cc20CompactMeasure ∂cc20CompactMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      unfold cc20CompactMeasureOperator cc20CompactKernelSection
      rw [← integral_mul_const]
      congr 1
      funext y
      simp [cc20CompactRegularKernel]
      ring
    _ = ∫ y, ∫ x, g x * cc20CompactRegularKernel (x, y) * f y
          ∂cc20CompactMeasure ∂cc20CompactMeasure :=
      integral_integral_swap hbil
    _ = ∫ y, f y * cc20CompactMeasureOperator g y ∂cc20CompactMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      unfold cc20CompactMeasureOperator cc20CompactKernelSection
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [← cc20CompactRegularKernel_swap (x, y)]
      simp [cc20CompactRegularKernel]
      ring

theorem cc20CompactL2Operator_inner_symmetry_continuous
    (f g : ContinuousMap CC20CompactInterval ℝ) :
    inner ℝ
        (cc20CompactL2Operator
          ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) f))
        ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) g) =
      inner ℝ
        ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) f)
        (cc20CompactL2Operator
          ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) g)) := by
  rw [cc20CompactL2Operator_agrees_on_continuous,
    cc20CompactL2Operator_agrees_on_continuous]
  change inner ℝ
      ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ)
        (cc20CompactMeasureContinuousOperator f))
      ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) g) =
    inner ℝ
      ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ) f)
      ((ContinuousMap.toLp 2 cc20CompactMeasure ℝ)
        (cc20CompactMeasureContinuousOperator g))
  rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  simpa [cc20CompactMeasureContinuousOperator, mul_comm]
    using cc20CompactMeasure_inner_symmetry_continuous f g

theorem cc20CompactL2Operator_inner_symmetry
    (u v : Lp ℝ 2 cc20CompactMeasure) :
    inner ℝ (cc20CompactL2Operator u) v =
      inner ℝ u (cc20CompactL2Operator v) := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 cc20CompactMeasure ℝ) :=
    ContinuousMap.toLp_denseRange (E := ℝ) (𝕜 := ℝ)
      (p := (2 : ENNReal)) (μ := cc20CompactMeasure) (by norm_num)
  refine DenseRange.induction_on₂ hdense ?_ (fun f g => ?_) u v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact cc20CompactL2Operator_inner_symmetry_continuous f g

end CC20Concrete
end Source
end ConnesWeilRH
