/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Symmetry of the CC20 regular kernel on the source Haar space

The ordinary CC20 kernel is real and symmetric. This module transports that
same-object symmetry through the exact multiplicative Haar measure and the
complex `L2` extension.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

theorem integrable_cc20CompactHaarKernel_bilinear
    (f g : ContinuousMap CC20CompactInterval ℂ) :
    Integrable
      (fun p : CC20CompactInterval × CC20CompactInterval =>
        conj (f p.2) * (cc20CompactRegularKernel p : ℂ) * g p.1)
      (cc20CompactHaarMeasure.prod cc20CompactHaarMeasure) := by
  have hc : Continuous
      (fun p : CC20CompactInterval × CC20CompactInterval =>
        conj (f p.2) * (cc20CompactRegularKernel p : ℂ) * g p.1) := by
    have hf : Continuous (fun p : CC20CompactInterval × CC20CompactInterval =>
        conj (f p.2)) :=
      Complex.continuous_conj.comp (f.continuous.comp continuous_snd)
    have hk : Continuous (fun p : CC20CompactInterval × CC20CompactInterval =>
        (cc20CompactRegularKernel p : ℂ)) :=
      Complex.continuous_ofReal.comp cc20CompactRegularKernel.continuous
    have hg : Continuous (fun p : CC20CompactInterval × CC20CompactInterval =>
        g p.1) := g.continuous.comp continuous_fst
    exact (hf.mul hk).mul hg
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := cc20CompactHaarMeasure.prod cc20CompactHaarMeasure)
      isCompact_univ).integrable

theorem cc20CompactSourceHaarAction_inner_symmetry_continuous
    (f g : ContinuousMap CC20CompactInterval ℂ) :
    ∫ x, conj (cc20CompactSourceHaarAction f x) * g x
        ∂cc20CompactHaarMeasure =
      ∫ x, conj (f x) * cc20CompactSourceHaarAction g x
        ∂cc20CompactHaarMeasure := by
  have hbil := integrable_cc20CompactHaarKernel_bilinear f g
  calc
    ∫ x, conj (cc20CompactSourceHaarAction f x) * g x
        ∂cc20CompactHaarMeasure =
        ∫ x, ∫ y, conj (f y) *
            (cc20CompactRegularKernel (x, y) : ℂ) * g x
          ∂cc20CompactHaarMeasure ∂cc20CompactHaarMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      unfold cc20CompactSourceHaarAction
      rw [← integral_conj, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      rw [map_mul, Complex.conj_ofReal]
      ring
    _ = ∫ y, ∫ x, conj (f y) *
            (cc20CompactRegularKernel (x, y) : ℂ) * g x
          ∂cc20CompactHaarMeasure ∂cc20CompactHaarMeasure :=
      integral_integral_swap hbil
    _ = ∫ y, conj (f y) * cc20CompactSourceHaarAction g y
          ∂cc20CompactHaarMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      unfold cc20CompactSourceHaarAction
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [← cc20CompactRegularKernel_swap (x, y)]
      ring

theorem cc20CompactHaarComplexL2Operator_inner_symmetry_continuous
    (f g : ContinuousMap CC20CompactInterval ℂ) :
    inner ℂ
        (cc20CompactHaarComplexL2Operator
          ((ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) f))
        ((ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) g) =
      inner ℂ
        ((ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) f)
        (cc20CompactHaarComplexL2Operator
          ((ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) g)) := by
  rw [cc20CompactHaarComplexL2Operator_apply,
    cc20CompactHaarComplexL2Operator_apply,
    ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  simpa only [cc20CompactHaarComplexKernelCoefficient_continuous_input, mul_comm]
    using cc20CompactSourceHaarAction_inner_symmetry_continuous f g

theorem cc20CompactHaarComplexL2Operator_inner_symmetry
    (u v : Lp ℂ 2 cc20CompactHaarMeasure) :
    inner ℂ (cc20CompactHaarComplexL2Operator u) v =
      inner ℂ u (cc20CompactHaarComplexL2Operator v) := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal)) (μ := cc20CompactHaarMeasure) (by norm_num)
  refine DenseRange.induction_on₂ hdense ?_ (fun f g => ?_) u v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact cc20CompactHaarComplexL2Operator_inner_symmetry_continuous f g

end CC20Concrete
end Source
end ConnesWeilRH
