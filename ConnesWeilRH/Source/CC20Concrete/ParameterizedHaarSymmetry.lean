/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Symmetry of the parameterized CC20 regular-kernel operators

For every `lambda > 1`, the ordinary CC20 kernel is real and symmetric on the
exact source Haar space over `[1/lambda, lambda]`.  This module transports the
same-object kernel symmetry through the Haar integral and the complex `L2`
extension.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

theorem cc20WindowComplexRegularKernel_swap
    (lambda : ℝ) (hlambda : 1 < lambda)
    (p : CC20WindowPoint lambda × CC20WindowPoint lambda) :
    cc20WindowComplexRegularKernel lambda hlambda (p.2, p.1) =
      cc20WindowComplexRegularKernel lambda hlambda p := by
  change ((cc20RegularKernel
      (cc20WindowPositiveCoordinate lambda hlambda p.2,
        cc20WindowPositiveCoordinate lambda hlambda p.1) : ℝ) : ℂ) =
    ((cc20RegularKernel
      (cc20WindowPositiveCoordinate lambda hlambda p.1,
        cc20WindowPositiveCoordinate lambda hlambda p.2) : ℝ) : ℂ)
  exact congrArg (fun r : ℝ => (r : ℂ))
    (cc20RegularKernel_swap
      (cc20WindowPositiveCoordinate lambda hlambda p.1,
        cc20WindowPositiveCoordinate lambda hlambda p.2))

theorem integrable_cc20WindowHaarKernel_bilinear
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f g : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    Integrable
      (fun p : CC20WindowPoint lambda × CC20WindowPoint lambda =>
        conj (f p.2) *
          (cc20WindowComplexRegularKernel lambda hlambda p) * g p.1)
      ((cc20WindowHaarMeasure lambda hlambda).prod
        (cc20WindowHaarMeasure lambda hlambda)) := by
  have hc : Continuous
      (fun p : CC20WindowPoint lambda × CC20WindowPoint lambda =>
        conj (f p.2) *
          (cc20WindowComplexRegularKernel lambda hlambda p) * g p.1) := by
    have hf : Continuous
        (fun p : CC20WindowPoint lambda × CC20WindowPoint lambda =>
          conj (f p.2)) :=
      Complex.continuous_conj.comp (f.continuous.comp continuous_snd)
    have hk : Continuous
        (fun p : CC20WindowPoint lambda × CC20WindowPoint lambda =>
          cc20WindowComplexRegularKernel lambda hlambda p) :=
      (cc20WindowComplexRegularKernel lambda hlambda).continuous
    have hg : Continuous
        (fun p : CC20WindowPoint lambda × CC20WindowPoint lambda => g p.1) :=
      g.continuous.comp continuous_fst
    exact (hf.mul hk).mul hg
  simpa only [Measure.restrict_univ] using
    (hc.continuousOn.integrableOn_compact
      (μ := (cc20WindowHaarMeasure lambda hlambda).prod
        (cc20WindowHaarMeasure lambda hlambda))
      isCompact_univ).integrable

theorem cc20WindowSourceHaarAction_inner_symmetry_continuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f g : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    ∫ x, conj (cc20WindowSourceHaarAction lambda hlambda f x) * g x
        ∂cc20WindowHaarMeasure lambda hlambda =
      ∫ x, conj (f x) * cc20WindowSourceHaarAction lambda hlambda g x
        ∂cc20WindowHaarMeasure lambda hlambda := by
  have hbil := integrable_cc20WindowHaarKernel_bilinear
    lambda hlambda f g
  calc
    ∫ x, conj (cc20WindowSourceHaarAction lambda hlambda f x) * g x
        ∂cc20WindowHaarMeasure lambda hlambda =
        ∫ x, ∫ y, conj (f y) *
            cc20WindowComplexRegularKernel lambda hlambda (x, y) * g x
          ∂cc20WindowHaarMeasure lambda hlambda
          ∂cc20WindowHaarMeasure lambda hlambda := by
      apply integral_congr_ae
      filter_upwards with x
      unfold cc20WindowSourceHaarAction
      rw [← integral_conj, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      rw [map_mul]
      have hkernel_conj :
          conj (cc20WindowComplexRegularKernel lambda hlambda (x, y)) =
            cc20WindowComplexRegularKernel lambda hlambda (x, y) := by
        change conj ((cc20RegularKernel
            (cc20WindowPositiveCoordinate lambda hlambda x,
              cc20WindowPositiveCoordinate lambda hlambda y) : ℝ) : ℂ) =
          ((cc20RegularKernel
            (cc20WindowPositiveCoordinate lambda hlambda x,
              cc20WindowPositiveCoordinate lambda hlambda y) : ℝ) : ℂ)
        exact Complex.conj_ofReal _
      rw [hkernel_conj]
      ring
    _ = ∫ y, ∫ x, conj (f y) *
            cc20WindowComplexRegularKernel lambda hlambda (x, y) * g x
          ∂cc20WindowHaarMeasure lambda hlambda
          ∂cc20WindowHaarMeasure lambda hlambda :=
      integral_integral_swap hbil
    _ = ∫ y, conj (f y) * cc20WindowSourceHaarAction lambda hlambda g y
          ∂cc20WindowHaarMeasure lambda hlambda := by
      apply integral_congr_ae
      filter_upwards with y
      unfold cc20WindowSourceHaarAction
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [← cc20WindowComplexRegularKernel_swap lambda hlambda (x, y)]
      ring

theorem cc20WindowHaarComplexL2Operator_inner_symmetry_continuous
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f g : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    inner ℂ
        (cc20WindowHaarComplexL2Operator lambda hlambda
          ((ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ) f))
        ((ContinuousMap.toLp 2
          (cc20WindowHaarMeasure lambda hlambda) ℂ) g) =
      inner ℂ
        ((ContinuousMap.toLp 2
          (cc20WindowHaarMeasure lambda hlambda) ℂ) f)
        (cc20WindowHaarComplexL2Operator lambda hlambda
          ((ContinuousMap.toLp 2
            (cc20WindowHaarMeasure lambda hlambda) ℂ) g)) := by
  rw [cc20WindowHaarComplexL2Operator_apply,
    cc20WindowHaarComplexL2Operator_apply,
    ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  simpa only [cc20WindowHaarComplexKernelCoefficient_continuous_input,
    mul_comm] using
      cc20WindowSourceHaarAction_inner_symmetry_continuous
        lambda hlambda f g

theorem cc20WindowHaarComplexL2Operator_inner_symmetry
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u v : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    inner ℂ (cc20WindowHaarComplexL2Operator lambda hlambda u) v =
      inner ℂ u (cc20WindowHaarComplexL2Operator lambda hlambda v) := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal)) (μ := cc20WindowHaarMeasure lambda hlambda)
      (by norm_num)
  refine DenseRange.induction_on₂ hdense ?_ (fun f g => ?_) u v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact cc20WindowHaarComplexL2Operator_inner_symmetry_continuous
      lambda hlambda f g

theorem cc20WindowHaarComplexL2Operator_isSelfAdjoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsSelfAdjoint (cc20WindowHaarComplexL2Operator lambda hlambda) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  exact cc20WindowHaarComplexL2Operator_inner_symmetry lambda hlambda

end CC20Concrete
end Source
end ConnesWeilRH
