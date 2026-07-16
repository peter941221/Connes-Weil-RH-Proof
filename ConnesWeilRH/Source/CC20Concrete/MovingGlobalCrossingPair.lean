/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.MovingGlobalCrossing

/-!
# The moving forward/adjoint CC20 outer-crossing pair

This module adds the genuine Hilbert-space adjoint of the concrete crossing
from `MovingGlobalCrossing`.  It reads the reverse response back as the
conjugate boundary correlation and packages the forward and reverse branches
before any estimate is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- The response owned by the Hilbert-space adjoint of the concrete moving
crossing. -/
noncomputable def cc20MovingSingleCrossingAdjointResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) : ℂ :=
  inner ℂ ((testPath a).toLp 2)
    ((cc20SingleCrossingOperator (boundaryShift a)).adjoint
      ((testPath a).toLp 2))

/-- The reverse boundary correlation seen by the adjoint crossing. -/
noncomputable def cc20MovingSingleCrossingAdjointBoundaryIntegrand
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ)) :
    ContinuousMap (cc20MovingTime × ℝ) ℂ where
  toFun q := conj (testPath q.1 (q.2 + boundaryShift q.1)) *
    testPath q.1 q.2
  continuous_toFun := by
    change Continuous (fun (q : cc20MovingTime × ℝ) =>
      conj (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
        (testPath q.1) (q.2 + boundaryShift q.1)) *
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
        (testPath q.1) q.2)
    fun_prop

@[simp] theorem cc20MovingSingleCrossingAdjointBoundaryIntegrand_apply
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) (t : ℝ) :
    cc20MovingSingleCrossingAdjointBoundaryIntegrand
        boundaryShift testPath (a, t) =
      conj (testPath a (t + boundaryShift a)) * testPath a t :=
  rfl

theorem cc20MovingSingleCrossingAdjointResponse_eq_star
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) :
    cc20MovingSingleCrossingAdjointResponse boundaryShift testPath a =
      star (cc20MovingSingleCrossingResponse boundaryShift testPath a) := by
  let h : cc20GlobalLogCrossingL2 := (testPath a).toLp 2
  let crossing := cc20SingleCrossingOperator (boundaryShift a)
  change inner ℂ h (crossing.adjoint h) = star (inner ℂ h (crossing h))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (crossing h) h).symm

theorem cc20MovingSingleCrossingAdjointResponse_eq_boundaryIntegral
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a)
    (a : cc20MovingTime) :
    cc20MovingSingleCrossingAdjointResponse boundaryShift testPath a =
      ∫ t in (-boundaryShift a)..0,
        cc20MovingSingleCrossingAdjointBoundaryIntegrand
          boundaryShift testPath (a, t) := by
  rw [cc20MovingSingleCrossingAdjointResponse_eq_star]
  rw [cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    boundaryShift testPath hshift]
  rw [intervalIntegral.integral_of_le (neg_nonpos.mpr (hshift a))]
  rw [intervalIntegral.integral_of_le (neg_nonpos.mpr (hshift a))]
  change conj (∫ t in Set.Ioc (-boundaryShift a) 0,
      cc20MovingSingleCrossingBoundaryIntegrand
        boundaryShift testPath (a, t)) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [cc20MovingSingleCrossingBoundaryIntegrand_apply,
    cc20MovingSingleCrossingAdjointBoundaryIntegrand_apply,
    map_mul, starRingEnd_apply, star_star]
  exact mul_comm _ _

theorem continuous_cc20MovingSingleCrossingAdjointResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Continuous
      (cc20MovingSingleCrossingAdjointResponse boundaryShift testPath) := by
  have hforward := continuous_cc20MovingSingleCrossingResponse
    boundaryShift testPath hshift
  apply (Complex.continuous_conj.comp hforward).congr
  intro a
  exact (cc20MovingSingleCrossingAdjointResponse_eq_star
    boundaryShift testPath a).symm

theorem integrable_cc20MovingSingleCrossingAdjointResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Integrable
      (cc20MovingSingleCrossingAdjointResponse boundaryShift testPath)
      cc20MovingTimeMeasure := by
  have hcontinuous := continuous_cc20MovingSingleCrossingAdjointResponse
    boundaryShift testPath hshift
  simpa only [Measure.restrict_univ] using
    (hcontinuous.continuousOn.integrableOn_compact
      (μ := cc20MovingTimeMeasure) isCompact_univ).integrable

/-- The forward and adjoint outer-crossing responses, combined before any
absolute value or norm estimate. -/
noncomputable def cc20MovingSingleCrossingPairResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) : ℂ :=
  cc20MovingSingleCrossingResponse boundaryShift testPath a +
    cc20MovingSingleCrossingAdjointResponse boundaryShift testPath a

theorem cc20MovingSingleCrossingPairResponse_eq_two_re
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) :
    cc20MovingSingleCrossingPairResponse boundaryShift testPath a =
      ((2 * (cc20MovingSingleCrossingResponse
        boundaryShift testPath a).re : ℝ) : ℂ) := by
  rw [cc20MovingSingleCrossingPairResponse,
    cc20MovingSingleCrossingAdjointResponse_eq_star,
    Complex.star_def, Complex.add_conj]

theorem cc20MovingSingleCrossingPairResponse_im
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) :
    (cc20MovingSingleCrossingPairResponse
      boundaryShift testPath a).im = 0 := by
  rw [cc20MovingSingleCrossingPairResponse_eq_two_re]
  exact Complex.ofReal_im _

theorem cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a)
    (a : cc20MovingTime) :
    cc20MovingSingleCrossingPairResponse boundaryShift testPath a =
      ∫ t in (-boundaryShift a)..0,
        (cc20MovingSingleCrossingBoundaryIntegrand
            boundaryShift testPath (a, t) +
          cc20MovingSingleCrossingAdjointBoundaryIntegrand
            boundaryShift testPath (a, t)) := by
  rw [cc20MovingSingleCrossingPairResponse]
  rw [cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    boundaryShift testPath hshift]
  rw [cc20MovingSingleCrossingAdjointResponse_eq_boundaryIntegral
    boundaryShift testPath hshift]
  have hforward : IntervalIntegrable
      (fun t => cc20MovingSingleCrossingBoundaryIntegrand
        boundaryShift testPath (a, t)) volume (-boundaryShift a) 0 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hadjoint : IntervalIntegrable
      (fun t => cc20MovingSingleCrossingAdjointBoundaryIntegrand
        boundaryShift testPath (a, t)) volume (-boundaryShift a) 0 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hforward hadjoint]

theorem continuous_cc20MovingSingleCrossingPairResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Continuous (cc20MovingSingleCrossingPairResponse boundaryShift testPath) := by
  exact (continuous_cc20MovingSingleCrossingResponse
    boundaryShift testPath hshift).add
      (continuous_cc20MovingSingleCrossingAdjointResponse
        boundaryShift testPath hshift)

theorem integrable_cc20MovingSingleCrossingPairResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Integrable (cc20MovingSingleCrossingPairResponse boundaryShift testPath)
      cc20MovingTimeMeasure := by
  have hcontinuous := continuous_cc20MovingSingleCrossingPairResponse
    boundaryShift testPath hshift
  simpa only [Measure.restrict_univ] using
    (hcontinuous.continuousOn.integrableOn_compact
      (μ := cc20MovingTimeMeasure) isCompact_univ).integrable

theorem integral_cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    ∫ a, cc20MovingSingleCrossingPairResponse boundaryShift testPath a
        ∂cc20MovingTimeMeasure =
      ∫ a, (∫ t in (-boundaryShift a)..0,
        (cc20MovingSingleCrossingBoundaryIntegrand
            boundaryShift testPath (a, t) +
          cc20MovingSingleCrossingAdjointBoundaryIntegrand
            boundaryShift testPath (a, t)))
        ∂cc20MovingTimeMeasure := by
  apply integral_congr_ae
  filter_upwards with a
  exact cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
    boundaryShift testPath hshift a

end CC20Concrete
end Source
end ConnesWeilRH
