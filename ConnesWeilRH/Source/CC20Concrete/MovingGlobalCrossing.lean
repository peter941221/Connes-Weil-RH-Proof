/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalCrossingKernelBridge
import ConnesWeilRH.Source.CC20Concrete.MovingRootSandwiched

/-!
# A moving producer for the concrete CC20 half-line crossing

This module lifts the existing concrete `cc20SingleCrossingOperator` boundary
identity to a continuous transport-time family.  It closes one genuine outer
crossing branch, while deliberately leaving the Sonin `R` and prolate
`K_prol` same-object identification open.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- The concrete crossing response of a moving Schwartz test and boundary
translation. -/
noncomputable def cc20MovingSingleCrossingResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) : ℂ :=
  inner ℂ ((testPath a).toLp 2)
    (cc20SingleCrossingOperator (boundaryShift a)
      ((testPath a).toLp 2))

/-- The jointly continuous integrand seen on the concrete crossing boundary. -/
noncomputable def cc20MovingSingleCrossingBoundaryIntegrand
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ)) :
    ContinuousMap (cc20MovingTime × ℝ) ℂ where
  toFun q := conj (testPath q.1 q.2) *
    testPath q.1 (q.2 + boundaryShift q.1)
  continuous_toFun := by
    change Continuous (fun (q : cc20MovingTime × ℝ) =>
      conj (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
        (testPath q.1) q.2) *
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
        (testPath q.1) (q.2 + boundaryShift q.1))
    fun_prop

@[simp] theorem cc20MovingSingleCrossingBoundaryIntegrand_apply
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) (t : ℝ) :
    cc20MovingSingleCrossingBoundaryIntegrand boundaryShift testPath (a, t) =
      conj (testPath a t) * testPath a (t + boundaryShift a) :=
  rfl

theorem cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a)
    (a : cc20MovingTime) :
    cc20MovingSingleCrossingResponse boundaryShift testPath a =
      ∫ t in (-boundaryShift a)..0,
        cc20MovingSingleCrossingBoundaryIntegrand boundaryShift testPath (a, t) := by
  unfold cc20MovingSingleCrossingResponse
  rw [cc20SingleCrossingOperator_schwartz_inner_eq_boundary_integral
    (testPath a) (boundaryShift a) (hshift a)]
  unfold cc20CrossingBoundaryInterval
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le
    (neg_nonpos.mpr (hshift a))]
  rfl

theorem continuous_cc20MovingSingleCrossingResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Continuous (cc20MovingSingleCrossingResponse boundaryShift testPath) := by
  let f := cc20MovingSingleCrossingBoundaryIntegrand boundaryShift testPath
  have hprimitive : Continuous (fun a =>
      ∫ t in (0 : ℝ)..(-boundaryShift a), f (a, t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun a t => f (a, t))
      (s := fun a => -boundaryShift a)
    · simpa only [Function.uncurry] using f.continuous
    · fun_prop
  have hboundary : Continuous (fun a =>
      ∫ t in (-boundaryShift a)..0, f (a, t)) := by
    convert hprimitive.neg using 1
    funext a
    rw [intervalIntegral.integral_symm]
  apply hboundary.congr
  intro a
  exact (cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    boundaryShift testPath hshift a).symm

theorem integrable_cc20MovingSingleCrossingResponse
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    Integrable (cc20MovingSingleCrossingResponse boundaryShift testPath)
      cc20MovingTimeMeasure := by
  have hcontinuous := continuous_cc20MovingSingleCrossingResponse
    boundaryShift testPath hshift
  simpa only [Measure.restrict_univ] using
    (hcontinuous.continuousOn.integrableOn_compact
      (μ := cc20MovingTimeMeasure) isCompact_univ).integrable

theorem integral_cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    (boundaryShift : ContinuousMap cc20MovingTime ℝ)
    (testPath : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (hshift : ∀ a : cc20MovingTime, 0 ≤ boundaryShift a) :
    ∫ a, cc20MovingSingleCrossingResponse boundaryShift testPath a
        ∂cc20MovingTimeMeasure =
      ∫ a, (∫ t in (-boundaryShift a)..0,
        cc20MovingSingleCrossingBoundaryIntegrand boundaryShift testPath (a, t))
        ∂cc20MovingTimeMeasure := by
  apply integral_congr_ae
  filter_upwards with a
  exact cc20MovingSingleCrossingResponse_eq_boundaryIntegral
    boundaryShift testPath hshift a

end CC20Concrete
end Source
end ConnesWeilRH
