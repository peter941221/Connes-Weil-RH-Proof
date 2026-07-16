/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RootSandwichedTrace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuous moving root-sandwiched response

This module turns the Proof 308 algebraic time owner into a genuine continuous
finite-window family.  The time carrier is the compact interval `[0, 1]`; the
source-specific `E_alpha/R_alpha/K_prol` construction is still supplied by a
later module.  No trace identity or Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- Compact transport-time carrier used by the continuous finite-window owner. -/
abbrev cc20MovingTime := Set.Icc (0 : ℝ) 1

/-- Ambient Lebesgue measure pulled back to the compact transport-time carrier. -/
noncomputable abbrev cc20MovingTimeMeasure : Measure cc20MovingTime :=
  Measure.comap Subtype.val volume

instance cc20MovingTimeMeasure_isFinite : IsFiniteMeasure cc20MovingTimeMeasure where
  measure_univ_lt_top := by
    unfold cc20MovingTimeMeasure cc20MovingTime
    rw [
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume
        Set.univ,
      Set.image_univ, Subtype.range_coe_subtype]
    change volume (Set.Icc (0 : ℝ) 1) < ⊤
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

/-- Slice a continuous time/space family at one transport time. -/
noncomputable def cc20MovingSlice
    {X : Type*} [TopologicalSpace X]
    (family : ContinuousMap (cc20MovingTime × X) ℂ)
    (a : cc20MovingTime) : ContinuousMap X ℂ where
  toFun x := family (a, x)
  continuous_toFun := family.continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem cc20MovingSlice_apply
    {X : Type*} [TopologicalSpace X]
    (family : ContinuousMap (cc20MovingTime × X) ℂ)
    (a : cc20MovingTime) (x : X) :
    cc20MovingSlice family a x = family (a, x) :=
  rfl

noncomputable def cc20MovingRootSandwichedTwoPointScalar
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ)
    (a : cc20MovingTime) : ℂ :=
  (∫ y, ∫ x,
    conj (cc20WindowRootSandwichedKernel lambda hlambda
      (cc20MovingSlice leftRoots a)
      (cc20MovingSlice rightKernels a)
      (cc20MovingSlice rightRoots a) (y, x)) *
    cc20WindowRootSandwichedKernel lambda hlambda
      (cc20MovingSlice leftRoots a)
      (cc20MovingSlice leftKernels a)
      (cc20MovingSlice rightRoots a) (y, x)
    ∂cc20WindowMeasure lambda hlambda
    ∂cc20WindowMeasure lambda hlambda) -
    (2 : ℂ) *
      (∫ x, conj (cc20MovingSlice rightRoots a x) *
        cc20MovingSlice leftRoots a x
        ∂cc20WindowMeasure lambda hlambda)

noncomputable def cc20MovingRootSandwichedResponse
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda))
    (a : cc20MovingTime) : ℂ :=
  cc20WindowRootSandwichedResponse lambda hlambda
    (cc20MovingSlice leftRoots a)
    (cc20MovingSlice leftKernels a)
    (cc20MovingSlice rightRoots a)
    (cc20MovingSlice rightKernels a) basis

theorem cc20MovingRootSandwichedResponse_eq_twoPointScalar
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda))
    (a : cc20MovingTime) :
    cc20MovingRootSandwichedResponse lambda hlambda
        leftRoots rightRoots leftKernels rightKernels basis a =
      cc20MovingRootSandwichedTwoPointScalar lambda hlambda
        leftRoots rightRoots leftKernels rightKernels a := by
  unfold cc20MovingRootSandwichedResponse
  rw [cc20WindowRootSandwichedResponse_eq_doubleIntegral_sub_residue]
  unfold cc20MovingRootSandwichedTwoPointScalar
  rw [cc20WindowRootToLp_inner_eq_integral]

theorem continuous_cc20MovingRootSandwichedTwoPointScalar
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ) :
    Continuous (cc20MovingRootSandwichedTwoPointScalar lambda hlambda
      leftRoots rightRoots leftKernels rightKernels) := by
  let f : (cc20MovingTime × CC20WindowPoint lambda) →
      CC20WindowPoint lambda → ℂ := fun q x =>
    conj (cc20WindowRootSandwichedKernel lambda hlambda
      (cc20MovingSlice leftRoots q.1)
      (cc20MovingSlice rightKernels q.1)
      (cc20MovingSlice rightRoots q.1) (q.2, x)) *
    cc20WindowRootSandwichedKernel lambda hlambda
      (cc20MovingSlice leftRoots q.1)
      (cc20MovingSlice leftKernels q.1)
      (cc20MovingSlice rightRoots q.1) (q.2, x)
  have hf : Continuous f.uncurry := by
    dsimp [f, cc20MovingSlice]
    fun_prop
  have hinner : Continuous (fun q =>
      ∫ x, f q x ∂cc20WindowMeasure lambda hlambda) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := cc20WindowMeasure lambda hlambda)
        (f := f) hf isCompact_univ)
  let r : cc20MovingTime → CC20WindowPoint lambda → ℂ := fun a x =>
    conj (cc20MovingSlice rightRoots a x) * cc20MovingSlice leftRoots a x
  have hr : Continuous r.uncurry := by
    dsimp [r, cc20MovingSlice]
    fun_prop
  have hres : Continuous (fun a =>
      ∫ x, r a x ∂cc20WindowMeasure lambda hlambda) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := cc20WindowMeasure lambda hlambda)
        (f := r) hr isCompact_univ)
  have houter : Continuous (fun a =>
      ∫ y, ∫ x, f (a, y) x ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) := by
    let g : cc20MovingTime → CC20WindowPoint lambda → ℂ := fun a y =>
      ∫ x, f (a, y) x ∂cc20WindowMeasure lambda hlambda
    have hg : Continuous g.uncurry := by
      simpa only [Function.uncurry, g] using hinner
    simpa only [Measure.restrict_univ, g] using
      (continuous_parametric_integral_of_continuous
        (μ := cc20WindowMeasure lambda hlambda)
        (f := g) hg isCompact_univ)
  simpa only [cc20MovingRootSandwichedTwoPointScalar, f, r,
    Function.uncurry] using
    houter.sub (continuous_const.mul hres)

theorem continuous_cc20MovingRootSandwichedResponse
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    Continuous (cc20MovingRootSandwichedResponse lambda hlambda
      leftRoots rightRoots leftKernels rightKernels basis) := by
  apply (continuous_cc20MovingRootSandwichedTwoPointScalar
    lambda hlambda leftRoots rightRoots leftKernels rightKernels).congr
  intro a
  exact (cc20MovingRootSandwichedResponse_eq_twoPointScalar
    lambda hlambda leftRoots rightRoots leftKernels rightKernels basis a).symm

theorem integrable_cc20MovingRootSandwichedTwoPointScalar
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ) :
    Integrable (cc20MovingRootSandwichedTwoPointScalar lambda hlambda
      leftRoots rightRoots leftKernels rightKernels)
      cc20MovingTimeMeasure := by
  have hcontinuous := continuous_cc20MovingRootSandwichedTwoPointScalar
    lambda hlambda leftRoots rightRoots leftKernels rightKernels
  simpa only [Measure.restrict_univ] using
    (hcontinuous.continuousOn.integrableOn_compact
      (μ := cc20MovingTimeMeasure) isCompact_univ).integrable

theorem integrable_cc20MovingRootSandwichedResponse
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels :
      ContinuousMap
        (cc20MovingTime ×
          (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    Integrable (cc20MovingRootSandwichedResponse lambda hlambda
      leftRoots rightRoots leftKernels rightKernels basis)
      cc20MovingTimeMeasure := by
  have hcontinuous := continuous_cc20MovingRootSandwichedResponse
    lambda hlambda leftRoots rightRoots leftKernels rightKernels basis
  simpa only [Measure.restrict_univ] using
    (hcontinuous.continuousOn.integrableOn_compact
      (μ := cc20MovingTimeMeasure) isCompact_univ).integrable

end CC20Concrete
end Source
end ConnesWeilRH
