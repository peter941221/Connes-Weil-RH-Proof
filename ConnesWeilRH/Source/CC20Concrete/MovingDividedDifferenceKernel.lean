/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.DividedDifferenceKernel
import ConnesWeilRH.Source.CC20Concrete.MovingRootSandwiched

/-!
# Continuous moving CC20 divided-difference kernels

This module instantiates the abstract moving root-sandwiched owner with the
CC20 divided-difference kernel.  Values and derivatives vary jointly
continuously in transport time and the real source coordinate.  The actual
moving `E_alpha/R_alpha/K_prol` identification remains a separate theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- A jointly continuous time family of source multipliers, together with the
pointwise derivative proof needed to remove every divided-difference diagonal. -/
structure CC20MovingDividedDifferenceData where
  value : ContinuousMap (cc20MovingTime × ℝ) ℂ
  derivative : ContinuousMap (cc20MovingTime × ℝ) ℂ
  hasDerivAt : ∀ (a : cc20MovingTime) (x : ℝ),
    HasDerivAt (fun y => value (a, y)) (derivative (a, x)) x

/-- Freeze one transport time to recover the static source contract. -/
noncomputable def CC20MovingDividedDifferenceData.at
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) : CC20DividedDifferenceData where
  value := cc20MovingSlice data.value a
  derivative := cc20MovingSlice data.derivative a
  hasDerivAt := data.hasDerivAt a

/-- Every static divided-difference witness gives a constant moving family. -/
noncomputable def CC20DividedDifferenceData.stationary
    (data : CC20DividedDifferenceData) : CC20MovingDividedDifferenceData where
  value :=
    { toFun := fun q => data.value q.2
      continuous_toFun := data.value.continuous.comp continuous_snd }
  derivative :=
    { toFun := fun q => data.derivative q.2
      continuous_toFun := data.derivative.continuous.comp continuous_snd }
  hasDerivAt := by
    intro _a x
    exact data.hasDerivAt x

/-- A continuous path in Schwartz space supplies a jointly continuous moving
divided-difference witness, including its derivative family. -/
noncomputable def cc20MovingDividedDifferenceDataOfSchwartzPath
    (path : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ)) :
    CC20MovingDividedDifferenceData where
  value :=
    { toFun := fun q => path q.1 q.2
      continuous_toFun := by
        change Continuous (fun (q : cc20MovingTime × ℝ) =>
          SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ (path q.1) q.2)
        fun_prop }
  derivative :=
    { toFun := fun q => SchwartzMap.derivCLM ℂ ℂ (path q.1) q.2
      continuous_toFun := by
        change Continuous (fun (q : cc20MovingTime × ℝ) =>
          SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
            (SchwartzMap.derivCLM ℂ ℂ (path q.1)) q.2)
        fun_prop }
  hasDerivAt := by
    intro a x
    simpa using (path a).hasDerivAt x

@[simp] theorem CC20MovingDividedDifferenceData.at_value_apply
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (x : ℝ) :
    (data.at a).value x = data.value (a, x) :=
  rfl

@[simp] theorem CC20MovingDividedDifferenceData.at_derivative_apply
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (x : ℝ) :
    (data.at a).derivative x = data.derivative (a, x) :=
  rfl

@[simp] theorem CC20DividedDifferenceData.stationary_at
    (data : CC20DividedDifferenceData) (a : cc20MovingTime) :
    data.stationary.at a = data := by
  cases data
  rfl

@[simp] theorem cc20MovingDividedDifferenceDataOfSchwartzPath_at
    (path : ContinuousMap cc20MovingTime (SchwartzMap ℝ ℂ))
    (a : cc20MovingTime) :
    (cc20MovingDividedDifferenceDataOfSchwartzPath path).at a =
      cc20DividedDifferenceDataOfSchwartz (path a) := by
  rfl

/-- Segment-average derivative with transport time retained as a coordinate. -/
noncomputable def cc20MovingSegmentAverageDerivative
    (data : CC20MovingDividedDifferenceData) :
    ContinuousMap (cc20MovingTime × (ℝ × ℝ)) ℂ where
  toFun q := ∫ u in (0 : ℝ)..1,
    data.derivative (q.1, q.2.2 + u * (q.2.1 - q.2.2))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop

@[simp] theorem cc20MovingSegmentAverageDerivative_apply
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (p : ℝ × ℝ) :
    cc20MovingSegmentAverageDerivative data (a, p) =
      cc20SegmentAverageDerivative (data.at a).derivative p :=
  rfl

theorem cc20MovingSegmentAverageDerivative_diag
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (t : ℝ) :
    cc20MovingSegmentAverageDerivative data (a, (t, t)) =
      data.derivative (a, t) := by
  rw [cc20MovingSegmentAverageDerivative_apply,
    cc20SegmentAverageDerivative_diag]
  rfl

theorem cc20MovingSegmentAverageDerivative_smul_eq_sub
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (s t : ℝ) :
    (s - t) • cc20MovingSegmentAverageDerivative data (a, (s, t)) =
      data.value (a, s) - data.value (a, t) := by
  simpa using cc20SegmentAverageDerivative_smul_eq_sub (data.at a) s t

theorem cc20MovingSegmentAverageDerivative_eq_dividedDifference
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) {s t : ℝ} (hst : s ≠ t) :
    cc20MovingSegmentAverageDerivative data (a, (s, t)) =
      (data.value (a, s) - data.value (a, t)) /
        ((s - t : ℝ) : ℂ) := by
  simpa using
    cc20SegmentAverageDerivative_eq_dividedDifference (data.at a) hst

/-- The jointly continuous moving CC20 kernel `i / pi * D_f`. -/
noncomputable def cc20MovingQuantizedDividedDifferenceKernel
    (data : CC20MovingDividedDifferenceData) :
    ContinuousMap (cc20MovingTime × (ℝ × ℝ)) ℂ where
  toFun q := (Complex.I / (Real.pi : ℂ)) *
    cc20MovingSegmentAverageDerivative data q
  continuous_toFun := by
    fun_prop

@[simp] theorem cc20MovingQuantizedDividedDifferenceKernel_apply
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (p : ℝ × ℝ) :
    cc20MovingQuantizedDividedDifferenceKernel data (a, p) =
      cc20QuantizedDividedDifferenceKernel (data.at a) p :=
  rfl

theorem cc20MovingQuantizedDividedDifferenceKernel_diag
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) (t : ℝ) :
    cc20MovingQuantizedDividedDifferenceKernel data (a, (t, t)) =
      (Complex.I / (Real.pi : ℂ)) * data.derivative (a, t) := by
  rw [cc20MovingQuantizedDividedDifferenceKernel_apply,
    cc20QuantizedDividedDifferenceKernel_diag]
  rfl

theorem cc20MovingQuantizedDividedDifferenceKernel_offDiagonal
    (data : CC20MovingDividedDifferenceData)
    (a : cc20MovingTime) {s t : ℝ} (hst : s ≠ t) :
    cc20MovingQuantizedDividedDifferenceKernel data (a, (s, t)) =
      (Complex.I / (Real.pi : ℂ)) *
        ((data.value (a, s) - data.value (a, t)) /
          ((s - t : ℝ) : ℂ)) := by
  simpa using
    cc20QuantizedDividedDifferenceKernel_offDiagonal (data.at a) hst

/-- Restrict the moving quantized kernel jointly to time and one CC20 window. -/
noncomputable def cc20MovingWindowQuantizedDividedDifferenceKernel
    (data : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (_hlambda : 1 < lambda) :
    ContinuousMap
      (cc20MovingTime ×
        (CC20WindowPoint lambda × CC20WindowPoint lambda)) ℂ where
  toFun q := cc20MovingQuantizedDividedDifferenceKernel data
    (q.1, (q.2.1.1, q.2.2.1))
  continuous_toFun := by
    fun_prop

@[simp] theorem cc20MovingWindowQuantizedDividedDifferenceKernel_apply
    (data : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (a : cc20MovingTime)
    (p : CC20WindowPoint lambda × CC20WindowPoint lambda) :
    cc20MovingWindowQuantizedDividedDifferenceKernel data lambda hlambda (a, p) =
      cc20WindowQuantizedDividedDifferenceKernel
        (data.at a) lambda hlambda p :=
  rfl

/-- The Proof 309 moving response instantiated by genuine moving CC20
divided-difference kernels. -/
noncomputable def cc20MovingRootSandwichedDividedDifferenceResponse
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda))
    (a : cc20MovingTime) : ℂ :=
  cc20MovingRootSandwichedResponse lambda hlambda leftRoots rightRoots
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      leftData lambda hlambda)
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      rightData lambda hlambda)
    basis a

theorem cc20MovingRootSandwichedDividedDifferenceResponse_eq_static
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda))
    (a : cc20MovingTime) :
    cc20MovingRootSandwichedDividedDifferenceResponse
        leftData rightData lambda hlambda leftRoots rightRoots basis a =
      cc20WindowRootSandwichedDividedDifferenceResponse
        (leftData.at a) (rightData.at a) lambda hlambda
        (cc20MovingSlice leftRoots a) (cc20MovingSlice rightRoots a) basis :=
  rfl

theorem continuous_cc20MovingRootSandwichedDividedDifferenceResponse
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    Continuous (cc20MovingRootSandwichedDividedDifferenceResponse
      leftData rightData lambda hlambda leftRoots rightRoots basis) := by
  exact continuous_cc20MovingRootSandwichedResponse lambda hlambda
    leftRoots rightRoots
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      leftData lambda hlambda)
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      rightData lambda hlambda)
    basis

theorem integrable_cc20MovingRootSandwichedDividedDifferenceResponse
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    Integrable (cc20MovingRootSandwichedDividedDifferenceResponse
      leftData rightData lambda hlambda leftRoots rightRoots basis)
      cc20MovingTimeMeasure := by
  exact integrable_cc20MovingRootSandwichedResponse lambda hlambda
    leftRoots rightRoots
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      leftData lambda hlambda)
    (cc20MovingWindowQuantizedDividedDifferenceKernel
      rightData lambda hlambda)
    basis

/-- Pointwise moving two-point readback with the source residue kept in the
same scalar. -/
theorem cc20MovingRootSandwichedDividedDifferenceResponse_eq_twoPoint
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda))
    (a : cc20MovingTime) :
    cc20MovingRootSandwichedDividedDifferenceResponse
        leftData rightData lambda hlambda leftRoots rightRoots basis a =
      (∫ y, ∫ x,
        (conj (leftRoots (a, y)) * leftRoots (a, y)) *
        (conj (rightRoots (a, x)) * rightRoots (a, x)) *
        conj (cc20MovingWindowQuantizedDividedDifferenceKernel
          rightData lambda hlambda (a, (y, x))) *
        cc20MovingWindowQuantizedDividedDifferenceKernel
          leftData lambda hlambda (a, (y, x))
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
      (2 : ℂ) * inner ℂ
        (cc20WindowRootToLp lambda hlambda (cc20MovingSlice rightRoots a))
        (cc20WindowRootToLp lambda hlambda (cc20MovingSlice leftRoots a)) := by
  rw [cc20MovingRootSandwichedDividedDifferenceResponse_eq_static,
    cc20WindowRootSandwichedDividedDifferenceResponse_eq_twoPoint]
  rfl

/-- Time-integrated readback of the complete moving divided-difference
response.  The regular two-point term and the explicit residue remain inside
one Bochner integrand. -/
theorem integral_cc20MovingRootSandwichedDividedDifferenceResponse_eq_twoPoint
    (leftData rightData : CC20MovingDividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots :
      ContinuousMap (cc20MovingTime × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    ∫ a, cc20MovingRootSandwichedDividedDifferenceResponse
        leftData rightData lambda hlambda leftRoots rightRoots basis a
        ∂cc20MovingTimeMeasure =
      ∫ a, ((∫ y, ∫ x,
        (conj (leftRoots (a, y)) * leftRoots (a, y)) *
        (conj (rightRoots (a, x)) * rightRoots (a, x)) *
        conj (cc20MovingWindowQuantizedDividedDifferenceKernel
          rightData lambda hlambda (a, (y, x))) *
        cc20MovingWindowQuantizedDividedDifferenceKernel
          leftData lambda hlambda (a, (y, x))
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
        (2 : ℂ) * inner ℂ
          (cc20WindowRootToLp lambda hlambda (cc20MovingSlice rightRoots a))
          (cc20WindowRootToLp lambda hlambda (cc20MovingSlice leftRoots a)))
        ∂cc20MovingTimeMeasure := by
  apply integral_congr_ae
  filter_upwards with a
  exact cc20MovingRootSandwichedDividedDifferenceResponse_eq_twoPoint
    leftData rightData lambda hlambda leftRoots rightRoots basis a

end CC20Concrete
end Source
end ConnesWeilRH
