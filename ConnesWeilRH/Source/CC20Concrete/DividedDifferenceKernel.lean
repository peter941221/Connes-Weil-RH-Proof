/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RootSandwichedTrace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous CC20 divided-difference kernels

The removable diagonal is represented by one object: the average of the
derivative along the segment from `t` to `s`.  This avoids an `if s = t`
definition and gives continuity before any off-diagonal algebra is used.
The source multiplier must provide a continuous derivative and a genuine
`HasDerivAt` proof; a bare quotient formula is not accepted as a witness.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped ComplexConjugate InnerProduct InnerProductSpace

/-- A source multiplier together with the regularity needed to remove the
divided-difference diagonal. -/
structure CC20DividedDifferenceData where
  value : ContinuousMap ℝ ℂ
  derivative : ContinuousMap ℝ ℂ
  hasDerivAt : ∀ x : ℝ, HasDerivAt (value : ℝ → ℂ) (derivative x) x

/-- Every complex Schwartz test function supplies the regularity witness
without an additional analytic premise. -/
noncomputable def cc20DividedDifferenceDataOfSchwartz
    (f : SchwartzMap ℝ ℂ) : CC20DividedDifferenceData where
  value :=
    { toFun := f
      continuous_toFun := f.continuous }
  derivative :=
    { toFun := SchwartzMap.derivCLM ℂ ℂ f
      continuous_toFun := (SchwartzMap.derivCLM ℂ ℂ f).continuous }
  hasDerivAt := by
    intro x
    simpa using f.hasDerivAt x

/-- The derivative averaged along the oriented segment `t..s`. -/
noncomputable def cc20SegmentAverageDerivative
    (derivative : ContinuousMap ℝ ℂ) : ContinuousMap (ℝ × ℝ) ℂ where
  toFun p := ∫ u in (0 : ℝ)..1, derivative (p.2 + u * (p.1 - p.2))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop

@[simp] theorem cc20SegmentAverageDerivative_apply
    (derivative : ContinuousMap ℝ ℂ) (p : ℝ × ℝ) :
    cc20SegmentAverageDerivative derivative p =
      ∫ u in (0 : ℝ)..1, derivative (p.2 + u * (p.1 - p.2)) :=
  rfl

theorem cc20SegmentAverageDerivative_diag
    (derivative : ContinuousMap ℝ ℂ) (t : ℝ) :
    cc20SegmentAverageDerivative derivative (t, t) = derivative t := by
  simp [cc20SegmentAverageDerivative]

theorem cc20SegmentAverageDerivative_smul_eq_sub
    (data : CC20DividedDifferenceData) (s t : ℝ) :
    (s - t) • cc20SegmentAverageDerivative data.derivative (s, t) =
      data.value s - data.value t := by
  have hcont : ContinuousOn
      (fun u : ℝ => data.derivative (t + u • (s - t))) (Icc 0 1) := by
    fun_prop
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivAt (data.value : ℝ → ℂ)
        (data.derivative (t + u • (s - t)))
        (t + u • (s - t)) := by
    intro u _hu
    exact data.hasDerivAt _
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := (data.value : ℝ → ℂ))
    (f' := fun x => data.derivative x)
    (z₀ := t) (z₁ := s - t) hcont hderiv
  simpa [cc20SegmentAverageDerivative, smul_eq_mul] using h

theorem cc20SegmentAverageDerivative_eq_dividedDifference
    (data : CC20DividedDifferenceData) {s t : ℝ} (hst : s ≠ t) :
    cc20SegmentAverageDerivative data.derivative (s, t) =
      (data.value s - data.value t) /
        ((s - t : ℝ) : ℂ) := by
  have hsub : (s - t : ℝ) ≠ 0 := sub_ne_zero.mpr hst
  have hsubC : ((s - t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsub
  apply (eq_div_iff hsubC).2
  have h := cc20SegmentAverageDerivative_smul_eq_sub data s t
  simpa [smul_eq_mul, mul_comm] using h

/-- The CC20 normalization `i / pi` applied to the continuous divided
difference. -/
noncomputable def cc20QuantizedDividedDifferenceKernel
    (data : CC20DividedDifferenceData) : ContinuousMap (ℝ × ℝ) ℂ where
  toFun p :=
    (Complex.I / (Real.pi : ℂ)) *
      cc20SegmentAverageDerivative data.derivative p
  continuous_toFun := by
    fun_prop

@[simp] theorem cc20QuantizedDividedDifferenceKernel_apply
    (data : CC20DividedDifferenceData) (p : ℝ × ℝ) :
    cc20QuantizedDividedDifferenceKernel data p =
      (Complex.I / (Real.pi : ℂ)) *
        cc20SegmentAverageDerivative data.derivative p :=
  rfl

theorem cc20QuantizedDividedDifferenceKernel_diag
    (data : CC20DividedDifferenceData) (t : ℝ) :
    cc20QuantizedDividedDifferenceKernel data (t, t) =
      (Complex.I / (Real.pi : ℂ)) * data.derivative t := by
  simp [cc20QuantizedDividedDifferenceKernel]

theorem cc20QuantizedDividedDifferenceKernel_offDiagonal
    (data : CC20DividedDifferenceData) {s t : ℝ} (hst : s ≠ t) :
    cc20QuantizedDividedDifferenceKernel data (s, t) =
      (Complex.I / (Real.pi : ℂ)) *
        ((data.value s - data.value t) /
          ((s - t : ℝ) : ℂ)) := by
  rw [cc20QuantizedDividedDifferenceKernel_apply,
    cc20SegmentAverageDerivative_eq_dividedDifference data hst]

/-- Restriction of the continuous quantized kernel to one CC20 Haar window. -/
noncomputable def cc20WindowQuantizedDividedDifferenceKernel
    (data : CC20DividedDifferenceData)
    (lambda : ℝ) (_hlambda : 1 < lambda) :
    ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ where
  toFun p :=
    cc20QuantizedDividedDifferenceKernel data (p.1.1, p.2.1)
  continuous_toFun := by
    exact (cc20QuantizedDividedDifferenceKernel data).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))

@[simp] theorem cc20WindowQuantizedDividedDifferenceKernel_apply
    (data : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (p : CC20WindowPoint lambda × CC20WindowPoint lambda) :
    cc20WindowQuantizedDividedDifferenceKernel data lambda hlambda p =
      cc20QuantizedDividedDifferenceKernel data (p.1.1, p.2.1) :=
  rfl

theorem cc20WindowQuantizedDividedDifferenceKernel_diag
    (data : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (t : CC20WindowPoint lambda) :
    cc20WindowQuantizedDividedDifferenceKernel data lambda hlambda (t, t) =
      (Complex.I / (Real.pi : ℂ)) * data.derivative t.1 := by
  rw [cc20WindowQuantizedDividedDifferenceKernel_apply,
    cc20QuantizedDividedDifferenceKernel_diag]

theorem cc20WindowQuantizedDividedDifferenceKernel_offDiagonal
    (data : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {p : CC20WindowPoint lambda × CC20WindowPoint lambda}
    (hne : p.1.1 ≠ p.2.1) :
    cc20WindowQuantizedDividedDifferenceKernel data lambda hlambda p =
      (Complex.I / (Real.pi : ℂ)) *
        ((data.value p.1.1 - data.value p.2.1) /
          ((p.1.1 - p.2.1 : ℝ) : ℂ)) := by
  rw [cc20WindowQuantizedDividedDifferenceKernel_apply,
    cc20QuantizedDividedDifferenceKernel_offDiagonal data hne]

theorem cc20WindowQuantizedDividedDifferenceKernel_constant_zero
    (data : CC20DividedDifferenceData)
    (hconstant : ∀ x : ℝ, data.derivative x = 0) :
    cc20QuantizedDividedDifferenceKernel data = 0 := by
  ext p
  simp [cc20QuantizedDividedDifferenceKernel, hconstant]

/-- The source-shaped divided-difference pair is immediately consumed by the
generic root-sandwiched `A†B` owner.  The moving E/R/K_prol equality is not
assumed here. -/
noncomputable def cc20WindowRootSandwichedDividedDifferencePairData
    (leftData rightData : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := cc20WindowSpace lambda hlambda) basis :=
  cc20WindowRootSandwichedPairData lambda hlambda
    leftRoot (cc20WindowQuantizedDividedDifferenceKernel leftData lambda hlambda)
    rightRoot (cc20WindowQuantizedDividedDifferenceKernel rightData lambda hlambda)
    basis

theorem cc20WindowRootSandwichedDividedDifferencePairData_traceProduct_isTraceClass
    (leftData rightData : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.IsTraceClassAlong basis
      (cc20WindowRootSandwichedDividedDifferencePairData
        leftData rightData lambda hlambda leftRoot rightRoot basis).traceProduct := by
  exact cc20WindowRootSandwichedPairData_traceProduct_isTraceClass
    lambda hlambda leftRoot
    (cc20WindowQuantizedDividedDifferenceKernel leftData lambda hlambda)
    rightRoot
    (cc20WindowQuantizedDividedDifferenceKernel rightData lambda hlambda)
    basis

/-- The divided-difference regular trace and the explicit source residue share
one scalar owner. -/
noncomputable def cc20WindowRootSandwichedDividedDifferenceResponse
    (leftData rightData : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) : ℂ :=
  cc20WindowRootSandwichedResponse lambda hlambda leftRoot
    (cc20WindowQuantizedDividedDifferenceKernel leftData lambda hlambda)
    rightRoot
    (cc20WindowQuantizedDividedDifferenceKernel rightData lambda hlambda)
    basis

/-- Pointwise factorization of the paired root sandwich.  It separates the
two root weights from the ordered divided-difference product and fixes all
conjugations before the continuous moving-projection bridge is attempted. -/
theorem cc20WindowRootSandwichedDividedDifference_pair_apply
    (leftData rightData : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (y x : CC20WindowPoint lambda) :
    conj (cc20WindowRootSandwichedKernel lambda hlambda leftRoot
        (cc20WindowQuantizedDividedDifferenceKernel rightData lambda hlambda)
        rightRoot (y, x)) *
      cc20WindowRootSandwichedKernel lambda hlambda leftRoot
        (cc20WindowQuantizedDividedDifferenceKernel leftData lambda hlambda)
        rightRoot (y, x) =
      (conj (leftRoot y) * leftRoot y) *
      (conj (rightRoot x) * rightRoot x) *
      conj (cc20WindowQuantizedDividedDifferenceKernel
        rightData lambda hlambda (y, x)) *
      cc20WindowQuantizedDividedDifferenceKernel
        leftData lambda hlambda (y, x) := by
  simp [cc20WindowRootSandwichedKernel_apply]
  ring

/-- Continuous Hardy two-point readback for the complete CC20 response.  The
regular trace is now an explicit ordered product of divided differences with
root weights, while the `-2` distributional residue remains visible. -/
theorem cc20WindowRootSandwichedDividedDifferenceResponse_eq_twoPoint
    (leftData rightData : CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    cc20WindowRootSandwichedDividedDifferenceResponse
        leftData rightData lambda hlambda leftRoot rightRoot basis =
      (∫ y, ∫ x,
        (conj (leftRoot y) * leftRoot y) *
        (conj (rightRoot x) * rightRoot x) *
        conj (cc20WindowQuantizedDividedDifferenceKernel
          rightData lambda hlambda (y, x)) *
        cc20WindowQuantizedDividedDifferenceKernel
          leftData lambda hlambda (y, x)
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
      (2 : ℂ) * inner ℂ
        (cc20WindowRootToLp lambda hlambda rightRoot)
        (cc20WindowRootToLp lambda hlambda leftRoot) := by
  unfold cc20WindowRootSandwichedDividedDifferenceResponse
  rw [cc20WindowRootSandwichedResponse_eq_doubleIntegral_sub_residue]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  exact cc20WindowRootSandwichedDividedDifference_pair_apply
    leftData rightData lambda hlambda leftRoot rightRoot y x

/-- Synchronized time integration of the divided-difference owner.  The full
root-weighted two-point expression and the `-2` residue stay in one Bochner
integrand; no branchwise or primewise absolute value is introduced. -/
theorem integral_cc20WindowRootSandwichedDividedDifferenceResponse_eq_integral_twoPoint
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (leftData rightData : α → CC20DividedDifferenceData)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots : α → ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    ∫ a, cc20WindowRootSandwichedDividedDifferenceResponse
        (leftData a) (rightData a) lambda hlambda
        (leftRoots a) (rightRoots a) basis ∂μ =
      ∫ a, ((∫ y, ∫ x,
        (conj (leftRoots a y) * leftRoots a y) *
        (conj (rightRoots a x) * rightRoots a x) *
        conj (cc20WindowQuantizedDividedDifferenceKernel
          (rightData a) lambda hlambda (y, x)) *
        cc20WindowQuantizedDividedDifferenceKernel
          (leftData a) lambda hlambda (y, x)
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
        (2 : ℂ) * inner ℂ
          (cc20WindowRootToLp lambda hlambda (rightRoots a))
          (cc20WindowRootToLp lambda hlambda (leftRoots a))) ∂μ := by
  apply integral_congr_ae
  filter_upwards with a
  exact cc20WindowRootSandwichedDividedDifferenceResponse_eq_twoPoint
    (leftData a) (rightData a) lambda hlambda
    (leftRoots a) (rightRoots a) basis

end CC20Concrete
end Source
end ConnesWeilRH
