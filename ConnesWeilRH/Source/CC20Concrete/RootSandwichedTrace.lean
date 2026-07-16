/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarL2

/-!
# Root-sandwiched finite-window trace data

This module isolates the first analytic leg of the Proof 305 bridge.  A
continuous regularized kernel on the compact source window is sandwiched by
two continuous roots and then packaged as an actual Hilbert--Schmidt pair.
The resulting `A†B` product has a legal diagonal trace.  The distributional
`-2` residue is kept as a separate scalar pairing; it is never encoded as a
continuous kernel.

The module deliberately does not claim that a supplied kernel is the CC20
quantized commutator off the diagonal.  That source identification is the
remaining Proof 305 premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace

noncomputable abbrev cc20WindowMeasure (lambda : ℝ) (hlambda : 1 < lambda) :=
  cc20WindowHaarMeasure lambda hlambda

noncomputable abbrev cc20WindowSpace (lambda : ℝ) (hlambda : 1 < lambda) :=
  Lp ℂ 2 (cc20WindowMeasure lambda hlambda)

/-- A root-sandwiched version of a kernel `K(y,x)`.  The first root belongs to
the output variable and is conjugated, while the second belongs to the input
variable. -/
noncomputable def cc20WindowRootSandwichedKernel
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (kernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ where
  toFun p := conj (leftRoot p.1) * kernel p * rightRoot p.2
  continuous_toFun := by
    exact
      ((Complex.continuous_conj.comp
          (leftRoot.continuous.comp continuous_fst)).mul kernel.continuous).mul
        (rightRoot.continuous.comp continuous_snd)

@[simp] theorem cc20WindowRootSandwichedKernel_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (kernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (p : CC20WindowPoint lambda × CC20WindowPoint lambda) :
    cc20WindowRootSandwichedKernel lambda hlambda leftRoot kernel rightRoot p =
      conj (leftRoot p.1) * kernel p * rightRoot p.2 :=
  rfl

/-- The continuous root viewed as an `L2` vector on the same Haar window. -/
noncomputable def cc20WindowRootToLp
    (lambda : ℝ) (hlambda : 1 < lambda)
    (root : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    cc20WindowSpace lambda hlambda :=
  ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ root

theorem cc20WindowRootToLp_inner_eq_integral
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    inner ℂ (cc20WindowRootToLp lambda hlambda leftRoot)
        (cc20WindowRootToLp lambda hlambda rightRoot) =
      ∫ x, conj (leftRoot x) * rightRoot x
        ∂cc20WindowMeasure lambda hlambda := by
  change inner ℂ
      (ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ leftRoot)
      (ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ rightRoot) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The actual continuous-kernel operator attached to a root sandwich. -/
noncomputable def cc20WindowRootSandwichedOperator
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (kernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ) :
    cc20WindowSpace lambda hlambda →L[ℂ] cc20WindowSpace lambda hlambda :=
  ContinuousKernelHilbertSchmidt.operator
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowRootSandwichedKernel lambda hlambda leftRoot kernel rightRoot)

theorem cc20WindowRootSandwichedOperator_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (kernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (u : cc20WindowSpace lambda hlambda) :
    cc20WindowRootSandwichedOperator lambda hlambda leftRoot kernel rightRoot u =
      ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ
        (ContinuousKernelHilbertSchmidt.coefficient
          (cc20WindowMeasure lambda hlambda)
          (cc20WindowRootSandwichedKernel lambda hlambda leftRoot kernel rightRoot)
          u) :=
  rfl

/-- Two root-sandwiched continuous kernels packaged as one trace-product
owner.  Keeping the two factors separate preserves the legal `A†B` route. -/
noncomputable def cc20WindowRootSandwichedPairData
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := cc20WindowSpace lambda hlambda) basis :=
  ContinuousKernelHilbertSchmidt.pairData
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowRootSandwichedKernel lambda hlambda leftRoot leftKernel rightRoot)
    (cc20WindowRootSandwichedKernel lambda hlambda leftRoot rightKernel rightRoot)
    basis

theorem cc20WindowRootSandwichedPairData_traceProduct_isTraceClass
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.IsTraceClassAlong basis
      (cc20WindowRootSandwichedPairData lambda hlambda
        leftRoot leftKernel rightRoot rightKernel basis).traceProduct := by
  exact PositiveTrace.BasisHilbertSchmidtPairData.traceProduct_isTraceClassAlong _

theorem cc20WindowRootSandwichedPairData_trace_eq_integral
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.ordinaryTraceAlong basis
        (cc20WindowRootSandwichedPairData lambda hlambda
          leftRoot leftKernel rightRoot rightKernel basis).traceProduct =
      ∫ y, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (cc20WindowMeasure lambda hlambda)
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot rightKernel rightRoot) y)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (cc20WindowMeasure lambda hlambda)
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot leftKernel rightRoot) y)
        ∂cc20WindowMeasure lambda hlambda := by
  apply ContinuousKernelHilbertSchmidt.pairData_trace_eq_kernel_inner
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowMeasure lambda hlambda)
    (cc20WindowRootSandwichedKernel lambda hlambda
      leftRoot leftKernel rightRoot)
    (cc20WindowRootSandwichedKernel lambda hlambda
      leftRoot rightKernel rightRoot)
    basis
  · intro i
    exact ContinuousKernelHilbertSchmidt.coefficient_inner_integrable
      (cc20WindowMeasure lambda hlambda)
      (cc20WindowMeasure lambda hlambda)
      (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot leftKernel rightRoot)
      (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot rightKernel rightRoot)
      basis i
  · exact ContinuousKernelHilbertSchmidt.coefficient_inner_integral_norm_summable
      (cc20WindowMeasure lambda hlambda)
      (cc20WindowMeasure lambda hlambda)
      (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot leftKernel rightRoot)
      (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot rightKernel rightRoot)
      basis

/-- The section-inner-product trace readback written as an actual two-point
integral.  This is the continuous scalar interface used by Hardy
divided-difference identities: no basis vectors remain on the right-hand
side. -/
theorem cc20WindowRootSandwichedPairData_trace_eq_doubleIntegral
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.ordinaryTraceAlong basis
        (cc20WindowRootSandwichedPairData lambda hlambda
          leftRoot leftKernel rightRoot rightKernel basis).traceProduct =
      ∫ y, ∫ x,
        conj (cc20WindowRootSandwichedKernel lambda hlambda
          leftRoot rightKernel rightRoot (y, x)) *
        cc20WindowRootSandwichedKernel lambda hlambda
          leftRoot leftKernel rightRoot (y, x)
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda := by
  rw [cc20WindowRootSandwichedPairData_trace_eq_integral]
  apply integral_congr_ae
  filter_upwards with y
  change inner ℂ
      (ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot rightKernel rightRoot) y))
      (ContinuousMap.toLp 2 (cc20WindowMeasure lambda hlambda) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot leftKernel rightRoot) y)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  change
    cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot leftKernel rightRoot (y, x) *
      conj (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot rightKernel rightRoot (y, x)) =
    conj (cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot rightKernel rightRoot (y, x)) *
      cc20WindowRootSandwichedKernel lambda hlambda
        leftRoot leftKernel rightRoot (y, x)
  ring

/-- The regular trace and the explicit CC20 residue are one scalar owner. -/
noncomputable def cc20WindowRootSandwichedResponse
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) : ℂ :=
  PositiveTrace.ordinaryTraceAlong basis
      (cc20WindowRootSandwichedPairData lambda hlambda
        leftRoot leftKernel rightRoot rightKernel basis).traceProduct -
    (2 : ℂ) * inner ℂ
      (cc20WindowRootToLp lambda hlambda rightRoot)
      (cc20WindowRootToLp lambda hlambda leftRoot)

theorem cc20WindowRootSandwichedResponse_eq_integral_sub_residue
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    cc20WindowRootSandwichedResponse lambda hlambda
        leftRoot leftKernel rightRoot rightKernel basis =
      (∫ y, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (cc20WindowMeasure lambda hlambda)
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot rightKernel rightRoot) y)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (cc20WindowMeasure lambda hlambda)
          (cc20WindowRootSandwichedKernel lambda hlambda
            leftRoot leftKernel rightRoot) y)
        ∂cc20WindowMeasure lambda hlambda) -
      (2 : ℂ) * inner ℂ
        (cc20WindowRootToLp lambda hlambda rightRoot)
        (cc20WindowRootToLp lambda hlambda leftRoot) := by
  unfold cc20WindowRootSandwichedResponse
  rw [cc20WindowRootSandwichedPairData_trace_eq_integral
    lambda hlambda leftRoot leftKernel rightRoot rightKernel basis]

/-- The complete regular-plus-residue response on the explicit two-point
kernel.  The distributional atom remains a separate scalar after the regular
trace has been expanded. -/
theorem cc20WindowRootSandwichedResponse_eq_doubleIntegral_sub_residue
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    (rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    (rightKernel : ContinuousMap
      (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    cc20WindowRootSandwichedResponse lambda hlambda
        leftRoot leftKernel rightRoot rightKernel basis =
      (∫ y, ∫ x,
        conj (cc20WindowRootSandwichedKernel lambda hlambda
          leftRoot rightKernel rightRoot (y, x)) *
        cc20WindowRootSandwichedKernel lambda hlambda
          leftRoot leftKernel rightRoot (y, x)
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
      (2 : ℂ) * inner ℂ
        (cc20WindowRootToLp lambda hlambda rightRoot)
        (cc20WindowRootToLp lambda hlambda leftRoot) := by
  unfold cc20WindowRootSandwichedResponse
  rw [cc20WindowRootSandwichedPairData_trace_eq_doubleIntegral
    lambda hlambda leftRoot leftKernel rightRoot rightKernel basis]

/-- A synchronized family of root-sandwiched responses can be integrated
without splitting the regular trace from the explicit residue.  The theorem
is intentionally pointwise in the time parameter: source modules must still
prove the measurability and integrability of their moving `E/R/K_prol` family.
Keeping the subtraction inside the integrand preserves the signed owner before
any estimate. -/
theorem integral_cc20WindowRootSandwichedResponse_eq_integral_doubleIntegral_sub_residue
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoots rightRoots : α → ContinuousMap (CC20WindowPoint lambda) ℂ)
    (leftKernels rightKernels : α →
      ContinuousMap (CC20WindowPoint lambda × CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    ∫ a, cc20WindowRootSandwichedResponse lambda hlambda
        (leftRoots a) (leftKernels a) (rightRoots a) (rightKernels a) basis ∂μ =
      ∫ a, ((∫ y, ∫ x,
        conj (cc20WindowRootSandwichedKernel lambda hlambda
          (leftRoots a) (rightKernels a) (rightRoots a) (y, x)) *
        cc20WindowRootSandwichedKernel lambda hlambda
          (leftRoots a) (leftKernels a) (rightRoots a) (y, x)
        ∂cc20WindowMeasure lambda hlambda
        ∂cc20WindowMeasure lambda hlambda) -
        (2 : ℂ) * inner ℂ
          (cc20WindowRootToLp lambda hlambda (rightRoots a))
          (cc20WindowRootToLp lambda hlambda (leftRoots a))) ∂μ := by
  apply integral_congr_ae
  filter_upwards with a
  exact cc20WindowRootSandwichedResponse_eq_doubleIntegral_sub_residue
    lambda hlambda (leftRoots a) (leftKernels a) (rightRoots a)
    (rightKernels a) basis

/-- Concrete regular-kernel specialization used as the first Proof 305
producer.  The missing source theorem is the identification of another
continuous kernel with the off-diagonal CC20 `[H,f]` divided difference. -/
noncomputable def cc20WindowRootSandwichedRegularPairData
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := cc20WindowSpace lambda hlambda) basis :=
  cc20WindowRootSandwichedPairData lambda hlambda
    leftRoot (cc20WindowComplexRegularKernel lambda hlambda)
    rightRoot (cc20WindowComplexRegularKernel lambda hlambda) basis

theorem cc20WindowRootSandwichedRegularPairData_traceProduct_isTraceClass
    (lambda : ℝ) (hlambda : 1 < lambda)
    (leftRoot rightRoot : ContinuousMap (CC20WindowPoint lambda) ℂ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (cc20WindowSpace lambda hlambda)) :
    PositiveTrace.IsTraceClassAlong basis
      (cc20WindowRootSandwichedRegularPairData lambda hlambda
        leftRoot rightRoot basis).traceProduct := by
  exact cc20WindowRootSandwichedPairData_traceProduct_isTraceClass
    lambda hlambda leftRoot (cc20WindowComplexRegularKernel lambda hlambda)
    rightRoot (cc20WindowComplexRegularKernel lambda hlambda) basis

end CC20Concrete
end Source
end ConnesWeilRH
