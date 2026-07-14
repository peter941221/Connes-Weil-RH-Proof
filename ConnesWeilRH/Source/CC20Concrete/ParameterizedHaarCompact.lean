/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarSymmetry
import ConnesWeilRH.Source.CC20Concrete.CompactBadSpace
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compactness of the parameterized CC20 regular-kernel operators

For every `lambda > 1`, the coefficient image of the `L2` unit ball is
pointwise bounded and equicontinuous.  Arzela--Ascoli therefore proves that
the ordinary regular-kernel operator on the exact window Haar space is compact.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Metric Set
open scoped BoundedContinuousFunction ComplexConjugate InnerProduct InnerProductSpace

noncomputable def cc20WindowHaarComplexKernelCoefficientBounded
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    CC20WindowPoint lambda →ᵇ ℂ where
  toContinuousMap := cc20WindowHaarComplexKernelCoefficient lambda hlambda u
  map_bounded' := by
    apply isBounded_range_iff.mp
    exact (isCompact_range
      (cc20WindowHaarComplexKernelCoefficient
        lambda hlambda u).continuous).isBounded

@[simp]
theorem cc20WindowHaarComplexKernelCoefficientBounded_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))
    (x : CC20WindowPoint lambda) :
    cc20WindowHaarComplexKernelCoefficientBounded lambda hlambda u x =
      cc20WindowHaarComplexKernelCoefficient lambda hlambda u x :=
  rfl

noncomputable def cc20WindowHaarCoefficientUnitBallImage
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Set (CC20WindowPoint lambda →ᵇ ℂ) :=
  cc20WindowHaarComplexKernelCoefficientBounded lambda hlambda ''
    closedBall (0 : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) 1

theorem cc20WindowHaarCoefficientUnitBallImage_equicontinuous
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Equicontinuous
      ((↑) : cc20WindowHaarCoefficientUnitBallImage lambda hlambda →
        CC20WindowPoint lambda → ℂ) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro epsilon hepsilon
  have hsections : ContinuousAt
      (cc20WindowHaarComplexKernelSectionToLp lambda hlambda) x :=
    (continuous_cc20WindowHaarComplexKernelSectionToLp
      lambda hlambda).continuousAt
  rw [Metric.continuousAt_iff] at hsections
  obtain ⟨delta, hdelta, hsection⟩ := hsections epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro y hy coefficient
  obtain ⟨u, hu, hcoefficient⟩ := coefficient.property
  rw [← hcoefficient]
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hsectionxy :
      dist (cc20WindowHaarComplexKernelSectionToLp lambda hlambda y)
        (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x) < epsilon :=
    hsection hy
  rw [dist_eq_norm] at hsectionxy ⊢
  change ‖inner ℂ
      (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x) u -
      inner ℂ
        (cc20WindowHaarComplexKernelSectionToLp lambda hlambda y) u‖ < epsilon
  rw [← inner_sub_left]
  calc
    ‖inner ℂ
        (cc20WindowHaarComplexKernelSectionToLp lambda hlambda x -
          cc20WindowHaarComplexKernelSectionToLp lambda hlambda y) u‖ ≤
        ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x -
          cc20WindowHaarComplexKernelSectionToLp lambda hlambda y‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖cc20WindowHaarComplexKernelSectionToLp lambda hlambda x -
          cc20WindowHaarComplexKernelSectionToLp lambda hlambda y‖ := by
      simpa using mul_le_of_le_one_right (norm_nonneg _) hunorm
    _ < epsilon := by
      simpa [dist_eq_norm, norm_sub_rev] using hsectionxy

noncomputable def cc20WindowHaarCoefficientRadius
    (lambda : ℝ) (hlambda : 1 < lambda) : ℝ :=
  lpNorm (fun _ : CC20WindowPoint lambda =>
    ‖cc20WindowComplexRegularKernel lambda hlambda‖)
    2 (cc20WindowHaarMeasure lambda hlambda)

theorem cc20WindowHaarCoefficientUnitBallImage_pointwise_bounded
    (lambda : ℝ) (hlambda : 1 < lambda)
    (coefficient : CC20WindowPoint lambda →ᵇ ℂ)
    (x : CC20WindowPoint lambda)
    (hcoefficient : coefficient ∈
      cc20WindowHaarCoefficientUnitBallImage lambda hlambda) :
    coefficient x ∈ closedBall (0 : ℂ)
      (cc20WindowHaarCoefficientRadius lambda hlambda) := by
  obtain ⟨u, hu, hcoefficient_eq⟩ := hcoefficient
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  rw [Metric.mem_closedBall, dist_zero_right, ← hcoefficient_eq]
  calc
    ‖cc20WindowHaarComplexKernelCoefficientBounded lambda hlambda u x‖ ≤
        ‖cc20WindowHaarComplexKernelCoefficient lambda hlambda u‖ :=
      (cc20WindowHaarComplexKernelCoefficient
        lambda hlambda u).norm_coe_le_norm x
    _ ≤ cc20WindowHaarCoefficientRadius lambda hlambda * ‖u‖ := by
      exact norm_cc20WindowHaarComplexKernelCoefficient_le lambda hlambda u
    _ ≤ cc20WindowHaarCoefficientRadius lambda hlambda * 1 := by
      exact mul_le_mul_of_nonneg_left hunorm lpNorm_nonneg
    _ = cc20WindowHaarCoefficientRadius lambda hlambda := mul_one _

theorem isCompact_closure_cc20WindowHaarCoefficientUnitBallImage
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsCompact
      (closure (cc20WindowHaarCoefficientUnitBallImage lambda hlambda)) := by
  apply BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ) (cc20WindowHaarCoefficientRadius lambda hlambda))
    (isCompact_closedBall (0 : ℂ)
      (cc20WindowHaarCoefficientRadius lambda hlambda))
  · intro coefficient x hcoefficient
    exact cc20WindowHaarCoefficientUnitBallImage_pointwise_bounded
      lambda hlambda coefficient x hcoefficient
  · exact cc20WindowHaarCoefficientUnitBallImage_equicontinuous
      lambda hlambda

theorem cc20WindowHaarComplexKernelCoefficientBounded_toLp
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :
    BoundedContinuousFunction.toLp 2
        (cc20WindowHaarMeasure lambda hlambda) ℂ
        (cc20WindowHaarComplexKernelCoefficientBounded lambda hlambda u) =
      cc20WindowHaarComplexL2Operator lambda hlambda u := by
  rw [cc20WindowHaarComplexL2Operator_apply]
  exact (ContinuousMap.toLp_comp_toContinuousMap
    (μ := cc20WindowHaarMeasure lambda hlambda)
    (cc20WindowHaarComplexKernelCoefficientBounded lambda hlambda u)).symm

theorem isCompactOperator_cc20WindowHaarComplexL2Operator
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsCompactOperator (cc20WindowHaarComplexL2Operator lambda hlambda) := by
  change IsCompactOperator
    ((cc20WindowHaarComplexL2Operator lambda hlambda).toLinearMap :
      Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) →
        Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (cc20WindowHaarComplexL2Operator lambda hlambda).toLinearMap
      (by norm_num : (0 : ℝ) < 1)).2 ?_
  let compactImage : Set (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :=
    BoundedContinuousFunction.toLp 2
      (cc20WindowHaarMeasure lambda hlambda) ℂ ''
        closure (cc20WindowHaarCoefficientUnitBallImage lambda hlambda)
  refine ⟨compactImage, ?_, ?_⟩
  · exact
      (isCompact_closure_cc20WindowHaarCoefficientUnitBallImage
        lambda hlambda).image
        (BoundedContinuousFunction.toLp 2
          (cc20WindowHaarMeasure lambda hlambda) ℂ).continuous
  · rintro output ⟨u, hu, rfl⟩
    refine ⟨cc20WindowHaarComplexKernelCoefficientBounded
      lambda hlambda u, ?_, ?_⟩
    · exact subset_closure ⟨u, hu, rfl⟩
    · exact cc20WindowHaarComplexKernelCoefficientBounded_toLp
        lambda hlambda u

theorem exists_finiteDimensional_cc20WindowHaarRegularRemainder_nonpositive
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ∃ controlSpace :
        Submodule ℂ (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)),
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda),
          x ∈ controlSpaceᗮ →
            (inner ℂ x
              (cc20WindowHaarComplexL2Operator lambda hlambda x -
                (2 : ℂ) • x)).re ≤ 0 := by
  exact CompactBadSpace.exists_finiteDimensional_remainder_nonpositive
    (cc20WindowHaarComplexL2Operator lambda hlambda)
    (isCompactOperator_cc20WindowHaarComplexL2Operator lambda hlambda)
    (by norm_num : (0 : ℝ) < 2)

/-- For every finite Haar window, any named Hilbert basis yields a finite set
of coordinate rows controlling the compact `-2 Id` remainder. -/
theorem exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_hilbertBasis_rows
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))) :
    ∃ rowIndices : Finset ι,
      FiniteDimensional ℂ
          (Submodule.span ℂ (basis '' (rowIndices : Set ι))) ∧
        ∀ x : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda),
          (∀ i ∈ rowIndices, inner ℂ x (basis i) = 0) →
            (inner ℂ x
              (cc20WindowHaarComplexL2Operator lambda hlambda x -
                (2 : ℂ) • x)).re ≤ 0 := by
  exact CompactBadSpace.exists_finite_hilbertBasis_controlRowIndices
    (cc20WindowHaarComplexL2Operator lambda hlambda)
    (isCompactOperator_cc20WindowHaarComplexL2Operator lambda hlambda)
    basis
    (by norm_num : (0 : ℝ) < 2)

end CC20Concrete
end Source
end ConnesWeilRH
