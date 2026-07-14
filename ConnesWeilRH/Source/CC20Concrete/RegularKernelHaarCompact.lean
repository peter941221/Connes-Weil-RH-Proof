/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarSymmetry
import ConnesWeilRH.Source.CC20Concrete.CompactBadSpace
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Compactness of the CC20 regular kernel on the source Haar space

The coefficient image of the `L2` unit ball is pointwise bounded and
equicontinuous because the kernel-section map is continuous into `L2`.
Arzela--Ascoli therefore makes the source Haar kernel operator compact.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Metric Set
open scoped BoundedContinuousFunction ComplexConjugate InnerProduct InnerProductSpace
open CompactBadSpace

noncomputable def cc20CompactHaarComplexKernelCoefficientBounded
    (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    CC20CompactInterval →ᵇ ℂ where
  toContinuousMap := cc20CompactHaarComplexKernelCoefficient u
  map_bounded' := by
    apply isBounded_range_iff.mp
    exact (isCompact_range
      (cc20CompactHaarComplexKernelCoefficient u).continuous).isBounded

@[simp]
theorem cc20CompactHaarComplexKernelCoefficientBounded_apply
    (u : Lp ℂ 2 cc20CompactHaarMeasure) (x : CC20CompactInterval) :
    cc20CompactHaarComplexKernelCoefficientBounded u x =
      cc20CompactHaarComplexKernelCoefficient u x :=
  rfl

noncomputable def cc20CompactHaarCoefficientUnitBallImage :
    Set (CC20CompactInterval →ᵇ ℂ) :=
  cc20CompactHaarComplexKernelCoefficientBounded ''
    closedBall (0 : Lp ℂ 2 cc20CompactHaarMeasure) 1

theorem cc20CompactHaarCoefficientUnitBallImage_equicontinuous :
    Equicontinuous
      ((↑) : cc20CompactHaarCoefficientUnitBallImage →
        CC20CompactInterval → ℂ) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro epsilon hepsilon
  have hsections : ContinuousAt
      cc20CompactHaarComplexKernelSectionToLp x :=
    continuous_cc20CompactHaarComplexKernelSectionToLp.continuousAt
  rw [Metric.continuousAt_iff] at hsections
  obtain ⟨delta, hdelta, hsection⟩ := hsections epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro y hy coefficient
  obtain ⟨u, hu, hcoefficient⟩ := coefficient.property
  rw [← hcoefficient]
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hsectionxy :
      dist (cc20CompactHaarComplexKernelSectionToLp y)
        (cc20CompactHaarComplexKernelSectionToLp x) < epsilon :=
    hsection hy
  rw [dist_eq_norm] at hsectionxy ⊢
  change ‖inner ℂ (cc20CompactHaarComplexKernelSectionToLp x) u -
      inner ℂ (cc20CompactHaarComplexKernelSectionToLp y) u‖ < epsilon
  rw [← inner_sub_left]
  calc
    ‖inner ℂ
        (cc20CompactHaarComplexKernelSectionToLp x -
          cc20CompactHaarComplexKernelSectionToLp y) u‖ ≤
        ‖cc20CompactHaarComplexKernelSectionToLp x -
          cc20CompactHaarComplexKernelSectionToLp y‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖cc20CompactHaarComplexKernelSectionToLp x -
          cc20CompactHaarComplexKernelSectionToLp y‖ := by
      simpa using mul_le_of_le_one_right (norm_nonneg _) hunorm
    _ < epsilon := by
      simpa [dist_eq_norm, norm_sub_rev] using hsectionxy

noncomputable def cc20CompactHaarCoefficientRadius : ℝ :=
  lpNorm (fun _ : CC20CompactInterval =>
    ‖cc20CompactComplexRegularKernel‖) 2 cc20CompactHaarMeasure

theorem cc20CompactHaarCoefficientUnitBallImage_pointwise_bounded
    (coefficient : CC20CompactInterval →ᵇ ℂ)
    (x : CC20CompactInterval)
    (hcoefficient : coefficient ∈ cc20CompactHaarCoefficientUnitBallImage) :
    coefficient x ∈ closedBall (0 : ℂ) cc20CompactHaarCoefficientRadius := by
  obtain ⟨u, hu, hcoefficient_eq⟩ := hcoefficient
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  rw [Metric.mem_closedBall, dist_zero_right, ← hcoefficient_eq]
  calc
    ‖cc20CompactHaarComplexKernelCoefficientBounded u x‖ ≤
        ‖cc20CompactHaarComplexKernelCoefficient u‖ :=
      (cc20CompactHaarComplexKernelCoefficient u).norm_coe_le_norm x
    _ ≤ cc20CompactHaarCoefficientRadius * ‖u‖ := by
      exact norm_cc20CompactHaarComplexKernelCoefficient_le u
    _ ≤ cc20CompactHaarCoefficientRadius * 1 := by
      exact mul_le_mul_of_nonneg_left hunorm lpNorm_nonneg
    _ = cc20CompactHaarCoefficientRadius := mul_one _

theorem isCompact_closure_cc20CompactHaarCoefficientUnitBallImage :
    IsCompact (closure cc20CompactHaarCoefficientUnitBallImage) := by
  apply BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ) cc20CompactHaarCoefficientRadius)
    (isCompact_closedBall (0 : ℂ) cc20CompactHaarCoefficientRadius)
  · intro coefficient x hcoefficient
    exact cc20CompactHaarCoefficientUnitBallImage_pointwise_bounded
      coefficient x hcoefficient
  · exact cc20CompactHaarCoefficientUnitBallImage_equicontinuous

theorem cc20CompactHaarComplexKernelCoefficientBounded_toLp
    (u : Lp ℂ 2 cc20CompactHaarMeasure) :
    BoundedContinuousFunction.toLp 2 cc20CompactHaarMeasure ℂ
        (cc20CompactHaarComplexKernelCoefficientBounded u) =
      cc20CompactHaarComplexL2Operator u := by
  rw [cc20CompactHaarComplexL2Operator_apply]
  exact (ContinuousMap.toLp_comp_toContinuousMap
    (μ := cc20CompactHaarMeasure)
    (cc20CompactHaarComplexKernelCoefficientBounded u)).symm

theorem isCompactOperator_cc20CompactHaarComplexL2Operator :
    IsCompactOperator cc20CompactHaarComplexL2Operator := by
  change IsCompactOperator
    (cc20CompactHaarComplexL2Operator.toLinearMap :
      Lp ℂ 2 cc20CompactHaarMeasure → Lp ℂ 2 cc20CompactHaarMeasure)
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    cc20CompactHaarComplexL2Operator.toLinearMap
      (by norm_num : (0 : ℝ) < 1)).2 ?_
  let compactImage : Set (Lp ℂ 2 cc20CompactHaarMeasure) :=
    BoundedContinuousFunction.toLp 2 cc20CompactHaarMeasure ℂ ''
      closure cc20CompactHaarCoefficientUnitBallImage
  refine ⟨compactImage, ?_, ?_⟩
  · exact isCompact_closure_cc20CompactHaarCoefficientUnitBallImage.image
      (BoundedContinuousFunction.toLp 2 cc20CompactHaarMeasure ℂ).continuous
  · rintro output ⟨u, hu, rfl⟩
    refine ⟨cc20CompactHaarComplexKernelCoefficientBounded u, ?_, ?_⟩
    · exact subset_closure ⟨u, hu, rfl⟩
    · exact cc20CompactHaarComplexKernelCoefficientBounded_toLp u

theorem exists_finiteDimensional_cc20HaarRegularRemainder_nonpositive :
    ∃ controlSpace : Submodule ℂ (Lp ℂ 2 cc20CompactHaarMeasure),
      FiniteDimensional ℂ controlSpace ∧
        ∀ x : Lp ℂ 2 cc20CompactHaarMeasure,
          x ∈ controlSpaceᗮ →
            (inner ℂ x
              (cc20CompactHaarComplexL2Operator x - (2 : ℂ) • x)).re ≤ 0 := by
  exact CompactBadSpace.exists_finiteDimensional_remainder_nonpositive
    cc20CompactHaarComplexL2Operator
    isCompactOperator_cc20CompactHaarComplexL2Operator
    (by norm_num : (0 : ℝ) < 2)

/-- The concrete Haar remainder admits a finite bad space generated by genuine
continuous-input `L2` vectors.  This is the source-bearing form needed before
one can impose exact detector rows on the same CC20 operator. -/
theorem exists_finiteDimensional_cc20HaarRegularRemainder_nonpositive_on_continuous_inputs :
    ∃ controlSpace : Submodule ℂ (Lp ℂ 2 cc20CompactHaarMeasure),
      FiniteDimensional ℂ controlSpace ∧
        controlSpace ≤ Submodule.span ℂ
          (Set.range (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ)) ∧
          ∀ evaluationSpace : Submodule ℂ (Lp ℂ 2 cc20CompactHaarMeasure),
            controlSpace ≤ evaluationSpace →
              ∀ x : Lp ℂ 2 cc20CompactHaarMeasure,
                x ∈ evaluationSpaceᗮ →
                  (inner ℂ x
                    (cc20CompactHaarComplexL2Operator x - (2 : ℂ) • x)).re ≤ 0 := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal)) (μ := cc20CompactHaarMeasure) (by norm_num)
  exact exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace_spanned_by_denseRange
    cc20CompactHaarComplexL2Operator
    isCompactOperator_cc20CompactHaarComplexL2Operator
    (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ)
    hdense
    (by norm_num : (0 : ℝ) < 2)

/-- The same concrete remainder contract, written with explicit finite row
vectors.  The only missing route producer is the displayed span coverage. -/
theorem exists_finite_cc20HaarRegularRemainder_nonpositive_on_finite_row_vanishing :
    ∃ sourceFrame : Set (Lp ℂ 2 cc20CompactHaarMeasure),
      sourceFrame.Finite ∧
        sourceFrame ⊆ Set.range (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) ∧
          FiniteDimensional ℂ (Submodule.span ℂ sourceFrame) ∧
            ∀ (n : ℕ)
              (rows : Fin n → Lp ℂ 2 cc20CompactHaarMeasure),
              Submodule.span ℂ sourceFrame ≤
                  Submodule.span ℂ (Set.range rows) →
                ∀ x : Lp ℂ 2 cc20CompactHaarMeasure,
                  (∀ i : Fin n, inner ℂ x (rows i) = 0) →
                    (inner ℂ x
                      (cc20CompactHaarComplexL2Operator x - (2 : ℂ) • x)).re ≤ 0 := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal)) (μ := cc20CompactHaarMeasure) (by norm_num)
  exact CompactBadSpace.exists_finite_source_controlFrame_with_finite_row_vanishing
    cc20CompactHaarComplexL2Operator
    isCompactOperator_cc20CompactHaarComplexL2Operator
    (ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ)
    hdense
    (by norm_num : (0 : ℝ) < 2)

/-- A named Hilbert basis of the concrete Haar carrier supplies finite
coordinate rows for the compact remainder. -/
theorem exists_finite_cc20HaarRegularRemainder_nonpositive_on_hilbertBasis_rows
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 cc20CompactHaarMeasure)) :
    ∃ rowIndices : Finset ι,
      FiniteDimensional ℂ
          (Submodule.span ℂ (basis '' (rowIndices : Set ι))) ∧
        ∀ x : Lp ℂ 2 cc20CompactHaarMeasure,
          (∀ i ∈ rowIndices, inner ℂ x (basis i) = 0) →
            (inner ℂ x
              (cc20CompactHaarComplexL2Operator x - (2 : ℂ) • x)).re ≤ 0 := by
  exact CompactBadSpace.exists_finite_hilbertBasis_controlRowIndices
    cc20CompactHaarComplexL2Operator
    isCompactOperator_cc20CompactHaarComplexL2Operator
    basis
    (by norm_num : (0 : ℝ) < 2)

end CC20Concrete
end Source
end ConnesWeilRH
