import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compact operators from continuous kernels

The `L2` unit ball is sent to a pointwise bounded, equicontinuous family of
continuous coefficient functions. Arzela--Ascoli makes its closure compact,
and the continuous `toLp` map transports compactness to the kernel operator.
-/

namespace ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt

open MeasureTheory Metric Set
open scoped BoundedContinuousFunction

variable {X Y : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

noncomputable def coefficientBounded
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u : Lp ℂ 2 μX) : Y →ᵇ ℂ :=
  ContinuousMap.equivBoundedOfCompact Y ℂ
    (coefficient μX kernel u)

@[simp] theorem coefficientBounded_apply
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u : Lp ℂ 2 μX) (y : Y) :
    coefficientBounded μX kernel u y = coefficient μX kernel u y :=
  rfl

noncomputable def coefficientUnitBallImage
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Set (Y →ᵇ ℂ) :=
  coefficientBounded μX kernel '' closedBall (0 : Lp ℂ 2 μX) 1

theorem coefficientUnitBallImage_equicontinuous
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    Equicontinuous
      ((↑) : coefficientUnitBallImage μX kernel → Y → ℂ) := by
  intro y
  rw [Metric.equicontinuousAt_iff]
  intro epsilon hepsilon
  have hsections : ContinuousAt (sectionToLp μX kernel) y :=
    (continuous_sectionToLp μX kernel).continuousAt
  rw [Metric.continuousAt_iff] at hsections
  obtain ⟨delta, hdelta, hsection⟩ := hsections epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro z hz output
  obtain ⟨u, hu, houtput⟩ := output.property
  rw [← houtput]
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hsectionyz :
      dist (sectionToLp μX kernel z) (sectionToLp μX kernel y) < epsilon :=
    hsection hz
  rw [dist_eq_norm] at hsectionyz ⊢
  change ‖inner ℂ (sectionToLp μX kernel y) u -
      inner ℂ (sectionToLp μX kernel z) u‖ < epsilon
  rw [← inner_sub_left]
  calc
    ‖inner ℂ (sectionToLp μX kernel y - sectionToLp μX kernel z) u‖ ≤
        ‖sectionToLp μX kernel y - sectionToLp μX kernel z‖ * ‖u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖sectionToLp μX kernel y - sectionToLp μX kernel z‖ := by
      simpa using mul_le_of_le_one_right (norm_nonneg _) hunorm
    _ < epsilon := by
      simpa [dist_eq_norm, norm_sub_rev] using hsectionyz

theorem coefficientUnitBallImage_pointwise_bounded
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ)
    (output : Y →ᵇ ℂ) (y : Y)
    (houtput : output ∈ coefficientUnitBallImage μX kernel) :
    output y ∈ closedBall (0 : ℂ) ‖sectionToLpMap μX kernel‖ := by
  obtain ⟨u, hu, rfl⟩ := houtput
  have hunorm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖coefficientBounded μX kernel u y‖ =
        ‖inner ℂ (sectionToLp μX kernel y) u‖ := rfl
    _ ≤ ‖sectionToLp μX kernel y‖ * ‖u‖ := norm_inner_le_norm _ _
    _ ≤ ‖sectionToLp μX kernel y‖ := by
      simpa using mul_le_of_le_one_right (norm_nonneg _) hunorm
    _ ≤ ‖sectionToLpMap μX kernel‖ :=
      (sectionToLpMap μX kernel).norm_coe_le_norm y

theorem isCompact_closure_coefficientUnitBallImage
    (μX : Measure X) [IsFiniteMeasure μX]
    (kernel : ContinuousMap (Y × X) ℂ) :
    IsCompact (closure (coefficientUnitBallImage μX kernel)) := by
  apply BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ) ‖sectionToLpMap μX kernel‖)
    (isCompact_closedBall (0 : ℂ) ‖sectionToLpMap μX kernel‖)
  · intro output y houtput
    exact coefficientUnitBallImage_pointwise_bounded μX kernel output y houtput
  · exact coefficientUnitBallImage_equicontinuous μX kernel

theorem coefficientBounded_toLp
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ)
    (u : Lp ℂ 2 μX) :
    BoundedContinuousFunction.toLp 2 μY ℂ
        (coefficientBounded μX kernel u) =
      operator μX μY kernel u := by
  rw [operator_apply]
  exact (ContinuousMap.toLp_comp_toContinuousMap
    (μ := μY) (coefficientBounded μX kernel u)).symm

theorem operator_isCompactOperator
    (μX : Measure X) (μY : Measure Y)
    [IsFiniteMeasure μX] [IsFiniteMeasure μY]
    (kernel : ContinuousMap (Y × X) ℂ) :
    IsCompactOperator (operator μX μY kernel) := by
  change IsCompactOperator
    ((operator μX μY kernel).toLinearMap : Lp ℂ 2 μX → Lp ℂ 2 μY)
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (operator μX μY kernel).toLinearMap (by norm_num : (0 : ℝ) < 1)).2 ?_
  let compactImage : Set (Lp ℂ 2 μY) :=
    BoundedContinuousFunction.toLp 2 μY ℂ ''
      closure (coefficientUnitBallImage μX kernel)
  refine ⟨compactImage, ?_, ?_⟩
  · exact (isCompact_closure_coefficientUnitBallImage μX kernel).image
      (BoundedContinuousFunction.toLp 2 μY ℂ).continuous
  · rintro output ⟨u, hu, rfl⟩
    refine ⟨coefficientBounded μX kernel u, ?_, ?_⟩
    · exact subset_closure ⟨u, hu, rfl⟩
    · exact coefficientBounded_toLp μX μY kernel u

end ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
