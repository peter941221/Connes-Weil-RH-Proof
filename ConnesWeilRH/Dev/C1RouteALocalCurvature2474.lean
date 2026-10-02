import ConnesWeilRH.Dev.C1RouteAWeightedChordPanel

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open MeasureTheory

/-  2474: cell-local curvature form of the weighted chord attachment.

The 2348 theorem uses one global curvature maximum.  This interface keeps a
separate bound for each cell, so a future actual-owner panel enclosure can
charge `sum_i curvature i * step^3 / 12` instead of the global maximum times
the whole interval.  No numerical local enclosure is smuggled in here.
-/

noncomputable def localCurvatureRemainder2474
    (curvature : ℕ → ℝ) (step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells, curvature index * step ^ 3 / 12

theorem stripNorm_le_localCurvature2474
    (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : WithTop (WithTop ℕ)) function)
    (radius step : ℝ) (cells : ℕ) (nodeUpper curvature : ℕ → ℝ)
    (hradius : 0 ≤ radius) (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hsupport : Function.support function ⊆ Set.Icc (-radius) radius)
    (hcurvature : ∀ index ∈ Finset.range cells, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ‖deriv (deriv (weightedFunction2348 sigma function)) coordinate‖ ≤
        curvature index)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-radius + index * step)) *
        ‖function (-radius + index * step)‖ ≤ nodeUpper index) :
    stripNorm sigma function ≤
      compositeNodeUpper2347 nodeUpper step cells +
        localCurvatureRemainder2474 curvature step cells := by
  have hend : -radius + (cells : ℝ) * step = radius := by
    rw [hgrid]
    ring
  let weighted := weightedFunction2348 sigma function
  have hweighted : ContDiff ℝ (2 : WithTop (WithTop ℕ)) weighted :=
    weightedFunction2348_contDiff sigma function hsmooth
  have hcont : Continuous (fun position => ‖weighted position‖) :=
    hweighted.continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun position => ‖weighted position‖) (μ := volume)
    (a := fun index : ℕ => -radius + index * step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (-radius + (index : ℝ) * step)
      (-radius + ((index + 1 : ℕ) : ℝ) * step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  have hcell : ∀ index ∈ Finset.range cells,
      (∫ position in (-radius + index * step)..
          (-radius + (index + 1) * step), ‖weighted position‖) ≤
        step / 2 * (‖weighted (-radius + index * step)‖ +
          ‖weighted (-radius + (index + 1) * step)‖) +
        curvature index * step ^ 3 / 12 := by
    intro index hindex
    have hindexReal : (index : ℝ) + 1 ≤ cells := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
    have horder : -radius + index * step <
        -radius + (index + 1) * step := by
      nlinarith
    have hbound : ∀ coordinate ∈
        Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
        ‖deriv (deriv weighted) coordinate‖ ≤ curvature index := by
      intro coordinate hcoordinate
      simpa only [weighted] using hcurvature index hindex coordinate hcoordinate
    have h := normIntegralChordUpper2347 weighted hweighted horder hbound
    have hwidth : (-radius + (index + 1) * step) -
        (-radius + index * step) = step := by ring
    simpa only [hwidth] using h
  have hinterval' :
      (∫ position in (-radius)..(-radius + (cells : ℝ) * step),
        ‖weighted position‖) ≤
      ∑ index ∈ Finset.range cells,
          (step / 2 * (‖weighted (-radius + index * step)‖ +
            ‖weighted (-radius + (index + 1) * step)‖) +
            curvature index * step ^ 3 / 12) := by
    rw [← hsum]
    exact Finset.sum_le_sum hcell
  have hinterval :
      (∫ position in (-radius)..radius, ‖weighted position‖) ≤
      ∑ index ∈ Finset.range cells,
        (step / 2 * (‖weighted (-radius + index * step)‖ +
          ‖weighted (-radius + (index + 1) * step)‖) +
          curvature index * step ^ 3 / 12) := by
    simpa only [hend] using hinterval'
  have hnodeWeighted : ∀ index ≤ cells,
      ‖weighted (-radius + index * step)‖ ≤ nodeUpper index := by
    intro index hindex
    rw [weightedFunction2348_norm]
    exact hnodes index hindex
  have hnodeSum :
      (∑ index ∈ Finset.range cells,
        step / 2 * (‖weighted (-radius + index * step)‖ +
          ‖weighted (-radius + (index + 1) * step)‖)) ≤
      compositeNodeUpper2347 nodeUpper step cells := by
    unfold compositeNodeUpper2347
    apply Finset.sum_le_sum
    intro index hindex
    apply mul_le_mul_of_nonneg_left _
      (div_nonneg hstep.le (by norm_num : (0 : ℝ) ≤ 2))
    have hleft := hnodeWeighted index
      (Nat.le_of_lt (Finset.mem_range.mp hindex))
    have hright := hnodeWeighted (index + 1)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hindex))
    exact add_le_add hleft (by simpa only [Nat.cast_add, Nat.cast_one] using hright)
  calc
    stripNorm sigma function =
        ∫ position in (-radius)..radius, ‖weighted position‖ := by
      simpa only [weighted] using
        weightedStripNorm2348_eq_interval sigma function radius hradius hsupport
    _ ≤
        ∑ index ∈ Finset.range cells,
          (step / 2 * (‖weighted (-radius + index * step)‖ +
            ‖weighted (-radius + (index + 1) * step)‖) +
            curvature index * step ^ 3 / 12) := hinterval
    _ ≤ compositeNodeUpper2347 nodeUpper step cells +
        localCurvatureRemainder2474 curvature step cells := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hnodeSum le_rfl

end ConnesWeilRH.Dev
