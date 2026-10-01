import ConnesWeilRH.Dev.C1RouteAExternalOwnerZeroExtension
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ConnesWeilRH.Dev

open scoped ContDiff
open MeasureTheory

theorem scalarChordUpper2347 (function first second : ℝ → ℝ)
    (hfirst : ∀ position, HasDerivAt function (first position) position)
    (hsecond : ∀ position, HasDerivAt first (second position) position)
    {left right position curvature : ℝ} (horder : left < right)
    (hposition : position ∈ Set.Icc left right)
    (hlower : ∀ coordinate ∈ Set.Icc left right, -curvature ≤ second coordinate) :
    function position ≤ (right - position) / (right - left) * function left +
      (position - left) / (right - left) * function right +
      curvature / 2 * (position - left) * (right - position) := by
  let shifted := fun coordinate => function coordinate + curvature / 2 * coordinate ^ 2
  let shiftedFirst := fun coordinate => first coordinate + curvature * coordinate
  have hshifted (coordinate : ℝ) : HasDerivAt shifted (shiftedFirst coordinate) coordinate := by
    convert (hfirst coordinate).add
      (((hasDerivAt_id coordinate).pow 2).const_mul (curvature / 2)) using 1
    dsimp [shifted, shiftedFirst]
    ring
  have hshiftedFirst (coordinate : ℝ) :
      HasDerivAt shiftedFirst (second coordinate + curvature) coordinate := by
    simpa [shiftedFirst] using (hsecond coordinate).add
      ((hasDerivAt_id coordinate).const_mul curvature)
  have hconvex : ConvexOn ℝ (Set.Icc left right) shifted := by
    have hdiff : Differentiable ℝ shifted := fun coordinate =>
      (hshifted coordinate).differentiableAt
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc left right)
      hdiff.continuous.continuousOn
      (fun coordinate _ => (hshifted coordinate).hasDerivWithinAt)
      (fun coordinate _ => (hshiftedFirst coordinate).hasDerivWithinAt)
    intro coordinate hcoordinate
    have hl := hlower coordinate (interior_subset hcoordinate)
    linarith
  have hdenom : 0 < right - left := sub_pos.mpr horder
  have hleft : 0 ≤ (right - position) / (right - left) :=
    div_nonneg (sub_nonneg.mpr hposition.2) hdenom.le
  have hright : 0 ≤ (position - left) / (right - left) :=
    div_nonneg (sub_nonneg.mpr hposition.1) hdenom.le
  have hsum : (right - position) / (right - left) +
      (position - left) / (right - left) = 1 := by field_simp; ring
  have hpoint : (right - position) / (right - left) * left +
      (position - left) / (right - left) * right = position := by field_simp; ring
  have hchord := hconvex.2 (Set.left_mem_Icc.mpr horder.le)
    (Set.right_mem_Icc.mpr horder.le) hleft hright hsum
  simp only [smul_eq_mul, hpoint] at hchord
  dsimp [shifted] at hchord
  have hidentity :
      (right - position) / (right - left) * (curvature / 2 * left ^ 2) +
      (position - left) / (right - left) * (curvature / 2 * right ^ 2) -
      curvature / 2 * position ^ 2 =
      curvature / 2 * (position - left) * (right - position) := by field_simp; ring
  nlinarith [hidentity]

theorem normChordUpper2347 {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] (function : ℝ → Space)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    {left right position curvature : ℝ} (horder : left < right)
    (hposition : position ∈ Set.Icc left right)
    (hcurvature : ∀ coordinate ∈ Set.Icc left right,
      ‖deriv (deriv function) coordinate‖ ≤ curvature) :
    ‖function position‖ ≤ (right - position) / (right - left) * ‖function left‖ +
      (position - left) / (right - left) * ‖function right‖ +
      curvature / 2 * (position - left) * (right - position) := by
  obtain ⟨projection, hprojection, hnorm⟩ := exists_dual_vector'' ℝ (function position)
  have hdiff := hsmooth.differentiable (by decide)
  have hsmoothFirst : ContDiff ℝ (1 : ℕ∞ω) (deriv function) := ContDiff.deriv' hsmooth
  have hdiffFirst := hsmoothFirst.differentiable (by decide)
  have hfirst (coordinate : ℝ) :
      HasDerivAt (fun argument => projection (function argument))
        (projection (deriv function coordinate)) coordinate :=
    projection.hasFDerivAt.comp_hasDerivAt coordinate (hdiff coordinate).hasDerivAt
  have hsecond (coordinate : ℝ) :
      HasDerivAt (fun argument => projection (deriv function argument))
        (projection (deriv (deriv function) coordinate)) coordinate :=
    projection.hasFDerivAt.comp_hasDerivAt coordinate (hdiffFirst coordinate).hasDerivAt
  have hprojectBound (value : Space) : ‖projection value‖ ≤ ‖value‖ := by
    calc ‖projection value‖ ≤ ‖projection‖ * ‖value‖ := projection.le_opNorm value
         _ ≤ 1 * ‖value‖ := mul_le_mul_of_nonneg_right hprojection (norm_nonneg value)
         _ = _ := one_mul _
  have hscalar := scalarChordUpper2347
    (fun coordinate => projection (function coordinate))
    (fun coordinate => projection (deriv function coordinate))
    (fun coordinate => projection (deriv (deriv function) coordinate))
    hfirst hsecond (curvature := curvature) horder hposition (by
      intro coordinate hcoordinate
      have hnormBound := (hprojectBound (deriv (deriv function) coordinate)).trans
        (hcurvature coordinate hcoordinate)
      have hnegative := neg_le_abs (projection (deriv (deriv function) coordinate))
      rw [Real.norm_eq_abs] at hnormBound
      linarith)
  dsimp only at hscalar
  rw [hnorm] at hscalar
  have hleft : projection (function left) ≤ ‖function left‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hprojectBound (function left))
  have hright : projection (function right) ≤ ‖function right‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hprojectBound (function right))
  have hdenom : 0 ≤ right - left := (sub_pos.mpr horder).le
  exact hscalar.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hleft (div_nonneg (sub_nonneg.mpr hposition.2) hdenom))
    (mul_le_mul_of_nonneg_left hright (div_nonneg (sub_nonneg.mpr hposition.1) hdenom))) le_rfl)

noncomputable def chordDensity2347 (left right leftValue rightValue curvature position : ℝ) : ℝ :=
  (right - position) / (right - left) * leftValue +
    (position - left) / (right - left) * rightValue +
    curvature / 2 * (position - left) * (right - position)

theorem chordDensity2347_integral (left right leftValue rightValue curvature : ℝ)
    (horder : left < right) :
    (∫ position in left..right,
      chordDensity2347 left right leftValue rightValue curvature position) =
      (right - left) / 2 * (leftValue + rightValue) + curvature * (right - left) ^ 3 / 12 := by
  let primitive := fun position : ℝ =>
    (leftValue * right / (right - left) - rightValue * left / (right - left) -
      curvature / 2 * left * right) * position +
    ((rightValue - leftValue) / (2 * (right - left)) +
      curvature / 4 * (left + right)) * position ^ 2 - curvature / 6 * position ^ 3
  have hdenom : right - left ≠ 0 := ne_of_gt (sub_pos.mpr horder)
  have hderiv (position : ℝ) :
      HasDerivAt primitive (chordDensity2347 left right leftValue rightValue curvature position)
        position := by
    convert (((hasDerivAt_id position).const_mul
      (leftValue * right / (right - left) - rightValue * left / (right - left) -
        curvature / 2 * left * right)).add
      (((hasDerivAt_id position).pow 2).const_mul
        ((rightValue - leftValue) / (2 * (right - left)) + curvature / 4 * (left + right)))).sub
      (((hasDerivAt_id position).pow 3).const_mul (curvature / 6)) using 1
    dsimp [chordDensity2347]
    field_simp
    ring
  have hcontinuous : Continuous
      (chordDensity2347 left right leftValue rightValue curvature) := by
    unfold chordDensity2347
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun position _ => hderiv position)
    (hcontinuous.intervalIntegrable left right)]
  dsimp [primitive]
  field_simp
  ring

theorem normIntegralChordUpper2347 {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] (function : ℝ → Space)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    {left right curvature : ℝ} (horder : left < right)
    (hcurvature : ∀ coordinate ∈ Set.Icc left right,
      ‖deriv (deriv function) coordinate‖ ≤ curvature) :
    (∫ position in left..right, ‖function position‖) ≤
      (right - left) / 2 * (‖function left‖ + ‖function right‖) +
        curvature * (right - left) ^ 3 / 12 := by
  have hdensity : Continuous (chordDensity2347 left right
      ‖function left‖ ‖function right‖ curvature) := by
    unfold chordDensity2347
    fun_prop
  calc (∫ position in left..right, ‖function position‖)
      ≤ ∫ position in left..right,
        chordDensity2347 left right ‖function left‖ ‖function right‖ curvature position := by
          apply intervalIntegral.integral_mono_on horder.le
            (hsmooth.continuous.norm.intervalIntegrable left right)
            (hdensity.intervalIntegrable left right)
          intro position hposition
          exact normChordUpper2347 function hsmooth horder hposition hcurvature
    _ = _ := chordDensity2347_integral _ _ _ _ _ horder


noncomputable def compositeTrap2347 {Space : Type*} [NormedAddCommGroup Space]
    (function : ℝ → Space) (left step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells, step / 2 *
    (‖function (left + index * step)‖ + ‖function (left + (index + 1) * step)‖)

theorem normIntegralCompositeUpper2347 {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] (function : ℝ → Space)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    (left step curvature : ℝ) (cells : ℕ) (hstep : 0 < step)
    (hcurvature : ∀ coordinate ∈ Set.Icc left (left + cells * step),
      ‖deriv (deriv function) coordinate‖ ≤ curvature) :
    (∫ position in left..(left + cells * step), ‖function position‖) ≤
      compositeTrap2347 function left step cells +
        step ^ 2 * (cells * step) * curvature / 12 := by
  have hcont : Continuous (fun position => ‖function position‖) := hsmooth.continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun position => ‖function position‖) (μ := volume)
    (a := fun index : ℕ => left + index * step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (left + (index : ℝ) * step) (left + ((index + 1 : ℕ) : ℝ) * step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  rw [← hsum]
  have hcell (index : ℕ) (hindex : index ∈ Finset.range cells) :
      (∫ position in (left + index * step)..(left + (index + 1) * step), ‖function position‖) ≤
        step / 2 * (‖function (left + index * step)‖ +
          ‖function (left + (index + 1) * step)‖) + curvature * step ^ 3 / 12 := by
    have hindexReal : (index : ℝ) + 1 ≤ cells := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
    have hindexNonneg : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
    have horder : left + index * step < left + (index + 1) * step := by
      nlinarith
    have hbound : ∀ coordinate ∈ Set.Icc (left + index * step)
        (left + (index + 1) * step), ‖deriv (deriv function) coordinate‖ ≤ curvature := by
      intro coordinate hcoordinate
      apply hcurvature coordinate
      constructor
      · nlinarith [hcoordinate.1]
      · push_cast at hcoordinate
        nlinarith [hcoordinate.2]
    have h := normIntegralChordUpper2347 function hsmooth horder hbound
    have hwidth : (left + (index + 1) * step) - (left + index * step) = step := by
      ring
    simpa only [hwidth] using h
  calc _ ≤ ∑ index ∈ Finset.range cells,
        (step / 2 * (‖function (left + index * step)‖ +
          ‖function (left + (index + 1) * step)‖) + curvature * step ^ 3 / 12) :=
      Finset.sum_le_sum hcell
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [compositeTrap2347, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring


noncomputable def compositeNodeUpper2347 (nodeUpper : ℕ → ℝ) (step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells, step / 2 * (nodeUpper index + nodeUpper (index + 1))

theorem normIntegralCompositeUpper_of_nodeBounds2347
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (function : ℝ → Space) (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    (left step curvature : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ) (hstep : 0 < step)
    (hcurvature : ∀ coordinate ∈ Set.Icc left (left + cells * step),
      ‖deriv (deriv function) coordinate‖ ≤ curvature)
    (hnodes : ∀ index ≤ cells, ‖function (left + index * step)‖ ≤ nodeUpper index) :
    (∫ position in left..(left + cells * step), ‖function position‖) ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (cells * step) * curvature / 12 := by
  apply (normIntegralCompositeUpper2347 function hsmooth left step curvature cells
    hstep hcurvature).trans
  apply add_le_add _ le_rfl
  unfold compositeTrap2347 compositeNodeUpper2347
  apply Finset.sum_le_sum
  intro index hindex
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hstep.le (by norm_num : (0 : ℝ) ≤ 2))
  have hnext : index + 1 ≤ cells := Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
  have hleft := hnodes index (Nat.le_of_lt (Finset.mem_range.mp hindex))
  have hright := hnodes (index + 1) hnext
  push_cast at hright
  exact add_le_add hleft hright


end ConnesWeilRH.Dev
