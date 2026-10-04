import ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def weightedUnitFourthCellUpper2574
    (sigma modulation radius left right : ℝ) : ℝ :=
  if cellNearAbs2538 left right < radius then
    weightedFamilyCellUpper2538 4 1 sigma modulation radius
      (cellNearAbs2538 left right / radius)
      (min (max |left| |right|) radius / radius) left right
  else 0

theorem weightedUnitFourthCellUpper_nonneg2574
    (sigma modulation : ℝ) {radius left right : ℝ} (hradius : 0 < radius) :
    0 ≤ weightedUnitFourthCellUpper2574 sigma modulation radius left right := by
  unfold weightedUnitFourthCellUpper2574
  split_ifs with hintersects
  · unfold weightedFamilyCellUpper2538
    apply mul_nonneg (norm_nonneg _)
    apply mul_nonneg (Real.exp_pos _).le
    apply Finset.sum_nonneg
    intro index _
    apply mul_nonneg (by positivity)
    exact localCoupledBumpUpper2536_nonneg _ hradius
      (div_nonneg (cellNearAbs2538_nonneg left right) hradius.le)
      ((div_lt_one hradius).mpr hintersects)
      (div_nonneg (le_min (le_max_of_le_left (abs_nonneg left)) hradius.le) hradius.le)
  · exact le_rfl

theorem weightedExternalFamily_fourth_le_cell2574
    (sigma modulation : ℝ) {radius left right : ℝ}
    (hradius : 0 < radius) (_horder : left ≤ right) :
    ∀ position ∈ Set.Icc left right,
      ‖iteratedDeriv 4 (weightedFunction2348 sigma
        (externalFamilyValue2344 1 modulation radius)) position‖ ≤
        weightedUnitFourthCellUpper2574 sigma modulation radius left right := by
  intro position hposition
  by_cases hintersects : cellNearAbs2538 left right < radius
  · by_cases hinside : |position| < radius
    · have hgeometry :
          cellNearAbs2538 left right / radius ≤ |position / radius| ∧
          |position / radius| ≤ min (max |left| |right|) radius / radius := by
        rw [abs_div, abs_of_pos hradius]
        exact ⟨div_le_div_of_nonneg_right (cellNearAbs2538_le hposition) hradius.le,
          div_le_div_of_nonneg_right
            (le_min (cellAbs_le_max2538 hposition) hinside.le) hradius.le⟩
      rw [weightedUnitFourthCellUpper2574, if_pos hintersects]
      exact weightedExternalFamily_iteratedDeriv_le_cell2538 4 (by decide)
        sigma 1 modulation hradius
        (div_nonneg (cellNearAbs2538_nonneg left right) hradius.le)
        ((div_lt_one hradius).mpr hintersects) hgeometry.1 hgeometry.2 hposition
    · rw [weightedExternalFamily_iteratedDeriv_zero_outside2538 4 sigma 1 modulation
          hradius (not_lt.mp hinside), norm_zero]
      exact weightedUnitFourthCellUpper_nonneg2574 sigma modulation hradius
  · have houtside : radius ≤ |position| :=
      (not_lt.mp hintersects).trans (cellNearAbs2538_le hposition)
    rw [weightedExternalFamily_iteratedDeriv_zero_outside2538 4 sigma 1 modulation
      hradius houtside, norm_zero, weightedUnitFourthCellUpper2574, if_neg hintersects]


noncomputable def signedFourthCellUpper2574 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ) (left right : ℝ) : ℝ :=
  ∑ index : Fin 30, (‖centers index‖ + errors index) *
    weightedUnitFourthCellUpper2574 sigma (modulations index) (storedWidth index ^ 2) left right

theorem weightedPhysical2539_fourth_le_cell2574 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {left right : ℝ} (horder : left ≤ right) :
    ∀ position ∈ Set.Icc left right,
      ‖iteratedDeriv 4 (weightedPhysical2539 sigma coefficients modulations) position‖ ≤
        signedFourthCellUpper2574 sigma centers errors modulations left right := by
  intro position hposition
  rw [weightedPhysical2539_iteratedDeriv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  have hcoefficient : ‖coefficients index‖ ≤ ‖centers index‖ + errors index := by
    calc
      ‖coefficients index‖ = ‖centers index + (coefficients index - centers index)‖ := by
        congr 1
        abel
      _ ≤ ‖centers index‖ + ‖coefficients index - centers index‖ := norm_add_le _ _
      _ ≤ ‖centers index‖ + errors index := add_le_add_right (herror index) _
  have hunit : ‖weightedUnitJet2539 4 sigma modulations index position‖ ≤
      weightedUnitFourthCellUpper2574 sigma (modulations index) (storedWidth index ^ 2)
        left right := by
    exact weightedExternalFamily_fourth_le_cell2574 sigma (modulations index)
      (pow_pos (storedWidth_pos index) 2) horder position hposition
  have hnonnegative : 0 ≤ ‖centers index‖ + errors index :=
    (norm_nonneg _).trans hcoefficient
  rw [norm_mul]
  exact mul_le_mul hcoefficient hunit (norm_nonneg _) hnonnegative

theorem weightedPhysical2539_second_norm_integral_le_chord2574 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {left right : ℝ} (horder : left < right) :
    (∫ position in left..right,
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) position‖) ≤
      (right - left) / 2 * (signedJetUpper2539 2 sigma centers errors modulations left +
        signedJetUpper2539 2 sigma centers errors modulations right) +
      signedFourthCellUpper2574 sigma centers errors modulations left right *
        (right - left) ^ 3 / 12 := by
  have hsmooth : ContDiff ℝ ∞
      (iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 2 (weightedPhysical2539_contDiff sigma coefficients modulations)
  have hfourth := weightedPhysical2539_fourth_le_cell2574 sigma coefficients centers errors
    modulations herror horder.le
  have h := normIntegralChordUpper2347
    (iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations))
    (hsmooth.of_le (by decide)) horder (by
      intro position hposition
      simpa only [← iteratedDeriv_succ] using hfourth position hposition)
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ (right - left) / 2)
  exact add_le_add
    (weightedPhysical2539_jet_le_center_error 2 sigma coefficients centers errors
      modulations herror left)
    (weightedPhysical2539_jet_le_center_error 2 sigma coefficients centers errors
      modulations herror right)

noncomputable def signedSecondChordCompositeUpper2574 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (left step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells,
    (step / 2 * (signedJetUpper2539 2 sigma centers errors modulations (left + index * step) +
      signedJetUpper2539 2 sigma centers errors modulations (left + (index + 1) * step)) +
    signedFourthCellUpper2574 sigma centers errors modulations
      (left + index * step) (left + (index + 1) * step) * step ^ 3 / 12)

theorem weightedPhysical2539_second_integral_le_chord_composite2574 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    (left step : ℝ) (cells : ℕ) (hstep : 0 < step) :
    (∫ position in left..(left + cells * step),
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) position‖) ≤
      signedSecondChordCompositeUpper2574 sigma centers errors modulations left step cells := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff sigma coefficients modulations).of_le
        (by decide))).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) position‖)
    (μ := volume) (a := fun index : ℕ => left + index * step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (left + (index : ℝ) * step) (left + ((index + 1 : ℕ) : ℝ) * step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  rw [← hsum]
  unfold signedSecondChordCompositeUpper2574
  apply Finset.sum_le_sum
  intro index _
  have horder : left + (index : ℝ) * step < left + ((index : ℝ) + 1) * step := by linarith
  have hwidth : (left + ((index : ℝ) + 1) * step) - (left + (index : ℝ) * step) = step := by
    ring
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 sigma coefficients centers
    errors modulations herror horder
  simpa only [hwidth] using h

theorem externalPhysical2344_stripSecond_le_secondChord2574 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index) :
    stripSecondNorm sigma (externalPhysical2344 coefficients modulations) ≤
      signedSecondChordCompositeUpper2574 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 +
      2 * |sigma| * signedFirstCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 +
      sigma ^ 2 * signedCompositeUpper2539 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
  rw [externalPhysical2344_stripSecond_eq_interval2562 sigma coefficients modulations]
  have hstep : 0 < 2 * stripRadius2303 / 10240 := by norm_num [stripRadius2303]
  have hab : (-stripRadius2303 : ℝ) ≤ stripRadius2303 := by linarith [hstep]
  have hgrid : (-stripRadius2303 : ℝ) + (10240 : ℝ) * (2 * stripRadius2303 / 10240)
      = stripRadius2303 := by ring
  have hcf : ContDiff ℝ 1
      (deriv (externalPhysical2344 coefficients modulations)) :=
    ContDiff.deriv' (externalPhysical2344_contDiff_two2562 coefficients modulations)
  have hc2 : Continuous
      (deriv (deriv (externalPhysical2344 coefficients modulations))) :=
    hcf.continuous_deriv (by decide)
  have hexpcont : Continuous fun x : ℝ => Real.exp (sigma * x) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hI2 : IntervalIntegrable (fun x =>
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (ContDiff.differentiable_iteratedDeriv' 2
      (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
        (by decide))).continuous.norm.intervalIntegrable _ _
  have hI1 : IntervalIntegrable (fun x =>
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (ContDiff.differentiable_iteratedDeriv' 1
      (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
        (by decide))).continuous.norm.intervalIntegrable _ _
  have hI0 : IntervalIntegrable (fun x =>
      ‖weightedPhysical2539 sigma coefficients modulations x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (weightedPhysical2539_contDiff sigma coefficients modulations).continuous.norm
      |>.intervalIntegrable _ _
  have hleft : IntervalIntegrable (fun x => Real.exp (sigma * x) *
      ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (hexpcont.mul hc2.norm).intervalIntegrable _ _
  have hI1c : IntervalIntegrable (fun x => (2 * |sigma|) *
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 := hI1.const_mul _
  have hI0c : IntervalIntegrable (fun x => (sigma ^ 2) *
      ‖weightedPhysical2539 sigma coefficients modulations x‖)
      volume (-stripRadius2303) stripRadius2303 := hI0.const_mul _
  have hsplit : (∫ x in (-stripRadius2303)..stripRadius2303, Real.exp (sigma * x) *
        ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖) ≤
      ∫ x in (-stripRadius2303)..stripRadius2303,
        ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖ +
          (2 * |sigma|) *
            ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖ +
          sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations x‖ := by
    refine intervalIntegral.integral_mono_on hab hleft ((hI2.add hI1c).add hI0c) ?_
    intro x _
    exact weightedPhysical2539_secondDeriv_integrand_le2562 sigma coefficients
      modulations x
  refine hsplit.trans ?_
  have e2a : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖ +
      (2 * |sigma|) *
        ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖ +
      sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations x‖) =
      ((∫ x in (-stripRadius2303)..stripRadius2303,
          ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖) +
        (∫ x in (-stripRadius2303)..stripRadius2303, (2 * |sigma|) *
          ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)) +
      (∫ x in (-stripRadius2303)..stripRadius2303, (sigma ^ 2) *
        ‖weightedPhysical2539 sigma coefficients modulations x‖) := by
    rw [intervalIntegral.integral_add (hI2.add hI1c) hI0c,
      intervalIntegral.integral_add hI2 hI1c]
  have e2b : (∫ x in (-stripRadius2303)..stripRadius2303, (2 * |sigma|) *
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) =
      (2 * |sigma|) * (∫ x in (-stripRadius2303)..stripRadius2303,
        ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) :=
    intervalIntegral.integral_const_mul (2 * |sigma|)
      (fun x => ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
  have e2c : (∫ x in (-stripRadius2303)..stripRadius2303, (sigma ^ 2) *
      ‖weightedPhysical2539 sigma coefficients modulations x‖) =
      (sigma ^ 2) * (∫ x in (-stripRadius2303)..stripRadius2303,
        ‖weightedPhysical2539 sigma coefficients modulations x‖) :=
    intervalIntegral.integral_const_mul (sigma ^ 2)
      (fun x => ‖weightedPhysical2539 sigma coefficients modulations x‖)
  rw [e2a, e2b, e2c]
  have t1 := weightedPhysical2539_second_integral_le_chord_composite2574 sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t2 := weightedPhysical2539_first_integral_le_composite2562 sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t3 := weightedPhysical2539_norm_integral_le_signed_composite sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t1' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedSecondChordCompositeUpper2574 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t1
  have t2' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedFirstCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t2
  have t3' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖weightedPhysical2539 sigma coefficients modulations x‖) ≤
      signedCompositeUpper2539 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t3
  exact add_le_add
    (add_le_add t1' (mul_le_mul_of_nonneg_left t2' (mul_nonneg zero_le_two (abs_nonneg sigma))))
    (mul_le_mul_of_nonneg_left t3' (pow_two_nonneg sigma))

end ConnesWeilRH.Dev
