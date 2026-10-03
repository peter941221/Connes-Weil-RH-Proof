import ConnesWeilRH.Dev.C1RouteAWeightedFamilyCell2538
import ConnesWeilRH.Dev.C1RouteAOwnerSupport

/-!
Signed midpoint-plus-error curvature and chord-integral bounds for the actual
30-family external physical function. The midpoint sum remains inside the
norm; only coefficient perturbations and third-derivative variation are summed
as scalar charges. No numerical node table is imported here.
-/

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def weightedPhysical2539 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) : ℝ → ℂ :=
  weightedFunction2348 sigma (externalPhysical2344 coefficients modulations)

noncomputable def weightedUnitJet2539 (order : ℕ) (sigma : ℝ)
    (modulations : Fin 30 → ℝ) (index : Fin 30) (position : ℝ) : ℂ :=
  iteratedDeriv order (weightedFunction2348 sigma
    (externalFamilyValue2344 1 (modulations index) (storedWidth index ^ 2))) position

theorem weightedExternalFamily_coefficient_linear2539 (order : ℕ)
    (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius position : ℝ} (hradius : 0 < radius) :
    iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius))
      position = coefficient * iteratedDeriv order
        (weightedFunction2348 sigma (externalFamilyValue2344 1 modulation radius)) position := by
  rw [weightedExternalFamily_iteratedDeriv2537 order sigma coefficient modulation hradius,
    weightedExternalFamily_iteratedDeriv2537 order sigma 1 modulation hradius]
  simp only [one_mul]

theorem weightedPhysical2539_eq_sum (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    weightedPhysical2539 sigma coefficients modulations = fun position =>
      ∑ index : Fin 30, weightedFunction2348 sigma
        (externalFamilyValue2344 (coefficients index) (modulations index)
          (storedWidth index ^ 2)) position := by
  funext position
  simp only [weightedPhysical2539, weightedFunction2348, externalPhysical2344, Finset.mul_sum]

theorem weightedPhysical2539_contDiff (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    ContDiff ℝ ∞ (weightedPhysical2539 sigma coefficients modulations) := by
  rw [weightedPhysical2539_eq_sum]
  exact ContDiff.sum fun index _ => weightedExternalFamily_contDiff2538 sigma
    (coefficients index) (modulations index) (pow_pos (storedWidth_pos index) 2)

theorem weightedPhysical2539_iteratedDeriv (order : ℕ) (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (position : ℝ) :
    iteratedDeriv order (weightedPhysical2539 sigma coefficients modulations) position =
      ∑ index : Fin 30, coefficients index *
        weightedUnitJet2539 order sigma modulations index position := by
  have hsmooth : ∀ index : Fin 30, ContDiffAt ℝ order
      (weightedFunction2348 sigma (externalFamilyValue2344 (coefficients index)
        (modulations index) (storedWidth index ^ 2))) position := fun index =>
    ((weightedExternalFamily_contDiff2538 sigma (coefficients index) (modulations index)
      (pow_pos (storedWidth_pos index) 2)).of_le
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  rw [weightedPhysical2539_eq_sum, iteratedDeriv_fun_sum (fun index _ => hsmooth index)]
  apply Finset.sum_congr rfl
  intro index _
  exact weightedExternalFamily_coefficient_linear2539 order sigma _ _
    (pow_pos (storedWidth_pos index) 2)

noncomputable def signedJetUpper2539 (order : ℕ) (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ) (position : ℝ) : ℝ :=
  ‖∑ index : Fin 30, centers index * weightedUnitJet2539 order sigma modulations index position‖ +
    ∑ index : Fin 30, errors index * ‖weightedUnitJet2539 order sigma modulations index position‖

theorem weightedPhysical2539_jet_le_center_error (order : ℕ) (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index) (position : ℝ) :
    ‖iteratedDeriv order (weightedPhysical2539 sigma coefficients modulations) position‖ ≤
      signedJetUpper2539 order sigma centers errors modulations position := by
  rw [weightedPhysical2539_iteratedDeriv]
  apply norm_sum_le_center_sum_add_error2531
  intro index _
  have heq : coefficients index * weightedUnitJet2539 order sigma modulations index position -
      centers index * weightedUnitJet2539 order sigma modulations index position =
      (coefficients index - centers index) *
        weightedUnitJet2539 order sigma modulations index position := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_right (herror index) (norm_nonneg _)

noncomputable def signedThirdCellUpper2539 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ) (a b : ℝ) : ℝ :=
  ∑ index : Fin 30, (‖centers index‖ + errors index) *
    weightedFamilyThirdCellUpper2538 sigma 1 (modulations index) (storedWidth index ^ 2) a b

theorem weightedPhysical2539_third_le_cell (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {a b : ℝ} (hab : a ≤ b) : ∀ x ∈ Set.Icc a b,
    ‖iteratedDeriv 3 (weightedPhysical2539 sigma coefficients modulations) x‖ ≤
      signedThirdCellUpper2539 sigma centers errors modulations a b := by
  intro x hx
  rw [weightedPhysical2539_iteratedDeriv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  have h := weightedExternalFamily_third_le_coefficient_ball2538 sigma
    (coefficients index) (centers index) (errors index) (modulations index)
    (pow_pos (storedWidth_pos index) 2) hab (herror index) x hx
  rw [weightedExternalFamily_coefficient_linear2539 3 sigma _ _
    (pow_pos (storedWidth_pos index) 2)] at h
  exact h

noncomputable def signedCurvatureUpper2539 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ) (a b : ℝ) : ℝ :=
  signedJetUpper2539 2 sigma centers errors modulations ((a+b)/2) +
    signedThirdCellUpper2539 sigma centers errors modulations a b * ((b-a)/2)

theorem weightedPhysical2539_second_le_signed_midpoint (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {a b : ℝ} (hab : a ≤ b) : ∀ x ∈ Set.Icc a b,
    ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖ ≤
      signedCurvatureUpper2539 sigma centers errors modulations a b := by
  let f := weightedPhysical2539 sigma coefficients modulations
  let L := signedThirdCellUpper2539 sigma centers errors modulations a b
  have hthird : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 3 f x‖ ≤ L :=
    weightedPhysical2539_third_le_cell sigma coefficients centers errors modulations herror hab
  have hL : 0 ≤ L := (norm_nonneg _).trans (hthird a ⟨le_rfl, hab⟩)
  have hsmooth := weightedPhysical2539_contDiff sigma coefficients modulations
  have hd : Differentiable ℝ (iteratedDeriv 2 f) :=
    ContDiff.differentiable_iteratedDeriv' 2 (hsmooth.of_le (by decide))
  have hmid : (a+b)/2 ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  intro x hx
  have hvariation := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd x)
    (fun x hx => by simpa only [← iteratedDeriv_succ] using hthird x hx)
    (convex_Icc a b) hmid hx
  have hdist : |x-(a+b)/2| ≤ (b-a)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hvariation' : ‖iteratedDeriv 2 f x - iteratedDeriv 2 f ((a+b)/2)‖ ≤
      L*|x-(a+b)/2| := by simpa only [Real.norm_eq_abs] using hvariation
  have hvar : ‖iteratedDeriv 2 f x - iteratedDeriv 2 f ((a+b)/2)‖ ≤ L*((b-a)/2) :=
    hvariation'.trans (mul_le_mul_of_nonneg_left hdist hL)
  have hcenter := weightedPhysical2539_jet_le_center_error 2 sigma coefficients centers
    errors modulations herror ((a+b)/2)
  change ‖iteratedDeriv 2 f x‖ ≤ _
  calc
    _ = ‖iteratedDeriv 2 f ((a+b)/2) +
        (iteratedDeriv 2 f x - iteratedDeriv 2 f ((a+b)/2))‖ := by congr 1; abel
    _ ≤ ‖iteratedDeriv 2 f ((a+b)/2)‖ +
        ‖iteratedDeriv 2 f x - iteratedDeriv 2 f ((a+b)/2)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hcenter hvar

theorem weightedPhysical2539_norm_integral_le_signed_cell (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, ‖weightedPhysical2539 sigma coefficients modulations x‖) ≤
      (b-a)/2 * (signedJetUpper2539 0 sigma centers errors modulations a +
        signedJetUpper2539 0 sigma centers errors modulations b) +
      signedCurvatureUpper2539 sigma centers errors modulations a b * (b-a)^3/12 := by
  have h := normIntegralChordUpper2347
    (weightedPhysical2539 sigma coefficients modulations)
    ((weightedPhysical2539_contDiff sigma coefficients modulations).of_le (by decide)) hab
    (by
      intro x hx
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        weightedPhysical2539_second_le_signed_midpoint sigma coefficients centers errors
          modulations herror hab.le x hx)
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ (b-a)/2)
  exact add_le_add
    (by
      simpa only [iteratedDeriv_zero] using
        weightedPhysical2539_jet_le_center_error
          0 sigma coefficients centers errors modulations herror a)
    (by
      simpa only [iteratedDeriv_zero] using
        weightedPhysical2539_jet_le_center_error
          0 sigma coefficients centers errors modulations herror b)

noncomputable def signedCompositeUpper2539 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (left step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells,
    (step/2 * (signedJetUpper2539 0 sigma centers errors modulations (left+index*step) +
      signedJetUpper2539 0 sigma centers errors modulations (left+(index+1)*step)) +
    signedCurvatureUpper2539 sigma centers errors modulations
      (left+index*step) (left+(index+1)*step) * step^3/12)

theorem weightedPhysical2539_norm_integral_le_signed_composite (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    (left step : ℝ) (cells : ℕ) (hstep : 0 < step) :
    (∫ x in left..(left+cells*step), ‖weightedPhysical2539 sigma coefficients modulations x‖) ≤
      signedCompositeUpper2539 sigma centers errors modulations left step cells := by
  have hcont := (weightedPhysical2539_contDiff sigma coefficients modulations).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 sigma coefficients modulations x‖) (μ := volume)
    (a := fun index : ℕ => left+index*step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (left+(index : ℝ)*step) (left+((index+1 : ℕ) : ℝ)*step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  rw [← hsum]
  unfold signedCompositeUpper2539
  apply Finset.sum_le_sum
  intro index _
  have horder : left+(index : ℝ)*step < left+((index : ℝ)+1)*step := by linarith
  have h := weightedPhysical2539_norm_integral_le_signed_cell sigma coefficients centers
    errors modulations herror horder
  have hwidth : (left+((index : ℝ)+1)*step)-(left+(index : ℝ)*step) = step := by ring
  simpa only [hwidth] using h

theorem externalPhysical2344_zero_at_or_beyond_pin2539
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {position : ℝ} (houtside : stripRadius2303 ≤ |position|) :
    externalPhysical2344 coefficients modulations position = 0 := by
  unfold externalPhysical2344
  apply Finset.sum_eq_zero
  intro index _
  have hwidth : storedWidth index ^ 2 ≤ |position| :=
    (storedWidth_sq_le_four index).trans (storedWidth_four_sq_le_pin.trans houtside)
  simp only [externalFamilyValue2344, if_neg (not_lt.mpr hwidth)]

theorem externalPhysical2344_strip_eq_interval2539 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    stripNorm sigma (externalPhysical2344 coefficients modulations) =
      ∫ x in (-stripRadius2303)..stripRadius2303,
        ‖weightedPhysical2539 sigma coefficients modulations x‖ := by
  have hsupp : Function.support (fun x => Real.exp (sigma*x) *
      ‖externalPhysical2344 coefficients modulations x‖) ⊆
      Set.Ioc (-stripRadius2303) stripRadius2303 := by
    intro x hx
    have hxinside : |x| < stripRadius2303 := by
      by_contra hn
      change Real.exp (sigma*x) * ‖externalPhysical2344 coefficients modulations x‖ ≠ 0 at hx
      apply hx
      rw [externalPhysical2344_zero_at_or_beyond_pin2539 coefficients modulations (not_lt.mp hn),
        norm_zero, mul_zero]
    exact ⟨(abs_lt.mp hxinside).1, (abs_lt.mp hxinside).2.le⟩
  unfold stripNorm
  simp only [weightedPhysical2539, weightedFunction2348_norm]
  exact (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupp).symm

theorem externalPhysical2344_strip_le_signed_10240_2539 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index) :
    stripNorm sigma (externalPhysical2344 coefficients modulations) ≤
      signedCompositeUpper2539 sigma centers errors modulations
        (-stripRadius2303) (2*stripRadius2303/10240) 10240 := by
  rw [externalPhysical2344_strip_eq_interval2539]
  have hstep : 0 < 2*stripRadius2303/10240 := by norm_num [stripRadius2303]
  have hgrid : -stripRadius2303 + (10240 : ℝ)*(2*stripRadius2303/10240) =
      stripRadius2303 := by ring
  have h := weightedPhysical2539_norm_integral_le_signed_composite sigma coefficients centers
    errors modulations herror (-stripRadius2303) (2*stripRadius2303/10240) 10240 hstep
  simpa only [Nat.cast_ofNat, hgrid] using h

end ConnesWeilRH.Dev
