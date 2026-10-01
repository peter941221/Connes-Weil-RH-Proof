import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget
import ConnesWeilRH.Dev.C1RouteACoordinateCharge

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem familyDerivativeBudget2350_nonneg
    (order : ℕ) (coefficient : ℂ) (modulation radius : ℝ)
    (hradius : 0 < radius) :
    0 ≤ familyDerivativeBudget2350 order coefficient modulation radius := by
  unfold familyDerivativeBudget2350
  positivity

theorem ownerDerivativeBudget2350_nonneg
    (order : ℕ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    0 ≤ ownerDerivativeBudget2350 order coefficients modulations := by
  unfold ownerDerivativeBudget2350
  apply Finset.sum_nonneg
  intro index hindex
  exact familyDerivativeBudget2350_nonneg order (coefficients index) (modulations index)
    (storedWidth_pos index).pow_pos

theorem correctedPhysical_weighted_coordinate_segment2359
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma a b : ℝ)
    (hsegment : ∀ x ∈ Set.Icc a b,
      x ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2)) :
    ∀ x ∈ Set.Icc a b,
      ‖weightedFunction2348 sigma (correctedPhysical coefficients modulations) x‖ ≤
        ‖weightedFunction2348 sigma (correctedPhysical coefficients modulations) a‖ +
          Real.exp (|sigma| * storedWidth 4 ^ 2) *
            (|sigma| * ownerDerivativeBudget2350 0 coefficients modulations +
              ownerDerivativeBudget2350 1 coefficients modulations) * (x - a) := by
  apply weightedFunction2348_norm_le_of_coordinate_segment2359 sigma
    (correctedPhysical coefficients modulations)
    ((correctedPhysical_contDiff coefficients modulations).of_le (by decide))
    (storedWidth 4 ^ 2) a b
    (ownerDerivativeBudget2350 0 coefficients modulations)
    (ownerDerivativeBudget2350 1 coefficients modulations)
  · intro x hx
    exact abs_le.mpr (hsegment x hx)
  · exact ownerDerivativeBudget2350_nonneg 0 coefficients modulations
  · exact ownerDerivativeBudget2350_nonneg 1 coefficients modulations
  · intro x hx
    simpa only [iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 0 (by decide) coefficients modulations x
  · intro x hx
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 1 (by decide) coefficients modulations x

theorem correctedPhysical_weighted_coordinate_transfer2359
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma actual ideal : ℝ)
    (hsegment : ∀ x ∈ Set.Icc (min actual ideal) (max actual),
      x ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2)) :
    ‖weightedFunction2348 sigma (correctedPhysical coefficients modulations) ideal‖ ≤
      ‖weightedFunction2348 sigma (correctedPhysical coefficients modulations) actual‖ +
        Real.exp (|sigma| * storedWidth 4 ^ 2) *
          (|sigma| * ownerDerivativeBudget2350 0 coefficients modulations +
            ownerDerivativeBudget2350 1 coefficients modulations) * |ideal - actual| := by
  have hsmooth := (correctedPhysical_contDiff coefficients modulations).of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hzero : ∀ x ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖correctedPhysical coefficients modulations x‖ ≤
        ownerDerivativeBudget2350 0 coefficients modulations := by
    intro x hx
    simpa only [iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 0 (by decide) coefficients modulations x
  have hfirst : ∀ x ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (correctedPhysical coefficients modulations) x‖ ≤
        ownerDerivativeBudget2350 1 coefficients modulations := by
    intro x hx
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 1 (by decide) coefficients modulations x
  rcases le_total actual ideal with hactual | hideal
  · have h := correctedPhysical_weighted_coordinate_segment2359 coefficients modulations
      sigma actual ideal (by
        intro x hx
        simpa [min_eq_left hactual, max_eq_right hactual] using hsegment x hx)
    have hpoint := h ideal ⟨le_rfl, hactual⟩
    simpa [abs_of_nonneg (sub_nonneg.mpr hactual)] using hpoint
  · have h := weightedFunction2348_norm_at_left_le_of_coordinate_segment2359 sigma
      (correctedPhysical coefficients modulations) hsmooth
      (storedWidth 4 ^ 2) ideal actual
      (ownerDerivativeBudget2350 0 coefficients modulations)
      (ownerDerivativeBudget2350 1 coefficients modulations)
      (by
        intro x hx
        simpa [min_eq_right hideal, max_eq_left hideal] using hsegment x hx)
      (ownerDerivativeBudget2350_nonneg 0 coefficients modulations)
      (ownerDerivativeBudget2350_nonneg 1 coefficients modulations) hzero hfirst
    simpa [abs_of_nonneg (sub_nonneg.mpr hideal)] using h

end ConnesWeilRH.Dev
