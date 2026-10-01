import ConnesWeilRH.Dev.C1RouteAOwnerCoordinateCharge
import ConnesWeilRH.Dev.C1RouteAWeightedChordPanel

namespace ConnesWeilRH.Dev

open scoped BigOperators

def compositeCellUpper2387 (nodeUpper : ℕ → ℝ) (step : ℝ) (index : ℕ) : ℝ :=
  step * ((nodeUpper index + nodeUpper (index + 1)) / 2)

theorem compositeNodeUpper_eq_sum_cellUpper2387
    (nodeUpper : ℕ → ℝ) (step : ℝ) (cells : ℕ) :
    compositeNodeUpper2347 nodeUpper step cells =
      ∑ index ∈ Finset.range cells, compositeCellUpper2387 nodeUpper step index := by
  unfold compositeNodeUpper2347 compositeCellUpper2387
  apply Finset.sum_congr rfl
  intro index hindex
  ring

theorem compositeNodeUpper_mono2387
    (actualUpper finalUpper : ℕ → ℝ) (step : ℝ) (cells : ℕ)
    (hstep : 0 ≤ step)
    (hnodes : ∀ index ≤ cells, actualUpper index ≤ finalUpper index) :
    compositeNodeUpper2347 actualUpper step cells ≤
      compositeNodeUpper2347 finalUpper step cells := by
  unfold compositeNodeUpper2347
  apply Finset.sum_le_sum
  intro index hindex
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hstep (by norm_num))
  have hleft := hnodes index (Nat.le_of_lt (Finset.mem_range.mp hindex))
  have hright := hnodes (index + 1)
    (Nat.succ_le_of_lt (Finset.mem_range.mp hindex))
  exact add_le_add hleft hright

theorem compositeNodeUpper_add_constant2359
    (nodeUpper : ℕ → ℝ) (step charge : ℝ) (cells : ℕ) :
    compositeNodeUpper2347 (fun index => nodeUpper index + charge) step cells =
      compositeNodeUpper2347 nodeUpper step cells + charge * (cells : ℝ) * step := by
  unfold compositeNodeUpper2347
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · intro index hindex
    ring

theorem compositeNodeUpper_add_coordinate_charge2359
    (nodeUpper : ℕ → ℝ) (step charge : ℝ) (cells : ℕ)
    (hcharge : 0 ≤ charge) :
    compositeNodeUpper2347 (fun index => nodeUpper index + charge) step cells =
      compositeNodeUpper2347 nodeUpper step cells +
        (cells : ℝ) * step * charge := by
  rw [compositeNodeUpper_add_constant2359]
  ring

theorem compositeNodeUpper_le_of_nodewise_coordinate_charge2359
    (actualValue idealValue : ℕ → ℝ) (step charge : ℝ) (cells : ℕ)
    (hstep : 0 ≤ step) (hcharge : 0 ≤ charge)
    (hnode : ∀ index ≤ cells, idealValue index ≤ actualValue index + charge) :
    compositeNodeUpper2347 idealValue step cells ≤
      compositeNodeUpper2347 actualValue step cells +
        (cells : ℝ) * step * charge := by
  calc
    compositeNodeUpper2347 idealValue step cells ≤
        compositeNodeUpper2347 (fun index => actualValue index + charge) step cells := by
      unfold compositeNodeUpper2347
      apply Finset.sum_le_sum
      intro index hindex
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hstep (by norm_num))
      have hleft := hnode index (Nat.le_of_lt (Finset.mem_range.mp hindex))
      have hright := hnode (index + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hindex))
      exact add_le_add hleft hright
    _ = compositeNodeUpper2347 actualValue step cells +
        (cells : ℝ) * step * charge := by
      rw [compositeNodeUpper_add_coordinate_charge2359 _ _ _ _ hcharge]

theorem correctedPhysical_stripNorm_le_of_actual_coordinate_charge2359
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step : ℝ) (cells : ℕ) (actualCoordinate actualUpper : ℕ → ℝ)
    (charge : ℝ) (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hcharge : 0 ≤ charge)
    (hactual : ∀ index ≤ cells,
      Real.exp (sigma * (actualCoordinate index)) *
        ‖correctedPhysical coefficients modulations (actualCoordinate index)‖ ≤
          actualUpper index)
    (htransfer : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
          ‖correctedPhysical coefficients modulations
            (-(storedWidth 4 ^ 2) + index * step)‖ ≤
        Real.exp (sigma * (actualCoordinate index)) *
            ‖correctedPhysical coefficients modulations (actualCoordinate index)‖ + charge) :
    stripNorm sigma (correctedPhysical coefficients modulations) ≤
      compositeNodeUpper2347 actualUpper step cells + (cells : ℝ) * step * charge +
        step ^ 2 * (2 * storedWidth 4 ^ 2) *
          weightedCurvature2348 sigma (storedWidth 4 ^ 2)
            (ownerDerivativeBudget2350 0 coefficients modulations)
            (ownerDerivativeBudget2350 1 coefficients modulations)
            (ownerDerivativeBudget2350 2 coefficients modulations) / 12 := by
  have hideal : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
          ‖correctedPhysical coefficients modulations
            (-(storedWidth 4 ^ 2) + index * step)‖ ≤
        actualUpper index + charge := by
    intro index hindex
    exact (htransfer index hindex).trans (add_le_add_right (hactual index hindex) _)
  have hpanel := correctedPhysical_stripNorm_le_nodeUpper_from_budget2350
    coefficients modulations sigma step cells
    (fun index => actualUpper index + charge) hstep hgrid hideal
  rw [compositeNodeUpper_add_coordinate_charge2359 actualUpper step charge cells hcharge] at hpanel
  exact hpanel

theorem correctedPhysical_stripNorm_le_of_nodeUpper_scalar2389
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step scalar : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
        ‖correctedPhysical coefficients modulations
          (-(storedWidth 4 ^ 2) + index * step)‖ ≤ nodeUpper index)
    (hscalar : compositeNodeUpper2347 nodeUpper step cells ≤ scalar) :
    stripNorm sigma (correctedPhysical coefficients modulations) ≤
      scalar + step ^ 2 * (2 * storedWidth 4 ^ 2) *
        weightedCurvature2348 sigma (storedWidth 4 ^ 2)
          (ownerDerivativeBudget2350 0 coefficients modulations)
          (ownerDerivativeBudget2350 1 coefficients modulations)
          (ownerDerivativeBudget2350 2 coefficients modulations) / 12 := by
  have hpanel := correctedPhysical_stripNorm_le_nodeUpper_from_budget2350
    coefficients modulations sigma step cells nodeUpper hstep hgrid hnodes
  exact hpanel.trans (add_le_add_right hscalar _)

end ConnesWeilRH.Dev
