import ConnesWeilRH.Dev.C1RouteAOwnerCoordinateCharge
import ConnesWeilRH.Dev.C1RouteAWeightedChordPanel

namespace ConnesWeilRH.Dev

open scoped BigOperators

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

end ConnesWeilRH.Dev
