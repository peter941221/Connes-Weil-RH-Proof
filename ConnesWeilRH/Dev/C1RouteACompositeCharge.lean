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

end ConnesWeilRH.Dev
