import ConnesWeilRH.Dev.C1RouteABoundaryIntegral2551
import ConnesWeilRH.Dev.C1RouteANeighborIntegral2557

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem neighborSegmentIntegralBound2557 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        (225 : ℝ) / 1000000000000 := by
  let a : ℕ → ℝ := fun i => if i = 0 then edgeLeftPosition2548
    else if i = 1 then edgeRightPosition2548 else neighborRightPosition2557
  have hcont :=
    (weightedPhysical2539_contDiff (1/2) coefficients nodeModulation2541).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖)
    (μ := MeasureTheory.volume) (a := a) (n := 2)
    (fun i _ => hcont.intervalIntegrable (a i) (a (i+1)))
  have hleft := boundaryCellIntegralBound2551 coefficients hcoeff
  have hright := neighborCellIntegralBound2557 coefficients hcoeff
  have heq : kernelN02701PlusPosition2555 = edgeRightPosition2548 := by
    norm_num [kernelN02701PlusPosition2555, edgeRightPosition2548]
  rw [heq] at hright
  norm_num [Finset.sum_range_succ, a] at hsum
  rw [← hsum]
  have h := add_le_add hleft hright
  norm_num [boundaryCellIntegralUpper2551, neighborCellIntegralUpper2557] at h
  simpa only [show (225 : ℝ) / 1000000000000 = 9 / 40000000000 by norm_num] using h

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborSegmentIntegralBound2557
