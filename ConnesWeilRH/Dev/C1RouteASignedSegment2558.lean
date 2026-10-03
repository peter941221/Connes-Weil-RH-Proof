import ConnesWeilRH.Dev.C1RouteABatchC02700MinusIntegral2558
import ConnesWeilRH.Dev.C1RouteABatchC02701MinusIntegral2558
import ConnesWeilRH.Dev.C1RouteANeighborSegment2557

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem negativeSegmentIntegralBound2558 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in kernelN02700MinusPosition2555..batchN02702MinusPosition2558,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
        (4934 : ℝ) / 1000000000000 := by
  let a : ℕ → ℝ := fun i => if i = 0 then kernelN02700MinusPosition2555
    else if i = 1 then kernelN02701MinusPosition2555 else batchN02702MinusPosition2558
  have hcont :=
    (weightedPhysical2539_contDiff (-1/2) coefficients nodeModulation2541).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖)
    (μ := MeasureTheory.volume) (a := a) (n := 2)
    (fun i _ => hcont.intervalIntegrable (a i) (a (i+1)))
  have hleft := batchC02700MinusCellIntegralBound2558 coefficients hcoeff
  have hright := batchC02701MinusCellIntegralBound2558 coefficients hcoeff
  norm_num [Finset.sum_range_succ, a] at hsum
  have hs : (-1 : ℝ) / 2 = -(1 / 2) := by norm_num
  rw [hs] at hleft hright ⊢
  rw [← hsum]
  have h := add_le_add hleft hright
  norm_num [batchC02700MinusCellIntegralUpper2558,
    batchC02701MinusCellIntegralUpper2558] at h
  simpa only [show (4934 : ℝ) / 1000000000000 = 2467 / 500000000000 by norm_num] using h

theorem bothSignsSegmentIntegralBound2558 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) +
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
        (5159 : ℝ) / 1000000000000 := by
  have hp := neighborSegmentIntegralBound2557 coefficients hcoeff
  have hn := negativeSegmentIntegralBound2558 coefficients hcoeff
  have hl : kernelN02700MinusPosition2555 = edgeLeftPosition2548 := by
    norm_num [kernelN02700MinusPosition2555, edgeLeftPosition2548]
  have hr : batchN02702MinusPosition2558 = neighborRightPosition2557 := by
    norm_num [batchN02702MinusPosition2558, neighborRightPosition2557]
  rw [hl, hr] at hn
  have h := add_le_add hp hn
  convert h using 1
  norm_num

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.negativeSegmentIntegralBound2558
#print axioms ConnesWeilRH.Dev.bothSignsSegmentIntegralBound2558
