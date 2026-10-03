import ConnesWeilRH.Dev.C1RouteABatchC05119PlusIntegral2559
import ConnesWeilRH.Dev.C1RouteABatchC05120PlusIntegral2559
import ConnesWeilRH.Dev.C1RouteABatchC05119MinusIntegral2559
import ConnesWeilRH.Dev.C1RouteABatchC05120MinusIntegral2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem centralPlusIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤ ((35314964141 : ℝ) /
        1000000000000) := by
  let a : ℕ → ℝ := fun i => if i = 0 then batchN05119PlusPosition2559
    else if i = 1 then batchN05120PlusPosition2559 else batchN05121PlusPosition2559
  have hcont :=
    (weightedPhysical2539_contDiff (1/2) coefficients nodeModulation2541).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖)
    (μ := MeasureTheory.volume) (a := a) (n := 2)
    (fun i _ => hcont.intervalIntegrable (a i) (a (i+1)))
  have hleft := batchC05119PlusCellIntegralBound2559 coefficients hcoeff
  have hright := batchC05120PlusCellIntegralBound2559 coefficients hcoeff
  norm_num [Finset.sum_range_succ, a] at hsum
  rw [← hsum]
  have h := add_le_add hleft hright
  norm_num [batchC05119PlusCellIntegralUpper2559, batchC05120PlusCellIntegralUpper2559] at h ⊢
  exact h

theorem centralMinusIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in batchN05119MinusPosition2559..batchN05121MinusPosition2559,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤ ((35314970373 : ℝ) /
        1000000000000) := by
  let a : ℕ → ℝ := fun i => if i = 0 then batchN05119MinusPosition2559
    else if i = 1 then batchN05120MinusPosition2559 else batchN05121MinusPosition2559
  have hcont :=
    (weightedPhysical2539_contDiff (-1/2) coefficients nodeModulation2541).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖)
    (μ := MeasureTheory.volume) (a := a) (n := 2)
    (fun i _ => hcont.intervalIntegrable (a i) (a (i+1)))
  have hleft := batchC05119MinusCellIntegralBound2559 coefficients hcoeff
  have hright := batchC05120MinusCellIntegralBound2559 coefficients hcoeff
  norm_num [Finset.sum_range_succ, a] at hsum
  have hs : (-1 : ℝ) / 2 = -(1 / 2) := by norm_num
  rw [hs] at hleft hright ⊢
  rw [← hsum]
  have h := add_le_add hleft hright
  norm_num [batchC05119MinusCellIntegralUpper2559, batchC05120MinusCellIntegralUpper2559] at h ⊢
  exact h

theorem centralBothSignsIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) +
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤ ((35314967257 : ℝ) /
        500000000000) := by
  have hp := centralPlusIntegralBound2559 coefficients hcoeff
  have hn := centralMinusIntegralBound2559 coefficients hcoeff
  have hl : batchN05119MinusPosition2559 = batchN05119PlusPosition2559 := by
    norm_num [batchN05119MinusPosition2559, batchN05119PlusPosition2559]
  have hr : batchN05121MinusPosition2559 = batchN05121PlusPosition2559 := by
    norm_num [batchN05121MinusPosition2559, batchN05121PlusPosition2559]
  rw [hl, hr] at hn
  have h := add_le_add hp hn
  convert h using 1
  norm_num

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.centralPlusIntegralBound2559
#print axioms ConnesWeilRH.Dev.centralMinusIntegralBound2559
#print axioms ConnesWeilRH.Dev.centralBothSignsIntegralBound2559
