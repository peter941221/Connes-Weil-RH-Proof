import ConnesWeilRH.Dev.C1RouteABatchC02703MinusIntegral2654
import ConnesWeilRH.Dev.C1RouteABatchC02704MinusIntegral2654
import ConnesWeilRH.Dev.C1RouteABatchC02703PlusIntegral2654
import ConnesWeilRH.Dev.C1RouteABatchC02704PlusIntegral2654

/-!
# Grid scale-out discharge (record 2654)

The first scale-out batch of the 2553-2559 generator pipeline: cells
2703/2704, BOTH signs, forty modules built green in the same session
(the `--record`/`--payload` generator extension).  Each cell's
integral certificate is conditional on the standard coefficient-ball
hypothesis; this record discharges all four in the two standard
forms established by records 2650-2652:

1. region form - the bound holds for EVERY tuple inside the
   record-2338 base boxes;
2. unconditional form - zero premises, at the exact-rational center
   owner.

Discharged uppers: cell2703 minus `2283/10^12`, cell2704 minus
`2203/10^12`, cell2703 plus `13/125000000000`, cell2704 plus
`101/10^12`.

Scope: cells 2703/2704, sigma = -+1/2, modulations fixed at
`nodeModulation2541`.  No other cell, sign, or grid claim.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-- Region form, cell2703 minus. -/
theorem batchC02703MinusCellBoxDischarge2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN02703MinusPosition2654..batchN02704MinusPosition2654,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02703MinusCellIntegralUpper2654 :=
  batchC02703MinusCellIntegralBound2654 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form, cell2703 minus. -/
theorem batchC02703MinusCellCenterDischarge2654 :
    (∫ x in batchN02703MinusPosition2654..batchN02704MinusPosition2654,
      ‖weightedPhysical2539 (-1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02703MinusCellIntegralUpper2654 :=
  batchC02703MinusCellBoxDischarge2654 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Region form, cell2704 minus. -/
theorem batchC02704MinusCellBoxDischarge2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN02704MinusPosition2654..batchN02705MinusPosition2654,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02704MinusCellIntegralUpper2654 :=
  batchC02704MinusCellIntegralBound2654 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form, cell2704 minus. -/
theorem batchC02704MinusCellCenterDischarge2654 :
    (∫ x in batchN02704MinusPosition2654..batchN02705MinusPosition2654,
      ‖weightedPhysical2539 (-1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02704MinusCellIntegralUpper2654 :=
  batchC02704MinusCellBoxDischarge2654 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Region form, cell2703 plus. -/
theorem batchC02703PlusCellBoxDischarge2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN02703PlusPosition2654..batchN02704PlusPosition2654,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02703PlusCellIntegralUpper2654 :=
  batchC02703PlusCellIntegralBound2654 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form, cell2703 plus. -/
theorem batchC02703PlusCellCenterDischarge2654 :
    (∫ x in batchN02703PlusPosition2654..batchN02704PlusPosition2654,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02703PlusCellIntegralUpper2654 :=
  batchC02703PlusCellBoxDischarge2654 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Region form, cell2704 plus. -/
theorem batchC02704PlusCellBoxDischarge2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN02704PlusPosition2654..batchN02705PlusPosition2654,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02704PlusCellIntegralUpper2654 :=
  batchC02704PlusCellIntegralBound2654 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form, cell2704 plus. -/
theorem batchC02704PlusCellCenterDischarge2654 :
    (∫ x in batchN02704PlusPosition2654..batchN02705PlusPosition2654,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02704PlusCellIntegralUpper2654 :=
  batchC02704PlusCellBoxDischarge2654 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Display anchors: the certified uppers are exact. -/
theorem batchC02703MinusUpperValue2654 :
    batchC02703MinusCellIntegralUpper2654 = ((2283 : ℝ) / 1000000000000) := rfl

theorem batchC02704MinusUpperValue2654 :
    batchC02704MinusCellIntegralUpper2654 = ((2203 : ℝ) / 1000000000000) := rfl

theorem batchC02703PlusUpperValue2654 :
    batchC02703PlusCellIntegralUpper2654 = ((13 : ℝ) / 125000000000) := rfl

theorem batchC02704PlusUpperValue2654 :
    batchC02704PlusCellIntegralUpper2654 = ((101 : ℝ) / 1000000000000) := rfl

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703MinusCellBoxDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusCellCenterDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusCellBoxDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusCellCenterDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCellBoxDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCellCenterDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusCellBoxDischarge2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusCellCenterDischarge2654
