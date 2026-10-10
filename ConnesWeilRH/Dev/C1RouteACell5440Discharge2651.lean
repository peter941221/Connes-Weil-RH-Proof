import ConnesWeilRH.Dev.C1RouteACellIntegral2546

/-!
# Cell5440 discharge (record 2651)

The 2546 cell-integral certificate is conditional on the same
coefficient-ball hypothesis as 2551.  Record 2650 established the
discharge pattern for cell2700; this record applies it to cell5440
verbatim, clearing the last sigma = +1/2 conditional entry of the
lane-A audit inventory:

1. `cell5440_boxDischarge2651` - region form: the 2546 bound holds
   for EVERY coefficient tuple inside the record-2338 base boxes.
2. `cell5440_center_discharge2651` - unconditional form: zero
   premises; the cell5440 integral upper `379207837/500000000000`
   holds outright at the exact-rational center owner.

Scope: cell5440, sigma = 1/2, modulations fixed at
`nodeModulation2541`, interval
`endpointLeftPosition2544..endpointRightPosition2544`.  No other
cell, sign, or grid claim.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-- Region form: the 2546 certificate extends from the ball to the
whole record-2338 coefficient region. -/
theorem cell5440_boxDischarge2651 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in endpointLeftPosition2544..endpointRightPosition2544,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
      cellIntegralUpper2546 :=
  cellIntegralBound2546 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form: zero premises - the concrete exact-rational
center tuple satisfies the certificate outright. -/
theorem cell5440_center_discharge2651 :
    (∫ x in endpointLeftPosition2544..endpointRightPosition2544,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ cellIntegralUpper2546 :=
  cell5440_boxDischarge2651 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Display anchor: the certified upper is exactly
379207837 / 5·10^11. -/
theorem cell5440_upper_value2651 :
    cellIntegralUpper2546 = ((379207837 : ℝ) / 500000000000) := rfl

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.cell5440_boxDischarge2651
#print axioms ConnesWeilRH.Dev.cell5440_center_discharge2651
