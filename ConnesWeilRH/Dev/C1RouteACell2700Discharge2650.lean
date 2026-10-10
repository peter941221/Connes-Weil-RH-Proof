import ConnesWeilRH.Dev.C1RouteABoundaryIntegral2551

/-!
# Cell2700 discharge (record 2650)

The 2551 boundary-integral certificate is conditional on the
coefficient-ball hypothesis `forall i, ||coefficients i -
baseCoefficientCenter2540 i|| <= baseCoefficientError2540 i`.  This
record discharges that hypothesis against the record-2338 coefficient
region in two forms:

1. `cell2700_boxDischarge2650` - the bound holds for EVERY coefficient
   tuple inside the record-2338 base boxes (the certified region of
   the interpolation repair).  The bridge is
   `baseCoefficient_error_of_box2540`: box membership forces the ball.
2. `cell2700_center_discharge2650` - instantiating at the exact
   rational box-center tuple removes the hypothesis entirely: the
   cell2700 integral upper `57 / 500000000000` holds unconditionally
   at the center owner, with no premise left in the statement.

Scope: cell2700, sigma = 1/2, modulation tuple fixed at
`nodeModulation2541`.  No other cell, sign, or grid claim; the
exact-owner transfer (asserting that a live external computation's
coefficients lie in the boxes) remains open.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-- Region form: the 2551 certificate extends from the ball to the
whole record-2338 coefficient region. -/
theorem cell2700_boxDischarge2650 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
      boundaryCellIntegralUpper2551 :=
  boundaryCellIntegralBound2551 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form: zero premises - the concrete exact-rational
center tuple satisfies the certificate outright. -/
theorem cell2700_center_discharge2650 :
    (∫ x in edgeLeftPosition2548..edgeRightPosition2548,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ boundaryCellIntegralUpper2551 :=
  cell2700_boxDischarge2650 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Display anchor: the certified upper is exactly 57 / 5·10^11. -/
theorem cell2700_upper_value2650 :
    boundaryCellIntegralUpper2551 = ((57 : ℝ) / 500000000000) := rfl

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.cell2700_boxDischarge2650
#print axioms ConnesWeilRH.Dev.cell2700_center_discharge2650
