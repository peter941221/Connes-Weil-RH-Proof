import ConnesWeilRH.Dev.C1RouteASignedSegment2558
import ConnesWeilRH.Dev.C1RouteACentralSegment2559
import ConnesWeilRH.Dev.C1RouteABatchC02702MinusIntegral2558
import ConnesWeilRH.Dev.C1RouteABatchC02702PlusIntegral2558

/-!
# Boundary-integral discharge, complete conditional inventory (record 2652)

Records 2650/2651 discharged the 2551/2546 cell certificates.  A full
inventory sweep then found that the 2553-2559 batch era had committed
the SAME ball-conditional shape across the whole signed-segment
family; the 2649 lane-A audit undercounted this inventory because it
scanned only four payloads.  This record discharges every top-level
boundary-integral certificate in that family, in the two standard
forms:

* region form (`_boxDischarge2652`): the bound holds for EVERY
  coefficient tuple in the record-2338 base boxes;
* unconditional form (`_center_discharge2652`): zero premises, at the
  exact-rational box-center tuple.

Targets (composition tops, so coverage is maximal):

1. `bothSignsSegmentIntegralBound2558` - plus AND minus integrals over
   `edgeLeftPosition2548..neighborRightPosition2557` (cells 2700/2701,
   both signs, plus side composed from 2551 + 2557), sum <= 5159/10^12.
2. `centralBothSignsIntegralBound2559` - plus AND minus integrals over
   `batchN05119*Position2559..batchN05121*Position2559` (cells
   5119/5120, both signs), sum <= 35314967257/500000000000.
3. `batchC02702MinusCellIntegralBound2558` - cell 2702 minus,
   <= 59/25000000000.
4. `batchC02702PlusCellIntegralBound2558` - cell 2702 plus,
   <= 27/250000000000.

After this record no committed boundary-integral certificate in the
2551-2559 family retains the coefficient-ball premise in discharged
form.  Scope: these cells and spans only, modulations fixed at
`nodeModulation2541`; exact-owner transfer and full-grid coverage
remain open.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-! ### Target 1: the signed segment over cells 2700/2701 (both signs) -/

/-- Region form of the both-signs segment bound. -/
theorem boundaryBothSigns_boxDischarge2652 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) +
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
      (5159 : ℝ) / 1000000000000 :=
  bothSignsSegmentIntegralBound2558 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form: zero premises at the exact-rational center
tuple. -/
theorem boundaryBothSigns_center_discharge2652 :
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) +
    (∫ x in edgeLeftPosition2548..neighborRightPosition2557,
      ‖weightedPhysical2539 (-1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤
      (5159 : ℝ) / 1000000000000 :=
  boundaryBothSigns_boxDischarge2652 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-! ### Target 2: the central both-signs segment over cells 5119/5120 -/

/-- Region form of the central both-signs bound. -/
theorem centralBothSigns_boxDischarge2652 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) +
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
      ((35314967257 : ℝ) / 500000000000) :=
  centralBothSignsIntegralBound2559 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form: zero premises at the exact-rational center
tuple. -/
theorem centralBothSigns_center_discharge2652 :
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) +
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (-1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤
      ((35314967257 : ℝ) / 500000000000) :=
  centralBothSigns_boxDischarge2652 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-! ### Target 3: cell 2702 minus -/

/-- Region form of the cell-2702 minus bound. -/
theorem cell2702minus_boxDischarge2652 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in batchN02702MinusPosition2558..batchN02703MinusPosition2558,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02702MinusCellIntegralUpper2558 :=
  batchC02702MinusCellIntegralBound2558 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form of the cell-2702 minus bound. -/
theorem cell2702minus_center_discharge2652 :
    (∫ x in batchN02702MinusPosition2558..batchN02703MinusPosition2558,
      ‖weightedPhysical2539 (-1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02702MinusCellIntegralUpper2558 :=
  cell2702minus_boxDischarge2652 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Display anchor: the cell-2702 minus upper. -/
theorem cell2702minus_upper_value2652 :
    batchC02702MinusCellIntegralUpper2558 = ((59 : ℝ) / 25000000000) := rfl

/-! ### Target 4: cell 2702 plus -/

/-- Region form of the cell-2702 plus bound. -/
theorem cell2702plus_boxDischarge2652 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    (∫ x in neighborRightPosition2557..batchN02703PlusPosition2558,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
      batchC02702PlusCellIntegralUpper2558 :=
  batchC02702PlusCellIntegralBound2558 coefficients
    (fun i => baseCoefficient_error_of_box2540 i _ (hbox i))

/-- Unconditional form of the cell-2702 plus bound. -/
theorem cell2702plus_center_discharge2652 :
    (∫ x in neighborRightPosition2557..batchN02703PlusPosition2558,
      ‖weightedPhysical2539 (1/2) baseCoefficientCenter2540
        nodeModulation2541 x‖) ≤ batchC02702PlusCellIntegralUpper2558 :=
  cell2702plus_boxDischarge2652 baseCoefficientCenter2540
    baseCoefficientCenter_mem2540

/-- Display anchor: the cell-2702 plus upper. -/
theorem cell2702plus_upper_value2652 :
    batchC02702PlusCellIntegralUpper2558 = ((27 : ℝ) / 250000000000) := rfl

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.boundaryBothSigns_center_discharge2652
#print axioms ConnesWeilRH.Dev.centralBothSigns_center_discharge2652
#print axioms ConnesWeilRH.Dev.cell2702minus_center_discharge2652
#print axioms ConnesWeilRH.Dev.cell2702plus_center_discharge2652
