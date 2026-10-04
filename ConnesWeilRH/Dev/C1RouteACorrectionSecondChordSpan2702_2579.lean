import ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2703_2579
import ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2702_2578

namespace ConnesWeilRH.Dev

open MeasureTheory


theorem nodeSecondChordMinusSpan2579Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02702MinusPointPosition2577..nodeJet2N02704MinusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordMinus2578Upper + nodeSecondChordMinus2579Upper := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff (-1/2) coefficients nodeModulation2541).of_le
        (by decide))).continuous.norm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable nodeJet2N02702MinusPointPosition2577
        nodeJet2N02703MinusPointPosition2577)
    (hcont.intervalIntegrable nodeJet2N02703MinusPointPosition2577
        nodeJet2N02704MinusPointPosition2577)]
  exact add_le_add (nodeSecondChordMinus2578Integral_le coefficients herror)
    (nodeSecondChordMinus2579Integral_le coefficients herror)

theorem nodeSecondChordPlusSpan2579Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02702PlusPointPosition2577..nodeJet2N02704PlusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordPlus2578Upper + nodeSecondChordPlus2579Upper := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff (1/2) coefficients nodeModulation2541).of_le
        (by decide))).continuous.norm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable nodeJet2N02702PlusPointPosition2577
        nodeJet2N02703PlusPointPosition2577)
    (hcont.intervalIntegrable nodeJet2N02703PlusPointPosition2577
        nodeJet2N02704PlusPointPosition2577)]
  exact add_le_add (nodeSecondChordPlus2578Integral_le coefficients herror)
    (nodeSecondChordPlus2579Integral_le coefficients herror)

end ConnesWeilRH.Dev
