import ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2704_2580
import ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2703_2579

namespace ConnesWeilRH.Dev

open MeasureTheory


theorem nodeSecondChordMinusSpan2580Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02703MinusPointPosition2577..nodeJet2N02705MinusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordMinus2579Upper + nodeSecondChordMinus2580Upper := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff (-1/2) coefficients nodeModulation2541).of_le
        (by decide))).continuous.norm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable nodeJet2N02703MinusPointPosition2577
        nodeJet2N02704MinusPointPosition2577)
    (hcont.intervalIntegrable nodeJet2N02704MinusPointPosition2577
        nodeJet2N02705MinusPointPosition2577)]
  exact add_le_add (nodeSecondChordMinus2579Integral_le coefficients herror)
    (nodeSecondChordMinus2580Integral_le coefficients herror)

theorem nodeSecondChordPlusSpan2580Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02703PlusPointPosition2577..nodeJet2N02705PlusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordPlus2579Upper + nodeSecondChordPlus2580Upper := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff (1/2) coefficients nodeModulation2541).of_le
        (by decide))).continuous.norm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable nodeJet2N02703PlusPointPosition2577
        nodeJet2N02704PlusPointPosition2577)
    (hcont.intervalIntegrable nodeJet2N02704PlusPointPosition2577
        nodeJet2N02705PlusPointPosition2577)]
  exact add_le_add (nodeSecondChordPlus2579Integral_le coefficients herror)
    (nodeSecondChordPlus2580Integral_le coefficients herror)

end ConnesWeilRH.Dev
