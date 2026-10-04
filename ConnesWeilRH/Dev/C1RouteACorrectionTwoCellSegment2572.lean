import ConnesWeilRH.Dev.C1RouteACorrectionSecondCell2700MinusCorr2570
import ConnesWeilRH.Dev.C1RouteACorrectionSecondCell2701MinusCorr2572

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def correctionCellAffine2572
    (sigma step curvature firstJet leftValue rightValue : ℝ) : ℝ :=
  step * curvature + 2 * |sigma| * step * (firstJet + curvature * (step / 2)) +
    sigma ^ 2 * (step / 2 * (leftValue + rightValue) + curvature * (step ^ 3 / 12))

theorem correctionCellAffine_eq2572
    (sigma step curvature firstJet leftValue rightValue : ℝ) :
    correctionCellAffine2572 sigma step curvature firstJet leftValue rightValue =
      (step + |sigma| * step ^ 2 + sigma ^ 2 * step ^ 3 / 12) * curvature +
      (2 * |sigma| * step) * firstJet +
      (sigma ^ 2 * step / 2) * (leftValue + rightValue) := by
  unfold correctionCellAffine2572
  ring

theorem correctionCellAffine_sum2572 {cells : ℕ}
    (sigma step : ℝ) (curvature firstJet leftValue rightValue : Fin cells → ℝ) :
    (∑ index : Fin cells, correctionCellAffine2572 sigma step (curvature index)
      (firstJet index) (leftValue index) (rightValue index)) =
      (step + |sigma| * step ^ 2 + sigma ^ 2 * step ^ 3 / 12) * (∑ index, curvature index) +
      (2 * |sigma| * step) * (∑ index, firstJet index) +
      (sigma ^ 2 * step / 2) * (∑ index, (leftValue index + rightValue index)) := by
  simp only [correctionCellAffine_eq2572]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]

theorem correctionCellAffine_sign2572
    (step curvature firstJet leftValue rightValue : ℝ) :
    correctionCellAffine2572 (-1 / 2) step curvature firstJet leftValue rightValue =
      correctionCellAffine2572 (1 / 2) step curvature firstJet leftValue rightValue := by
  unfold correctionCellAffine2572
  norm_num

noncomputable def correctionProductionSummand2572 (index : ℕ) : ℝ :=
  let step := 2 * stripRadius2303 / 10240
  let left := -stripRadius2303 + (index : ℝ) * step
  let right := -stripRadius2303 + ((index : ℝ) + 1) * step
  correctionCellAffine2572 (-1 / 2) step
    (signedCurvatureUpper2539 (-1 / 2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 left right)
    (signedJetUpper2539 1 (-1 / 2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
      (-stripRadius2303 + ((index : ℝ) + 1 / 2) * step))
    (signedJetUpper2539 0 (-1 / 2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 left)
    (signedJetUpper2539 0 (-1 / 2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 right)

theorem correctionProduction2700_le2572 :
    correctionProductionSummand2572 2700 ≤ corrSecondCell2700MinusUpper2570 := by
  simpa only [correctionProductionSummand2572, correctionCellAffine2572,
    Nat.cast_ofNat, mul_assoc, show (2700 : ℝ) + 1 = 2701 by norm_num,
    show (2700 : ℝ) + 1 / 2 = 5401 / 2 by norm_num] using
    corrSecondCell2700MinusSummand_le_2570

theorem correctionProduction2701_le2572 :
    correctionProductionSummand2572 2701 ≤ corrSecondCell2701MinusUpper2572 := by
  simpa only [correctionProductionSummand2572, correctionCellAffine2572,
    Nat.cast_ofNat, mul_assoc, show (2701 : ℝ) + 1 = 2702 by norm_num,
    show (2701 : ℝ) + 1 / 2 = 5403 / 2 by norm_num] using
    corrSecondCell2701MinusSummand_le_2572

theorem correctionTwoCellSum_le2572 :
    correctionProductionSummand2572 2700 + correctionProductionSummand2572 2701 ≤
      (66626849459 : ℝ) / 1000000000000 := by
  have bound := add_le_add correctionProduction2700_le2572 correctionProduction2701_le2572
  norm_num [corrSecondCell2700MinusUpper2570, corrSecondCell2701MinusUpper2572] at bound ⊢
  exact bound

end ConnesWeilRH.Dev
