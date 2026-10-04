import ConnesWeilRH.Dev.C1RouteACorrectionSecondChord2574
import ConnesWeilRH.Dev.C1RouteANodeJet2N02702MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02703MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02702PlusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02703PlusBounds2577
import ConnesWeilRH.Dev.C1RouteABatchC02702MinusFourth2558
import ConnesWeilRH.Dev.C1RouteANeighborRight2557
import ConnesWeilRH.Dev.C1RouteABatchC02702PlusFourth2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic


noncomputable def nodeSecondChordMinus2578FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02702MinusFourthUpper2558 index

noncomputable def nodeSecondChordMinus2578FourthUpper : ℝ := ((((((138222157861703 * 10^40
        + 1108308290995640017202651541808784867473) * 10^40
        + 7844122555887679716043974707163469933132) * 10^40
        + 3890876693383747578021470698715645014693) * 10^40
        + 8707279197544088507046525460903279452997) : ℝ) /
        ((((1524291284 * 10^40
        + 3339805817292955223599444852288076868481) * 10^40
        + 3044475544773419207604434558868169936821) * 10^40
        + 4386470689042884243711624327585667956874) * 10^40
        + 6524830597120000000000000000000000000000))

noncomputable def nodeSecondChordMinus2578Upper : ℝ := (((((((2 * 10^40
        + 6083094369034238748562673123723573251783) * 10^40
        + 7463901102289019949932331824174461391940) * 10^40
        + 1387786922353223552976752271709516257901) * 10^40
        + 4022496351601499241993046502228969893340) * 10^40
        + 7156255007690940608379710372062816542999) : ℝ) /
        (((((81 * 10^40
        + 8347651974035467503297424206899788054160) * 10^40
        + 5115107661973708228420240334491011686387) * 10^40
        + 2081752308147603928772167103189001775230) * 10^40
        + 4314136471348263332131897344000000000000) * 10^40
        + 0))

theorem nodeSecondChordMinus2578Fourth_bound :
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702MinusPointPosition2577
          nodeJet2N02703MinusPointPosition2577 ≤
        nodeSecondChordMinus2578FourthL1 := by
  have hleft : nodeJet2N02702MinusPointPosition2577 = batchN02702MinusPosition2558 := by
    norm_num [nodeJet2N02702MinusPointPosition2577, batchN02702MinusPosition2558]
  have hright : nodeJet2N02703MinusPointPosition2577 = batchN02703MinusPosition2558 := by
    norm_num [nodeJet2N02703MinusPointPosition2577, batchN02703MinusPosition2558]
  unfold signedFourthCellUpper2574 nodeSecondChordMinus2578FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (-1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) batchN02702MinusPosition2558
        batchN02703MinusPosition2558 ≤ batchC02702MinusFourthUpper2558 index := by
    exact batchC02702MinusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (-1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := batchN02702MinusPosition2558) (right := batchN02703MinusPosition2558)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordMinus2578Fourth_eq :
    nodeSecondChordMinus2578FourthL1 = nodeSecondChordMinus2578FourthUpper := by
  unfold nodeSecondChordMinus2578FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02702MinusFourthUpper2558,
        nodeSecondChordMinus2578FourthUpper,
    batchC02702MinusFourthP000Upper2558,
      batchC02702MinusFourthP001Upper2558,
      batchC02702MinusFourthP002Upper2558,
      batchC02702MinusFourthP003Upper2558,
      batchC02702MinusFourthP004Upper2558,
      batchC02702MinusFourthP005Upper2558,
      batchC02702MinusFourthP006Upper2558,
      batchC02702MinusFourthP007Upper2558,
      batchC02702MinusFourthP008Upper2558,
      batchC02702MinusFourthP009Upper2558,
      batchC02702MinusFourthP010Upper2558,
      batchC02702MinusFourthP011Upper2558,
      batchC02702MinusFourthP012Upper2558,
      batchC02702MinusFourthP013Upper2558,
      batchC02702MinusFourthP014Upper2558,
      batchC02702MinusFourthP015Upper2558,
      batchC02702MinusFourthP016Upper2558,
      batchC02702MinusFourthP017Upper2558,
      batchC02702MinusFourthP018Upper2558,
      batchC02702MinusFourthP019Upper2558,
      batchC02702MinusFourthP020Upper2558,
      batchC02702MinusFourthP021Upper2558,
      batchC02702MinusFourthP022Upper2558,
      batchC02702MinusFourthP023Upper2558,
      batchC02702MinusFourthP024Upper2558,
      batchC02702MinusFourthP025Upper2558,
      batchC02702MinusFourthP026Upper2558,
      batchC02702MinusFourthP027Upper2558,
      batchC02702MinusFourthP028Upper2558,
      batchC02702MinusFourthP029Upper2558]

theorem nodeSecondChordMinus2578Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702MinusPointPosition2577 +
      signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703MinusPointPosition2577) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702MinusPointPosition2577
          nodeJet2N02703MinusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordMinus2578Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02702MinusSignedUpper2577 +
            nodeJet2N02703MinusSignedUpper2577) +
        nodeSecondChordMinus2578FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02702MinusSignedUpper_le2577
            nodeJet2N02703MinusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordMinus2578Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordMinus2578Upper := by
      rw [nodeSecondChordMinus2578Fourth_eq]
      norm_num [nodeJet2N02702MinusSignedUpper2577, nodeJet2N02703MinusSignedUpper2577,
          nodeSecondChordMinus2578FourthUpper, nodeSecondChordMinus2578Upper]


theorem nodeSecondChordMinus2578ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordMinus2578Upper := by
  have hleft : -stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02702MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02702MinusPointPosition2577]
  have hright : -stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02703MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02703MinusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordMinus2578Summand_le

theorem nodeSecondChordMinus2578Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02702MinusPointPosition2577..nodeJet2N02703MinusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordMinus2578Upper := by
  have horder : nodeJet2N02702MinusPointPosition2577 < nodeJet2N02703MinusPointPosition2577 :=
      by norm_num [nodeJet2N02702MinusPointPosition2577, nodeJet2N02703MinusPointPosition2577]
  have hwidth : nodeJet2N02703MinusPointPosition2577 - nodeJet2N02702MinusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02702MinusPointPosition2577,
            nodeJet2N02703MinusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordMinus2578Summand_le

noncomputable def nodeSecondChordPlus2578FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02702PlusFourthUpper2558 index

noncomputable def nodeSecondChordPlus2578FourthUpper : ℝ := ((((((12523531411699 * 10^40
        + 5644959558207195839017223126702804659101) * 10^40
        + 4297226802698030863266781083158635857582) * 10^40
        + 408244540187723462853987748642441414835) * 10^40
        + 6483754022889644550127298752626994037811) : ℝ) /
        ((((3048582568 * 10^40
        + 6679611634585910447198889704576153736962) * 10^40
        + 6088951089546838415208869117736339873642) * 10^40
        + 8772941378085768487423248655171335913749) * 10^40
        + 3049661194240000000000000000000000000000))

noncomputable def nodeSecondChordPlus2578Upper : ℝ :=
    ((((((2384394993735359850849542253334736689234 * 10^40
        + 7052278893651808237537065316812599110708) * 10^40
        + 1196746386941317500192293732351022320277) * 10^40
        + 2282443098900138928276558933483744096233) * 10^40
        + 2750127059881742662371271035905369041937) : ℝ) /
        (((((163 * 10^40
        + 6695303948070935006594848413799576108321) * 10^40
        + 230215323947416456840480668982023372774) * 10^40
        + 4163504616295207857544334206378003550460) * 10^40
        + 8628272942696526664263794688000000000000) * 10^40
        + 0))

theorem nodeSecondChordPlus2578Fourth_bound :
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702PlusPointPosition2577
          nodeJet2N02703PlusPointPosition2577 ≤
        nodeSecondChordPlus2578FourthL1 := by
  have hleft : nodeJet2N02702PlusPointPosition2577 = neighborRightPosition2557 := by
    norm_num [nodeJet2N02702PlusPointPosition2577, neighborRightPosition2557]
  have hright : nodeJet2N02703PlusPointPosition2577 = batchN02703PlusPosition2558 := by
    norm_num [nodeJet2N02703PlusPointPosition2577, batchN02703PlusPosition2558]
  unfold signedFourthCellUpper2574 nodeSecondChordPlus2578FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) neighborRightPosition2557
        batchN02703PlusPosition2558 ≤ batchC02702PlusFourthUpper2558 index := by
    exact batchC02702PlusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := neighborRightPosition2557) (right := batchN02703PlusPosition2558)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordPlus2578Fourth_eq :
    nodeSecondChordPlus2578FourthL1 = nodeSecondChordPlus2578FourthUpper := by
  unfold nodeSecondChordPlus2578FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02702PlusFourthUpper2558,
        nodeSecondChordPlus2578FourthUpper,
    batchC02702PlusFourthP000Upper2558,
      batchC02702PlusFourthP001Upper2558,
      batchC02702PlusFourthP002Upper2558,
      batchC02702PlusFourthP003Upper2558,
      batchC02702PlusFourthP004Upper2558,
      batchC02702PlusFourthP005Upper2558,
      batchC02702PlusFourthP006Upper2558,
      batchC02702PlusFourthP007Upper2558,
      batchC02702PlusFourthP008Upper2558,
      batchC02702PlusFourthP009Upper2558,
      batchC02702PlusFourthP010Upper2558,
      batchC02702PlusFourthP011Upper2558,
      batchC02702PlusFourthP012Upper2558,
      batchC02702PlusFourthP013Upper2558,
      batchC02702PlusFourthP014Upper2558,
      batchC02702PlusFourthP015Upper2558,
      batchC02702PlusFourthP016Upper2558,
      batchC02702PlusFourthP017Upper2558,
      batchC02702PlusFourthP018Upper2558,
      batchC02702PlusFourthP019Upper2558,
      batchC02702PlusFourthP020Upper2558,
      batchC02702PlusFourthP021Upper2558,
      batchC02702PlusFourthP022Upper2558,
      batchC02702PlusFourthP023Upper2558,
      batchC02702PlusFourthP024Upper2558,
      batchC02702PlusFourthP025Upper2558,
      batchC02702PlusFourthP026Upper2558,
      batchC02702PlusFourthP027Upper2558,
      batchC02702PlusFourthP028Upper2558,
      batchC02702PlusFourthP029Upper2558]

theorem nodeSecondChordPlus2578Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702PlusPointPosition2577 +
      signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703PlusPointPosition2577) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02702PlusPointPosition2577
          nodeJet2N02703PlusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordPlus2578Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02702PlusSignedUpper2577 +
            nodeJet2N02703PlusSignedUpper2577) +
        nodeSecondChordPlus2578FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02702PlusSignedUpper_le2577
            nodeJet2N02703PlusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordPlus2578Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordPlus2578Upper := by
      rw [nodeSecondChordPlus2578Fourth_eq]
      norm_num [nodeJet2N02702PlusSignedUpper2577, nodeJet2N02703PlusSignedUpper2577,
          nodeSecondChordPlus2578FourthUpper, nodeSecondChordPlus2578Upper]


theorem nodeSecondChordPlus2578ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordPlus2578Upper := by
  have hleft : -stripRadius2303 + 2702 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02702PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02702PlusPointPosition2577]
  have hright : -stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02703PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02703PlusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordPlus2578Summand_le

theorem nodeSecondChordPlus2578Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02702PlusPointPosition2577..nodeJet2N02703PlusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordPlus2578Upper := by
  have horder : nodeJet2N02702PlusPointPosition2577 < nodeJet2N02703PlusPointPosition2577 :=
      by norm_num [nodeJet2N02702PlusPointPosition2577, nodeJet2N02703PlusPointPosition2577]
  have hwidth : nodeJet2N02703PlusPointPosition2577 - nodeJet2N02702PlusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02702PlusPointPosition2577,
            nodeJet2N02703PlusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordPlus2578Summand_le

end ConnesWeilRH.Dev
