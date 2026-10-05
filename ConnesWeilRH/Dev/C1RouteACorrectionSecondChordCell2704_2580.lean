import ConnesWeilRH.Dev.C1RouteACorrectionSecondChord2574
import ConnesWeilRH.Dev.C1RouteANodeJet2N02704MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02705MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02704PlusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02705PlusBounds2577
import ConnesWeilRH.Dev.C1RouteABatchC02704MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02704PlusFourth2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic


noncomputable def nodeSecondChordMinus2580FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02704MinusFourthUpper2558 index

noncomputable def nodeSecondChordMinus2580FourthUpper : ℝ := ((((((280880977650889 * 10^40
        + 1598355722707313351818403540700320789347) * 10^40
        + 4388410978103952747920076770314436981710) * 10^40
        + 8098640773592641384598964145593567397267) * 10^40
        + 6633549847369511331833537444142050203797) : ℝ) /
        ((((3048582568 * 10^40
        + 6679611634585910447198889704576153736962) * 10^40
        + 6088951089546838415208869117736339873642) * 10^40
        + 8772941378085768487423248655171335913749) * 10^40
        + 3049661194240000000000000000000000000000))

noncomputable def nodeSecondChordMinus2580Upper : ℝ := (((((((15 * 10^40
        + 9168855433659578032454214455380231282889) * 10^40
        + 2294304860264414807560632231628643646212) * 10^40
        + 2338181301621714705992927916860848463698) * 10^40
        + 1686918751313715001541480471805386106016) * 10^40
        + 3483474551721992827376013961510906779797) : ℝ) /
        (((((491 * 10^40
        + 85911844212805019784545241398728324963) * 10^40
        + 690645971842249370521442006946070118323) * 10^40
        + 2490513848885623572633002619134010651382) * 10^40
        + 5884818828089579992791384064000000000000) * 10^40
        + 0))

theorem nodeSecondChordMinus2580Fourth_bound :
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704MinusPointPosition2577
          nodeJet2N02705MinusPointPosition2577 ≤
        nodeSecondChordMinus2580FourthL1 := by
  have hleft : nodeJet2N02704MinusPointPosition2577 = nodeExpN02704MinusPointPosition2577 := by
    norm_num [nodeJet2N02704MinusPointPosition2577, nodeExpN02704MinusPointPosition2577]
  have hright : nodeJet2N02705MinusPointPosition2577 = nodeExpN02705MinusPointPosition2577 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, nodeExpN02705MinusPointPosition2577]
  unfold signedFourthCellUpper2574 nodeSecondChordMinus2580FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (-1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) nodeExpN02704MinusPointPosition2577
        nodeExpN02705MinusPointPosition2577 ≤ batchC02704MinusFourthUpper2558 index := by
    exact batchC02704MinusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (-1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := nodeExpN02704MinusPointPosition2577) (right := nodeExpN02705MinusPointPosition2577)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordMinus2580Fourth_eq :
    nodeSecondChordMinus2580FourthL1 = nodeSecondChordMinus2580FourthUpper := by
  unfold nodeSecondChordMinus2580FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02704MinusFourthUpper2558,
        nodeSecondChordMinus2580FourthUpper,
    batchC02704MinusFourthP000Upper2558,
      batchC02704MinusFourthP001Upper2558,
      batchC02704MinusFourthP002Upper2558,
      batchC02704MinusFourthP003Upper2558,
      batchC02704MinusFourthP004Upper2558,
      batchC02704MinusFourthP005Upper2558,
      batchC02704MinusFourthP006Upper2558,
      batchC02704MinusFourthP007Upper2558,
      batchC02704MinusFourthP008Upper2558,
      batchC02704MinusFourthP009Upper2558,
      batchC02704MinusFourthP010Upper2558,
      batchC02704MinusFourthP011Upper2558,
      batchC02704MinusFourthP012Upper2558,
      batchC02704MinusFourthP013Upper2558,
      batchC02704MinusFourthP014Upper2558,
      batchC02704MinusFourthP015Upper2558,
      batchC02704MinusFourthP016Upper2558,
      batchC02704MinusFourthP017Upper2558,
      batchC02704MinusFourthP018Upper2558,
      batchC02704MinusFourthP019Upper2558,
      batchC02704MinusFourthP020Upper2558,
      batchC02704MinusFourthP021Upper2558,
      batchC02704MinusFourthP022Upper2558,
      batchC02704MinusFourthP023Upper2558,
      batchC02704MinusFourthP024Upper2558,
      batchC02704MinusFourthP025Upper2558,
      batchC02704MinusFourthP026Upper2558,
      batchC02704MinusFourthP027Upper2558,
      batchC02704MinusFourthP028Upper2558,
      batchC02704MinusFourthP029Upper2558]

theorem nodeSecondChordMinus2580Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704MinusPointPosition2577 +
      signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02705MinusPointPosition2577) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704MinusPointPosition2577
          nodeJet2N02705MinusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordMinus2580Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02704MinusSignedUpper2577 +
            nodeJet2N02705MinusSignedUpper2577) +
        nodeSecondChordMinus2580FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02704MinusSignedUpper_le2577
            nodeJet2N02705MinusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordMinus2580Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordMinus2580Upper := by
      rw [nodeSecondChordMinus2580Fourth_eq]
      norm_num [nodeJet2N02704MinusSignedUpper2577, nodeJet2N02705MinusSignedUpper2577,
          nodeSecondChordMinus2580FourthUpper, nodeSecondChordMinus2580Upper]


theorem nodeSecondChordMinus2580ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordMinus2580Upper := by
  have hleft : -stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02704MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02704MinusPointPosition2577]
  have hright : -stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02705MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02705MinusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordMinus2580Summand_le

theorem nodeSecondChordMinus2580Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02704MinusPointPosition2577..nodeJet2N02705MinusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordMinus2580Upper := by
  have horder : nodeJet2N02704MinusPointPosition2577 < nodeJet2N02705MinusPointPosition2577 :=
      by norm_num [nodeJet2N02704MinusPointPosition2577, nodeJet2N02705MinusPointPosition2577]
  have hwidth : nodeJet2N02705MinusPointPosition2577 - nodeJet2N02704MinusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02704MinusPointPosition2577,
            nodeJet2N02705MinusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordMinus2580Summand_le

noncomputable def nodeSecondChordPlus2580FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02704PlusFourthUpper2558 index

noncomputable def nodeSecondChordPlus2580FourthUpper : ℝ := ((((((25514276195254 * 10^40
        + 6123525367289733699960097369867379198687) * 10^40
        + 8130575463488569051656773649620231996087) * 10^40
        + 7565957427639359406227284558148872357671) * 10^40
        + 3001772085627485080164459402597831269111) : ℝ) /
        ((((6097165137 * 10^40
        + 3359223269171820894397779409152307473925) * 10^40
        + 2177902179093676830417738235472679747285) * 10^40
        + 7545882756171536974846497310342671827498) * 10^40
        + 6099322388480000000000000000000000000000))

noncomputable def nodeSecondChordPlus2580Upper : ℝ := (((((((1 * 10^40
        + 4587558564119674898752764281663423243201) * 10^40
        + 5611373176264195349881283501495561102979) * 10^40
        + 8763563737504813402190872819567784912129) * 10^40
        + 8181887759298164377030387015060317254625) * 10^40
        + 3238452099530828895259204919552774757111) : ℝ) /
        (((((982 * 10^40
        + 171823688425610039569090482797456649926) * 10^40
        + 1381291943684498741042884013892140236646) * 10^40
        + 4981027697771247145266005238268021302765) * 10^40
        + 1769637656179159985582768128000000000000) * 10^40
        + 0))

theorem nodeSecondChordPlus2580Fourth_bound :
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704PlusPointPosition2577
          nodeJet2N02705PlusPointPosition2577 ≤
        nodeSecondChordPlus2580FourthL1 := by
  have hleft : nodeJet2N02704PlusPointPosition2577 = nodeExpN02704PlusPointPosition2577 := by
    norm_num [nodeJet2N02704PlusPointPosition2577, nodeExpN02704PlusPointPosition2577]
  have hright : nodeJet2N02705PlusPointPosition2577 = nodeExpN02705PlusPointPosition2577 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, nodeExpN02705PlusPointPosition2577]
  unfold signedFourthCellUpper2574 nodeSecondChordPlus2580FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) nodeExpN02704PlusPointPosition2577
        nodeExpN02705PlusPointPosition2577 ≤ batchC02704PlusFourthUpper2558 index := by
    exact batchC02704PlusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := nodeExpN02704PlusPointPosition2577) (right := nodeExpN02705PlusPointPosition2577)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordPlus2580Fourth_eq :
    nodeSecondChordPlus2580FourthL1 = nodeSecondChordPlus2580FourthUpper := by
  unfold nodeSecondChordPlus2580FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02704PlusFourthUpper2558,
        nodeSecondChordPlus2580FourthUpper,
    batchC02704PlusFourthP000Upper2558,
      batchC02704PlusFourthP001Upper2558,
      batchC02704PlusFourthP002Upper2558,
      batchC02704PlusFourthP003Upper2558,
      batchC02704PlusFourthP004Upper2558,
      batchC02704PlusFourthP005Upper2558,
      batchC02704PlusFourthP006Upper2558,
      batchC02704PlusFourthP007Upper2558,
      batchC02704PlusFourthP008Upper2558,
      batchC02704PlusFourthP009Upper2558,
      batchC02704PlusFourthP010Upper2558,
      batchC02704PlusFourthP011Upper2558,
      batchC02704PlusFourthP012Upper2558,
      batchC02704PlusFourthP013Upper2558,
      batchC02704PlusFourthP014Upper2558,
      batchC02704PlusFourthP015Upper2558,
      batchC02704PlusFourthP016Upper2558,
      batchC02704PlusFourthP017Upper2558,
      batchC02704PlusFourthP018Upper2558,
      batchC02704PlusFourthP019Upper2558,
      batchC02704PlusFourthP020Upper2558,
      batchC02704PlusFourthP021Upper2558,
      batchC02704PlusFourthP022Upper2558,
      batchC02704PlusFourthP023Upper2558,
      batchC02704PlusFourthP024Upper2558,
      batchC02704PlusFourthP025Upper2558,
      batchC02704PlusFourthP026Upper2558,
      batchC02704PlusFourthP027Upper2558,
      batchC02704PlusFourthP028Upper2558,
      batchC02704PlusFourthP029Upper2558]

theorem nodeSecondChordPlus2580Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704PlusPointPosition2577 +
      signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02705PlusPointPosition2577) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704PlusPointPosition2577
          nodeJet2N02705PlusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordPlus2580Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02704PlusSignedUpper2577 +
            nodeJet2N02705PlusSignedUpper2577) +
        nodeSecondChordPlus2580FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02704PlusSignedUpper_le2577
            nodeJet2N02705PlusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordPlus2580Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordPlus2580Upper := by
      rw [nodeSecondChordPlus2580Fourth_eq]
      norm_num [nodeJet2N02704PlusSignedUpper2577, nodeJet2N02705PlusSignedUpper2577,
          nodeSecondChordPlus2580FourthUpper, nodeSecondChordPlus2580Upper]


theorem nodeSecondChordPlus2580ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordPlus2580Upper := by
  have hleft : -stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02704PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02704PlusPointPosition2577]
  have hright : -stripRadius2303 + 2705 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02705PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02705PlusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordPlus2580Summand_le

theorem nodeSecondChordPlus2580Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02704PlusPointPosition2577..nodeJet2N02705PlusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordPlus2580Upper := by
  have horder : nodeJet2N02704PlusPointPosition2577 < nodeJet2N02705PlusPointPosition2577 :=
      by norm_num [nodeJet2N02704PlusPointPosition2577, nodeJet2N02705PlusPointPosition2577]
  have hwidth : nodeJet2N02705PlusPointPosition2577 - nodeJet2N02704PlusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02704PlusPointPosition2577,
            nodeJet2N02705PlusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordPlus2580Summand_le

end ConnesWeilRH.Dev
