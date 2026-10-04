import ConnesWeilRH.Dev.C1RouteACorrectionSecondChord2574
import ConnesWeilRH.Dev.C1RouteANodeJet2N02703MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02704MinusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02703PlusBounds2577
import ConnesWeilRH.Dev.C1RouteANodeJet2N02704PlusBounds2577
import ConnesWeilRH.Dev.C1RouteABatchC02703MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02703PlusFourth2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic


noncomputable def nodeSecondChordMinus2579FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02703MinusFourthUpper2558 index

noncomputable def nodeSecondChordMinus2579FourthUpper : ℝ := ((((((111461951755142 * 10^40
        + 4326221850555686960592188714232556300555) * 10^40
        + 2556533590048164679268718191055572139869) * 10^40
        + 8227440823460876352696180415741008208357) * 10^40
        + 4631659957595564037421787992204038661741) : ℝ) /
        ((((1219433027 * 10^40
        + 4671844653834364178879555881830461494785) * 10^40
        + 435580435818735366083547647094535949457) * 10^40
        + 1509176551234307394969299462068534365499) * 10^40
        + 7219864477696000000000000000000000000000))

noncomputable def nodeSecondChordMinus2579Upper : ℝ := (((((((6 * 10^40
        + 3131478769859812840389266289135877430987) * 10^40
        + 2670823691996362854840614392967518711309) * 10^40
        + 5416275360577822428073606943132170187751) * 10^40
        + 8455765090843586086316592730362121138917) * 10^40
        + 2281570248754876851419345441774621189741) : ℝ) /
        (((((196 * 10^40
        + 4034364737685122007913818096559491329985) * 10^40
        + 2276258388736899748208576802778428047329) * 10^40
        + 2996205539554249429053201047653604260553) * 10^40
        + 353927531235831997116553625600000000000) * 10^40
        + 0))

theorem nodeSecondChordMinus2579Fourth_bound :
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703MinusPointPosition2577
          nodeJet2N02704MinusPointPosition2577 ≤
        nodeSecondChordMinus2579FourthL1 := by
  have hleft : nodeJet2N02703MinusPointPosition2577 = nodeExpN02703MinusPointPosition2577 := by
    norm_num [nodeJet2N02703MinusPointPosition2577, nodeExpN02703MinusPointPosition2577]
  have hright : nodeJet2N02704MinusPointPosition2577 = nodeExpN02704MinusPointPosition2577 := by
    norm_num [nodeJet2N02704MinusPointPosition2577, nodeExpN02704MinusPointPosition2577]
  unfold signedFourthCellUpper2574 nodeSecondChordMinus2579FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (-1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) nodeExpN02703MinusPointPosition2577
        nodeExpN02704MinusPointPosition2577 ≤ batchC02703MinusFourthUpper2558 index := by
    exact batchC02703MinusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (-1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := nodeExpN02703MinusPointPosition2577) (right := nodeExpN02704MinusPointPosition2577)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordMinus2579Fourth_eq :
    nodeSecondChordMinus2579FourthL1 = nodeSecondChordMinus2579FourthUpper := by
  unfold nodeSecondChordMinus2579FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02703MinusFourthUpper2558,
        nodeSecondChordMinus2579FourthUpper,
    batchC02703MinusFourthP000Upper2558,
      batchC02703MinusFourthP001Upper2558,
      batchC02703MinusFourthP002Upper2558,
      batchC02703MinusFourthP003Upper2558,
      batchC02703MinusFourthP004Upper2558,
      batchC02703MinusFourthP005Upper2558,
      batchC02703MinusFourthP006Upper2558,
      batchC02703MinusFourthP007Upper2558,
      batchC02703MinusFourthP008Upper2558,
      batchC02703MinusFourthP009Upper2558,
      batchC02703MinusFourthP010Upper2558,
      batchC02703MinusFourthP011Upper2558,
      batchC02703MinusFourthP012Upper2558,
      batchC02703MinusFourthP013Upper2558,
      batchC02703MinusFourthP014Upper2558,
      batchC02703MinusFourthP015Upper2558,
      batchC02703MinusFourthP016Upper2558,
      batchC02703MinusFourthP017Upper2558,
      batchC02703MinusFourthP018Upper2558,
      batchC02703MinusFourthP019Upper2558,
      batchC02703MinusFourthP020Upper2558,
      batchC02703MinusFourthP021Upper2558,
      batchC02703MinusFourthP022Upper2558,
      batchC02703MinusFourthP023Upper2558,
      batchC02703MinusFourthP024Upper2558,
      batchC02703MinusFourthP025Upper2558,
      batchC02703MinusFourthP026Upper2558,
      batchC02703MinusFourthP027Upper2558,
      batchC02703MinusFourthP028Upper2558,
      batchC02703MinusFourthP029Upper2558]

theorem nodeSecondChordMinus2579Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703MinusPointPosition2577 +
      signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704MinusPointPosition2577) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703MinusPointPosition2577
          nodeJet2N02704MinusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordMinus2579Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02703MinusSignedUpper2577 +
            nodeJet2N02704MinusSignedUpper2577) +
        nodeSecondChordMinus2579FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02703MinusSignedUpper_le2577
            nodeJet2N02704MinusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordMinus2579Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordMinus2579Upper := by
      rw [nodeSecondChordMinus2579Fourth_eq]
      norm_num [nodeJet2N02703MinusSignedUpper2577, nodeJet2N02704MinusSignedUpper2577,
          nodeSecondChordMinus2579FourthUpper, nodeSecondChordMinus2579Upper]


theorem nodeSecondChordMinus2579ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordMinus2579Upper := by
  have hleft : -stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02703MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02703MinusPointPosition2577]
  have hright : -stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02704MinusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02704MinusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordMinus2579Summand_le

theorem nodeSecondChordMinus2579Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02703MinusPointPosition2577..nodeJet2N02704MinusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordMinus2579Upper := by
  have horder : nodeJet2N02703MinusPointPosition2577 < nodeJet2N02704MinusPointPosition2577 :=
      by norm_num [nodeJet2N02703MinusPointPosition2577, nodeJet2N02704MinusPointPosition2577]
  have hwidth : nodeJet2N02704MinusPointPosition2577 - nodeJet2N02703MinusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02703MinusPointPosition2577,
            nodeJet2N02704MinusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordMinus2579Summand_le

noncomputable def nodeSecondChordPlus2579FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02703PlusFourthUpper2558 index

noncomputable def nodeSecondChordPlus2579FourthUpper : ℝ := ((((((25279686305586 * 10^40
        + 6363936978908770172745158571444366347232) * 10^40
        + 5169564630515264977322685289838186510563) * 10^40
        + 6241730137438970639066929781738397491728) * 10^40
        + 8542378563627535360276760835945613444563) : ℝ) /
        ((((6097165137 * 10^40
        + 3359223269171820894397779409152307473925) * 10^40
        + 2177902179093676830417738235472679747285) * 10^40
        + 7545882756171536974846497310342671827498) * 10^40
        + 6099322388480000000000000000000000000000))

noncomputable def nodeSecondChordPlus2579Upper : ℝ := (((((((1 * 10^40
        + 4446338103750024548575814010328612021554) * 10^40
        + 9967439752120902591450127936469956231351) * 10^40
        + 8771807584983389906743306765177834578912) * 10^40
        + 5442802977599385651893193749051355077129) * 10^40
        + 8307126204868672261271071349417199748563) : ℝ) /
        (((((982 * 10^40
        + 171823688425610039569090482797456649926) * 10^40
        + 1381291943684498741042884013892140236646) * 10^40
        + 4981027697771247145266005238268021302765) * 10^40
        + 1769637656179159985582768128000000000000) * 10^40
        + 0))

theorem nodeSecondChordPlus2579Fourth_bound :
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703PlusPointPosition2577
          nodeJet2N02704PlusPointPosition2577 ≤
        nodeSecondChordPlus2579FourthL1 := by
  have hleft : nodeJet2N02703PlusPointPosition2577 = nodeExpN02703PlusPointPosition2577 := by
    norm_num [nodeJet2N02703PlusPointPosition2577, nodeExpN02703PlusPointPosition2577]
  have hright : nodeJet2N02704PlusPointPosition2577 = nodeExpN02704PlusPointPosition2577 := by
    norm_num [nodeJet2N02704PlusPointPosition2577, nodeExpN02704PlusPointPosition2577]
  unfold signedFourthCellUpper2574 nodeSecondChordPlus2579FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) nodeExpN02703PlusPointPosition2577
        nodeExpN02704PlusPointPosition2577 ≤ batchC02703PlusFourthUpper2558 index := by
    exact batchC02703PlusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := nodeExpN02703PlusPointPosition2577) (right := nodeExpN02704PlusPointPosition2577)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem nodeSecondChordPlus2579Fourth_eq :
    nodeSecondChordPlus2579FourthL1 = nodeSecondChordPlus2579FourthUpper := by
  unfold nodeSecondChordPlus2579FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02703PlusFourthUpper2558,
        nodeSecondChordPlus2579FourthUpper,
    batchC02703PlusFourthP000Upper2558,
      batchC02703PlusFourthP001Upper2558,
      batchC02703PlusFourthP002Upper2558,
      batchC02703PlusFourthP003Upper2558,
      batchC02703PlusFourthP004Upper2558,
      batchC02703PlusFourthP005Upper2558,
      batchC02703PlusFourthP006Upper2558,
      batchC02703PlusFourthP007Upper2558,
      batchC02703PlusFourthP008Upper2558,
      batchC02703PlusFourthP009Upper2558,
      batchC02703PlusFourthP010Upper2558,
      batchC02703PlusFourthP011Upper2558,
      batchC02703PlusFourthP012Upper2558,
      batchC02703PlusFourthP013Upper2558,
      batchC02703PlusFourthP014Upper2558,
      batchC02703PlusFourthP015Upper2558,
      batchC02703PlusFourthP016Upper2558,
      batchC02703PlusFourthP017Upper2558,
      batchC02703PlusFourthP018Upper2558,
      batchC02703PlusFourthP019Upper2558,
      batchC02703PlusFourthP020Upper2558,
      batchC02703PlusFourthP021Upper2558,
      batchC02703PlusFourthP022Upper2558,
      batchC02703PlusFourthP023Upper2558,
      batchC02703PlusFourthP024Upper2558,
      batchC02703PlusFourthP025Upper2558,
      batchC02703PlusFourthP026Upper2558,
      batchC02703PlusFourthP027Upper2558,
      batchC02703PlusFourthP028Upper2558,
      batchC02703PlusFourthP029Upper2558]

theorem nodeSecondChordPlus2579Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703PlusPointPosition2577 +
      signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02704PlusPointPosition2577) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 nodeJet2N02703PlusPointPosition2577
          nodeJet2N02704PlusPointPosition2577 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ nodeSecondChordPlus2579Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (nodeJet2N02703PlusSignedUpper2577 +
            nodeJet2N02704PlusSignedUpper2577) +
        nodeSecondChordPlus2579FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add nodeJet2N02703PlusSignedUpper_le2577
            nodeJet2N02704PlusSignedUpper_le2577) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right nodeSecondChordPlus2579Fourth_bound (by norm_num)) (by
              norm_num)
    _ = nodeSecondChordPlus2579Upper := by
      rw [nodeSecondChordPlus2579Fourth_eq]
      norm_num [nodeJet2N02703PlusSignedUpper2577, nodeJet2N02704PlusSignedUpper2577,
          nodeSecondChordPlus2579FourthUpper, nodeSecondChordPlus2579Upper]


theorem nodeSecondChordPlus2579ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ nodeSecondChordPlus2579Upper := by
  have hleft : -stripRadius2303 + 2703 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02703PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02703PlusPointPosition2577]
  have hright : -stripRadius2303 + 2704 * (2 * stripRadius2303 / 10240) =
      nodeJet2N02704PlusPointPosition2577 := by
    norm_num [stripRadius2303, nodeJet2N02704PlusPointPosition2577]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact nodeSecondChordPlus2579Summand_le

theorem nodeSecondChordPlus2579Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in nodeJet2N02703PlusPointPosition2577..nodeJet2N02704PlusPointPosition2577,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        nodeSecondChordPlus2579Upper := by
  have horder : nodeJet2N02703PlusPointPosition2577 < nodeJet2N02704PlusPointPosition2577 :=
      by norm_num [nodeJet2N02703PlusPointPosition2577, nodeJet2N02704PlusPointPosition2577]
  have hwidth : nodeJet2N02704PlusPointPosition2577 - nodeJet2N02703PlusPointPosition2577 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [nodeJet2N02703PlusPointPosition2577,
            nodeJet2N02704PlusPointPosition2577]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans nodeSecondChordPlus2579Summand_le

end ConnesWeilRH.Dev
