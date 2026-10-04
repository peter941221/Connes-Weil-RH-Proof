import ConnesWeilRH.Dev.C1RouteACorrectionSecondChord2574
import ConnesWeilRH.Dev.C1RouteACorrSecondN02700MinusBounds2575
import ConnesWeilRH.Dev.C1RouteACorrSecondN02701MinusBounds2575
import ConnesWeilRH.Dev.C1RouteACorrSecondN02700PlusBounds2575
import ConnesWeilRH.Dev.C1RouteACorrSecondN02701PlusBounds2575
import ConnesWeilRH.Dev.C1RouteABatchC02700MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02700PlusFourth2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic


noncomputable def corrSecondChordMinus2575FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02700MinusFourthUpper2558 index

noncomputable def corrSecondChordMinus2575FourthUpper : ℝ := ((((((136035739256870 * 10^40
        + 4487737385566699185258286584762073139108) * 10^40
        + 8401110798541149128576537897114284247014) * 10^40
        + 8774026477916051017805699550145939793578) * 10^40
        + 1266268813824877087176048650655864698041) : ℝ) /
        ((((1524291284 * 10^40
        + 3339805817292955223599444852288076868481) * 10^40
        + 3044475544773419207604434558868169936821) * 10^40
        + 4386470689042884243711624327585667956874) * 10^40
        + 6524830597120000000000000000000000000000))

noncomputable def corrSecondChordMinus2575Upper : ℝ := (((((((7 * 10^40
        + 6934065475467910877794742051181504972250) * 10^40
        + 4250998743814650850856236322522663204672) * 10^40
        + 1063838384439154710550693726628950947764) * 10^40
        + 2608247377681649020653186556775109499047) * 10^40
        + 6413655231957622095675124952905717626041) : ℝ) /
        (((((245 * 10^40
        + 5042955922106402509892272620699364162481) * 10^40
        + 5345322985921124685260721003473035059161) * 10^40
        + 6245256924442811786316501309567005325691) * 10^40
        + 2942409414044789996395692032000000000000) * 10^40
        + 0))

theorem corrSecondChordMinus2575Fourth_bound :
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700MinusPointPosition2575
          corrSecondN02701MinusPointPosition2575 ≤
        corrSecondChordMinus2575FourthL1 := by
  have hleft : corrSecondN02700MinusPointPosition2575 = kernelN02700MinusPosition2555 := by
    norm_num [corrSecondN02700MinusPointPosition2575, kernelN02700MinusPosition2555]
  have hright : corrSecondN02701MinusPointPosition2575 = kernelN02701MinusPosition2555 := by
    norm_num [corrSecondN02701MinusPointPosition2575, kernelN02701MinusPosition2555]
  unfold signedFourthCellUpper2574 corrSecondChordMinus2575FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (-1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) kernelN02700MinusPosition2555
        kernelN02701MinusPosition2555 ≤ batchC02700MinusFourthUpper2558 index := by
    exact batchC02700MinusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (-1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := kernelN02700MinusPosition2555) (right := kernelN02701MinusPosition2555)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem corrSecondChordMinus2575Fourth_eq :
    corrSecondChordMinus2575FourthL1 = corrSecondChordMinus2575FourthUpper := by
  unfold corrSecondChordMinus2575FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02700MinusFourthUpper2558,
        corrSecondChordMinus2575FourthUpper,
    batchC02700MinusFourthP000Upper2558,
      batchC02700MinusFourthP001Upper2558,
      batchC02700MinusFourthP002Upper2558,
      batchC02700MinusFourthP003Upper2558,
      batchC02700MinusFourthP004Upper2558,
      batchC02700MinusFourthP005Upper2558,
      batchC02700MinusFourthP006Upper2558,
      batchC02700MinusFourthP007Upper2558,
      batchC02700MinusFourthP008Upper2558,
      batchC02700MinusFourthP009Upper2558,
      batchC02700MinusFourthP010Upper2558,
      batchC02700MinusFourthP011Upper2558,
      batchC02700MinusFourthP012Upper2558,
      batchC02700MinusFourthP013Upper2558,
      batchC02700MinusFourthP014Upper2558,
      batchC02700MinusFourthP015Upper2558,
      batchC02700MinusFourthP016Upper2558,
      batchC02700MinusFourthP017Upper2558,
      batchC02700MinusFourthP018Upper2558,
      batchC02700MinusFourthP019Upper2558,
      batchC02700MinusFourthP020Upper2558,
      batchC02700MinusFourthP021Upper2558,
      batchC02700MinusFourthP022Upper2558,
      batchC02700MinusFourthP023Upper2558,
      batchC02700MinusFourthP024Upper2558,
      batchC02700MinusFourthP025Upper2558,
      batchC02700MinusFourthP026Upper2558,
      batchC02700MinusFourthP027Upper2558,
      batchC02700MinusFourthP028Upper2558,
      batchC02700MinusFourthP029Upper2558]

theorem corrSecondChordMinus2575Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700MinusPointPosition2575 +
      signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02701MinusPointPosition2575) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700MinusPointPosition2575
          corrSecondN02701MinusPointPosition2575 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ corrSecondChordMinus2575Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (corrSecondN02700MinusSignedUpper2575 +
            corrSecondN02701MinusSignedUpper2575) +
        corrSecondChordMinus2575FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add corrSecondN02700MinusSignedUpper_le2575
            corrSecondN02701MinusSignedUpper_le2575) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right corrSecondChordMinus2575Fourth_bound (by norm_num)) (by
              norm_num)
    _ = corrSecondChordMinus2575Upper := by
      rw [corrSecondChordMinus2575Fourth_eq]
      norm_num [corrSecondN02700MinusSignedUpper2575, corrSecondN02701MinusSignedUpper2575,
          corrSecondChordMinus2575FourthUpper, corrSecondChordMinus2575Upper]


theorem corrSecondChordMinus2575ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (-1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ corrSecondChordMinus2575Upper := by
  have hleft : -stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240) =
      corrSecondN02700MinusPointPosition2575 := by
    norm_num [stripRadius2303, corrSecondN02700MinusPointPosition2575]
  have hright : -stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240) =
      corrSecondN02701MinusPointPosition2575 := by
    norm_num [stripRadius2303, corrSecondN02701MinusPointPosition2575]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact corrSecondChordMinus2575Summand_le

theorem corrSecondChordMinus2575Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in corrSecondN02700MinusPointPosition2575..corrSecondN02701MinusPointPosition2575,
      ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541) position‖) ≤
        corrSecondChordMinus2575Upper := by
  have horder : corrSecondN02700MinusPointPosition2575 < corrSecondN02701MinusPointPosition2575 :=
      by norm_num [corrSecondN02700MinusPointPosition2575, corrSecondN02701MinusPointPosition2575]
  have hwidth : corrSecondN02701MinusPointPosition2575 - corrSecondN02700MinusPointPosition2575 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [corrSecondN02700MinusPointPosition2575,
            corrSecondN02701MinusPointPosition2575]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans corrSecondChordMinus2575Summand_le

noncomputable def corrSecondChordPlus2575FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    batchC02700PlusFourthUpper2558 index

noncomputable def corrSecondChordPlus2575FourthUpper : ℝ := ((((((6147940579243 * 10^40
        + 7084446473747593566563816040419108175683) * 10^40
        + 3094724025163917084257218045956869058015) * 10^40
        + 9501171382707180560198398367376824196575) * 10^40
        + 1122488676265319898935757109859386376743) : ℝ) /
        ((((1524291284 * 10^40
        + 3339805817292955223599444852288076868481) * 10^40
        + 3044475544773419207604434558868169936821) * 10^40
        + 4386470689042884243711624327585667956874) * 10^40
        + 6524830597120000000000000000000000000000))

noncomputable def corrSecondChordPlus2575Upper : ℝ :=
    ((((((1169179348424496544223700855440200603810 * 10^40
        + 4342519829497794603987914779793242426372) * 10^40
        + 8600523318300764001501454794628652444396) * 10^40
        + 6296785807428278635473097983770563839498) * 10^40
        + 6544173195493083519566442460005619373581) : ℝ) /
        (((((81 * 10^40
        + 8347651974035467503297424206899788054160) * 10^40
        + 5115107661973708228420240334491011686387) * 10^40
        + 2081752308147603928772167103189001775230) * 10^40
        + 4314136471348263332131897344000000000000) * 10^40
        + 0))

theorem corrSecondChordPlus2575Fourth_bound :
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700PlusPointPosition2575
          corrSecondN02701PlusPointPosition2575 ≤
        corrSecondChordPlus2575FourthL1 := by
  have hleft : corrSecondN02700PlusPointPosition2575 = kernelN02700PlusPosition2555 := by
    norm_num [corrSecondN02700PlusPointPosition2575, kernelN02700PlusPosition2555]
  have hright : corrSecondN02701PlusPointPosition2575 = kernelN02701PlusPosition2555 := by
    norm_num [corrSecondN02701PlusPointPosition2575, kernelN02701PlusPosition2555]
  unfold signedFourthCellUpper2574 corrSecondChordPlus2575FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 (1/2) (nodeModulation2541 index)
      (storedWidth index ^ 2) kernelN02700PlusPosition2555
        kernelN02701PlusPosition2555 ≤ batchC02700PlusFourthUpper2558 index := by
    exact batchC02700PlusFourthBound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 (1/2)
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := kernelN02700PlusPosition2555) (right := kernelN02701PlusPosition2555)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem corrSecondChordPlus2575Fourth_eq :
    corrSecondChordPlus2575FourthL1 = corrSecondChordPlus2575FourthUpper := by
  unfold corrSecondChordPlus2575FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, batchC02700PlusFourthUpper2558,
        corrSecondChordPlus2575FourthUpper,
    batchC02700PlusFourthP000Upper2558,
      batchC02700PlusFourthP001Upper2558,
      batchC02700PlusFourthP002Upper2558,
      batchC02700PlusFourthP003Upper2558,
      batchC02700PlusFourthP004Upper2558,
      batchC02700PlusFourthP005Upper2558,
      batchC02700PlusFourthP006Upper2558,
      batchC02700PlusFourthP007Upper2558,
      batchC02700PlusFourthP008Upper2558,
      batchC02700PlusFourthP009Upper2558,
      batchC02700PlusFourthP010Upper2558,
      batchC02700PlusFourthP011Upper2558,
      batchC02700PlusFourthP012Upper2558,
      batchC02700PlusFourthP013Upper2558,
      batchC02700PlusFourthP014Upper2558,
      batchC02700PlusFourthP015Upper2558,
      batchC02700PlusFourthP016Upper2558,
      batchC02700PlusFourthP017Upper2558,
      batchC02700PlusFourthP018Upper2558,
      batchC02700PlusFourthP019Upper2558,
      batchC02700PlusFourthP020Upper2558,
      batchC02700PlusFourthP021Upper2558,
      batchC02700PlusFourthP022Upper2558,
      batchC02700PlusFourthP023Upper2558,
      batchC02700PlusFourthP024Upper2558,
      batchC02700PlusFourthP025Upper2558,
      batchC02700PlusFourthP026Upper2558,
      batchC02700PlusFourthP027Upper2558,
      batchC02700PlusFourthP028Upper2558,
      batchC02700PlusFourthP029Upper2558]

theorem corrSecondChordPlus2575Summand_le :
    ((65536001 : ℝ) /
        51200000000) / 2 * (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700PlusPointPosition2575 +
      signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02701PlusPointPosition2575) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 corrSecondN02700PlusPointPosition2575
          corrSecondN02701PlusPointPosition2575 *
        ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 ≤ corrSecondChordPlus2575Upper := by
  calc
    _ ≤ ((65536001 : ℝ) /
        51200000000) / 2 * (corrSecondN02700PlusSignedUpper2575 +
            corrSecondN02701PlusSignedUpper2575) +
        corrSecondChordPlus2575FourthL1 * ((65536001 : ℝ) /
        51200000000) ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add corrSecondN02700PlusSignedUpper_le2575
            corrSecondN02701PlusSignedUpper_le2575) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right corrSecondChordPlus2575Fourth_bound (by norm_num)) (by
              norm_num)
    _ = corrSecondChordPlus2575Upper := by
      rw [corrSecondChordPlus2575Fourth_eq]
      norm_num [corrSecondN02700PlusSignedUpper2575, corrSecondN02701PlusSignedUpper2575,
          corrSecondChordPlus2575FourthUpper, corrSecondChordPlus2575Upper]


theorem corrSecondChordPlus2575ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 (1/2) correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ corrSecondChordPlus2575Upper := by
  have hleft : -stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240) =
      corrSecondN02700PlusPointPosition2575 := by
    norm_num [stripRadius2303, corrSecondN02700PlusPointPosition2575]
  have hright : -stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240) =
      corrSecondN02701PlusPointPosition2575 := by
    norm_num [stripRadius2303, corrSecondN02701PlusPointPosition2575]
  have hstep : 2 * stripRadius2303 / 10240 = ((65536001 : ℝ) /
        51200000000) := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact corrSecondChordPlus2575Summand_le

theorem corrSecondChordPlus2575Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in corrSecondN02700PlusPointPosition2575..corrSecondN02701PlusPointPosition2575,
      ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) position‖) ≤
        corrSecondChordPlus2575Upper := by
  have horder : corrSecondN02700PlusPointPosition2575 < corrSecondN02701PlusPointPosition2575 :=
      by norm_num [corrSecondN02700PlusPointPosition2575, corrSecondN02701PlusPointPosition2575]
  have hwidth : corrSecondN02701PlusPointPosition2575 - corrSecondN02700PlusPointPosition2575 =
      ((65536001 : ℝ) /
        51200000000) := by norm_num [corrSecondN02700PlusPointPosition2575,
            corrSecondN02701PlusPointPosition2575]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror
        horder
  rw [hwidth] at h
  exact h.trans corrSecondChordPlus2575Summand_le

end ConnesWeilRH.Dev
