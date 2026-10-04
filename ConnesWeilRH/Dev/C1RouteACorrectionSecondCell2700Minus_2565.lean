import ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562
import ConnesWeilRH.Dev.C1RouteABoundaryLeft2548
import ConnesWeilRH.Dev.C1RouteABoundaryRight2548
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548
import ConnesWeilRH.Dev.C1RouteABatchC02700MinusAssembly2558
import ConnesWeilRH.Dev.C1RouteASharedN02700Minus2556
import ConnesWeilRH.Dev.C1RouteASharedN02701Minus2556
import ConnesWeilRH.Dev.C1RouteAFirstJetMidpointMinus2565

/-!
Correction-second single-cell certificate at production cell 2700, sigma=-1/2.
Mirror of the plus-sign record 2563: the three-piece summand of the 2562
decomposition of `stripSecondNorm` is bounded by 5071985/10^12 on the
production cell, from the certified minus curvature charge (2558, bridged
from its L2 coefficient norms to an L1 rational ceiling), the new order-1
minus midpoint jet certificate (2565), and the shared minus endpoint values
(2556). Family centers and errors stay explicit at the boxes; actual
coefficients enter only through the membership premise of the 2562 consumer
theorems, so no membership claim is made here.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def correctionSecondCell2700MinusUpper2565 : ℝ :=
  ((5071985 : ℝ) / 1000000000000)

noncomputable def correctionThirdL1Cell2565 (i : Fin 30) : ℝ :=
  (|(baseCoefficientCenter2540 i).re| + |(baseCoefficientCenter2540 i).im| +
    baseCoefficientError2540 i) * batchC02700MinusThirdCell2558 i

noncomputable def correctionThirdL1Sum2565 : ℝ :=
  ∑ i : Fin 30, correctionThirdL1Cell2565 i

noncomputable def correctionThirdL1Upper2565 : ℝ :=
  ((90003427712263015194132112776719368699858940112810875667767574999223 : ℝ) * 10^109 +
      (59182773713947293363288007825817794791100237735426283343558342716365 : ℝ) * 10^41 +
      (82011618282523054589118517575045863528287 : ℝ)) /
    ((47634102635436893179040485073748265163400240214004076398607741693502 : ℝ) * 10^110 +
      (37638579964630310525669957720903259013261598826023705212365233289009 : ℝ) * 10^42 +
      (561600000000000000000000000000000000000000 : ℝ))

theorem correctionThirdL1Sum_eq_2565 :
    correctionThirdL1Sum2565 = correctionThirdL1Upper2565 := by
  unfold correctionThirdL1Sum2565
  simp only [correctionThirdL1Cell2565, correctionThirdL1Upper2565]
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540,
    batchC02700MinusThirdCell2558, batchC02700MinusLeftNormUpper2558,
    batchC02700MinusRightNormUpper2558, batchC02700MinusFourthUpper2558,
    kernelN02700MinusPosition2555, kernelN02701MinusPosition2555,
    batchC02700MinusLeftP000NormUpper2558, batchC02700MinusLeftP001NormUpper2558,
    batchC02700MinusLeftP002NormUpper2558, batchC02700MinusLeftP003NormUpper2558,
    batchC02700MinusLeftP004NormUpper2558, batchC02700MinusLeftP005NormUpper2558,
    batchC02700MinusLeftP006NormUpper2558, batchC02700MinusLeftP007NormUpper2558,
    batchC02700MinusLeftP008NormUpper2558, batchC02700MinusLeftP009NormUpper2558,
    batchC02700MinusLeftP010NormUpper2558, batchC02700MinusLeftP011NormUpper2558,
    batchC02700MinusLeftP012NormUpper2558, batchC02700MinusLeftP013NormUpper2558,
    batchC02700MinusLeftP014NormUpper2558, batchC02700MinusLeftP015NormUpper2558,
    batchC02700MinusLeftP016NormUpper2558, batchC02700MinusLeftP017NormUpper2558,
    batchC02700MinusLeftP018NormUpper2558, batchC02700MinusLeftP019NormUpper2558,
    batchC02700MinusLeftP020NormUpper2558, batchC02700MinusLeftP021NormUpper2558,
    batchC02700MinusLeftP022NormUpper2558, batchC02700MinusLeftP023NormUpper2558,
    batchC02700MinusLeftP024NormUpper2558, batchC02700MinusLeftP025NormUpper2558,
    batchC02700MinusLeftP026NormUpper2558, batchC02700MinusLeftP027NormUpper2558,
    batchC02700MinusLeftP028NormUpper2558, batchC02700MinusLeftP029NormUpper2558,
    batchC02700MinusRightP000NormUpper2558, batchC02700MinusRightP001NormUpper2558,
    batchC02700MinusRightP002NormUpper2558, batchC02700MinusRightP003NormUpper2558,
    batchC02700MinusRightP004NormUpper2558, batchC02700MinusRightP005NormUpper2558,
    batchC02700MinusRightP006NormUpper2558, batchC02700MinusRightP007NormUpper2558,
    batchC02700MinusRightP008NormUpper2558, batchC02700MinusRightP009NormUpper2558,
    batchC02700MinusRightP010NormUpper2558, batchC02700MinusRightP011NormUpper2558,
    batchC02700MinusRightP012NormUpper2558, batchC02700MinusRightP013NormUpper2558,
    batchC02700MinusRightP014NormUpper2558, batchC02700MinusRightP015NormUpper2558,
    batchC02700MinusRightP016NormUpper2558, batchC02700MinusRightP017NormUpper2558,
    batchC02700MinusRightP018NormUpper2558, batchC02700MinusRightP019NormUpper2558,
    batchC02700MinusRightP020NormUpper2558, batchC02700MinusRightP021NormUpper2558,
    batchC02700MinusRightP022NormUpper2558, batchC02700MinusRightP023NormUpper2558,
    batchC02700MinusRightP024NormUpper2558, batchC02700MinusRightP025NormUpper2558,
    batchC02700MinusRightP026NormUpper2558, batchC02700MinusRightP027NormUpper2558,
    batchC02700MinusRightP028NormUpper2558, batchC02700MinusRightP029NormUpper2558,
    batchC02700MinusFourthP000Upper2558, batchC02700MinusFourthP001Upper2558,
    batchC02700MinusFourthP002Upper2558, batchC02700MinusFourthP003Upper2558,
    batchC02700MinusFourthP004Upper2558, batchC02700MinusFourthP005Upper2558,
    batchC02700MinusFourthP006Upper2558, batchC02700MinusFourthP007Upper2558,
    batchC02700MinusFourthP008Upper2558, batchC02700MinusFourthP009Upper2558,
    batchC02700MinusFourthP010Upper2558, batchC02700MinusFourthP011Upper2558,
    batchC02700MinusFourthP012Upper2558, batchC02700MinusFourthP013Upper2558,
    batchC02700MinusFourthP014Upper2558, batchC02700MinusFourthP015Upper2558,
    batchC02700MinusFourthP016Upper2558, batchC02700MinusFourthP017Upper2558,
    batchC02700MinusFourthP018Upper2558, batchC02700MinusFourthP019Upper2558,
    batchC02700MinusFourthP020Upper2558, batchC02700MinusFourthP021Upper2558,
    batchC02700MinusFourthP022Upper2558, batchC02700MinusFourthP023Upper2558,
    batchC02700MinusFourthP024Upper2558, batchC02700MinusFourthP025Upper2558,
    batchC02700MinusFourthP026Upper2558, batchC02700MinusFourthP027Upper2558,
    batchC02700MinusFourthP028Upper2558, batchC02700MinusFourthP029Upper2558]

theorem correctionSecondCell2700MinusSummand_le_2565 :
    (2 * stripRadius2303 / 10240) *
        signedCurvatureUpper2539 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
          nodeModulation2541
          (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
          (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) +
      2 * |(-1 / 2 : ℝ)| * ((2 * stripRadius2303 / 10240) *
        (signedJetUpper2539 1 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + ((5401 : ℝ) / 2) * (2 * stripRadius2303 / 10240)) +
          signedCurvatureUpper2539 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
            (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) *
            ((2 * stripRadius2303 / 10240) / 2))) +
      ((-1 / 2 : ℝ) ^ 2) *
        ((2 * stripRadius2303 / 10240) / 2 *
          (signedJetUpper2539 0 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240)) +
          signedJetUpper2539 0 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240))) +
        signedCurvatureUpper2539 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
          nodeModulation2541
          (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
          (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) *
          ((2 * stripRadius2303 / 10240) ^ 3 / 12)) ≤
      correctionSecondCell2700MinusUpper2565 := by
  have hC := batchC02700MinusCurvature_bound2558
  have hJ1 := firstJetMidpointMinusUpper_le2565
  have hJ0l := sharedN02700MinusSigned_le2556
  have hJ0r := sharedN02701MinusSigned_le2556
  have hkl : kernelN02700MinusPosition2555 = edgeLeftPosition2548 := by
    norm_num [kernelN02700MinusPosition2555, edgeLeftPosition2548]
  have hkr : kernelN02701MinusPosition2555 = edgeRightPosition2548 := by
    norm_num [kernelN02701MinusPosition2555, edgeRightPosition2548]
  rw [hkl, hkr] at hC
  have hsl : sharedN02700MinusPosition2556 = edgeLeftPosition2548 := by
    norm_num [sharedN02700MinusPosition2556, edgeLeftPosition2548]
  have hsr : sharedN02701MinusPosition2556 = edgeRightPosition2548 := by
    norm_num [sharedN02701MinusPosition2556, edgeRightPosition2548]
  rw [hsl] at hJ0l
  rw [hsr] at hJ0r
  rw [edgeLeftGrid2548, edgeRightGrid2548, edgeMidpointGrid2548]
  have hagg : batchC02700MinusThirdAggregate2558 ≤ correctionThirdL1Sum2565 := by
    unfold batchC02700MinusThirdAggregate2558 correctionThirdL1Sum2565
    simp only [correctionThirdL1Cell2565]
    refine Finset.sum_le_sum fun i _ => ?_
    have ht : 0 ≤ batchC02700MinusThirdCell2558 i := by
      fin_cases i <;>
        norm_num [batchC02700MinusThirdCell2558, batchC02700MinusLeftNormUpper2558,
          batchC02700MinusRightNormUpper2558, batchC02700MinusFourthUpper2558,
          kernelN02700MinusPosition2555, kernelN02701MinusPosition2555,
          batchC02700MinusLeftP000NormUpper2558, batchC02700MinusLeftP001NormUpper2558,
          batchC02700MinusLeftP002NormUpper2558, batchC02700MinusLeftP003NormUpper2558,
          batchC02700MinusLeftP004NormUpper2558, batchC02700MinusLeftP005NormUpper2558,
          batchC02700MinusLeftP006NormUpper2558, batchC02700MinusLeftP007NormUpper2558,
          batchC02700MinusLeftP008NormUpper2558, batchC02700MinusLeftP009NormUpper2558,
          batchC02700MinusLeftP010NormUpper2558, batchC02700MinusLeftP011NormUpper2558,
          batchC02700MinusLeftP012NormUpper2558, batchC02700MinusLeftP013NormUpper2558,
          batchC02700MinusLeftP014NormUpper2558, batchC02700MinusLeftP015NormUpper2558,
          batchC02700MinusLeftP016NormUpper2558, batchC02700MinusLeftP017NormUpper2558,
          batchC02700MinusLeftP018NormUpper2558, batchC02700MinusLeftP019NormUpper2558,
          batchC02700MinusLeftP020NormUpper2558, batchC02700MinusLeftP021NormUpper2558,
          batchC02700MinusLeftP022NormUpper2558, batchC02700MinusLeftP023NormUpper2558,
          batchC02700MinusLeftP024NormUpper2558, batchC02700MinusLeftP025NormUpper2558,
          batchC02700MinusLeftP026NormUpper2558, batchC02700MinusLeftP027NormUpper2558,
          batchC02700MinusLeftP028NormUpper2558, batchC02700MinusLeftP029NormUpper2558,
          batchC02700MinusRightP000NormUpper2558, batchC02700MinusRightP001NormUpper2558,
          batchC02700MinusRightP002NormUpper2558, batchC02700MinusRightP003NormUpper2558,
          batchC02700MinusRightP004NormUpper2558, batchC02700MinusRightP005NormUpper2558,
          batchC02700MinusRightP006NormUpper2558, batchC02700MinusRightP007NormUpper2558,
          batchC02700MinusRightP008NormUpper2558, batchC02700MinusRightP009NormUpper2558,
          batchC02700MinusRightP010NormUpper2558, batchC02700MinusRightP011NormUpper2558,
          batchC02700MinusRightP012NormUpper2558, batchC02700MinusRightP013NormUpper2558,
          batchC02700MinusRightP014NormUpper2558, batchC02700MinusRightP015NormUpper2558,
          batchC02700MinusRightP016NormUpper2558, batchC02700MinusRightP017NormUpper2558,
          batchC02700MinusRightP018NormUpper2558, batchC02700MinusRightP019NormUpper2558,
          batchC02700MinusRightP020NormUpper2558, batchC02700MinusRightP021NormUpper2558,
          batchC02700MinusRightP022NormUpper2558, batchC02700MinusRightP023NormUpper2558,
          batchC02700MinusRightP024NormUpper2558, batchC02700MinusRightP025NormUpper2558,
          batchC02700MinusRightP026NormUpper2558, batchC02700MinusRightP027NormUpper2558,
          batchC02700MinusRightP028NormUpper2558, batchC02700MinusRightP029NormUpper2558,
          batchC02700MinusFourthP000Upper2558, batchC02700MinusFourthP001Upper2558,
          batchC02700MinusFourthP002Upper2558, batchC02700MinusFourthP003Upper2558,
          batchC02700MinusFourthP004Upper2558, batchC02700MinusFourthP005Upper2558,
          batchC02700MinusFourthP006Upper2558, batchC02700MinusFourthP007Upper2558,
          batchC02700MinusFourthP008Upper2558, batchC02700MinusFourthP009Upper2558,
          batchC02700MinusFourthP010Upper2558, batchC02700MinusFourthP011Upper2558,
          batchC02700MinusFourthP012Upper2558, batchC02700MinusFourthP013Upper2558,
          batchC02700MinusFourthP014Upper2558, batchC02700MinusFourthP015Upper2558,
          batchC02700MinusFourthP016Upper2558, batchC02700MinusFourthP017Upper2558,
          batchC02700MinusFourthP018Upper2558, batchC02700MinusFourthP019Upper2558,
          batchC02700MinusFourthP020Upper2558, batchC02700MinusFourthP021Upper2558,
          batchC02700MinusFourthP022Upper2558, batchC02700MinusFourthP023Upper2558,
          batchC02700MinusFourthP024Upper2558, batchC02700MinusFourthP025Upper2558,
          batchC02700MinusFourthP026Upper2558, batchC02700MinusFourthP027Upper2558,
          batchC02700MinusFourthP028Upper2558, batchC02700MinusFourthP029Upper2558]
    exact mul_le_mul_of_nonneg_right
      (add_le_add (Complex.norm_le_abs_re_add_abs_im _) le_rfl) ht
  have hstep : 0 ≤ (2 * stripRadius2303 / 10240) := by norm_num [stripRadius2303]
  have hhalf : 0 ≤ ((2 * stripRadius2303 / 10240) / 2) := by norm_num [stripRadius2303]
  have hwidth : 0 ≤ ((edgeRightPosition2548 - edgeLeftPosition2548) / 2) := by
    norm_num [edgeRightPosition2548, edgeLeftPosition2548]
  have hC2 : signedCurvatureUpper2539 (-1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeLeftPosition2548 edgeRightPosition2548 ≤
      batchC02700MinusSignedMidpointUpper2558 +
        correctionThirdL1Sum2565 * ((edgeRightPosition2548 - edgeLeftPosition2548) / 2) :=
    hC.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hagg hwidth))
  rw [correctionThirdL1Sum_eq_2565] at hC2
  have hcube : 0 ≤ ((2 * stripRadius2303 / 10240) ^ 3 / 12) := by
    norm_num [stripRadius2303]
  have hsigma : 0 ≤ 2 * |(-1 / 2 : ℝ)| := by norm_num
  have hsig2 : 0 ≤ (-1 / 2 : ℝ) ^ 2 := by norm_num
  refine le_trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hC2 hstep)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add hJ1 (mul_le_mul_of_nonneg_right hC2 hhalf)) hstep)
      hsigma))
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hJ0l hJ0r) hhalf)
        (mul_le_mul_of_nonneg_right hC2 hcube))
      hsig2)) ?_
  norm_num [correctionSecondCell2700MinusUpper2565, stripRadius2303,
    batchC02700MinusSignedMidpointUpper2558, correctionThirdL1Upper2565, fjminUpper2565,
    sharedN02700MinusUpper2556, sharedN02701MinusUpper2556, edgeLeftPosition2548,
    edgeRightPosition2548, edgeMidpointPosition2548]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.correctionSecondCell2700MinusSummand_le_2565
#print axioms ConnesWeilRH.Dev.correctionThirdL1Sum_eq_2565
