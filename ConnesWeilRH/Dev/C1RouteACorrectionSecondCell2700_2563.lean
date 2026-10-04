import ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562
import ConnesWeilRH.Dev.C1RouteABoundaryIntegral2551
import ConnesWeilRH.Dev.C1RouteASharedN02700Plus2556
import ConnesWeilRH.Dev.C1RouteASharedN02701Plus2556
import ConnesWeilRH.Dev.C1RouteAFirstJetMidpoint2563

/-!
Correction-second single-cell certificate at production cell 2700, sigma=+1/2.
The three-piece summand of the 2562 decomposition of `stripSecondNorm` is
bounded by 236901/10^12 on the production cell, from the certified curvature
charge (2551), the new order-1 midpoint jet certificate (2563), and the shared
endpoint values (2556). Family centers and errors stay explicit at the boxes;
actual coefficients enter only through the membership premise of the 2562
consumer theorems, so no membership claim is made here.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def correctionSecondCell2700Upper2563 : ℝ :=
  ((236901 : ℝ) / 1000000000000)

theorem correctionSecondCell2700Summand_le_2563 :
    (2 * stripRadius2303 / 10240) *
        signedCurvatureUpper2539 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
          nodeModulation2541
          (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
          (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) +
      2 * |(1 / 2 : ℝ)| * ((2 * stripRadius2303 / 10240) *
        (signedJetUpper2539 1 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + ((5401 : ℝ) / 2) * (2 * stripRadius2303 / 10240)) +
          signedCurvatureUpper2539 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
            (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) *
            ((2 * stripRadius2303 / 10240) / 2))) +
      ((1 / 2 : ℝ) ^ 2) *
        ((2 * stripRadius2303 / 10240) / 2 *
          (signedJetUpper2539 0 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240)) +
          signedJetUpper2539 0 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
            nodeModulation2541
            (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240))) +
        signedCurvatureUpper2539 (1 / 2) baseCoefficientCenter2540 baseCoefficientError2540
          nodeModulation2541
          (-stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240))
          (-stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240)) *
          ((2 * stripRadius2303 / 10240) ^ 3 / 12)) ≤
      correctionSecondCell2700Upper2563 := by
  have hC := boundaryCellCurvatureBound2551
  have hJ1 := firstJetMidpointUpper_le2563
  have hJ0l := sharedN02700PlusSigned_le2556
  have hJ0r := sharedN02701PlusSigned_le2556
  have hpl : sharedN02700PlusPosition2556 = edgeLeftPosition2548 := by
    norm_num [sharedN02700PlusPosition2556, edgeLeftPosition2548]
  have hpr : sharedN02701PlusPosition2556 = edgeRightPosition2548 := by
    norm_num [sharedN02701PlusPosition2556, edgeRightPosition2548]
  rw [hpl] at hJ0l
  rw [hpr] at hJ0r
  rw [edgeLeftGrid2548, edgeRightGrid2548, edgeMidpointGrid2548]
  have hstep : 0 ≤ (2 * stripRadius2303 / 10240) := by norm_num [stripRadius2303]
  have hhalf : 0 ≤ ((2 * stripRadius2303 / 10240) / 2) := by norm_num [stripRadius2303]
  have hcube : 0 ≤ ((2 * stripRadius2303 / 10240) ^ 3 / 12) := by
    norm_num [stripRadius2303]
  have hsigma : 0 ≤ 2 * |(1 / 2 : ℝ)| := by norm_num
  have hsig2 : 0 ≤ (1 / 2 : ℝ) ^ 2 := by norm_num
  refine le_trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hC hstep)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add hJ1 (mul_le_mul_of_nonneg_right hC hhalf)) hstep)
      hsigma))
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hJ0l hJ0r) hhalf)
        (mul_le_mul_of_nonneg_right hC hcube))
      hsig2)) ?_
  norm_num [correctionSecondCell2700Upper2563, stripRadius2303, boundaryCellCurvatureUpper2551,
    fjmidUpper2563, sharedN02700PlusUpper2556, sharedN02701PlusUpper2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.correctionSecondCell2700Summand_le_2563
