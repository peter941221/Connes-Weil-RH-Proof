import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCorrelatedTaxiMiddlePoint3236
import ConnesWeilRH.Dev.C1RouteAOwnerWindowZeroExtension3201

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680MiddlePointWeightArgument3239 : ℝ :=
  (-1 / 2 : ℝ) * record2680Center3212 17168

noncomputable def record2680MiddlePointWeightTaylorSum3239 : ℝ :=
  ∑ m ∈ Finset.range 30,
    record2680MiddlePointWeightArgument3239 ^ m / (m.factorial : ℝ)

noncomputable def record2680MiddlePointWeightTaylorError3239 : ℝ :=
  |record2680MiddlePointWeightArgument3239| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))

noncomputable def record2680MiddlePointWeightLower3239 : ℝ :=
  record2680MiddlePointWeightTaylorSum3239 -
    record2680MiddlePointWeightTaylorError3239

noncomputable def record2680MiddlePointWeightUpper3239 : ℝ :=
  record2680MiddlePointWeightTaylorSum3239 +
    record2680MiddlePointWeightTaylorError3239

noncomputable def record2680MiddlePointWeightBall3239 : ComplexTaxiBall3235 :=
  { center :=
      (((record2680MiddlePointWeightLower3239 +
        record2680MiddlePointWeightUpper3239) / 2 : ℝ) : ℂ)
    radius :=
      (record2680MiddlePointWeightUpper3239 -
        record2680MiddlePointWeightLower3239) / 2 }

theorem record2680_middle_point_weight_argument_bound3239 :
    |record2680MiddlePointWeightArgument3239| ≤ 1 := by
  norm_num [record2680MiddlePointWeightArgument3239,
    record2680Center3212, record2680Grid3212, diagnosticRadius3201]

theorem record2680_middle_point_weight_ball_mem3239 :
    (record2680MiddlePointWeightBall3239).Mem
      ((Real.exp record2680MiddlePointWeightArgument3239 : ℝ) : ℂ) := by
  have hTaylor := expTwoSided2676 (n := 30) (by norm_num)
    record2680_middle_point_weight_argument_bound3239
    (S := record2680MiddlePointWeightTaylorSum3239)
    (E := record2680MiddlePointWeightTaylorError3239) rfl rfl
  have herror : 0 ≤ record2680MiddlePointWeightTaylorError3239 := by
    dsimp [record2680MiddlePointWeightTaylorError3239]
    positivity
  constructor
  · change 0 ≤
      (record2680MiddlePointWeightUpper3239 -
        record2680MiddlePointWeightLower3239) / 2
    dsimp [record2680MiddlePointWeightUpper3239,
      record2680MiddlePointWeightLower3239]
    linarith
  · change
      taxiNorm3235
        (((Real.exp record2680MiddlePointWeightArgument3239 : ℝ) : ℂ) -
          (((record2680MiddlePointWeightLower3239 +
            record2680MiddlePointWeightUpper3239) / 2 : ℝ) : ℂ)) ≤
        (record2680MiddlePointWeightUpper3239 -
          record2680MiddlePointWeightLower3239) / 2
    simp only [taxiNorm3235, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero, add_zero,
      record2680MiddlePointWeightUpper3239,
      record2680MiddlePointWeightLower3239]
    rw [abs_le]
    constructor <;> linarith [hTaylor.1, hTaylor.2]

noncomputable def record2680MiddlePointWeightedAggregateBall3239 :
    ComplexTaxiBall3235 :=
  (record2680MiddlePointWeightBall3239).mul
    record2680MiddlePointAggregateBall3236

theorem record2680_middle_point_weighted_aggregate_ball_mem3239 :
    (record2680MiddlePointWeightedAggregateBall3239).Mem
      (weightedFunction2348 (-1 / 2)
        (externalPhysical2344 record2680CorrectionCoefficient
          capturedModulations2584)
        (record2680Center3212 17168)) := by
  unfold record2680MiddlePointWeightedAggregateBall3239
  have hweight := record2680_middle_point_weight_ball_mem3239
  have haggregate := record2680_middle_point_aggregate_ball_mem3236
  simpa [record2680MiddlePointWeightArgument3239,
    weightedFunction2348, weightedExp2348] using
    (ComplexTaxiBall3235.mem_mul hweight haggregate)

theorem taxi_ball_real_upper3239 {ball : ComplexTaxiBall3235} {z : ℂ}
    (hmem : ball.Mem z) :
    z.re ≤ ball.center.re + ball.radius := by
  have hreal : |z.re - ball.center.re| ≤ ball.radius := by
    calc
      |z.re - ball.center.re| ≤ taxiNorm3235 (z - ball.center) := by
        unfold taxiNorm3235
        exact le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ ball.radius := hmem.2
  have hupper := (abs_le.mp hreal).2
  linarith

theorem record2680_middle_point_weighted_value_upper3239 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 17168) ≤
      record2680MiddlePointWeightedAggregateBall3239.center.re +
        record2680MiddlePointWeightedAggregateBall3239.radius := by
  have h := taxi_ball_real_upper3239
    (record2680_middle_point_weighted_aggregate_ball_mem3239)
  change Real.exp ((-1 / 2 : ℝ) * record2680Center3212 17168) *
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)).re ≤
    record2680MiddlePointWeightedAggregateBall3239.center.re +
      record2680MiddlePointWeightedAggregateBall3239.radius
  change (((Real.exp ((-1 / 2 : ℝ) * record2680Center3212 17168) : ℝ) : ℂ) *
      externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)).re ≤
    record2680MiddlePointWeightedAggregateBall3239.center.re +
      record2680MiddlePointWeightedAggregateBall3239.radius at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, zero_mul, sub_zero] using h

end ConnesWeilRH.Dev
