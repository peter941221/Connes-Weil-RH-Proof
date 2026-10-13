import ConnesWeilRH.Dev.C1RouteARepairedOwnerCellCharge2686
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2688BaseM0

namespace ConnesWeilRH.Dev

private theorem record2688WeightedNormIntervalIntegrable
    {f : ℝ → ℂ} {a b sigma : ℝ}
    (hf : Continuous f) :
    IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖f x‖)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.norm

private theorem record2688ExternalPhysicalContinuous :
    Continuous (externalPhysical2344 record2688BaseCoefficient capturedModulations2584) := by
  rw [externalPhysical2344_eq_correctedPhysical]
  exact (correctedPhysical_contDiff record2688BaseCoefficient capturedModulations2584).continuous

def record2688BaseM0Norm : ℝ := binary64Value2674 0x40342d84f50a0754
def record2688BaseM0Charge : ℝ := binary64Value2674 0x3fc08797ed30c495

theorem record2688BaseM0CellContainedForIntegral {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2688CellRight) :
    record2688BaseM0Rect.Mem
      (externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x) := by
  exact record2688BaseM0CellContained hx

theorem record2688BaseM0IntegralCharge :
    (∫ x in (0 : ℝ)..record2688CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x‖)
      ≤ record2688BaseM0Charge := by
  have hbound :
      (∫ x in (0 : ℝ)..record2688CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x‖)
        ≤ (record2688CellRight - 0) * (1 * record2688BaseM0Norm) := by
    apply weightedNormIntegral_le_of_cellRectangle
      (a := 0) (b := record2688CellRight) (sigma := (-1 / 2 : ℝ))
      (weightBound := 1) (normBound := record2688BaseM0Norm)
      (rect := record2688BaseM0Rect)
      (by norm_num [record2688CellRight, binary64Value2674,
        binary64ExponentBits2674, binary64Significand2674,
        binary64FractionBits2674, binary64Sign2674])
      (fun x hx => record2688BaseM0CellContainedForIntegral hx)
      (ComplexRect2427.cornerNorm_le_of_sq_le (by
        norm_num [record2688BaseM0Norm, binary64Value2674,
          binary64ExponentBits2674, binary64Significand2674,
          binary64FractionBits2674, binary64Sign2674]) (by
        norm_num [record2688BaseM0Rect, record2688BaseM0Norm,
          ComplexRect2427.cornerNormSq, binary64Value2674,
          binary64ExponentBits2674, binary64Significand2674,
          binary64FractionBits2674, binary64Sign2674]))
      (by norm_num)
      (fun x hx => by
        have harg : ((-1 / 2 : ℝ) * x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.1
        calc
          Real.exp ((-1 / 2 : ℝ) * x) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr harg
          _ = 1 := Real.exp_zero)
      (record2688WeightedNormIntervalIntegrable
        (a := 0) (b := record2688CellRight) (sigma := (-1 / 2 : ℝ))
        (f := externalPhysical2344 record2688BaseCoefficient capturedModulations2584)
        record2688ExternalPhysicalContinuous)
  calc
    _ ≤ (record2688CellRight - 0) * (1 * record2688BaseM0Norm) := hbound
    _ ≤ record2688BaseM0Charge := by
      norm_num [record2688CellRight, record2688BaseM0Norm, record2688BaseM0Charge,
        binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
        binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
