import ConnesWeilRH.Dev.C1RouteAAnalyticMomentNormalization2618
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

namespace ConnesWeilRH.Dev

open MeasureTheory

theorem probeMeasurable2628 (radius nodeReal : ℝ) :
    Measurable (realNormalizedMomentIntegrand2618 radius nodeReal) := by
  have hset : MeasurableSet {a : ℝ | |a| < 1} := by
    rw [show {a : ℝ | |a| < 1} = Set.Ioo (-1) 1 by ext; simp [abs_lt]]
    exact measurableSet_Ioo
  unfold realNormalizedMomentIntegrand2618
  apply Measurable.ite hset
  · apply Measurable.exp
    apply Measurable.add
    · apply Measurable.div measurable_const
      exact Measurable.sub measurable_const (Measurable.pow measurable_id measurable_const)
    · exact Measurable.mul (Measurable.mul measurable_const measurable_const) measurable_id
  · exact measurable_const

theorem probeIntervalIntegrable2628 (radius nodeReal a b : ℝ) :
    IntervalIntegrable (realNormalizedMomentIntegrand2618 radius nodeReal) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (probeMeasurable2628 radius nodeReal).aestronglyMeasurable ?_
    (M := Real.exp (|nodeReal * radius|))
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  by_cases hx : |x| < 1
  · unfold realNormalizedMomentIntegrand2618
    rw [if_pos hx, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    have hx1 : (0 : ℝ) < 1 - x ^ 2 := by
      have habs : |x| < 1 := hx
      have hbounds := abs_lt.mp habs
      nlinarith [sq_nonneg (1 - x), sq_nonneg (1 + x)]
    calc
      -30 / (1 - x ^ 2) + nodeReal * radius * x
          ≤ nodeReal * radius * x := by
            have hdiv : -30 / (1 - x ^ 2) ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg (by norm_num) hx1.le
            linarith
      _ ≤ |nodeReal * radius| := by
        calc
          nodeReal * radius * x ≤ |nodeReal * radius * x| := le_abs_self _
          _ = |nodeReal * radius| * |x| := by rw [abs_mul]
          _ ≤ |nodeReal * radius| := by
            exact mul_le_of_le_one_right (abs_nonneg _) hx.le
  · unfold realNormalizedMomentIntegrand2618
    rw [if_neg hx]
    simpa using (Real.exp_nonneg (|nodeReal * radius|))

end ConnesWeilRH.Dev
