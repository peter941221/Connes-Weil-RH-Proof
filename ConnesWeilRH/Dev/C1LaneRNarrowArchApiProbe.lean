import ConnesWeilRH.Dev.C1LaneRD3Root
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory
open ConnesWeilRH Source
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest

#check SchwartzMap.memLp
#check Homeomorph.neg
#check Homeomorph.measurableEmbedding
#check Homeomorph.addRight
#check Homeomorph.addLeft
#check Homeomorph.subRight
#check Homeomorph.subLeft

example (g : CompactLogTest) (y : ℝ) :
    ‖g.convolutionSquare.test y‖ ≤
      (g.convolutionSquare.test 0).re := by
  rw [convolutionSquare_apply]
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hbase : MemLp (g.test : ℝ → ℂ) (ENNReal.ofReal (2 : ℝ)) :=
    SchwartzMap.memLp g.test (ENNReal.ofReal (2 : ℝ))
  have hneg : MeasurePreserving (fun t : ℝ => -t) volume volume := by
    exact Measure.measurePreserving_neg volume
  have hsub : MeasurePreserving (fun t : ℝ => y - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).add_left volume y
  have hleft : MemLp (fun t : ℝ => g.test (-t))
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [Function.comp_apply] using hbase.comp_measurePreserving hneg
  have hright : MemLp (fun t : ℝ => g.test (y - t))
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [Function.comp_apply] using hbase.comp_measurePreserving hsub
  have hbound :
      ‖∫ t : ℝ, star (g.test (-t)) * g.test (y - t)‖ ≤
        ∫ t : ℝ, ‖star (g.test (-t)) * g.test (y - t)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have hholder_bound := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      hholder hleft hright

  have hneg_norm_integral :
      (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, ‖g.test t‖ ^ (2 : ℝ) := by
    simpa only [Function.comp_apply] using
      hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
        (fun t : ℝ => ‖g.test t‖ ^ (2 : ℝ))

  have hsub_norm_integral :
      (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, ‖g.test t‖ ^ (2 : ℝ) := by
    simpa only [Function.comp_apply] using
      hsub.integral_comp (Homeomorph.subLeft y).measurableEmbedding
        (fun t : ℝ => ‖g.test t‖ ^ (2 : ℝ))

  have hmass : 0 ≤ ∫ t : ℝ, Complex.normSq (g.test t) := by
    exact integral_nonneg fun t => Complex.normSq_nonneg (g.test t)

  have hneg_normSq_integral :
      (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, Complex.normSq (g.test t) := by
    rw [hneg_norm_integral]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

  have hsub_normSq_integral :
      (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) =
        ∫ t : ℝ, Complex.normSq (g.test t) := by
    rw [hsub_norm_integral]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

  have hholder_bound' :
      (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
        (∫ t : ℝ, Complex.normSq (g.test t)) := by
    have hraw :
        (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
          (∫ t : ℝ, ‖g.test (-t)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫ t : ℝ, ‖g.test (y - t)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        hholder hleft hright
    rw [hneg_normSq_integral, hsub_normSq_integral] at hraw
    calc
      (∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖) ≤
          (∫ t : ℝ, Complex.normSq (g.test t)) ^ (1 / (2 : ℝ)) *
            (∫ t : ℝ, Complex.normSq (g.test t)) ^ (1 / (2 : ℝ)) := hraw
      _ = ∫ t : ℝ, Complex.normSq (g.test t) := by
        rw [← Real.sqrt_eq_rpow]
        simpa only [pow_two] using Real.sq_sqrt hmass

  calc
    ‖∫ t : ℝ, star (g.test (-t)) * g.test (y - t)‖ ≤
        ∫ t : ℝ, ‖star (g.test (-t)) * g.test (y - t)‖ := hbound
    _ = ∫ t : ℝ, ‖g.test (-t)‖ * ‖g.test (y - t)‖ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [norm_mul, norm_star]
    _ ≤ ∫ t : ℝ, Complex.normSq (g.test t) := hholder_bound'
    _ = (g.convolutionSquare.test 0).re := by
      rw [g.convolutionSquare_zero_eq_integral_normSq]
      simp

#check MeasureTheory.integrableOn_const
#check MeasureTheory.setIntegral_const
#check MeasureTheory.integral_const
#check integral_re
#check MeasureTheory.setIntegral_union
#check intervalIntegral.integral_of_le
#check Real.volume_Ioc

example (A R : ℝ) (hR : 0 ≤ R) :
    (∫ y in Set.Ioc (0 : ℝ) R, A) = A * R := by
  rw [MeasureTheory.setIntegral_const]
  simp [Real.volume_Ioc, hR]
  ring
