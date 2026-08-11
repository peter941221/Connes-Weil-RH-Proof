import Mathlib
open MeasureTheory Filter Set
open scoped Real
noncomputable section

#check MeasureTheory.isFiniteMeasure_restrict
#check MeasureTheory.Measure.restrict.isFiniteMeasure
#check MeasureTheory.Measure.isFiniteMeasure
#check MeasureTheory.isFiniteMeasure_restrict.mpr

example (K : ℝ) : Integrable (fun _ : ℝ => K) (volume.restrict (Ioc (0:ℝ) 1)) := by
  have hfin : (volume : Measure ℝ) (Ioc (0:ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; norm_num
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) := by
    -- try restrict with hfin
    rw [MeasureTheory.restrict_lt_top'... ] 
    -- fallback
    unfold IsFiniteMeasure
    rw [Measure.restrict_univ]
    exact hfin
  exact MeasureTheory.integrable_const K