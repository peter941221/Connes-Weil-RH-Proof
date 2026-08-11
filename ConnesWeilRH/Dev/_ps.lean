import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

#check intervalIntegral.integral_add_adjacent_intervals
#check intervalIntegral.integral_eq_integral_of_support_subset
#check intervalIntegral.integral_comp_mul_left
#check measureSpace_coe
#check (∫ x in (0 : ℝ)..(1 : ℝ), (x : ℝ))
