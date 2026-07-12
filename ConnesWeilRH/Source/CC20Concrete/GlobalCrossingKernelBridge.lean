/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Restrict the global crossing to its finite boundary interval

The global crossing is supported on `Icc (-b) 0` for `b ≥ 0`.  This theorem
records the exact translation seen on that restricted carrier, which is the
geometric input needed before comparing with compact crossing kernels.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

abbrev cc20CrossingBoundaryInterval (b : ℝ) := Set.Icc (-b) 0

noncomputable instance cc20CrossingBoundaryIntervalMeasureSpace (b : ℝ) :
    MeasureSpace (cc20CrossingBoundaryInterval b) := Measure.Subtype.measureSpace

theorem cc20SingleCrossingOperator_restrict_coeFn_eq_translation
    (b : ℝ) (hb : 0 ≤ b) (u : cc20GlobalLogCrossingL2) :
    ∀ᵐ t ∂(volume.restrict (cc20CrossingBoundaryInterval b)),
      (cc20SingleCrossingOperator b u : ℝ → ℂ) t = u (t + b) := by
  have hglobal := cc20SingleCrossingOperator_coeFn_eq_Icc_indicator b hb u
  have hrestrict := ae_restrict_of_ae (s := cc20CrossingBoundaryInterval b) hglobal
  have hmem : ∀ᵐ t ∂(volume.restrict (cc20CrossingBoundaryInterval b)),
      t ∈ cc20CrossingBoundaryInterval b :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hrestrict, hmem] with t ht htm
  rw [ht]
  simp only [Set.indicator_of_mem htm]

theorem cc20SingleCrossingOperator_schwartz_inner_eq_boundary_integral
    (h : SchwartzMap ℝ ℂ) (b : ℝ) (hb : 0 ≤ b) :
    inner ℂ (h.toLp 2) (cc20SingleCrossingOperator b (h.toLp 2)) =
      ∫ t in cc20CrossingBoundaryInterval b,
        star (h t) * h (t + b) := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator measurableSet_Icc]
  have hh := h.coeFn_toLp 2 (volume : Measure ℝ)
  have hhShift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq hh
  have hcross := cc20SingleCrossingOperator_coeFn_eq_Icc_indicator
    b hb (h.toLp 2)
  apply integral_congr_ae
  filter_upwards [hh, hhShift, hcross] with t hht hhShiftAt hcrossAt
  rw [hcrossAt]
  simp only [RCLike.inner_apply]
  rw [hht]
  by_cases ht : t ∈ cc20CrossingBoundaryInterval b
  · simp only [Set.indicator_of_mem ht]
    have hshiftValue : (h.toLp 2 : ℝ → ℂ) (t + b) = h (t + b) := by
      simpa only [Function.comp_apply] using hhShiftAt
    rw [hshiftValue]
    exact mul_comm _ _
  · simp only [Set.indicator, ht, if_false, zero_mul]

end CC20Concrete
end Source
end ConnesWeilRH
