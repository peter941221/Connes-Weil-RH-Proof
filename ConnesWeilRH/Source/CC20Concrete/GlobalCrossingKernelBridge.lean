/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing

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

end CC20Concrete
end Source
end ConnesWeilRH
