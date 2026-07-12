/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelCompactOperator

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

noncomputable def cc20CompactMeasure : Measure CC20CompactInterval :=
  Measure.comap Subtype.val volume

theorem cc20CompactMeasure_univ :
    cc20CompactMeasure Set.univ = ENNReal.ofReal (3 / 2 : ℝ) := by
  rw [cc20CompactMeasure,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume Set.univ,
    Set.image_univ, Subtype.range_coe_subtype]
  change volume (Set.Icc (1 / 2 : ℝ) 2) = ENNReal.ofReal (3 / 2 : ℝ)
  rw [Real.volume_Icc]
  norm_num

instance : IsFiniteMeasure cc20CompactMeasure where
  measure_univ_lt_top := by
    rw [cc20CompactMeasure_univ]
    exact ENNReal.ofReal_lt_top

end CC20Concrete
end Source
end ConnesWeilRH
