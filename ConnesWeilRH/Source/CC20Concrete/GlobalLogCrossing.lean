/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogHaar

/-!
# Half-line projection for the global logarithmic `L2` carrier

The half-line projection is defined through the `Lp` restriction/indicator
equivalence, so it remains valid for the infinite-measure set `Ici 0`.  This
module records only the bounded projection API; it does not assert a trace
identity for any crossing composition.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set

noncomputable abbrev cc20GlobalLogCrossingL2 := cc20GlobalLogL2

noncomputable def cc20PositiveHalfLine : Set ℝ := Set.Ici 0

theorem measurableSet_cc20PositiveHalfLine :
    MeasurableSet cc20PositiveHalfLine := by
  exact measurableSet_Ici

noncomputable def cc20PositiveHalfLineProjectionLinearMap :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 where
  toFun u :=
    ((memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp u).restrict cc20PositiveHalfLine)).toLp
      (cc20PositiveHalfLine.indicator u)
  map_add' u v := by
    let hu :=
      (memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp u).restrict cc20PositiveHalfLine)
    let hv :=
      (memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp v).restrict cc20PositiveHalfLine)
    let huv :=
      (memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp (u + v)).restrict cc20PositiveHalfLine)
    apply MemLp.toLp_congr huv (hu.add hv)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      cc20PositiveHalfLine ?_ ?_
    · filter_upwards
        [ae_restrict_of_ae (Lp.coeFn_add u v),
          ae_restrict_mem measurableSet_cc20PositiveHalfLine] with t hsum ht
      simp only [Set.indicator_of_mem ht, Pi.add_apply]
      simpa only [Pi.add_apply] using hsum
    · filter_upwards
        [ae_restrict_mem measurableSet_cc20PositiveHalfLine.compl] with t ht
      have hnot : t ∉ cc20PositiveHalfLine := ht
      simp [Set.indicator, hnot]
  map_smul' c u := by
    let hu :=
      (memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp u).restrict cc20PositiveHalfLine)
    let hcu :=
      (memLp_indicator_iff_restrict
        measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp (c • u)).restrict cc20PositiveHalfLine)
    apply MemLp.toLp_congr hcu (hu.const_smul c)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      cc20PositiveHalfLine ?_ ?_
    · filter_upwards
        [ae_restrict_of_ae (Lp.coeFn_smul c u),
          ae_restrict_mem measurableSet_cc20PositiveHalfLine] with t hsmul ht
      simp only [Set.indicator_of_mem ht, Pi.smul_apply]
      simpa only [Pi.smul_apply] using hsmul
    · filter_upwards
        [ae_restrict_mem measurableSet_cc20PositiveHalfLine.compl] with t ht
      have hnot : t ∉ cc20PositiveHalfLine := ht
      simp [Set.indicator, hnot]

theorem norm_cc20PositiveHalfLineProjectionLinearMap_le
    (u : cc20GlobalLogCrossingL2) :
    ‖cc20PositiveHalfLineProjectionLinearMap u‖ ≤ ‖u‖ := by
  change ‖((memLp_indicator_iff_restrict
      measurableSet_cc20PositiveHalfLine).2
    ((Lp.memLp u).restrict cc20PositiveHalfLine)).toLp
      (cc20PositiveHalfLine.indicator u)‖ ≤ ‖u‖
  rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    measurableSet_cc20PositiveHalfLine]
  exact ENNReal.toReal_mono (by finiteness)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

noncomputable def cc20PositiveHalfLineProjection :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  LinearMap.mkContinuous
    cc20PositiveHalfLineProjectionLinearMap
    1
    (fun u => by
      simpa only [one_mul] using
        norm_cc20PositiveHalfLineProjectionLinearMap_le u)

theorem cc20PositiveHalfLineProjection_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (cc20PositiveHalfLineProjection u : ℝ → ℂ) =ᵐ[volume]
      cc20PositiveHalfLine.indicator (fun t => u t) := by
  change
    ((memLp_indicator_iff_restrict
      measurableSet_cc20PositiveHalfLine).2
      ((Lp.memLp u).restrict cc20PositiveHalfLine)).toLp
      (cc20PositiveHalfLine.indicator u) =ᵐ[volume]
      cc20PositiveHalfLine.indicator (fun t => u t)
  exact MemLp.coeFn_toLp _

theorem cc20PositiveHalfLineProjection_idempotent
    (u : cc20GlobalLogCrossingL2) :
    cc20PositiveHalfLineProjection
        (cc20PositiveHalfLineProjection u) =
      cc20PositiveHalfLineProjection u := by
  rw [Lp.ext_iff]
  filter_upwards
    [cc20PositiveHalfLineProjection_coeFn u,
      cc20PositiveHalfLineProjection_coeFn
        (cc20PositiveHalfLineProjection u)] with t hu hpu
  by_cases ht : t ∈ cc20PositiveHalfLine
  · simpa only [Set.indicator_of_mem ht] using hpu
  · calc
      (cc20PositiveHalfLineProjection
          (cc20PositiveHalfLineProjection u) : ℝ → ℂ) t = 0 := by
        simpa [Set.indicator, ht] using hpu
      _ = (cc20PositiveHalfLineProjection u : ℝ → ℂ) t := by
        symm
        simpa [Set.indicator, ht] using hu

noncomputable def cc20GlobalLogTranslation (b : ℝ) :
    cc20GlobalLogCrossingL2 →ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => t + b)
    (measurePreserving_add_right volume b)

theorem cc20GlobalLogTranslation_coeFn
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    (cc20GlobalLogTranslation b u : ℝ → ℂ) =ᵐ[volume]
      fun t => u (t + b) := by
  exact Lp.coeFn_compMeasurePreserving u
    (measurePreserving_add_right volume b)

theorem norm_cc20GlobalLogTranslation
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    ‖cc20GlobalLogTranslation b u‖ = ‖u‖ := by
  exact (cc20GlobalLogTranslation b).norm_map u

theorem cc20GlobalLogTranslation_neg_apply
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalLogTranslation b
        (cc20GlobalLogTranslation (-b) u) = u := by
  rw [Lp.ext_iff]
  have hnegShift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq
      (cc20GlobalLogTranslation_coeFn (-b) u)
  filter_upwards
    [hnegShift,
      cc20GlobalLogTranslation_coeFn b
        (cc20GlobalLogTranslation (-b) u)] with t hnegShiftAt hb
  rw [hb]
  simpa [Function.comp_def] using hnegShiftAt

/-- Global logarithmic translations form an additive representation. -/
theorem cc20GlobalLogTranslation_add_apply
    (a b : ℝ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalLogTranslation a (cc20GlobalLogTranslation b u) =
      cc20GlobalLogTranslation (a + b) u := by
  rw [Lp.ext_iff]
  have hinner :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq
      (cc20GlobalLogTranslation_coeFn b u)
  filter_upwards
    [hinner,
      cc20GlobalLogTranslation_coeFn a (cc20GlobalLogTranslation b u),
      cc20GlobalLogTranslation_coeFn (a + b) u] with t hinnerAt ha hab
  rw [ha, hab]
  simpa only [Function.comp_apply, add_assoc] using hinnerAt

/-- Any two global logarithmic translations commute. -/
theorem cc20GlobalLogTranslation_commute
    (a b : ℝ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalLogTranslation a (cc20GlobalLogTranslation b u) =
      cc20GlobalLogTranslation b (cc20GlobalLogTranslation a u) := by
  rw [cc20GlobalLogTranslation_add_apply,
    cc20GlobalLogTranslation_add_apply, add_comm]

noncomputable def cc20NegativeHalfLineProjection :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
    cc20PositiveHalfLineProjection

theorem cc20NegativeHalfLineProjection_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (cc20NegativeHalfLineProjection u : ℝ → ℂ) =ᵐ[volume]
      (Set.Iio 0).indicator (fun t => u t) := by
  simp only [cc20NegativeHalfLineProjection,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  filter_upwards
    [Lp.coeFn_sub u (cc20PositiveHalfLineProjection u),
      cc20PositiveHalfLineProjection_coeFn u] with t hsub hpos
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hpos]
  by_cases ht : t ∈ cc20PositiveHalfLine
  · have hnot : t ∉ Set.Iio 0 := by
      simpa [cc20PositiveHalfLine] using ht
    simp [Set.indicator, ht, hnot]
  · have hlt : t ∈ Set.Iio 0 := by
      simpa [cc20PositiveHalfLine, Set.mem_Iio] using ht
    simp [Set.indicator, ht, hlt]

noncomputable def cc20SingleCrossingOperator (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20NegativeHalfLineProjection.comp
    ((cc20GlobalLogTranslation b).toContinuousLinearMap.comp
      cc20PositiveHalfLineProjection)

theorem cc20SingleCrossingOperator_apply
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    cc20SingleCrossingOperator b u =
      cc20NegativeHalfLineProjection
        (cc20GlobalLogTranslation b
          (cc20PositiveHalfLineProjection u)) := by
  rfl

theorem cc20SingleCrossingOperator_coeFn
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    (cc20SingleCrossingOperator b u : ℝ → ℂ) =ᵐ[volume]
      (Set.Iio 0).indicator (fun t =>
        (Set.Ici 0).indicator (fun x => u x) (t + b)) := by
  rw [cc20SingleCrossingOperator_apply]
  have hneg := cc20NegativeHalfLineProjection_coeFn
    (cc20GlobalLogTranslation b
      (cc20PositiveHalfLineProjection u))
  have htrans := cc20GlobalLogTranslation_coeFn b
    (cc20PositiveHalfLineProjection u)
  have hpos := cc20PositiveHalfLineProjection_coeFn u
  have hpos_shift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq hpos
  filter_upwards [hneg, htrans, hpos_shift] with t hnegAt htransAt hposAt
  rw [hnegAt]
  by_cases ht : t ∈ Set.Iio 0
  · simp only [Set.indicator_of_mem ht]
    rw [htransAt]
    simpa only [Function.comp_apply] using hposAt
  · simp only [Set.indicator, ht, if_false]

theorem cc20SingleCrossingOperator_coeFn_eq_Icc_indicator
    (b : ℝ) (hb : 0 ≤ b) (u : cc20GlobalLogCrossingL2) :
    (cc20SingleCrossingOperator b u : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (-b) 0).indicator (fun t => u (t + b)) := by
  have hcross := cc20SingleCrossingOperator_coeFn b u
  filter_upwards [hcross, MeasureTheory.volume.ae_ne (0 : ℝ)] with t ht hzero
  by_cases hIcc : t ∈ Set.Icc (-b) 0
  · have htneg : t ∈ Set.Iio 0 := by
      exact lt_of_le_of_ne hIcc.2 hzero
    have htlow : -b ≤ t := hIcc.1
    have htpos : t + b ∈ Set.Ici 0 := by
      change 0 ≤ t + b
      linarith
    simp only [Set.indicator_of_mem hIcc]
    rw [ht]
    simp only [Set.indicator_of_mem htneg, Set.indicator_of_mem htpos]
  · simp only [Set.indicator, hIcc, if_false]
    by_cases htneg : t ∈ Set.Iio 0
    · have htlt : t < -b := by
        by_contra hnot
        have htge : -b ≤ t := le_of_not_gt hnot
        exact hIcc ⟨htge, le_of_lt htneg⟩
      have htpos : t + b ∉ Set.Ici 0 := by
        simp only [Set.mem_Ici, not_le]
        linarith
      rw [ht]
      simp only [Set.indicator, htneg, htpos, if_true, if_false]
    · rw [ht]
      simp only [Set.indicator, htneg, if_false]

end CC20Concrete
end Source
end ConnesWeilRH
