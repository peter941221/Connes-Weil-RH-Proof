import ConnesWeilRH.Source.CC20YoshidaCriticalContraction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest

noncomputable section

def smoothSeedRaw (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 2) * Real.smoothTransition (2 - x)

def smoothSeedComplex (x : ℝ) : ℂ :=
  (smoothSeedRaw x : ℂ)

theorem smoothSeedRaw_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothSeedRaw := by
  unfold smoothSeedRaw
  simpa only [Function.comp_apply] using
    (Real.smoothTransition.contDiff.comp
      (contDiff_id.add contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub contDiff_id))

theorem smoothSeedRaw_nonneg (x : ℝ) : 0 ≤ smoothSeedRaw x := by
  unfold smoothSeedRaw
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem smoothSeedRaw_le_one (x : ℝ) : smoothSeedRaw x ≤ 1 := by
  unfold smoothSeedRaw
  have h₁ := Real.smoothTransition.le_one (x + 2)
  have h₂ := Real.smoothTransition.le_one (2 - x)
  have h₁₀ := Real.smoothTransition.nonneg (x + 2)
  have h₂₀ := Real.smoothTransition.nonneg (2 - x)
  nlinarith

theorem smoothSeedRaw_eq_zero_of_le {x : ℝ} (hx : x ≤ -2) :
    smoothSeedRaw x = 0 := by
  unfold smoothSeedRaw
  have harg : x + 2 ≤ 0 := by linarith
  rw [Real.smoothTransition.zero_of_nonpos harg]
  simp

theorem smoothSeedRaw_eq_zero_of_ge {x : ℝ} (hx : 2 ≤ x) :
    smoothSeedRaw x = 0 := by
  unfold smoothSeedRaw
  have harg : 2 - x ≤ 0 := by linarith
  rw [Real.smoothTransition.zero_of_nonpos harg]
  simp

theorem smoothSeedRaw_support_subset :
    Function.support smoothSeedRaw ⊆ Set.Icc (-2) 2 := by
  intro x hx
  have hne : smoothSeedRaw x ≠ 0 := Function.mem_support.mp hx
  by_cases hleft : x < -2
  · exact (hne (smoothSeedRaw_eq_zero_of_le hleft.le)).elim
  by_cases hright : 2 < x
  · exact (hne (smoothSeedRaw_eq_zero_of_ge hright.le)).elim
  exact ⟨by linarith, by linarith⟩

theorem smoothSeedRaw_eq_one_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) : smoothSeedRaw x = 1 := by
  unfold smoothSeedRaw
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le]
  · norm_num
  · linarith [hx.2]
  · linarith [hx.1]

theorem smoothSeedComplex_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothSeedComplex := by
  unfold smoothSeedComplex
  exact Complex.ofRealCLM.contDiff.comp smoothSeedRaw_contDiff

theorem smoothSeedComplex_support_subset :
    Function.support smoothSeedComplex ⊆ Set.Icc (-2) 2 := by
  intro x hx
  have hne : smoothSeedRaw x ≠ 0 := by
    intro hzero
    apply Function.mem_support.mp hx
    simp [smoothSeedComplex, hzero]
  exact smoothSeedRaw_support_subset (Function.mem_support.mpr hne)

theorem smoothSeedComplex_hasCompactSupport :
    HasCompactSupport smoothSeedComplex :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    smoothSeedComplex_support_subset

def smoothSeed : CCM25Concrete.CompactLogConvolution.CompactLogTest :=
  { test := smoothSeedComplex_hasCompactSupport.toSchwartzMap
      (by simpa using smoothSeedComplex_contDiff)
    compactSupport := by simpa using smoothSeedComplex_hasCompactSupport }

theorem smoothSeed_apply (x : ℝ) :
    smoothSeed.test x = smoothSeedComplex x :=
  rfl

theorem smoothSeed_laplaceAt_zero_eq_real_integral :
    laplaceAt smoothSeed 0 = ∫ x : ℝ, (smoothSeedRaw x : ℂ) := by
  unfold laplaceAt
  apply integral_congr_ae
  filter_upwards with x
  simp [smoothSeed_apply, smoothSeedComplex]

theorem smoothSeed_laplaceAt_zero_ne_zero :
    laplaceAt smoothSeed 0 ≠ 0 := by
  rw [smoothSeed_laplaceAt_zero_eq_real_integral, integral_complex_ofReal]
  apply Complex.ofReal_ne_zero.mpr
  have hint : Integrable smoothSeedRaw :=
    smoothSeedRaw_contDiff.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
        smoothSeedRaw_support_subset)
  have hpos : 0 < ∫ x : ℝ, smoothSeedRaw x := by
    apply integral_pos_of_integrable_nonneg_nonzero
      smoothSeedRaw_contDiff.continuous hint smoothSeedRaw_nonneg
    rw [smoothSeedRaw_eq_one_of_mem_Icc
      (show (0 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)]
    norm_num
  exact ne_of_gt hpos

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed