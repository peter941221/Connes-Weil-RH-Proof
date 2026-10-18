import ConnesWeilRH.Dev.C1RouteBExpRectMembership2963
import ConnesWeilRH.Dev.C1RouteBExpDenominatorNonzero2964

namespace ConnesWeilRH.Dev

noncomputable def routeBExpDenominatorInverseTightRect2971 : ComplexRect2427 :=
  ComplexRect2427.mk ((473 : ℝ) / 1000) ((480 : ℝ) / 1000)
    ((42 : ℝ) / 1000) ((44 : ℝ) / 1000)

theorem routeBExpDenominatorInverseTightRectMem2971 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    ComplexRect2427.Mem ((w + 1)⁻¹) routeBExpDenominatorInverseTightRect2971 := by
  have hxl := hw.1
  have hxh := hw.2.1
  have hyl := hw.2.2.1
  have hyh := hw.2.2.2
  norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk] at hxl hxh hyl hyh
  have hxr : (20914 : ℝ) / 10000 ≤ (w + 1).re := by
    simp
    linarith
  have hxrhi : (w + 1).re ≤ (20923 : ℝ) / 10000 := by
    simp
    linarith
  have hyr : -(1893 : ℝ) / 10000 ≤ (w + 1).im := by
    simp
    linarith
  have hyrhi : (w + 1).im ≤ -(1887 : ℝ) / 10000 := by
    simp
    linarith
  have hdenpos : 0 < Complex.normSq (w + 1) := by
    have : w + 1 ≠ 0 := routeBExpDenominatorNonzero2964 hw
    exact (Complex.normSq_pos).mpr this
  have hdenlo : (440 : ℝ) / 100 ≤ Complex.normSq (w + 1) := by
    simp [Complex.normSq_apply]
    nlinarith
  have hdenhi : Complex.normSq (w + 1) ≤ (442 : ℝ) / 100 := by
    simp [Complex.normSq_apply]
    nlinarith
  have hformre : ((w + 1)⁻¹).re = (w + 1).re / Complex.normSq (w + 1) := by
    simp [Complex.inv_re, Complex.normSq_apply]
  have hformim : ((w + 1)⁻¹).im = -(w + 1).im / Complex.normSq (w + 1) := by
    simp [Complex.inv_im, Complex.normSq_apply]
  change (473 : ℝ) / 1000 ≤ ((w + 1)⁻¹).re ∧
    ((w + 1)⁻¹).re ≤ 480 / 1000 ∧
    (42 : ℝ) / 1000 ≤ ((w + 1)⁻¹).im ∧
    ((w + 1)⁻¹).im ≤ 44 / 1000
  rw [hformre, hformim]
  constructor
  · apply (le_div_iff₀ hdenpos).2
    nlinarith
  constructor
  · apply (div_le_iff₀ hdenpos).2
    nlinarith
  constructor
  · apply (le_div_iff₀ hdenpos).2
    nlinarith
  · apply (div_le_iff₀ hdenpos).2
    nlinarith

end ConnesWeilRH.Dev
