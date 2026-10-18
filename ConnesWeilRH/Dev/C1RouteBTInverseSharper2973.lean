import ConnesWeilRH.Dev.C1RouteBTSourceNonzero2968

namespace ConnesWeilRH.Dev

noncomputable def routeBTInverseSharperRect2973 : ComplexRect2427 :=
  ComplexRect2427.mk ((1025 : ℝ) / 100) ((1040 : ℝ) / 100)
    ((1705 : ℝ) / 100) ((1730 : ℝ) / 100)

theorem routeBTInverseSharperRectMem2973 {t : ℂ}
    (ht : ComplexRect2427.Mem t routeBTSourceRect2968) :
    ComplexRect2427.Mem t⁻¹ routeBTInverseSharperRect2973 := by
  have hxl := ht.1
  have hxh := ht.2.1
  have hyl := ht.2.2.1
  have hyh := ht.2.2.2
  norm_num [routeBTSourceRect2968, ComplexRect2427.mk] at hxl hxh hyl hyh
  have hdenpos : 0 < Complex.normSq t := by
    exact (Complex.normSq_pos).mpr (routeBTSourceNonzero2968 ht)
  have hdenlo : (2493 : ℝ) / 1000000 ≤ Complex.normSq t := by
    simp [Complex.normSq_apply]
    nlinarith
  have hdenhi : Complex.normSq t ≤ (2507 : ℝ) / 1000000 := by
    simp [Complex.normSq_apply]
    nlinarith
  have hformre : (t⁻¹).re = t.re / Complex.normSq t := by
    simp [Complex.inv_re, Complex.normSq_apply]
  have hformim : (t⁻¹).im = -t.im / Complex.normSq t := by
    simp [Complex.inv_im, Complex.normSq_apply]
  change (1025 : ℝ) / 100 ≤ (t⁻¹).re ∧ (t⁻¹).re ≤ 1040 / 100 ∧
    (1705 : ℝ) / 100 ≤ (t⁻¹).im ∧ (t⁻¹).im ≤ 1730 / 100
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
