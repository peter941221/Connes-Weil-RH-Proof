import ConnesWeilRH.Dev.C1RouteBLocalStageARect2906

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageDoubleARect2947 : ComplexRect2427 :=
  ComplexRect2427.mk ((0.10231836241932215 : ℚ) : ℝ)
    ((0.10285105279864694 : ℚ) : ℝ)
    ((-0.1715760948859532 : ℚ) : ℝ)
    ((-0.1712505045774558 : ℚ) : ℝ)

theorem routeBLocalStageDoubleA_mem2947 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageARect2906) :
    ComplexRect2427.Mem (2 * z) routeBLocalStageDoubleARect2947 := by
  rcases hz with ⟨hreLo, hreHi, himLo, himHi⟩
  simp [ComplexRect2427.Mem, routeBLocalStageARect2906,
    routeBLocalStageDoubleARect2947, Complex.mul_re, Complex.mul_im] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hreLo]
  · linarith [hreHi]
  · linarith [himLo]
  · linarith [himHi]

end ConnesWeilRH.Dev
