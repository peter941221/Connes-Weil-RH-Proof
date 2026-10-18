import ConnesWeilRH.Dev.C1RouteBArgumentImagFormula2987
import ConnesWeilRH.Dev.C1RouteBExpRectStageConsumer2940

namespace ConnesWeilRH.Dev

noncomputable def routeBArgumentTargetRect2988 : ComplexRect2427 :=
  ComplexRect2427.mk
    ((10231836241932215 : ℝ) / 10 ^ 17) ((103 : ℝ) / 1000)
    (-(1715760948859532 : ℝ) / 10 ^ 16)
    (-(1712505045774558 : ℝ) / 10 ^ 16)

theorem routeBArgumentRectOfNumeratorBounds2988
    {d nr ni : ℝ}
    (hd : 0 < d)
    (hrlo : routeBArgumentTargetRect2988.reLo * d ≤ nr)
    (hrhi : nr ≤ routeBArgumentTargetRect2988.reHi * d)
    (hilo : routeBArgumentTargetRect2988.imLo * d ≤ ni)
    (hihi : ni ≤ routeBArgumentTargetRect2988.imHi * d) :
    ComplexRect2427.Mem (⟨nr / d, ni / d⟩ : ℂ)
      routeBArgumentTargetRect2988 := by
  change routeBArgumentTargetRect2988.reLo ≤ nr / d ∧
    nr / d ≤ routeBArgumentTargetRect2988.reHi ∧
    routeBArgumentTargetRect2988.imLo ≤ ni / d ∧
    ni / d ≤ routeBArgumentTargetRect2988.imHi
  constructor
  · exact (le_div_iff₀ hd).2 hrlo
  constructor
  · exact (div_le_iff₀ hd).2 hrhi
  constructor
  · exact (le_div_iff₀ hd).2 hilo
  · exact (div_le_iff₀ hd).2 hihi

end ConnesWeilRH.Dev
