import ConnesWeilRH.Dev.C1RouteBDirectZFormula2975

namespace ConnesWeilRH.Dev

noncomputable def routeBDirectZTargetRect2976 : ComplexRect2427 :=
  ComplexRect2427.mk
    ((1.987794698109531521319423660106520404133121413129593559369033550776606 : ℚ) : ℝ)
    ((2.013861574620613032648932693386981825796577911760516505483174440338523 : ℚ) : ℝ)
    ((-0.006708710493875596218744770411729341108042591851448337565211759477967063 : ℚ) : ℝ)
    ((0.009643062445654370475342615516971944180724636541596131025489457605677501 : ℚ) : ℝ)

theorem routeBDirectZRectOfNumeratorBounds2976
    {zr zi d nr ni : ℝ}
    (hd : 0 < d)
    (hrlo : routeBDirectZTargetRect2976.reLo * d ≤ nr)
    (hrhi : nr ≤ routeBDirectZTargetRect2976.reHi * d)
    (hilo : routeBDirectZTargetRect2976.imLo * d ≤ ni)
    (hihi : ni ≤ routeBDirectZTargetRect2976.imHi * d) :
    ComplexRect2427.Mem (⟨nr / d, ni / d⟩ : ℂ) routeBDirectZTargetRect2976 := by
  change routeBDirectZTargetRect2976.reLo ≤ nr / d ∧
    nr / d ≤ routeBDirectZTargetRect2976.reHi ∧
    routeBDirectZTargetRect2976.imLo ≤ ni / d ∧
    ni / d ≤ routeBDirectZTargetRect2976.imHi
  constructor
  · exact (le_div_iff₀ hd).2 hrlo
  constructor
  · exact (div_le_iff₀ hd).2 hrhi
  constructor
  · exact (le_div_iff₀ hd).2 hilo
  · exact (div_le_iff₀ hd).2 hihi

end ConnesWeilRH.Dev
