import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

open Complex

def phaseRect2441 : ComplexRect2427 :=
  { reLo := -1, reHi := 1, imLo := -1, imHi := 1 }

def phaseRectOfBounds2444 (cLo cHi sLo sHi : ℝ) : ComplexRect2427 :=
  { reLo := cLo, reHi := cHi, imLo := sLo, imHi := sHi }

theorem phase_mem_of_sin_cos_bounds2444
    {t cLo cHi sLo sHi : ℝ}
    (hcLo : cLo ≤ Real.cos t)
    (hcHi : Real.cos t ≤ cHi)
    (hsLo : sLo ≤ Real.sin t)
    (hsHi : Real.sin t ≤ sHi) :
    (phaseRectOfBounds2444 cLo cHi sLo sHi).Mem
      (Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I]
  constructor
  · exact hcLo
  constructor
  · exact hcHi
  constructor
  · exact hsLo
  · exact hsHi

theorem phase_mem_phaseRect2441 (t : ℝ) :
    phaseRect2441.Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I]
  constructor
  · exact neg_one_le_cos t
  constructor
  · exact cos_le_one t
  constructor
  · exact neg_one_le_sin t
  · exact sin_le_one t

end ConnesWeilRH.Dev
