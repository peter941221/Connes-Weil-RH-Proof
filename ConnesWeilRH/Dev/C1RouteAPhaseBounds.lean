import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import Mathlib.Analysis.Complex.Trigonometric

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
  simpa only [ComplexRect2427.Mem, phaseRectOfBounds2444,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] using
    (show cLo ≤ Real.cos t ∧ Real.cos t ≤ cHi ∧
      sLo ≤ Real.sin t ∧ Real.sin t ≤ sHi from ⟨hcLo, hcHi, hsLo, hsHi⟩)

theorem phase_mem_phaseRect2441 (t : ℝ) :
    phaseRect2441.Mem (Complex.exp ((t : ℂ) * Complex.I)) := by
  exact phase_mem_of_sin_cos_bounds2444 (Real.neg_one_le_cos t)
    (Real.cos_le_one t) (Real.neg_one_le_sin t) (Real.sin_le_one t)

end ConnesWeilRH.Dev
