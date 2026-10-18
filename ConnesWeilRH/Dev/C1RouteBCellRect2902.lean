import ConnesWeilRH.Dev.C1RouteANormBridge2453

namespace ConnesWeilRH.Dev

theorem norm_le_of_rect_mem_of_sq_bound2902 {z : ℂ} (r : ComplexRect2427)
    (h : ComplexRect2427.Mem z r) {B : ℝ} (hB : 0 ≤ B)
    (hsq : (max |r.reLo| |r.reHi|) ^ 2 +
      (max |r.imLo| |r.imHi|) ^ 2 ≤ B ^ 2) :
    ‖z‖ ≤ B := by
  have hre : |z.re| ≤ max |r.reLo| |r.reHi| := by
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact h.2.1.trans (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [abs_of_nonpos hneg]
      calc -z.re ≤ -r.reLo := neg_le_neg h.1
        _ ≤ |r.reLo| := by
          have habs := le_abs_self (-r.reLo)
          rwa [abs_neg] at habs
        _ ≤ max |r.reLo| |r.reHi| := le_max_left _ _
  have him : |z.im| ≤ max |r.imLo| |r.imHi| := by
    rcases le_total 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact h.2.2.2.trans (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [abs_of_nonpos hneg]
      calc -z.im ≤ -r.imLo := neg_le_neg h.2.2.1
        _ ≤ |r.imLo| := by
          have habs := le_abs_self (-r.imLo)
          rwa [abs_neg] at habs
        _ ≤ max |r.imLo| |r.imHi| := le_max_left _ _
  have hsqz : Complex.normSq z ≤ B ^ 2 := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (max |r.reLo| |r.reHi|),
      sq_nonneg (max |r.imLo| |r.imHi|)]
  rw [Complex.norm_def]
  have hsqrt : Real.sqrt (Complex.normSq z) ≤ Real.sqrt (B ^ 2) :=
    Real.sqrt_le_sqrt hsqz
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB] at hsqrt
  exact hsqrt

/- Representative 256-cell rectangle (cell 214), generated from the
   committed 2889 artifact.  Membership remains an explicit premise until
   interval soundness is formalized. -/
noncomputable def routeBCellRect2902 : ComplexRect2427 :=
  ComplexRect2427.mk ((12.38798369147758383550008930781557878573645385892358563185294828556948 : ℚ) : ℝ) ((13.75960204634963355062811181245732141228968461863747844108312595734489 : ℚ) : ℝ)
    ((-0.4018516673523189155353809936589514532296302852328021989462456756841968 : ℚ) : ℝ) ((0.7315648100385260157546419408619820736028488292369928838707634870253127 : ℚ) : ℝ)

theorem routeBCellRectNormBound2902 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBCellRect2902) :
    ‖z‖ ≤ (1377903608911727 : ℝ) / 10 ^ 14 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBCellRect2902 hz (by norm_num)
  norm_num [routeBCellRect2902, ComplexRect2427.mk]
  nlinarith

end ConnesWeilRH.Dev
