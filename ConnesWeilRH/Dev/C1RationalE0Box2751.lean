import ConnesWeilRH.Dev.C1RationalExponentialJet2750

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def unitExpBox2751 : RationalBox2744 :=
  { lo := 0, hi := 1, ordered := by norm_num }

theorem unitExpBox_mem2751 {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hphase : transitionPhase2731 x ≤ 0) :
    unitExpBox2751.Mem (transitionExp2731 x) := by
  simp only [unitExpBox2751, RationalBox2744.Mem, Rat.cast_zero, Rat.cast_one]
  constructor
  · change (0 : ℝ) ≤ transitionExp2731 x
    exact le_of_lt (Real.exp_pos _)
  · change transitionExp2731 x ≤ (1 : ℝ)
    unfold transitionExp2731
    exact Real.exp_le_one_iff.mpr hphase

 theorem unitExpBox_mem_of_half2751 {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ (1 / 2 : ℝ)) :
    unitExpBox2751.Mem (transitionExp2731 x) := by
  apply unitExpBox_mem2751 hx0
  · have hx1 : x < 1 := by linarith
    exact hx1
  · unfold transitionPhase2731
    have hp : 0 < 1 - x := by linarith
    have hleft : (1 - x)⁻¹ ≤ x⁻¹ := by
      exact (inv_le_inv₀ (by positivity) hx0).2 (by linarith)
    linarith

end
end ConnesWeilRH.Dev
