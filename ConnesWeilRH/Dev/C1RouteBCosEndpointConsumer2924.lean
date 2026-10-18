import ConnesWeilRH.Dev.C1RouteBCosTaylorEquality2922
import ConnesWeilRH.Dev.C1RouteBTrigCosTaylorRemainder2920

namespace ConnesWeilRH.Dev

theorem routeBCosEndpoint_of_mathlibRemainder2924
    (hrem : ‖Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.cos 20
        (Set.Icc 0 ((52523502177204355 : ℝ) / 10 ^ 16)) 0
        ((52523502177204355 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20) :
    (513 : ℝ) / 1000 <
        Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) < (516 : ℝ) / 1000 := by
  have hpoly := routeBCosTaylor20_eq_mathlib2922
    (x := (52523502177204355 : ℝ) / 10 ^ 16) (by norm_num)
  rw [hpoly] at hrem
  rw [abs_le] at hrem
  have harith := routeBTrigTaylor20_left_arithmetic2916
  rcases harith with ⟨_, _, hclo, hchi⟩
  constructor <;> linarith

end ConnesWeilRH.Dev
