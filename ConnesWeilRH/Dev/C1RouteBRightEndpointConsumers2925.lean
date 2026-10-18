import ConnesWeilRH.Dev.C1RouteBTrigTaylor2916
import ConnesWeilRH.Dev.C1RouteBTrigTaylorRemainder2919
import ConnesWeilRH.Dev.C1RouteBTrigCosTaylorRemainder2920

namespace ConnesWeilRH.Dev

theorem routeBSinRightEndpoint_of_mathlibRemainder2925
    (hrem : ‖Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.sin 20
        (Set.Icc 0 ((52554181792962067 : ℝ) / 10 ^ 16)) 0
        ((52554181792962067 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20) :
    (-859 : ℝ) / 1000 <
        Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) ∧
      Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) < (-853 : ℝ) / 1000 := by
  have hp := routeBSinTaylor20_eq_mathlib2919
    (x := (52554181792962067 : ℝ) / 10 ^ 16) (by norm_num)
  rw [hp, abs_le] at hrem
  have ha := routeBTrigTaylor20_right_arithmetic2925
  rcases ha with ⟨hlo, hhi, _, _⟩
  constructor <;> linarith

theorem routeBCosRightEndpoint_of_mathlibRemainder2925
    (hrem : ‖Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.cos 20
        (Set.Icc 0 ((52554181792962067 : ℝ) / 10 ^ 16)) 0
        ((52554181792962067 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20) :
    (514 : ℝ) / 1000 <
        Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) ∧
      Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) < (519 : ℝ) / 1000 := by
  have hp := routeBCosTaylor20_eq_mathlib2922
    (x := (52554181792962067 : ℝ) / 10 ^ 16) (by norm_num)
  rw [hp, abs_le] at hrem
  have ha := routeBTrigTaylor20_right_arithmetic2925
  rcases ha with ⟨_, _, hlo, hhi⟩
  constructor <;> linarith

end ConnesWeilRH.Dev
