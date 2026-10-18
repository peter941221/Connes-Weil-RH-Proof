import ConnesWeilRH.Dev.C1RouteBTrigTaylor2916
import ConnesWeilRH.Dev.C1RouteBTrigTaylorRemainder2919
import ConnesWeilRH.Dev.C1RouteBAngleShift2926

namespace ConnesWeilRH.Dev

theorem routeBSinLeftEndpointClosed2930 :
    (-867 : ℝ) / 1000 <
        Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) < (-864 : ℝ) / 1000 := by
  have hr := routeBSinTaylorRemainderBound2919
    (x := (52523502177204355 : ℝ) / 10 ^ 16) (by norm_num)
  have hrem : ‖Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.sin 20
        (Set.Icc 0 ((52523502177204355 : ℝ) / 10 ^ 16)) 0
        ((52523502177204355 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20 := by
    calc
      _ ≤ ((52523502177204355 : ℝ) / 10 ^ 16) ^ 21 /
          (Nat.factorial 20 : ℝ) := hr
      _ ≤ ((526 : ℝ) / 100) ^ 21 / (Nat.factorial 20 : ℝ) := by
        gcongr <;> norm_num
      _ < (1 : ℝ) / 10 ^ 20 := routeBLocalTaylorRemainderBudget2915
  exact routeBSinEndpoint_of_mathlibRemainder2923 (by positivity) hrem

end ConnesWeilRH.Dev
