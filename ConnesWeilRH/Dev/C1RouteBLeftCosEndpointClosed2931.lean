import ConnesWeilRH.Dev.C1RouteBCosEndpointConsumer2924
import ConnesWeilRH.Dev.C1RouteBTrigCosTaylorRemainder2920
import ConnesWeilRH.Dev.C1RouteBEndpointAngles2915

namespace ConnesWeilRH.Dev

theorem routeBCosLeftEndpointClosed2931 :
    (513 : ℝ) / 1000 <
        Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) < (516 : ℝ) / 1000 := by
  have hr := routeBCosTaylorRemainderBound2920
    (x := (52523502177204355 : ℝ) / 10 ^ 16) (by norm_num)
  have hrem : ‖Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.cos 20
        (Set.Icc 0 ((52523502177204355 : ℝ) / 10 ^ 16)) 0
        ((52523502177204355 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20 := by
    calc
      _ ≤ ((52523502177204355 : ℝ) / 10 ^ 16) ^ 21 /
          (Nat.factorial 20 : ℝ) := hr
      _ ≤ ((526 : ℝ) / 100) ^ 21 / (Nat.factorial 20 : ℝ) := by
        gcongr <;> norm_num
      _ < (1 : ℝ) / 10 ^ 20 := routeBLocalTaylorRemainderBudget2915
  exact routeBCosEndpoint_of_mathlibRemainder2924 hrem

end ConnesWeilRH.Dev
