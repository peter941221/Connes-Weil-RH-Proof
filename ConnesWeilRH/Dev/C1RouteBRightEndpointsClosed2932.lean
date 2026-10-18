import ConnesWeilRH.Dev.C1RouteBRightEndpointConsumers2925
import ConnesWeilRH.Dev.C1RouteBTrigTaylorRemainder2919
import ConnesWeilRH.Dev.C1RouteBTrigCosTaylorRemainder2920
import ConnesWeilRH.Dev.C1RouteBEndpointAngles2915

namespace ConnesWeilRH.Dev

theorem routeBSinRightEndpointClosed2932 :
    (-859 : ℝ) / 1000 <
        Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) ∧
      Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) < (-853 : ℝ) / 1000 := by
  have hr := routeBSinTaylorRemainderBound2919
    (x := (52554181792962067 : ℝ) / 10 ^ 16) (by norm_num)
  have hrem : ‖Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.sin 20
        (Set.Icc 0 ((52554181792962067 : ℝ) / 10 ^ 16)) 0
        ((52554181792962067 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20 := by
    calc
      _ ≤ ((52554181792962067 : ℝ) / 10 ^ 16) ^ 21 /
          (Nat.factorial 20 : ℝ) := hr
      _ ≤ ((526 : ℝ) / 100) ^ 21 / (Nat.factorial 20 : ℝ) := by
        gcongr <;> norm_num
      _ < (1 : ℝ) / 10 ^ 20 := routeBLocalTaylorRemainderBudget2915
  exact routeBSinRightEndpoint_of_mathlibRemainder2925 hrem

theorem routeBCosRightEndpointClosed2932 :
    (514 : ℝ) / 1000 <
        Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) ∧
      Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) < (519 : ℝ) / 1000 := by
  have hr := routeBCosTaylorRemainderBound2920
    (x := (52554181792962067 : ℝ) / 10 ^ 16) (by norm_num)
  have hrem : ‖Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.cos 20
        (Set.Icc 0 ((52554181792962067 : ℝ) / 10 ^ 16)) 0
        ((52554181792962067 : ℝ) / 10 ^ 16)‖ ≤ (1 : ℝ) / 10 ^ 20 := by
    calc
      _ ≤ ((52554181792962067 : ℝ) / 10 ^ 16) ^ 21 /
          (Nat.factorial 20 : ℝ) := hr
      _ ≤ ((526 : ℝ) / 100) ^ 21 / (Nat.factorial 20 : ℝ) := by
        gcongr <;> norm_num
      _ < (1 : ℝ) / 10 ^ 20 := routeBLocalTaylorRemainderBudget2915
  exact routeBCosRightEndpoint_of_mathlibRemainder2925 hrem

end ConnesWeilRH.Dev
