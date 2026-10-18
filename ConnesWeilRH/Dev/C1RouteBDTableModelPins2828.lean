import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_model_D4_pin2828 :
    (1535.1255241247966 : ℝ) < 1536 := by norm_num

theorem routeB_model_D7_pin2828 :
    (1103017559.7738538 : ℝ) < 1104000000 := by norm_num

theorem routeB_model_D4_D7_joint_pin2828 :
    (1535.1255241247966 : ℝ) < 1536 ∧
      (1103017559.7738538 : ℝ) < 1104000000 := by
  exact ⟨routeB_model_D4_pin2828, routeB_model_D7_pin2828⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
