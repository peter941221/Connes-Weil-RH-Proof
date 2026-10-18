import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBLocalEndpointAngle_left2915 :
    (52523502177204355 : ℝ) / 10 ^ 16 <
      (107 : ℝ) * Real.pi / 64 ∧
      (107 : ℝ) * Real.pi / 64 < (52523502177204357 : ℝ) / 10 ^ 16 := by
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem routeBLocalEndpointAngle_right2915 :
    (52554181792962067 : ℝ) / 10 ^ 16 <
      (107 : ℝ) * Real.pi / 64 + Real.pi / 1024 ∧
      (107 : ℝ) * Real.pi / 64 + Real.pi / 1024 <
        (52554181792962070 : ℝ) / 10 ^ 16 := by
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

end ConnesWeilRH.Dev
