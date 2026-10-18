import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

def routeBSinTaylor20 (x : ℝ) : ℝ :=
  ∑ j in Finset.range 21, (-1 : ℝ) ^ j * x ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)

def routeBCosTaylor20 (x : ℝ) : ℝ :=
  ∑ j in Finset.range 21, (-1 : ℝ) ^ j * x ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)

theorem routeBTrigTaylor20_left_arithmetic2916 :
    let x : ℝ := (52523502177204355 : ℝ) / 10 ^ 16
    (-866 : ℝ) / 1000 < routeBSinTaylor20 x ∧
      routeBSinTaylor20 x < (-865 : ℝ) / 1000 ∧
      (514 : ℝ) / 1000 < routeBCosTaylor20 x ∧
      routeBCosTaylor20 x < (515 : ℝ) / 1000 := by
  norm_num [routeBSinTaylor20, routeBCosTaylor20]

end ConnesWeilRH.Dev
