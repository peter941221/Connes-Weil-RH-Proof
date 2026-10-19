import Mathlib

namespace ConnesWeilRH.Dev

def routeBSeedRowAllowance3038 : Fin 8192 → ℝ := fun _ => (1 : ℝ) / 10 ^ 20

theorem routeBSeedRowAllowance_sum3038 :
    (∑ i : Fin 8192, routeBSeedRowAllowance3038 i) = (8192 : ℝ) / 10 ^ 20 := by
  simp [routeBSeedRowAllowance3038]

theorem routeBSeedRowAllowance_d4_margin3038 :
    (8192 : ℝ) / 10 ^ 20 < 1500 - 1400 := by
  norm_num

theorem routeBSeedRowAllowance_d7_margin3038 :
    (8192 : ℝ) / 10 ^ 20 < 2000000000 - 1999999000 := by
  norm_num

end ConnesWeilRH.Dev
