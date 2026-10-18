import Mathlib.Analysis.Calculus.Taylor
import ConnesWeilRH.Dev.C1RouteBTrigDerivBound2918

namespace ConnesWeilRH.Dev

theorem routeBSinTaylorRemainderBound2919 {x : ℝ} (hx : 0 < x) :
    ‖Real.sin x -
        taylorWithinEval Real.sin 20 (Set.Icc 0 x) 0 x‖ ≤
      x ^ 21 / (Nat.factorial 20 : ℝ) := by
  have hmain :
      ‖Real.sin x - taylorWithinEval Real.sin 20 (Set.Icc 0 x) 0 x‖ ≤
        (1 : ℝ) * (x - 0) ^ (20 + 1) / (Nat.factorial 20 : ℝ) := by
    apply taylor_mean_remainder_bound (f := Real.sin) (a := 0) (b := x)
      (C := (1 : ℝ)) (n := 20) (by exact le_of_lt hx)
    · exact Real.contDiff_sin.contDiffOn
    · exact ⟨by exact le_of_lt hx, le_rfl⟩
    · intro y hy
      rw [Real.iteratedDerivWithin_sin_Icc 21 hx hy]
      exact routeBIteratedDerivSinNorm_le_one2918 21 y
  simpa using hmain

end ConnesWeilRH.Dev
