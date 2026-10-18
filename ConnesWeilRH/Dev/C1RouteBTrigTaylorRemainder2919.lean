import Mathlib.Analysis.Calculus.Taylor
import ConnesWeilRH.Dev.C1RouteBTrigDerivBound2918

namespace ConnesWeilRH.Dev

theorem routeBSinTaylorRemainderBound2919 {x : ℝ} (hx : 0 ≤ x) :
    ‖Real.sin x -
        taylorWithinEval Real.sin 20 (Set.Icc 0 x) 0 x‖ ≤
      x ^ 21 / (Nat.factorial 20 : ℝ) := by
  apply taylor_mean_remainder_bound (f := Real.sin) (a := 0) (b := x)
    (C := (1 : ℝ)) (n := 20) (by exact hx)
  · exact Real.contDiff_sin.contDiffOn
  · exact ⟨by exact hx, le_rfl⟩
  · intro y hy
    rw [Real.iteratedDerivWithin_sin_Icc 21 (by exact hx.lt_of_ne)]
    exact routeBIteratedDerivSinNorm_le_one2918 21 y

end ConnesWeilRH.Dev
