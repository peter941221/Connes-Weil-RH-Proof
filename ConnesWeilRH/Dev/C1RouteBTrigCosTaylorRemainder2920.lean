import Mathlib.Analysis.Calculus.Taylor
import ConnesWeilRH.Dev.C1RouteBTrigDerivBound2918

namespace ConnesWeilRH.Dev

theorem routeBCosTaylorRemainderBound2920 {x : ℝ} (hx : 0 ≤ x) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 20 (Set.Icc 0 x) 0 x‖ ≤
      x ^ 21 / (Nat.factorial 20 : ℝ) := by
  apply taylor_mean_remainder_bound (f := Real.cos) (a := 0) (b := x)
    (C := (1 : ℝ)) (n := 20) (by exact hx)
  · exact Real.contDiff_cos.contDiffOn
  · exact ⟨by exact hx, le_rfl⟩
  · intro y hy
    rw [Real.iteratedDerivWithin_cos_Icc 21 (by exact hx.lt_of_ne)]
    exact routeBIteratedDerivCosNorm_le_one2918 21 y

end ConnesWeilRH.Dev
