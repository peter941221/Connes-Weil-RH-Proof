import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ConnesWeilRH.Dev

theorem routeBExpOneLtThree2943 : Real.exp 1 < 3 := by
  exact Real.exp_one_lt_d9.trans (by norm_num)

theorem routeBExpTaylorRemainderBound2943 {x : ℝ} (hx : 0 ≤ x) :
    ‖Real.exp x -
        taylorWithinEval Real.exp 20 (Set.Icc 0 x) 0 x‖ ≤
      Real.exp 1 * x ^ 21 / (Nat.factorial 20 : ℝ) := by
  apply taylor_mean_remainder_bound (f := Real.exp) (a := 0) (b := x)
    (C := Real.exp 1) (n := 20) (by exact hx)
  · exact Real.contDiff_exp.contDiffOn
  · exact ⟨by exact hx, le_rfl⟩
  · intro y hy
    rw [Real.iteratedDerivWithin_eq_iteratedDeriv (by exact uniqueDiffOn_Icc hx.lt_of_ne)
      Real.contDiff_exp.contDiffAt hy]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    exact Real.exp_le_exp.mpr hy.2

end ConnesWeilRH.Dev
