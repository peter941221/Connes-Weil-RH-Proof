import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBExpOneLtThree2943 : Real.exp 1 < 3 := by
  exact Real.exp_one_lt_d9.trans (by norm_num)

def routeBExpTaylor20 (x : ℝ) : ℝ :=
  ∑ j in Finset.range 21, x ^ j / (Nat.factorial j : ℝ)

theorem routeBExpTaylor20_eq_mathlib2943 {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.exp 20 (Set.Icc 0 x) 0 x = routeBExpTaylor20 x := by
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_exp_Icc _ hx]
  simp [routeBExpTaylor20, Real.iteratedDeriv_exp, smul_eq_mul, div_eq_mul_inv]

theorem routeBExpTaylor20_upper_at_40_over_3992943 :
    routeBExpTaylor20 ((40 : ℝ) / 399) +
        3 * ((40 : ℝ) / 399) ^ 21 / (Nat.factorial 20 : ℝ) <
      (111 : ℝ) / 100 := by
  norm_num [routeBExpTaylor20, Finset.sum_range_succ, Nat.factorial]

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
