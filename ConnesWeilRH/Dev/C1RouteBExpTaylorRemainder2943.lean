import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

noncomputable section

open scoped BigOperators

theorem routeBExpOneLtThree2943 : Real.exp 1 < 3 := by
  exact lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)

def routeBExpTaylor20 (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 21, x ^ j / (Nat.factorial j : ℝ)

theorem routeBExpTaylor20_eq_mathlib2943 {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.exp 20 (Set.Icc 0 x) 0 x = routeBExpTaylor20 x := by
  have hderiv (n : ℕ) :
      iteratedDerivWithin n Real.exp (Set.Icc 0 x) 0 = Real.exp 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      Real.contDiff_exp.contDiffAt (by constructor <;> positivity)]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  rw [taylor_within_apply]
  simp only [hderiv]
  simp [routeBExpTaylor20, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem routeBExpTaylorRemainderBound2943 {x : ℝ} (hx : 0 < x)
    (hx1 : x ≤ 1) :
    ‖Real.exp x -
        taylorWithinEval Real.exp 20 (Set.Icc 0 x) 0 x‖ ≤
      Real.exp 1 * x ^ 21 / (Nat.factorial 20 : ℝ) := by
  have hmain :
        ‖Real.exp x -
            taylorWithinEval Real.exp 20 (Set.Icc 0 x) 0 x‖ ≤
          Real.exp 1 * (x - 0) ^ (20 + 1) / (Nat.factorial 20 : ℝ) := by
      apply taylor_mean_remainder_bound (f := Real.exp) (a := 0) (b := x)
        (C := Real.exp 1) (n := 20) (by exact le_of_lt hx)
      · exact Real.contDiff_exp.contDiffOn
      · exact ⟨le_of_lt hx, le_rfl⟩
      · intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
          Real.contDiff_exp.contDiffAt hy]
        rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hy.2.trans hx1)
  simpa using hmain

theorem routeBExpTaylor20_upper_at_40_over_3992943 :
    routeBExpTaylor20 ((40 : ℝ) / 399) +
        3 * ((40 : ℝ) / 399) ^ 21 / (Nat.factorial 20 : ℝ) <
      (111 : ℝ) / 100 := by
  norm_num [routeBExpTaylor20, Finset.sum_range_succ, Nat.factorial]

theorem routeBExpAtNormBound2943 :
    Real.exp ((40 : ℝ) / 399) < (111 : ℝ) / 100 := by
  have hrem := routeBExpTaylorRemainderBound2943 (x := (40 : ℝ) / 399)
    (by norm_num) (by norm_num)
  rw [routeBExpTaylor20_eq_mathlib2943 (by norm_num)] at hrem
  rw [Real.norm_eq_abs] at hrem
  have h1 : Real.exp (1 : ℝ) ≤ 3 := routeBExpOneLtThree2943.le
  have hbound :
      |Real.exp ((40 : ℝ) / 399) - routeBExpTaylor20 ((40 : ℝ) / 399)| ≤
        3 * ((40 : ℝ) / 399) ^ 21 / (Nat.factorial 20 : ℝ) := by
    calc
      |Real.exp ((40 : ℝ) / 399) - routeBExpTaylor20 ((40 : ℝ) / 399)| ≤
          Real.exp 1 * ((40 : ℝ) / 399) ^ 21 / (Nat.factorial 20 : ℝ) := hrem
      _ ≤ 3 * ((40 : ℝ) / 399) ^ 21 / (Nat.factorial 20 : ℝ) := by
        gcongr
  rw [abs_le] at hbound
  have hupper := routeBExpTaylor20_upper_at_40_over_3992943
  linarith

end
end ConnesWeilRH.Dev
