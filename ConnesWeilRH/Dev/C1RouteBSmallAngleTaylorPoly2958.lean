import ConnesWeilRH.Dev.C1RouteBTrigIteratedDerivZero2951
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

noncomputable section
open scoped BigOperators

theorem routeBSmallAngleTaylorPoly2958 :
    taylorWithinEval Real.sin 20
        (Set.Icc 0 ((1715760948859532 : ℝ) / 10 ^ 16)) 0
        ((1715760948859532 : ℝ) / 10 ^ 16) =
      ∑ j ∈ Finset.range 10,
        (-1 : ℝ) ^ j * ((1715760948859532 : ℝ) / 10 ^ 16) ^ (2 * j + 1) /
          (Nat.factorial (2 * j + 1) : ℝ) := by
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_sin_Icc
    (a := (0 : ℝ)) (b := (1715760948859532 : ℝ) / 10 ^ 16)
    (x := (0 : ℝ)) _ (by norm_num) (by norm_num)]
  norm_num [Finset.sum_range_succ, routeBSinIteratedDerivEvenZero2951,
    routeBSinIteratedDerivOddZero2951, smul_eq_mul, div_eq_mul_inv, mul_comm]

end
end ConnesWeilRH.Dev

