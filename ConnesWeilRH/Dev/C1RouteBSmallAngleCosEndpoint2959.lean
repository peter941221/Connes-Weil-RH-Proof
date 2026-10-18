import ConnesWeilRH.Dev.C1RouteBTrigIteratedDerivZero2951
import ConnesWeilRH.Dev.C1RouteBTrigCosTaylorRemainder2920
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

noncomputable section
open scoped BigOperators

theorem routeBSmallAngleCosEndpoint2959 :
    (9853167 : ℝ) / 10 ^ 7 <
        Real.cos ((1715760948859532 : ℝ) / 10 ^ 16) ∧
      Real.cos ((1715760948859532 : ℝ) / 10 ^ 16) <
        (9853170 : ℝ) / 10 ^ 7 := by
  let u : ℝ := (1715760948859532 : ℝ) / 10 ^ 16
  have hu : 0 < u := by norm_num [u]
  have hpoly :
      taylorWithinEval Real.cos 20 (Set.Icc 0 u) 0 u =
        ∑ j ∈ Finset.range 11,
          (-1 : ℝ) ^ j * u ^ (2 * j) /
            (Nat.factorial (2 * j) : ℝ) := by
    rw [taylor_within_apply]
    simp_rw [Real.iteratedDerivWithin_cos_Icc
      (a := (0 : ℝ)) (b := u) (x := (0 : ℝ)) _ hu (by norm_num [u])]
    norm_num [Finset.sum_range_succ, routeBCosIteratedDerivEvenZero2951,
      routeBCosIteratedDerivOddZero2951, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hrem := routeBCosTaylorRemainderBound2920 hu
  rw [hpoly] at hrem
  rw [Real.norm_eq_abs, abs_le] at hrem
  constructor <;> norm_num [u, Finset.sum_range_succ, Nat.factorial] at hrem ⊢ <;>
    linarith

end
end ConnesWeilRH.Dev

