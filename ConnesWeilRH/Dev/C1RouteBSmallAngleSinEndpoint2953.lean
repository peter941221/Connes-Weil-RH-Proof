import ConnesWeilRH.Dev.C1RouteBSmallAngleTaylorPoly2952
import ConnesWeilRH.Dev.C1RouteBTrigTaylorRemainder2919
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBSmallAngleSinEndpoint2953 :
    (1704146 : ℝ) / 10 ^ 7 <
        Real.sin ((1712505045774558 : ℝ) / 10 ^ 16) ∧
      Real.sin ((1712505045774558 : ℝ) / 10 ^ 16) <
        (1704148 : ℝ) / 10 ^ 7 := by
  let u : ℝ := (1712505045774558 : ℝ) / 10 ^ 16
  have hu : 0 < u := by norm_num [u]
  have hrem := routeBSinTaylorRemainderBound2919 hu
  rw [routeBSmallAngleTaylorPoly2952] at hrem
  rw [Real.norm_eq_abs, abs_le] at hrem
  constructor <;>
    norm_num [u, Finset.sum_range_succ, Nat.factorial] at hrem ⊢ <;>
    linarith

end ConnesWeilRH.Dev
