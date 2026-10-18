import ConnesWeilRH.Dev.C1RouteBSmallAngleTaylorPoly2952
import ConnesWeilRH.Dev.C1RouteBSmallAngleTaylorPoly2958
import ConnesWeilRH.Dev.C1RouteBTrigTaylorRemainder2919
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBSmallAngleSinEndpoint2956 :
    (1707354 : ℝ) / 10 ^ 7 <
        Real.sin ((1715760948859532 : ℝ) / 10 ^ 16) ∧
      Real.sin ((1715760948859532 : ℝ) / 10 ^ 16) <
        (1707357 : ℝ) / 10 ^ 7 := by
  let u : ℝ := (1715760948859532 : ℝ) / 10 ^ 16
  have hu : 0 < u := by norm_num [u]
  have hrem := routeBSinTaylorRemainderBound2919 hu
  rw [routeBSmallAngleTaylorPoly2958] at hrem
  rw [Real.norm_eq_abs, abs_le] at hrem
  constructor <;>
    norm_num [u, Finset.sum_range_succ, Nat.factorial] at hrem ⊢ <;>
    linarith

end ConnesWeilRH.Dev






