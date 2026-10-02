import ConnesWeilRH.Dev.C1RouteAOwnerExpBridge2501

/-! Record 2506: automatic integer selection for the owner exponential split.

The split theorem does not need a stored integer table: for every nonnegative
exponent, `Nat.floor` supplies the required integer and the standard floor
lemmas supply the one-unit remainder interval.  The cell-specific hcell
inequality and its numerical margin remain separate obligations.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope

theorem ownerExpSplitUpper_auto2506
    (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤
      expNegOneUpper2498 ^ (⌊x⌋₊ : ℕ) *
        (expTaylor20 (x - (⌊x⌋₊ : ℕ)) + expTaylor20Error) := by
  apply exp_neg_nat_interval_upper2498 x (⌊x⌋₊ : ℕ)
  · exact Nat.floor_le hx
  · exact (Nat.lt_floor_add_one x).le

theorem ownerCellExpSplitUpper_auto2506
    {a : ℝ} (hx : 0 ≤ 30 / (1 - a ^ 2)) :
    Real.exp (-(30 / (1 - a ^ 2))) ≤
      expNegOneUpper2498 ^
          (⌊30 / (1 - a ^ 2)⌋₊ : ℕ) *
        (expTaylor20
            (30 / (1 - a ^ 2) - (⌊30 / (1 - a ^ 2)⌋₊ : ℕ)) +
          expTaylor20Error) := by
  exact ownerExpSplitUpper_auto2506 (30 / (1 - a ^ 2)) hx

theorem ownerCellExpSplitUpper_auto_of_abs_lt_one2506
    {a : ℝ} (ha : |a| < 1) :
    Real.exp (-(30 / (1 - a ^ 2))) ≤
      expNegOneUpper2498 ^
          (⌊30 / (1 - a ^ 2)⌋₊ : ℕ) *
        (expTaylor20
            (30 / (1 - a ^ 2) - (⌊30 / (1 - a ^ 2)⌋₊ : ℕ)) +
          expTaylor20Error) := by
  have ha' : -1 < a ∧ a < 1 := (abs_lt.mp ha)
  have hleft : 0 ≤ 1 - a := by linarith [ha'.2]
  have hright : 0 ≤ 1 + a := by linarith [ha'.1]
  have hprod : 0 ≤ (1 - a) * (1 + a) := mul_nonneg hleft hright
  have hden : 0 < 1 - a ^ 2 := by nlinarith [hprod]
  apply ownerCellExpSplitUpper_auto2506
  exact (div_nonneg (by norm_num) hden.le)

end ConnesWeilRH.Dev
