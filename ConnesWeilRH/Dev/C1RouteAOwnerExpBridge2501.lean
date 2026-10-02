import ConnesWeilRH.Dev.C1RouteAExpSplit2498
import ConnesWeilRH.Dev.C1RouteAOwnerCellLowerRatio2501

/-! Record 2504: the owner-cell consumer bridge for the formal split.

The table layer will later provide the rational `n` and interval checks.  This
lemma is deliberately parameterized: it does not treat stored JSON numbers as
proofs and it does not assert the hcell/table inequality.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope

theorem ownerCellExpSplitUpper2501
    (a : ℝ) (n : ℕ)
    (hn0 : (n : ℝ) ≤ 30 / (1 - a ^ 2))
    (hn1 : 30 / (1 - a ^ 2) ≤ (n : ℝ) + 1) :
    Real.exp (-(30 / (1 - a ^ 2))) ≤
      expNegOneUpper2498 ^ n *
        (expTaylor20 (30 / (1 - a ^ 2) - (n : ℝ)) + expTaylor20Error) := by
  exact exp_neg_nat_interval_upper2498
    (30 / (1 - a ^ 2)) n hn0 hn1

theorem ownerCellExpSplitUpper_of_lowerRatio2501
    {radius step : ℝ} {index : ℕ} (i : Fin 30) (n : ℕ)
    (hn0 : (n : ℝ) ≤
      30 / (1 - (ownerCellLowerRatio2501 radius step index i) ^ 2))
    (hn1 : 30 / (1 - (ownerCellLowerRatio2501 radius step index i) ^ 2) ≤
      (n : ℝ) + 1) :
    Real.exp (-(30 /
      (1 - (ownerCellLowerRatio2501 radius step index i) ^ 2))) ≤
      expNegOneUpper2498 ^ n *
        (expTaylor20
          (30 / (1 - (ownerCellLowerRatio2501 radius step index i) ^ 2) -
            (n : ℝ)) + expTaylor20Error) := by
  exact ownerCellExpSplitUpper2501
    (ownerCellLowerRatio2501 radius step index i) n hn0 hn1

end ConnesWeilRH.Dev
