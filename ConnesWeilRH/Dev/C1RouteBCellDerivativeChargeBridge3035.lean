import ConnesWeilRH.Dev.C1RouteBCellExactNormBridge3034
import ConnesWeilRH.Dev.C1RouteBCellAllowanceComparison3033

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeBCell_derivative_charge_le_ledger_add_allowance3035
    (i order : ℕ) (hi : i < 8192) {x : ℝ}
    (hx : (routeBSeedCell2809 i).Mem x)
    {norm ledger allowance : ℝ}
    (hrow : 4 * ((2047 : ℝ) / 33554432) * norm ≤ ledger + allowance)
    (hsource : routeBSourceNorm2834 i order ≤ norm) :
    4 * ((2047 : ℝ) / 33554432) *
        ‖iteratedDeriv order Real.smoothTransition x‖ ≤ ledger + allowance := by
  have hnorm := routeBCell_exact_norm_le_sourceNorm3034 i order hi hx
  exact le_trans
    (mul_le_mul_of_nonneg_left (hnorm.trans hsource) (by positivity)) hrow

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
