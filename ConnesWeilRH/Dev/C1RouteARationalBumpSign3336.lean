import ConnesWeilRH.Dev.C1RouteARationalBumpSelector3335

namespace ConnesWeilRH.Dev

theorem signed_bump_factor3336_cell0_order2_family4_nonneg :
    let radius := storedWidthRat3287 4 ^ 2
    let position := |record2680CenterRat3279 0|
    let u := position / radius
    0 ≤
      (1 - u ^ 2)⁻¹ ^ (2 * 2) *
        ratBumpNumerator3310 2 u / radius ^ 2 := by
  norm_num [ratBumpNumerator3310, record2680CenterRat3279,
    storedWidthRat3287, Matrix.cons_val_four]

theorem ratInterval_mul_lo_nonneg3336
    {a b : RatInterval3276}
    (haLo : 0 ≤ a.lo) (haHi : 0 ≤ a.hi)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi) :
    0 ≤ (RatInterval3276.mul a b).lo := by
  unfold RatInterval3276.mul
  apply le_min
  · apply le_min <;> positivity
  · apply le_min <;> positivity

end ConnesWeilRH.Dev
