import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3347

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3366_cell0_order0_family4_hi_le :
    (ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).hi ≤ 1 / 10 ^ 40 := by
  rw [signed_bump_endpoint3347_cell0_order0_family4_hi_eq]
  rw [ratBaseInterval3284_powNat_hi_eq_pow3346]
  norm_num (config := { maxSteps := 2000000000 }) [
    ratBaseInterval3284,
    ratTaylorInterval3283,
    ratTaylorSum3283,
    ratTaylorError3283,
    storedWidthRat3287,
    record2680CenterRat3279,
    ratBumpNumerator3310,
    Matrix.cons_val_four]

end ConnesWeilRH.Dev