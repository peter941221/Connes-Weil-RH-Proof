import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3380

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint_cell1_order2_family4_hi_le3423 :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).hi ≤ 1 / 10 ^ 18 := by
  rw [signed_bump_endpoint3380_cell1_order2_family4_hi_eq]
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
