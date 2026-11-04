import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhysicalTermRect3310_cell0_order2_family4_reHi_le_3333 :
    (ratWeightedPhysicalTermRect3310 2 0 4).reHi ≤ 1 / 10 ^ 14 := by
  rw [ratWeightedPhysicalTermRect3310_cell0_order2_family4_reHi_signed3332]
  norm_num [
    ratWeightedUnitJetRect3310,
    ratWeightedPhaseRect3310,
    ratBumpRect3310,
    ratBumpJetInterval3310,
    ratTailBumpInterval3298,
    ratScaledBumpInterval3298,
    ratBaseInterval3284,
    ratTaylorInterval3283,
    ratTaylorSum3283,
    ratTaylorError3283,
    ratCellWeightInterval3289,
    ratCellWeightArgument3289,
    ratWeightedLambdaRect3310,
    ratScalarRect3310,
    RatRect3276.add,
    RatRect3276.mul,
    RatInterval3276.mul,
    RatInterval3276.powNat,
    ratPhaseRect3279,
    ratPhaseRe3279,
    ratPhaseIm3279,
    ratPhaseError3279,
    record2680PhaseAngleRat3279,
    record2680CenterRat3279,
    storedWidthRat3287,
    ratCoefficientRect3282]

end ConnesWeilRH.Dev
