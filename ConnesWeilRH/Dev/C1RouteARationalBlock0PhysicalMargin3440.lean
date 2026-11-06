import ConnesWeilRH.Dev.C1RouteARationalBlock0PhysicalProducer3439
import ConnesWeilRH.Dev.C1RouteARationalCorrectedManifestMargin3438

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def record2680FormalUniformSixthUpper3440 : ℝ :=
  (949880889674242404871827673187893888216315230823 : ℝ) /
    40564819207303340847894502572032

noncomputable def record2680Block0PhysicalTaylorUpper3440 : ℝ :=
  Finset.sum (Finset.range 256)
    (record2680CellUpper3209 record2680Grid3212
      ratCellValueUpperTight3298 record2680RationalSecondUpper3439
      record2680RationalFourthUpper3439
      (fun _ => record2680FormalUniformSixthUpper3440))

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem record2680Block0PhysicalTaylorUpper3440_le_manifest :
    record2680Block0PhysicalTaylorUpper3440 ≤
      (routeACorrectedSignedBlockUpper3438 0 : ℝ) := by
  norm_num [record2680Block0PhysicalTaylorUpper3440,
    record2680CellUpper3209, record2680Grid3212,
    record2680RationalSecondUpper3439, record2680RationalFourthUpper3439,
    record2680FormalUniformSixthUpper3440,
    ratWeightedPhysicalRect3310, ratWeightedPhysicalTermRect3310,
    ratWeightedUnitJetSumRect3310, ratWeightedUnitJetRect3310,
    ratWeightedPhaseRect3310, ratBumpRect3310,
    ratBumpJetInterval3310, ratWeightedLambdaRect3310,
    ratRectPowNat3310, routeACorrectedSignedBlockUpper3438,
    routeACorrectedSignedBlockUpper3309, routeASignedJetRectBlockDelta3436,
    ratCellValueUpperTight3298, ratCellRealSum3298,
    ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
    ratCellBumpInterval3298, ratRealIntervalSum3298,
    Finset.sum_range_succ, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]


end ConnesWeilRH.Dev
