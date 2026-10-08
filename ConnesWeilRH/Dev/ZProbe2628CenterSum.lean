import ConnesWeilRH.Dev.ZProbe2628Sum

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem centerBlock2628_0 :
    ∑ p ∈ Finset.Ico 0 30, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_0 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_0, Finset.sum_range_succ]
  ring

private theorem centerBlock2628_1 :
    ∑ p ∈ Finset.Ico 30 60, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_1 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_1, Finset.sum_range_succ]
  ring

private theorem centerBlock2628_2 :
    ∑ p ∈ Finset.Ico 60 90, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_2 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_2, Finset.sum_range_succ]
  ring

private theorem centerBlock2628_3 :
    ∑ p ∈ Finset.Ico 90 120, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_3 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_3, Finset.sum_range_succ]
  ring

private theorem centerBlock2628_4 :
    ∑ p ∈ Finset.Ico 120 150, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_4 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_4, Finset.sum_range_succ]
  ring

private theorem centerBlock2628_5 :
    ∑ p ∈ Finset.Ico 150 180, (partitionCenter2628 p : ℝ) =
      (chunkCenters2628_5 : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [partitionCenter2628, chunkCenters2628_5, Finset.sum_range_succ]
  ring

theorem partitionCentersSum2628 :
    ∑ p ∈ Finset.range 180, (partitionCenter2628 p : ℝ) =
      (totalCenters2628 : ℚ) := by
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 150 ≤ 180 by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 120 ≤ 150 by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 90 ≤ 120 by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 60 ≤ 90 by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 30 ≤ 60 by norm_num)]
  rw [← Finset.sum_range_add_sum_Ico (f := fun p => (partitionCenter2628 p : ℝ)) (show 0 ≤ 30 by norm_num)]
  rw [centerBlock2628_0, centerBlock2628_1, centerBlock2628_2,
    centerBlock2628_3, centerBlock2628_4, centerBlock2628_5]
  norm_num [totalCenters2628]
  ring

end ConnesWeilRH.Dev
