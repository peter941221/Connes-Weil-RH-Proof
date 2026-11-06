import ConnesWeilRH.Dev.C1RouteARationalBlock0PhysicalProducer3439

namespace ConnesWeilRH.Dev

theorem record2680_block0_family_ne4_inactive3441
    {index : ℕ} (hindex : index < 256)
    (family : Fin 30) (hfamily : family ≠ 4) :
    ¬ |record2680CenterRat3279 index| < storedWidthRat3287 family ^ 2 := by
  have hcenter_neg : record2680CenterRat3279 index < 0 := by
    dsimp [record2680CenterRat3279]
    have hindex' : (index : ℚ) ≤ 255 := by
      exact_mod_cast (show index ≤ 255 by omega)
    norm_num
    nlinarith
  have habs : (6 : ℚ) ≤ |record2680CenterRat3279 index| := by
    rw [abs_of_neg hcenter_neg]
    have hindex' : (index : ℚ) ≤ 255 := by
      exact_mod_cast (show index ≤ 255 by omega)
    dsimp [record2680CenterRat3279]
    norm_num
    nlinarith
  have hradius : storedWidthRat3287 family ^ 2 < (6 : ℚ) := by
    fin_cases family <;>
      norm_num [storedWidthRat3287, Matrix.cons_val_four] at hfamily ⊢ <;>
      simp_all
  intro hactive
  linarith

theorem record2680_block0_real_family_ne4_zero3441
    {index : ℕ} (hindex : index < 256)
    (family : Fin 30) (hfamily : family ≠ 4) :
    ratCellRealFamilyInterval3298 index family =
      ({lo := 0, hi := 0} : RatInterval3276) := by
  have hactive : ¬ |record2680CenterRat3279 index| <
      storedWidthRat3287 family ^ 2 :=
    record2680_block0_family_ne4_inactive3441 hindex family hfamily
  have hbump : ratCellBumpInterval3298 index family =
      ({lo := 0, hi := 0} : RatInterval3276) := by
    dsimp [ratCellBumpInterval3298]
    rw [if_neg hactive]
  unfold ratCellRealFamilyInterval3298 ratRealFamilyInterval3298
  rw [hbump, ratInterval_zero_mul3298]

theorem record2680_block0_real_sum_eq_family4_3441
    {index : ℕ} (hindex : index < 256) :
    ratCellRealSum3298 index = ratCellRealFamilyInterval3298 index 4 := by
  have hsum_zero (g : Fin 30 → ℚ)
      (hg : ∀ family : Fin 30, family ≠ 4 → g family = 0) :
      ∑ family : Fin 30, g family = g 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 4)]
    have hzero : ∑ family ∈ (Finset.univ : Finset (Fin 30)).erase 4,
        g family = 0 := by
      apply Finset.sum_eq_zero
      intro family hmem
      exact hg family (Finset.mem_erase.mp hmem).1
    rw [hzero, zero_add]
  unfold ratCellRealSum3298 ratRealIntervalSum3298
  congr 1
  · simpa using hsum_zero
      (fun family => (ratCellRealFamilyInterval3298 index family).lo)
      (fun family hfamily => by
        exact congrArg RatInterval3276.lo
          (record2680_block0_real_family_ne4_zero3441 hindex family hfamily))
  · simpa using hsum_zero
      (fun family => (ratCellRealFamilyInterval3298 index family).hi)
      (fun family hfamily => by
        exact congrArg RatInterval3276.hi
          (record2680_block0_real_family_ne4_zero3441 hindex family hfamily))

set_option maxRecDepth 1000000 in
theorem record2680_cell0_weight_hi_le_27_3441 :
    (ratCellWeightInterval3289 0).hi ≤ (27 : ℚ) := by
  norm_num (config := { maxSteps := 2000000000 })
    [ratCellWeightInterval3289, ratCellWeightArgument3289,
    record2680CenterRat3279, RatInterval3276.powNat,
    RatInterval3276.mul, ratTaylorInterval3283, ratTaylorSum3283,
    ratTaylorError3283, Finset.sum_range_succ]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_cell0_family0_real_hi_le_1_100_3441 :
    (ratCellRealFamilyInterval3298 0 0).hi ≤ (1 / 100 : ℚ) := by
  norm_num (config := { maxSteps := 2000000000 })
    [ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
      ratCellBumpInterval3298, ratCoefficientPhaseRealInterval3298,
      ratTailBumpInterval3298, ratBumpT3286, ratBumpNumerator3310,
      ratCoefficientRect3282, storedWidthRat3287,
      record2680CenterRat3279, record2680PhaseAngleRat3279,
      RatInterval3276.mul, RatInterval3276.add, RatInterval3276.sub,
      RatRect3276.mul, RatRect3276.powSq, ratPhaseRect3279,
      Finset.sum_range_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

end ConnesWeilRH.Dev
