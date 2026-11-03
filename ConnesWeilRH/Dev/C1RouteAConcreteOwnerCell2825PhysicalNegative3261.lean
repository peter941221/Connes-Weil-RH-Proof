import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedBumpCell2825Split3259

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped BigOperators

theorem record2680_cell2825_shared_bump_zero3261 :
    record2680Cell2825SharedBumpValueSplit3259 = 0 := by
  change (widthBump (storedWidth 8 ^ 2) (record2680Center3212 2825) : ℂ) = 0
  rw [widthBump]
  have houtside :
      ¬ |record2680Center3212 2825| < storedWidth 8 ^ 2 := by
    have hwidth : storedWidth (8 : Fin 30) =
        (3963167672086037 / 2251799813685248 : ℝ) := by
      norm_num [storedWidth, Matrix.cons_val_8, Fin.ext_iff]
    rw [hwidth]
    norm_num [record2680Center3212, record2680Grid3212,
      diagnosticRadius3201]
  simp [if_neg houtside]

theorem record2680_cell2825_physical_block_zero3261 :
    (
      ∑ slot : Fin 22,
        externalFamilyValue2344
          (record2680CorrectionCoefficient (record2680Cell2825FamilyIndexSplit3258 slot))
          (capturedModulations2584 (record2680Cell2825FamilyIndexSplit3258 slot))
          (storedWidth (record2680Cell2825FamilyIndexSplit3258 slot) ^ 2)
          (record2680Center3212 2825)
    ).re = 0 := by
  rw [record2680_cell2825_shared_bump_target_eq_split3259]
  rw [record2680_cell2825_shared_bump_zero3261]
  simp

theorem record2680_cell2825_physical_block_zero_eq3261 :
    ∑ slot : Fin 22,
        externalFamilyValue2344
          (record2680CorrectionCoefficient (record2680Cell2825FamilyIndexSplit3258 slot))
          (capturedModulations2584 (record2680Cell2825FamilyIndexSplit3258 slot))
          (storedWidth (record2680Cell2825FamilyIndexSplit3258 slot) ^ 2)
          (record2680Center3212 2825) = 0 := by
  rw [record2680_cell2825_shared_bump_target_eq_split3259]
  rw [record2680_cell2825_shared_bump_zero3261]
  simp

end ConnesWeilRH.Dev
