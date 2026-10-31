import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825CoeffPhaseAggregateSplit3258

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped BigOperators

noncomputable def record2680Cell2825SharedBumpValueSplit3259 : ℂ :=
  widthBump (storedWidth 8 ^ 2) (record2680Center3212 2825)

theorem record2680_cell2825_shared_family_width_split3259
    (slot : Fin 22) :
    storedWidth (record2680Cell2825FamilyIndexSplit3258 slot) = storedWidth 8 := by
  fin_cases slot <;>
    simp [record2680Cell2825FamilyIndexSplit3258, storedWidth, Fin.ext_iff]

theorem record2680_cell2825_shared_bump_target_eq_split3259 :
    ∑ slot : Fin 22,
        externalFamilyValue2344
          (record2680CorrectionCoefficient (record2680Cell2825FamilyIndexSplit3258 slot))
          (capturedModulations2584 (record2680Cell2825FamilyIndexSplit3258 slot))
          (storedWidth (record2680Cell2825FamilyIndexSplit3258 slot) ^ 2)
          (record2680Center3212 2825) =
      record2680Cell2825SharedBumpValueSplit3259 *
        ∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseValueSplit3258 slot := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot hslot
  rw [externalFamilyValue2344_eq_familyTerm]
  rw [record2680_cell2825_shared_family_width_split3259 slot]
  simp only [record2680Cell2825SharedBumpValueSplit3259,
    record2680Cell2825FamilyCoeffPhaseValueSplit3258,
    Complex.ofReal_mul, mul_assoc]
  ring

end ConnesWeilRH.Dev
