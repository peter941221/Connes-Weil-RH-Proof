import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell17168Support3262

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped BigOperators

noncomputable def record2680Cell17168Block10to14FamilyIndex3263
    (slot : Fin 5) : Fin 30 :=
  ⟨slot.val + 10, by omega⟩

noncomputable def record2680Cell17168Block10to14PhaseValue3263
    (slot : Fin 5) : ℂ :=
  record2680CorrectionCoefficient
      (record2680Cell17168Block10to14FamilyIndex3263 slot) *
    Complex.exp (((capturedModulations2584
      (record2680Cell17168Block10to14FamilyIndex3263 slot) *
      record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)

noncomputable def record2680Cell17168Weight3263 : ℂ :=
  (Real.exp ((-1 / 2 : ℝ) * record2680Center3212 17168) : ℝ)

noncomputable def record2680Cell17168Block10to14Bump3263 : ℂ :=
  (widthBump (storedWidth 10 ^ 2) (record2680Center3212 17168) : ℝ)

theorem record2680_cell17168_block10to14_shared_width3263
    (slot : Fin 5) :
    storedWidth (record2680Cell17168Block10to14FamilyIndex3263 slot) =
      storedWidth 10 := by
  fin_cases slot <;>
    simp [record2680Cell17168Block10to14FamilyIndex3263, storedWidth,
      Fin.ext_iff]

theorem record2680_cell17168_block10to14_weighted_shared_target_eq3263 :
    ∑ slot : Fin 5,
        record2680Cell17168Weight3263 *
          externalFamilyValue2344
            (record2680CorrectionCoefficient
              (record2680Cell17168Block10to14FamilyIndex3263 slot))
            (capturedModulations2584
              (record2680Cell17168Block10to14FamilyIndex3263 slot))
            (storedWidth
              (record2680Cell17168Block10to14FamilyIndex3263 slot) ^ 2)
            (record2680Center3212 17168) =
      (record2680Cell17168Weight3263 *
        record2680Cell17168Block10to14Bump3263) *
        ∑ slot : Fin 5, record2680Cell17168Block10to14PhaseValue3263 slot := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot hslot
  rw [externalFamilyValue2344_eq_familyTerm]
  rw [record2680_cell17168_block10to14_shared_width3263 slot]
  simp only [record2680Cell17168Weight3263,
    record2680Cell17168Block10to14Bump3263,
    record2680Cell17168Block10to14PhaseValue3263,
    Complex.ofReal_mul, mul_assoc]
  ring

end ConnesWeilRH.Dev
