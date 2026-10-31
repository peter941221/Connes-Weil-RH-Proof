import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCorrelatedTaxiMiddlePoint3236

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168BumpRect3245
    (family : Fin 30) : ComplexRect2427 :=
  { reLo := (record2680MiddlePointBumpInterval3231 family).lo
    reHi := (record2680MiddlePointBumpInterval3231 family).hi
    imLo := 0
    imHi := 0 }

noncomputable def record2680Cell17168FamilyRect3245
    (family : Fin 30) : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient family)).mul
    (record2680Cell17168BumpRect3245 family) |>.mul
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 17168)) 9)

noncomputable def record2680Cell17168AggregateRect3245 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell17168FamilyRect3245 Finset.univ

theorem record2680_cell17168_bump_rect_mem3245 (family : Fin 30) :
    (record2680Cell17168BumpRect3245 family).Mem
      (widthBump (storedWidth family ^ 2)
        (record2680Center3212 17168) : ℂ) := by
  have h := record2680_middle_point_bump_mem3231 (family := family)
  exact ⟨h.1, h.2, by simp [record2680Cell17168BumpRect3245],
    by simp [record2680Cell17168BumpRect3245]⟩

theorem record2680_cell17168_phase_scaled5123245
    {family : Fin 30} :
    |(capturedModulations2584 family * record2680Center3212 17168) / 512| ≤ 1 := by
  fin_cases family <;>
    norm_num [capturedModulations2584, record2680Center3212,
      record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
      Matrix.cons_val_four, Fin.ext_iff]

theorem record2680_cell17168_phase_rect_mem3245 (family : Fin 30) :
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 17168)) 9).Mem
      (Complex.exp (((capturedModulations2584 family *
        record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell17168_phase_scaled5123245
    (family := family)
  have hphase := complexRectPowSq_mem3218
    (phaseRect_mem3218 hscaled) 9
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hphase
  rw [complex_phase_eq_pow512_3218]
  exact hphase

theorem record2680_cell17168_family_rect_mem3245 (family : Fin 30) :
    (record2680Cell17168FamilyRect3245 family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 17168)) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul
      (ComplexRect2427.point_mem _)
      (record2680_cell17168_bump_rect_mem3245 family))
    (record2680_cell17168_phase_rect_mem3245 family)

theorem record2680_cell17168_aggregate_rect_mem3245 :
    record2680Cell17168AggregateRect3245.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)) := by
  unfold record2680Cell17168AggregateRect3245
  apply ComplexRect2427.mem_sumFinset
  intro family _
  exact record2680_cell17168_family_rect_mem3245 family

theorem record2680_cell17168_unweighted_rect_value_upper3245 :
    (externalPhysical2344 record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 17168)).re ≤
      record2680Cell17168AggregateRect3245.reHi := by
  exact record2680_cell17168_aggregate_rect_mem3245.2.1

end ConnesWeilRH.Dev
