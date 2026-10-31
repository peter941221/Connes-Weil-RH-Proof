import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell17168Rect3245

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped BigOperators

noncomputable def record2680Cell17168SharedFamilies3247 : Finset (Fin 30) :=
  (Finset.univ : Finset (Fin 30)).filter (fun family => 8 ≤ family.val)

noncomputable def record2680Cell17168PhaseRect3247
    (family : Fin 30) : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient family)).mul
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 17168)) 9)

noncomputable def record2680Cell17168SharedBumpRect3247 : ComplexRect2427 :=
  { reLo := (record2680MiddlePointBumpInterval3231 8).lo
    reHi := (record2680MiddlePointBumpInterval3231 8).hi
    imLo := 0
    imHi := 0 }

noncomputable def record2680Cell17168SharedPhaseRect3247 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell17168PhaseRect3247
    record2680Cell17168SharedFamilies3247

noncomputable def record2680Cell17168SharedBlockRect3247 : ComplexRect2427 :=
  record2680Cell17168SharedBumpRect3247.mul
    record2680Cell17168SharedPhaseRect3247

theorem record2680_cell17168_shared_family_width3247
    {family : Fin 30} (hfamily : family ∈
      record2680Cell17168SharedFamilies3247) :
    storedWidth family = storedWidth 8 := by
  simp [record2680Cell17168SharedFamilies3247] at hfamily
  fin_cases family <;> simp_all [storedWidth, Fin.ext_iff]

theorem record2680_cell17168_shared_bump_rect_mem3247 :
    record2680Cell17168SharedBumpRect3247.Mem
      (widthBump (storedWidth 8 ^ 2)
        (record2680Center3212 17168) : ℂ) := by
  have h := record2680_middle_point_bump_mem3231 (family := (8 : Fin 30))
  exact ⟨h.1, h.2, by simp [record2680Cell17168SharedBumpRect3247],
    by simp [record2680Cell17168SharedBumpRect3247]⟩

theorem record2680_cell17168_phase_rect_mem3247 (family : Fin 30) :
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 17168)) 9).Mem
      (Complex.exp (((capturedModulations2584 family *
        record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled :
      |(capturedModulations2584 family * record2680Center3212 17168) / 512| ≤ 1 := by
    fin_cases family <;>
      norm_num [capturedModulations2584, record2680Center3212,
        record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hphase := complexRectPowSq_mem3218
    (phaseRect_mem3218 hscaled) 9
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hphase
  rw [complex_phase_eq_pow512_3218]
  exact hphase

theorem record2680_cell17168_phase_block_rect_mem3247 :
    record2680Cell17168SharedPhaseRect3247.Mem
      (∑ family ∈ record2680Cell17168SharedFamilies3247,
        record2680CorrectionCoefficient family *
          Complex.exp (((capturedModulations2584 family *
            record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  unfold record2680Cell17168SharedPhaseRect3247
  apply ComplexRect2427.mem_sumFinset
  intro family hfamily
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    (record2680_cell17168_phase_rect_mem3247 family)

theorem record2680_cell17168_shared_block_rect_mem3247 :
    record2680Cell17168SharedBlockRect3247.Mem
      ((widthBump (storedWidth 8 ^ 2) (record2680Center3212 17168) : ℂ) *
        ∑ family ∈ record2680Cell17168SharedFamilies3247,
          record2680CorrectionCoefficient family *
            Complex.exp (((capturedModulations2584 family *
              record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul
    record2680_cell17168_shared_bump_rect_mem3247
    record2680_cell17168_phase_block_rect_mem3247

theorem record2680_cell17168_shared_block_target_eq3247 :
    (widthBump (storedWidth 8 ^ 2) (record2680Center3212 17168) : ℂ) *
        ∑ family ∈ record2680Cell17168SharedFamilies3247,
          record2680CorrectionCoefficient family *
            Complex.exp (((capturedModulations2584 family *
              record2680Center3212 17168 : ℝ) : ℂ) * Complex.I) =
      ∑ family ∈ record2680Cell17168SharedFamilies3247,
        externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2)
          (record2680Center3212 17168) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro family hfamily
  rw [externalFamilyValue2344_eq_familyTerm]
  rw [record2680_cell17168_shared_family_width3247 hfamily]
  simp only [Complex.ofReal_mul, mul_assoc]
  ring

end ConnesWeilRH.Dev
