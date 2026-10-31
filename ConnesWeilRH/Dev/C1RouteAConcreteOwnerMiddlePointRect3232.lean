import ConnesWeilRH.Dev.C1RouteAConcreteOwnerMiddlePoint3231

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680MiddlePointBumpRect3232
    (family : Fin 30) : ComplexRect2427 :=
  { reLo := (record2680MiddlePointBumpInterval3231 family).lo
    reHi := (record2680MiddlePointBumpInterval3231 family).hi
    imLo := 0
    imHi := 0 }

noncomputable def record2680MiddlePointFamilyRect3232
    (family : Fin 30) : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient family)).mul
    (record2680MiddlePointBumpRect3232 family)
  |>.mul (complexRectPowSq3218
    (phaseRect3218
      (capturedModulations2584 family * record2680Center3212 17168)) 9)

theorem record2680_middle_point_phase_mem3232 {family : Fin 30} :
    (complexRectPowSq3218
      (phaseRect3218
        (capturedModulations2584 family * record2680Center3212 17168)) 9).Mem
      (Complex.exp (((capturedModulations2584 family *
        record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled :
      |(capturedModulations2584 family * record2680Center3212 17168) / 512| ≤ 1 := by
    fin_cases family <;>
      norm_num [capturedModulations2584, record2680Center3212,
        record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hsmall := phaseRect_mem3218 hscaled
  have hpow := complexRectPowSq_mem3218 hsmall 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hpow
  rw [complex_phase_eq_pow512_3218]
  exact hpow

theorem record2680_middle_point_family_mem3232 {family : Fin 30} :
    (record2680MiddlePointFamilyRect3232 family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 17168)) := by
  have hinside :
      |record2680Center3212 17168| < storedWidth family ^ 2 := by
    fin_cases family <;>
      norm_num [record2680Center3212, record2680Grid3212,
        diagnosticRadius3201, storedWidth, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hbump :
      (record2680MiddlePointBumpRect3232 family).Mem
        (widthBump (storedWidth family ^ 2)
          (record2680Center3212 17168) : ℂ) := by
    have h := record2680_middle_point_bump_mem3231 (family := family)
    rcases h with ⟨hlo, hhi⟩
    change (record2680MiddlePointBumpInterval3231 family).lo ≤
        widthBump (storedWidth family ^ 2) (record2680Center3212 17168) ∧
      widthBump (storedWidth family ^ 2) (record2680Center3212 17168) ≤
        (record2680MiddlePointBumpInterval3231 family).hi ∧
      (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0
    exact ⟨hlo, hhi, le_rfl, le_rfl⟩
  have hphase := record2680_middle_point_phase_mem3232 (family := family)
  rw [externalFamilyValue2344_eq_familyTerm]
  have hcoeff := ComplexRect2427.point_mem
    (record2680CorrectionCoefficient family)
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul hcoeff hbump) hphase

noncomputable def record2680MiddlePointAggregateRect3232 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680MiddlePointFamilyRect3232 Finset.univ

theorem record2680_middle_point_aggregate_mem3232 :
    record2680MiddlePointAggregateRect3232.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)) := by
  unfold externalPhysical2344
  exact ComplexRect2427.mem_sumFinset
    (fun family _ => record2680_middle_point_family_mem3232 (family := family))

end ConnesWeilRH.Dev
