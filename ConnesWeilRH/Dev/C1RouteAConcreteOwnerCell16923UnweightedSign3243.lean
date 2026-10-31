import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell16923Value3242
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell16923BumpRect3243
    (family : Fin 30) : ComplexRect2427 :=
  { reLo := (record2680Cell16923BumpInterval3242 family).lo
    reHi := (record2680Cell16923BumpInterval3242 family).hi
    imLo := 0
    imHi := 0 }

noncomputable def record2680Cell16923FamilyRect3243
    (family : Fin 30) : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient family)).mul
    (record2680Cell16923BumpRect3243 family) |>.mul
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 16923)) 9)

noncomputable def record2680Cell16923AggregateRect3243 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell16923FamilyRect3243 Finset.univ

theorem record2680_cell16923_bump_rect_mem3243 (family : Fin 30) :
    (record2680Cell16923BumpRect3243 family).Mem
      (widthBump (storedWidth family ^ 2)
        (record2680Center3212 16923) : ℂ) := by
  have h := record2680_cell16923_bump_mem3242 (family := family)
  exact ⟨h.1, h.2, by simp [record2680Cell16923BumpRect3243],
    by simp [record2680Cell16923BumpRect3243]⟩

theorem record2680_cell16923_phase_rect_mem3243 (family : Fin 30) :
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 family *
        record2680Center3212 16923)) 9).Mem
      (Complex.exp (((capturedModulations2584 family *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell16923_phase_scaled5123242
    (family := family)
  have hphase := complexRectPowSq_mem3218
    (phaseRect_mem3218 hscaled) 9
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hphase
  rw [complex_phase_eq_pow512_3218]
  exact hphase

theorem record2680_cell16923_family_rect_mem3243 (family : Fin 30) :
    (record2680Cell16923FamilyRect3243 family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 16923)) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul
      (ComplexRect2427.point_mem _)
      (record2680_cell16923_bump_rect_mem3243 family))
    (record2680_cell16923_phase_rect_mem3243 family)

theorem record2680_cell16923_aggregate_rect_mem3243 :
    record2680Cell16923AggregateRect3243.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 16923)) := by
  unfold record2680Cell16923AggregateRect3243
  apply ComplexRect2427.mem_sumFinset
  intro family _
  exact record2680_cell16923_family_rect_mem3243 family

theorem record2680_cell16923_unweighted_rect_value_upper3243 :
    (externalPhysical2344 record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 16923)).re ≤
      record2680Cell16923AggregateRect3243.reHi := by
  exact record2680_cell16923_aggregate_rect_mem3243.2.1

end ConnesWeilRH.Dev
