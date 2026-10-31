import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family8CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family9CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family10CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family11CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family12CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family13CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family14CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family15CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family16CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family17CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family18CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family19CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family20CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family21CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family22CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family23CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family24CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family25CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family26CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family27CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family28CoeffPhaseUpper3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family29CoeffPhaseUpper3258

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell2825FamilyCoeffPhaseRectSplit3258 (slot : Fin 22) : ComplexRect2427 := match slot.val with
  | 0 => (ComplexRect2427.point (record2680CorrectionCoefficient 8)).mul (record2680Cell2825Family8TightStageBox3258 9)
  | 1 => (ComplexRect2427.point (record2680CorrectionCoefficient 9)).mul (record2680Cell2825Family9TightStageBox3258 9)
  | 2 => (ComplexRect2427.point (record2680CorrectionCoefficient 10)).mul (record2680Cell2825Family10TightStageBox3258 9)
  | 3 => (ComplexRect2427.point (record2680CorrectionCoefficient 11)).mul (record2680Cell2825Family11TightStageBox3258 9)
  | 4 => (ComplexRect2427.point (record2680CorrectionCoefficient 12)).mul (record2680Cell2825Family12TightStageBox3258 9)
  | 5 => (ComplexRect2427.point (record2680CorrectionCoefficient 13)).mul (record2680Cell2825Family13TightStageBox3258 9)
  | 6 => (ComplexRect2427.point (record2680CorrectionCoefficient 14)).mul (record2680Cell2825Family14TightStageBox3258 9)
  | 7 => (ComplexRect2427.point (record2680CorrectionCoefficient 15)).mul (record2680Cell2825Family15TightStageBox3258 9)
  | 8 => (ComplexRect2427.point (record2680CorrectionCoefficient 16)).mul (record2680Cell2825Family16TightStageBox3258 9)
  | 9 => (ComplexRect2427.point (record2680CorrectionCoefficient 17)).mul (record2680Cell2825Family17TightStageBox3258 9)
  | 10 => (ComplexRect2427.point (record2680CorrectionCoefficient 18)).mul (record2680Cell2825Family18TightStageBox3258 9)
  | 11 => (ComplexRect2427.point (record2680CorrectionCoefficient 19)).mul (record2680Cell2825Family19TightStageBox3258 9)
  | 12 => (ComplexRect2427.point (record2680CorrectionCoefficient 20)).mul (record2680Cell2825Family20TightStageBox3258 9)
  | 13 => (ComplexRect2427.point (record2680CorrectionCoefficient 21)).mul (record2680Cell2825Family21TightStageBox3258 9)
  | 14 => (ComplexRect2427.point (record2680CorrectionCoefficient 22)).mul (record2680Cell2825Family22TightStageBox3258 9)
  | 15 => (ComplexRect2427.point (record2680CorrectionCoefficient 23)).mul (record2680Cell2825Family23TightStageBox3258 9)
  | 16 => (ComplexRect2427.point (record2680CorrectionCoefficient 24)).mul (record2680Cell2825Family24TightStageBox3258 9)
  | 17 => (ComplexRect2427.point (record2680CorrectionCoefficient 25)).mul (record2680Cell2825Family25TightStageBox3258 9)
  | 18 => (ComplexRect2427.point (record2680CorrectionCoefficient 26)).mul (record2680Cell2825Family26TightStageBox3258 9)
  | 19 => (ComplexRect2427.point (record2680CorrectionCoefficient 27)).mul (record2680Cell2825Family27TightStageBox3258 9)
  | 20 => (ComplexRect2427.point (record2680CorrectionCoefficient 28)).mul (record2680Cell2825Family28TightStageBox3258 9)
  | 21 => (ComplexRect2427.point (record2680CorrectionCoefficient 29)).mul (record2680Cell2825Family29TightStageBox3258 9)
  | _ => (ComplexRect2427.point (record2680CorrectionCoefficient 29)).mul (record2680Cell2825Family29TightStageBox3258 9)

noncomputable def record2680Cell2825CoeffPhaseAggregateRectSplit3258 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell2825FamilyCoeffPhaseRectSplit3258 Finset.univ

noncomputable def record2680Cell2825FamilyIndexSplit3258 (slot : Fin 22) : Fin 30 :=
  ⟨slot.val + 8, by omega⟩

noncomputable def record2680Cell2825FamilyCoeffPhaseValueSplit3258 (slot : Fin 22) : ℂ :=
  record2680CorrectionCoefficient (record2680Cell2825FamilyIndexSplit3258 slot) *
    Complex.exp (((capturedModulations2584 (record2680Cell2825FamilyIndexSplit3258 slot) *
      record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)

theorem record2680_cell2825_coeff_phase_aggregate_rect_mem_split3258 :
    record2680Cell2825CoeffPhaseAggregateRectSplit3258.Mem
      (∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseValueSplit3258 slot) := by
  unfold record2680Cell2825CoeffPhaseAggregateRectSplit3258
  apply ComplexRect2427.mem_sumFinset
  intro slot hslot
  fin_cases slot
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family8_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family9_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family10_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family11_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family12_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family13_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family14_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family15_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family16_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family17_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family18_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family19_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family20_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family21_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family22_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family23_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family24_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family25_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family26_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family27_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family28_tight_phase_box_mem3258
  · apply ComplexRect2427.mem_mul
    · exact ComplexRect2427.point_mem _
    · exact record2680_cell2825_family29_tight_phase_box_mem3258

noncomputable def record2680Cell2825FamilyCoeffPhaseUpperSplit3258 (slot : Fin 22) : ℝ := match slot.val with
  | 0 => (-3000000000000 : ℝ)
  | 1 => (-388000000000000 : ℝ)
  | 2 => (-1200000000000000 : ℝ)
  | 3 => (-3611000000000000 : ℝ)
  | 4 => (-6983000000000000 : ℝ)
  | 5 => (-4006000000000000 : ℝ)
  | 6 => (-247549000000000000 : ℝ)
  | 7 => (-238689000000000000 : ℝ)
  | 8 => (-6617000000000000 : ℝ)
  | 9 => (552000000000000 : ℝ)
  | 10 => (583000000000000 : ℝ)
  | 11 => (-338000000000000 : ℝ)
  | 12 => (123000000000000 : ℝ)
  | 13 => (-53000000000000 : ℝ)
  | 14 => (114000000000000 : ℝ)
  | 15 => (-66000000000000 : ℝ)
  | 16 => (27000000000000 : ℝ)
  | 17 => (-38000000000000 : ℝ)
  | 18 => (-12000000000000 : ℝ)
  | 19 => (12000000000000 : ℝ)
  | 20 => (19000000000000 : ℝ)
  | 21 => (-5000000000000 : ℝ)
  | _ => (-5000000000000 : ℝ)

set_option maxHeartbeats 10000000 in
theorem record2680_cell2825_coeff_phase_aggregate_re_upper_split3258 :
  record2680Cell2825CoeffPhaseAggregateRectSplit3258.reHi < 0 := by
  have hsum : (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRectSplit3258 slot).reHi) ≤
      ∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseUpperSplit3258 slot := by
    apply Finset.sum_le_sum
    intro slot hslot
    fin_cases slot
    · exact record2680_cell2825_family8_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family9_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family10_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family11_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family12_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family13_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family14_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family15_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family16_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family17_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family18_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family19_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family20_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family21_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family22_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family23_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family24_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family25_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family26_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family27_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family28_coeff_phase_re_hi_upper_split3258
    · exact record2680_cell2825_family29_coeff_phase_re_hi_upper_split3258
  change (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRectSplit3258 slot).reHi) < 0
  calc
    (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRectSplit3258 slot).reHi) ≤
        ∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseUpperSplit3258 slot := hsum
    _ < 0 := by
      simp only [Fin.sum_univ_succ]
      norm_num [record2680Cell2825FamilyCoeffPhaseUpperSplit3258]

theorem record2680_cell2825_coeff_phase_aggregate_value_re_upper_split3259 :
    (∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseValueSplit3258 slot).re < 0 := by
  have hmem := record2680_cell2825_coeff_phase_aggregate_rect_mem_split3258
  exact lt_of_le_of_lt hmem.2.1
    record2680_cell2825_coeff_phase_aggregate_re_upper_split3258

end ConnesWeilRH.Dev
