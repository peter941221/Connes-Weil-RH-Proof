import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family8TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family9TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family10TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family11TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family12TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family13TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family14TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family15TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family16TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family17TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family18TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family19TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family20TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family21TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family22TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family23TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family24TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family25TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family26TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family27TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family28TightStaged3258
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825Family29TightStaged3258

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell2825FamilyIndex3258
    (slot : Fin 22) : Fin 30 :=
  ⟨slot.val + 8, by omega⟩

noncomputable def record2680Cell2825FamilyPhaseBox3258
    (slot : Fin 22) : ComplexRect2427 :=
  match slot.val with
  | 0 => record2680Cell2825Family8TightStageBox3258 9
  | 1 => record2680Cell2825Family9TightStageBox3258 9
  | 2 => record2680Cell2825Family10TightStageBox3258 9
  | 3 => record2680Cell2825Family11TightStageBox3258 9
  | 4 => record2680Cell2825Family12TightStageBox3258 9
  | 5 => record2680Cell2825Family13TightStageBox3258 9
  | 6 => record2680Cell2825Family14TightStageBox3258 9
  | 7 => record2680Cell2825Family15TightStageBox3258 9
  | 8 => record2680Cell2825Family16TightStageBox3258 9
  | 9 => record2680Cell2825Family17TightStageBox3258 9
  | 10 => record2680Cell2825Family18TightStageBox3258 9
  | 11 => record2680Cell2825Family19TightStageBox3258 9
  | 12 => record2680Cell2825Family20TightStageBox3258 9
  | 13 => record2680Cell2825Family21TightStageBox3258 9
  | 14 => record2680Cell2825Family22TightStageBox3258 9
  | 15 => record2680Cell2825Family23TightStageBox3258 9
  | 16 => record2680Cell2825Family24TightStageBox3258 9
  | 17 => record2680Cell2825Family25TightStageBox3258 9
  | 18 => record2680Cell2825Family26TightStageBox3258 9
  | 19 => record2680Cell2825Family27TightStageBox3258 9
  | 20 => record2680Cell2825Family28TightStageBox3258 9
  | 21 => record2680Cell2825Family29TightStageBox3258 9
  | _ => record2680Cell2825Family29TightStageBox3258 9


noncomputable def record2680Cell2825FamilyCoeffPhaseRect3258
    (slot : Fin 22) : ComplexRect2427 :=
  (ComplexRect2427.point
      (record2680CorrectionCoefficient (record2680Cell2825FamilyIndex3258 slot))).mul
    (record2680Cell2825FamilyPhaseBox3258 slot)

noncomputable def record2680Cell2825CoeffPhaseAggregateRect3258 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell2825FamilyCoeffPhaseRect3258 Finset.univ

theorem record2680_cell2825_family_coeff_phase_rect_mem3258
    (slot : Fin 22) :
    (record2680Cell2825FamilyCoeffPhaseRect3258 slot).Mem
      (record2680CorrectionCoefficient (record2680Cell2825FamilyIndex3258 slot) *
        Complex.exp (((capturedModulations2584 (record2680Cell2825FamilyIndex3258 slot) *
          record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    (by
      fin_cases slot
      · exact record2680_cell2825_family8_tight_phase_box_mem3258
      · exact record2680_cell2825_family9_tight_phase_box_mem3258
      · exact record2680_cell2825_family10_tight_phase_box_mem3258
      · exact record2680_cell2825_family11_tight_phase_box_mem3258
      · exact record2680_cell2825_family12_tight_phase_box_mem3258
      · exact record2680_cell2825_family13_tight_phase_box_mem3258
      · exact record2680_cell2825_family14_tight_phase_box_mem3258
      · exact record2680_cell2825_family15_tight_phase_box_mem3258
      · exact record2680_cell2825_family16_tight_phase_box_mem3258
      · exact record2680_cell2825_family17_tight_phase_box_mem3258
      · exact record2680_cell2825_family18_tight_phase_box_mem3258
      · exact record2680_cell2825_family19_tight_phase_box_mem3258
      · exact record2680_cell2825_family20_tight_phase_box_mem3258
      · exact record2680_cell2825_family21_tight_phase_box_mem3258
      · exact record2680_cell2825_family22_tight_phase_box_mem3258
      · exact record2680_cell2825_family23_tight_phase_box_mem3258
      · exact record2680_cell2825_family24_tight_phase_box_mem3258
      · exact record2680_cell2825_family25_tight_phase_box_mem3258
      · exact record2680_cell2825_family26_tight_phase_box_mem3258
      · exact record2680_cell2825_family27_tight_phase_box_mem3258
      · exact record2680_cell2825_family28_tight_phase_box_mem3258
      · exact record2680_cell2825_family29_tight_phase_box_mem3258
)

theorem record2680_cell2825_coeff_phase_aggregate_rect_mem3258 :
    record2680Cell2825CoeffPhaseAggregateRect3258.Mem
      (Finset.univ.sum (fun slot =>
        record2680CorrectionCoefficient (record2680Cell2825FamilyIndex3258 slot) *
          Complex.exp (((capturedModulations2584 (record2680Cell2825FamilyIndex3258 slot) *
            record2680Center3212 2825 : ℝ) : ℂ) * Complex.I))) := by
  unfold record2680Cell2825CoeffPhaseAggregateRect3258
  apply ComplexRect2427.mem_sumFinset
  intro slot _
  exact record2680_cell2825_family_coeff_phase_rect_mem3258 slot

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000000 in
theorem record2680_cell2825_coeff_phase_aggregate_re_upper3258 :
    record2680Cell2825CoeffPhaseAggregateRect3258.reHi < 0 := by
  norm_num (config := { maxSteps := 2000000000 }) [record2680Cell2825CoeffPhaseAggregateRect3258,
    record2680Cell2825FamilyCoeffPhaseRect3258,
    record2680Cell2825FamilyPhaseBox3258,
    record2680Cell2825FamilyIndex3258,
    ComplexRect2427.sumFinset, ComplexRect2427.point, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
    min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_8, Matrix.cons_val_9, Matrix.cons_val_10, Matrix.cons_val_11, Matrix.cons_val_12, Matrix.cons_val_13, Matrix.cons_val_14, Matrix.cons_val_15, Matrix.cons_val_16, Matrix.cons_val_17, Matrix.cons_val_18, Matrix.cons_val_19, Matrix.cons_val_20, Matrix.cons_val_21, Matrix.cons_val_22, Matrix.cons_val_23, Matrix.cons_val_24, Matrix.cons_val_25, Matrix.cons_val_26, Matrix.cons_val_27, Matrix.cons_val_28, Matrix.cons_val_29, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674,
    record2680Cell2825Family8TightStageBox3258, record2680Cell2825Family9TightStageBox3258, record2680Cell2825Family10TightStageBox3258, record2680Cell2825Family11TightStageBox3258, record2680Cell2825Family12TightStageBox3258, record2680Cell2825Family13TightStageBox3258, record2680Cell2825Family14TightStageBox3258, record2680Cell2825Family15TightStageBox3258, record2680Cell2825Family16TightStageBox3258, record2680Cell2825Family17TightStageBox3258, record2680Cell2825Family18TightStageBox3258, record2680Cell2825Family19TightStageBox3258, record2680Cell2825Family20TightStageBox3258, record2680Cell2825Family21TightStageBox3258, record2680Cell2825Family22TightStageBox3258, record2680Cell2825Family23TightStageBox3258, record2680Cell2825Family24TightStageBox3258, record2680Cell2825Family25TightStageBox3258, record2680Cell2825Family26TightStageBox3258, record2680Cell2825Family27TightStageBox3258, record2680Cell2825Family28TightStageBox3258, record2680Cell2825Family29TightStageBox3258]

end ConnesWeilRH.Dev
