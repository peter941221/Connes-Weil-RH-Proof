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
noncomputable def record2680Cell2825FamilyIndex3258 (slot : Fin 22) : Fin 30 := ⟨slot.val + 8, by omega⟩
noncomputable def record2680Cell2825FamilyPhaseBox3258 (slot : Fin 22) : ComplexRect2427 := match slot.val with
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
noncomputable def record2680Cell2825FamilyCoeffPhaseRect3258 (slot : Fin 22) : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient (record2680Cell2825FamilyIndex3258 slot))).mul
    (record2680Cell2825FamilyPhaseBox3258 slot)
noncomputable def record2680Cell2825CoeffPhaseAggregateRect3258 : ComplexRect2427 :=
  ComplexRect2427.sumFinset record2680Cell2825FamilyCoeffPhaseRect3258 Finset.univ
noncomputable def record2680Cell2825FamilyCoeffPhaseUpper3258 (slot : Fin 22) : ℝ := match slot.val with
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
theorem record2680_cell2825_family8_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨0, by omega⟩)).reHi ≤ (-3000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 8)).mul
    (record2680Cell2825Family8TightStageBox3258 9)).reHi ≤ (-3000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family8TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_8, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family9_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨1, by omega⟩)).reHi ≤ (-388000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 9)).mul
    (record2680Cell2825Family9TightStageBox3258 9)).reHi ≤ (-388000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family9TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_9, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family10_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨2, by omega⟩)).reHi ≤ (-1200000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 10)).mul
    (record2680Cell2825Family10TightStageBox3258 9)).reHi ≤ (-1200000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family10TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family11_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨3, by omega⟩)).reHi ≤ (-3611000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 11)).mul
    (record2680Cell2825Family11TightStageBox3258 9)).reHi ≤ (-3611000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family11TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_11, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family12_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨4, by omega⟩)).reHi ≤ (-6983000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 12)).mul
    (record2680Cell2825Family12TightStageBox3258 9)).reHi ≤ (-6983000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family12TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_12, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family13_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨5, by omega⟩)).reHi ≤ (-4006000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 13)).mul
    (record2680Cell2825Family13TightStageBox3258 9)).reHi ≤ (-4006000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family13TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_13, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family14_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨6, by omega⟩)).reHi ≤ (-247549000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 14)).mul
    (record2680Cell2825Family14TightStageBox3258 9)).reHi ≤ (-247549000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family14TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_14, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family15_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨7, by omega⟩)).reHi ≤ (-238689000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 15)).mul
    (record2680Cell2825Family15TightStageBox3258 9)).reHi ≤ (-238689000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family15TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_15, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family16_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨8, by omega⟩)).reHi ≤ (-6617000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 16)).mul
    (record2680Cell2825Family16TightStageBox3258 9)).reHi ≤ (-6617000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family16TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_16, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family17_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨9, by omega⟩)).reHi ≤ (552000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 17)).mul
    (record2680Cell2825Family17TightStageBox3258 9)).reHi ≤ (552000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family17TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_17, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family18_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨10, by omega⟩)).reHi ≤ (583000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 18)).mul
    (record2680Cell2825Family18TightStageBox3258 9)).reHi ≤ (583000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family18TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_18, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family19_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨11, by omega⟩)).reHi ≤ (-338000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 19)).mul
    (record2680Cell2825Family19TightStageBox3258 9)).reHi ≤ (-338000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family19TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_19, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family20_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨12, by omega⟩)).reHi ≤ (123000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 20)).mul
    (record2680Cell2825Family20TightStageBox3258 9)).reHi ≤ (123000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family20TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_20, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family21_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨13, by omega⟩)).reHi ≤ (-53000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 21)).mul
    (record2680Cell2825Family21TightStageBox3258 9)).reHi ≤ (-53000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family21TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_21, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family22_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨14, by omega⟩)).reHi ≤ (114000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 22)).mul
    (record2680Cell2825Family22TightStageBox3258 9)).reHi ≤ (114000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family22TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_22, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family23_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨15, by omega⟩)).reHi ≤ (-66000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 23)).mul
    (record2680Cell2825Family23TightStageBox3258 9)).reHi ≤ (-66000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family23TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_23, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family24_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨16, by omega⟩)).reHi ≤ (27000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 24)).mul
    (record2680Cell2825Family24TightStageBox3258 9)).reHi ≤ (27000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family24TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_24, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family25_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨17, by omega⟩)).reHi ≤ (-38000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 25)).mul
    (record2680Cell2825Family25TightStageBox3258 9)).reHi ≤ (-38000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family25TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_25, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family26_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨18, by omega⟩)).reHi ≤ (-12000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 26)).mul
    (record2680Cell2825Family26TightStageBox3258 9)).reHi ≤ (-12000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family26TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_26, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family27_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨19, by omega⟩)).reHi ≤ (12000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 27)).mul
    (record2680Cell2825Family27TightStageBox3258 9)).reHi ≤ (12000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family27TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_27, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family28_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨20, by omega⟩)).reHi ≤ (19000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 28)).mul
    (record2680Cell2825Family28TightStageBox3258 9)).reHi ≤ (19000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family28TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_28, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
theorem record2680_cell2825_family29_coeff_phase_re_hi_upper3258 :
    (record2680Cell2825FamilyCoeffPhaseRect3258 (⟨21, by omega⟩)).reHi ≤ (-5000000000000 : ℝ) := by
  change ((ComplexRect2427.point (record2680CorrectionCoefficient 29)).mul
    (record2680Cell2825Family29TightStageBox3258 9)).reHi ≤ (-5000000000000 : ℝ)
  norm_num [ComplexRect2427.point, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, min_def, max_def,
    record2680CorrectionCoefficient, record2680Cell2825Family29TightStageBox3258,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_29, Fin.ext_iff,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_coeff_phase_aggregate_re_upper3258 :
    record2680Cell2825CoeffPhaseAggregateRect3258.reHi < 0 := by
  have hsum : (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRect3258 slot).reHi) ≤
      ∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseUpper3258 slot := by
    apply Finset.sum_le_sum
    intro slot hslot
    fin_cases slot
    · exact record2680_cell2825_family8_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family9_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family10_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family11_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family12_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family13_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family14_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family15_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family16_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family17_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family18_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family19_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family20_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family21_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family22_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family23_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family24_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family25_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family26_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family27_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family28_coeff_phase_re_hi_upper3258
    · exact record2680_cell2825_family29_coeff_phase_re_hi_upper3258
  change (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRect3258 slot).reHi) < 0
  calc
    (∑ slot : Fin 22, (record2680Cell2825FamilyCoeffPhaseRect3258 slot).reHi) ≤
        ∑ slot : Fin 22, record2680Cell2825FamilyCoeffPhaseUpper3258 slot := hsum
    _ < 0 := by norm_num [record2680Cell2825FamilyCoeffPhaseUpper3258, Fin.sum_univ_succ]
end ConnesWeilRH.Dev
