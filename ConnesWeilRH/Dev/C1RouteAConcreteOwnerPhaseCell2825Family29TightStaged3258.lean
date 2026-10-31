import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family29TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((640679371987309 : ℝ) / 1000000000000000), reHi := ((640679371987310 : ℝ) / 1000000000000000), imLo := ((767808532324268 : ℝ) / 1000000000000000), imHi := ((767808532324269 : ℝ) / 1000000000000000) }
  | 1 => { reLo := -((179059884619897 : ℝ) / 1000000000000000), reHi := -((179059884619891 : ℝ) / 1000000000000000), imLo := ((983838176592017 : ℝ) / 1000000000000000), imHi := ((983838176592023 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((935875115439829 : ℝ) / 1000000000000000), reHi := -((935875115439813 : ℝ) / 1000000000000000), imLo := -((352331900770436 : ℝ) / 1000000000000000), imHi := -((352331900770420 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((751724463398974 : ℝ) / 1000000000000000), reHi := ((751724463399018 : ℝ) / 1000000000000000), imLo := ((659477316613290 : ℝ) / 1000000000000000), imHi := ((659477316613334 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((130179337744950 : ℝ) / 1000000000000000), reHi := ((130179337745078 : ℝ) / 1000000000000000), imLo := ((991490463909840 : ℝ) / 1000000000000000), imHi := ((991490463909967 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((966106680048689 : ℝ) / 1000000000000000), reHi := -((966106680048401 : ℝ) / 1000000000000000), imLo := ((258143143944431 : ℝ) / 1000000000000000), imHi := ((258143143944721 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((866724234468477 : ℝ) / 1000000000000000), reHi := ((866724234469186 : ℝ) / 1000000000000000), imLo := -((498787631547532 : ℝ) / 1000000000000000), imHi := -((498787631546820 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((502421797230169 : ℝ) / 1000000000000000), reHi := ((502421797232112 : ℝ) / 1000000000000000), imLo := -((864622656231468 : ℝ) / 1000000000000000), imHi := -((864622656229523 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((495144675336768 : ℝ) / 1000000000000000), reHi := -((495144675331449 : ℝ) / 1000000000000000), imLo := -((868810537742835 : ℝ) / 1000000000000000), imHi := -((868810537737518 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((509663500983910 : ℝ) / 1000000000000000), reHi := -((509663500969400 : ℝ) / 1000000000000000), imLo := ((860373823265169 : ℝ) / 1000000000000000), imHi := ((860373823279679 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((509663500983910 : ℝ) / 1000000000000000), reHi := -((509663500969400 : ℝ) / 1000000000000000), imLo := ((860373823265169 : ℝ) / 1000000000000000), imHi := ((860373823279679 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family29_3258 : |(capturedModulations2584 29 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_29, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family29_tight_base_mem3258 : (record2680Cell2825Family29TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 29 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family29_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 29 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family29TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_29, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family29_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family29TightStageBox3258 stage).Mem w) : (record2680Cell2825Family29TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family29TightStageBox3258 stage).mul (record2680Cell2825Family29TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family29TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family29_tight_phase_box_mem3258 : (record2680Cell2825Family29TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 29 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family29_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family29_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
