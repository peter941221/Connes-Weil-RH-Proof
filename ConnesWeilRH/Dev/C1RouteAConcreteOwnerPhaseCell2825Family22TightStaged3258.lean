import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family22TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((783062449616391 : ℝ) / 1000000000000000), reHi := ((783062449616392 : ℝ) / 1000000000000000), imLo := ((621943084213319 : ℝ) / 1000000000000000), imHi := ((621943084213320 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((226373599998445 : ℝ) / 1000000000000000), reHi := ((226373599998450 : ℝ) / 1000000000000000), imLo := ((974040550092108 : ℝ) / 1000000000000000), imHi := ((974040550092114 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((897509986447494 : ℝ) / 1000000000000000), reHi := -((897509986447477 : ℝ) / 1000000000000000), imLo := ((440994131737631 : ℝ) / 1000000000000000), imHi := ((440994131737646 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((611048351545909 : ℝ) / 1000000000000000), reHi := ((611048351545955 : ℝ) / 1000000000000000), imLo := -((791593274398560 : ℝ) / 1000000000000000), imHi := -((791593274398515 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((253239824146063 : ℝ) / 1000000000000000), reHi := -((253239824145932 : ℝ) / 1000000000000000), imLo := -((967403530832211 : ℝ) / 1000000000000000), imHi := -((967403530832081 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((871739182933167 : ℝ) / 1000000000000000), reHi := -((871739182932847 : ℝ) / 1000000000000000), imLo := ((489970200052138 : ℝ) / 1000000000000000), imHi := ((489970200052461 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((519858406120978 : ℝ) / 1000000000000000), reHi := ((519858406121855 : ℝ) / 1000000000000000), imLo := -((854252443710667 : ℝ) / 1000000000000000), imHi := -((854252443709787 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((459494475171004 : ℝ) / 1000000000000000), reHi := -((459494475168586 : ℝ) / 1000000000000000), imLo := -((888180627626255 : ℝ) / 1000000000000000), imHi := -((888180627623839 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((577729654580115 : ℝ) / 1000000000000000), reHi := -((577729654573599 : ℝ) / 1000000000000000), imLo := ((816228182689841 : ℝ) / 1000000000000000), imHi := ((816228182696359 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((332456892454072 : ℝ) / 1000000000000000), reHi := -((332456892435900 : ℝ) / 1000000000000000), imLo := -((943118452095446 : ℝ) / 1000000000000000), imHi := -((943118452077275 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((332456892454072 : ℝ) / 1000000000000000), reHi := -((332456892435900 : ℝ) / 1000000000000000), imLo := -((943118452095446 : ℝ) / 1000000000000000), imHi := -((943118452077275 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family22_3258 : |(capturedModulations2584 22 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_22, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family22_tight_base_mem3258 : (record2680Cell2825Family22TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 22 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family22_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 22 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family22TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_22, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family22_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family22TightStageBox3258 stage).Mem w) : (record2680Cell2825Family22TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family22TightStageBox3258 stage).mul (record2680Cell2825Family22TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family22TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family22_tight_phase_box_mem3258 : (record2680Cell2825Family22TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 22 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family22_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family22_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
