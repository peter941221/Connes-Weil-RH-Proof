import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family16TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((887882828567321 : ℝ) / 1000000000000000), reHi := ((887882828567322 : ℝ) / 1000000000000000), imLo := ((460069649874116 : ℝ) / 1000000000000000), imHi := ((460069649874117 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((576671834529413 : ℝ) / 1000000000000000), reHi := ((576671834529418 : ℝ) / 1000000000000000), imLo := ((816975884136413 : ℝ) / 1000000000000000), imHi := ((816975884136418 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((334899190520965 : ℝ) / 1000000000000000), reHi := -((334899190520948 : ℝ) / 1000000000000000), imLo := ((942253963742467 : ℝ) / 1000000000000000), imHi := ((942253963742484 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((775685064376838 : ℝ) / 1000000000000000), reHi := -((775685064376791 : ℝ) / 1000000000000000), imLo := -((631120179445059 : ℝ) / 1000000000000000), imHi := -((631120179445012 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((203374638194461 : ℝ) / 1000000000000000), reHi := ((203374638194597 : ℝ) / 1000000000000000), imLo := ((979100994044591 : ℝ) / 1000000000000000), imHi := ((979100994044726 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((917277513078644 : ℝ) / 1000000000000000), reHi := -((917277513078322 : ℝ) / 1000000000000000), imLo := ((398248620839310 : ℝ) / 1000000000000000), imHi := ((398248620839634 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((682796071998479 : ℝ) / 1000000000000000), reHi := ((682796071999331 : ℝ) / 1000000000000000), imLo := -((730609009021560 : ℝ) / 1000000000000000), imHi := -((730609009020706 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((67579048126915 : ℝ) / 1000000000000000), reHi := -((67579048124501 : ℝ) / 1000000000000000), imLo := -((997713923054491 : ℝ) / 1000000000000000), imHi := -((997713923052077 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((990866144511371 : ℝ) / 1000000000000000), reHi := -((990866144506224 : ℝ) / 1000000000000000), imLo := ((134849114440841 : ℝ) / 1000000000000000), imHi := ((134849114445987 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((963631432661761 : ℝ) / 1000000000000000), reHi := ((963631432673352 : ℝ) / 1000000000000000), imLo := -((267234844243737 : ℝ) / 1000000000000000), imHi := -((267234844232148 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((963631432661761 : ℝ) / 1000000000000000), reHi := ((963631432673352 : ℝ) / 1000000000000000), imLo := -((267234844243737 : ℝ) / 1000000000000000), imHi := -((267234844232148 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family16_3258 : |(capturedModulations2584 16 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_16, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family16_tight_base_mem3258 : (record2680Cell2825Family16TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 16 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family16_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 16 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family16TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_16, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family16_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family16TightStageBox3258 stage).Mem w) : (record2680Cell2825Family16TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family16TightStageBox3258 stage).mul (record2680Cell2825Family16TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family16TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family16_tight_phase_box_mem3258 : (record2680Cell2825Family16TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 16 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family16_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family16_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
