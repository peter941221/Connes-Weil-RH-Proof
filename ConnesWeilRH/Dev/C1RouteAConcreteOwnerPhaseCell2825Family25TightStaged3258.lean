import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family25TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((719732525741012 : ℝ) / 1000000000000000), reHi := ((719732525741013 : ℝ) / 1000000000000000), imLo := ((694251461208734 : ℝ) / 1000000000000000), imHi := ((694251461208735 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((36029817219071 : ℝ) / 1000000000000000), reHi := ((36029817219077 : ℝ) / 1000000000000000), imLo := ((999350715350299 : ℝ) / 1000000000000000), imHi := ((999350715350305 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((997403704542328 : ℝ) / 1000000000000000), reHi := -((997403704542313 : ℝ) / 1000000000000000), imLo := ((72012847223637 : ℝ) / 1000000000000000), imHi := ((72012847223652 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((989628299669471 : ℝ) / 1000000000000000), reHi := ((989628299669506 : ℝ) / 1000000000000000), imLo := -((143651761191024 : ℝ) / 1000000000000000), imHi := -((143651761190989 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((958728343013404 : ℝ) / 1000000000000000), reHi := ((958728343013486 : ℝ) / 1000000000000000), imLo := -((284323696344007 : ℝ) / 1000000000000000), imHi := -((284323696343925 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((838320071394507 : ℝ) / 1000000000000000), reHi := ((838320071394713 : ℝ) / 1000000000000000), imLo := -((545178372550720 : ℝ) / 1000000000000000), imHi := -((545178372550513 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((405561084205838 : ℝ) / 1000000000000000), reHi := ((405561084206412 : ℝ) / 1000000000000000), imLo := -((914067944399148 : ℝ) / 1000000000000000), imHi := -((914067944398573 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((671040413955871 : ℝ) / 1000000000000000), reHi := -((671040413954351 : ℝ) / 1000000000000000), imLo := -((741420773137691 : ℝ) / 1000000000000000), imHi := -((741420773136172 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((99409525680066 : ℝ) / 1000000000000000), reHi := -((99409525675771 : ℝ) / 1000000000000000), imLo := ((995046605039302 : ℝ) / 1000000000000000), imHi := ((995046605043598 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((980235492413710 : ℝ) / 1000000000000000), reHi := -((980235492404304 : ℝ) / 1000000000000000), imLo := -((197834222073890 : ℝ) / 1000000000000000), imHi := -((197834222064485 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((980235492413710 : ℝ) / 1000000000000000), reHi := -((980235492404304 : ℝ) / 1000000000000000), imLo := -((197834222073890 : ℝ) / 1000000000000000), imHi := -((197834222064485 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family25_3258 : |(capturedModulations2584 25 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_25, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family25_tight_base_mem3258 : (record2680Cell2825Family25TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 25 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family25_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 25 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family25TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_25, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family25_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family25TightStageBox3258 stage).Mem w) : (record2680Cell2825Family25TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family25TightStageBox3258 stage).mul (record2680Cell2825Family25TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family25TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family25_tight_phase_box_mem3258 : (record2680Cell2825Family25TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 25 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family25_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family25_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
