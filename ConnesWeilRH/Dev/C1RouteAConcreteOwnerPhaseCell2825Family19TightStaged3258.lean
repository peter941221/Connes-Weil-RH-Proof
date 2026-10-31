import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family19TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((834000304923526 : ℝ) / 1000000000000000), reHi := ((834000304923527 : ℝ) / 1000000000000000), imLo := ((551763981596719 : ℝ) / 1000000000000000), imHi := ((551763981596720 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((391113017225067 : ℝ) / 1000000000000000), reHi := ((391113017225073 : ℝ) / 1000000000000000), imLo := ((920342657794963 : ℝ) / 1000000000000000), imHi := ((920342657794969 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((694061215514213 : ℝ) / 1000000000000000), reHi := -((694061215514195 : ℝ) / 1000000000000000), imLo := ((719915987542249 : ℝ) / 1000000000000000), imHi := ((719915987542268 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((36558058237919 : ℝ) / 1000000000000000), reHi := -((36558058237863 : ℝ) / 1000000000000000), imLo := -((999331530763405 : ℝ) / 1000000000000000), imHi := -((999331530763349 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((997327016755809 : ℝ) / 1000000000000000), reHi := -((997327016755690 : ℝ) / 1000000000000000), imLo := ((73067240601157 : ℝ) / 1000000000000000), imHi := ((73067240601276 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((989322356701718 : ℝ) / 1000000000000000), reHi := ((989322356701976 : ℝ) / 1000000000000000), imLo := -((145743866182901 : ℝ) / 1000000000000000), imHi := -((145743866182643 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((957517450939901 : ℝ) / 1000000000000000), reHi := ((957517450940489 : ℝ) / 1000000000000000), imLo := -((288375330333852 : ℝ) / 1000000000000000), imHi := -((288375330333263 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((833679337709286 : ℝ) / 1000000000000000), reHi := ((833679337710755 : ℝ) / 1000000000000000), imLo := -((552248822430784 : ℝ) / 1000000000000000), imHi := -((552248822429314 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((390042476247205 : ℝ) / 1000000000000000), reHi := ((390042476251281 : ℝ) / 1000000000000000), imLo := -((920796865071282 : ℝ) / 1000000000000000), imHi := -((920796865067206 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((695733733448051 : ℝ) / 1000000000000000), reHi := -((695733733437362 : ℝ) / 1000000000000000), imLo := -((718299778753640 : ℝ) / 1000000000000000), imHi := -((718299778742952 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((695733733448051 : ℝ) / 1000000000000000), reHi := -((695733733437362 : ℝ) / 1000000000000000), imLo := -((718299778753640 : ℝ) / 1000000000000000), imHi := -((718299778742952 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family19_3258 : |(capturedModulations2584 19 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_19, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family19_tight_base_mem3258 : (record2680Cell2825Family19TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 19 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family19_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 19 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family19TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_19, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family19_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family19TightStageBox3258 stage).Mem w) : (record2680Cell2825Family19TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family19TightStageBox3258 stage).mul (record2680Cell2825Family19TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family19TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family19_tight_phase_box_mem3258 : (record2680Cell2825Family19TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 19 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family19_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family19_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
