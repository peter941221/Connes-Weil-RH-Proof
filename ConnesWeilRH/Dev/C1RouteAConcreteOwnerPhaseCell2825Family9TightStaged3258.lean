import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family9TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((973218033313011 : ℝ) / 1000000000000000), reHi := ((973218033313012 : ℝ) / 1000000000000000), imLo := ((229884013437981 : ℝ) / 1000000000000000), imHi := ((229884013437982 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((894306680731289 : ℝ) / 1000000000000000), reHi := ((894306680731295 : ℝ) / 1000000000000000), imLo := ((447454534896426 : ℝ) / 1000000000000000), imHi := ((447454534896431 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((599568878401233 : ℝ) / 1000000000000000), reHi := ((599568878401251 : ℝ) / 1000000000000000), imLo := ((800323159762769 : ℝ) / 1000000000000000), imHi := ((800323159762787 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((281034320105380 : ℝ) / 1000000000000000), reHi := -((281034320105327 : ℝ) / 1000000000000000), imLo := ((959697718514987 : ℝ) / 1000000000000000), imHi := ((959697718515040 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((842039421845911 : ℝ) / 1000000000000000), reHi := -((842039421845777 : ℝ) / 1000000000000000), imLo := -((539415991659119 : ℝ) / 1000000000000000), imHi := -((539415991658984 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((418060775884778 : ℝ) / 1000000000000000), reHi := ((418060775885152 : ℝ) / 1000000000000000), imLo := ((908419059501793 : ℝ) / 1000000000000000), imHi := ((908419059502168 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((650450375333422 : ℝ) / 1000000000000000), reHi := -((650450375332425 : ℝ) / 1000000000000000), imLo := ((759548753687678 : ℝ) / 1000000000000000), imHi := ((759548753688674 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((153828618459927 : ℝ) / 1000000000000000), reHi := -((153828618457114 : ℝ) / 1000000000000000), imLo := -((988097543841663 : ℝ) / 1000000000000000), imHi := -((988097543838850 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((952673512289504 : ℝ) / 1000000000000000), reHi := -((952673512283077 : ℝ) / 1000000000000000), imLo := ((303995360139194 : ℝ) / 1000000000000000), imHi := ((303995360145622 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((815173642015706 : ℝ) / 1000000000000000), reHi := ((815173642031863 : ℝ) / 1000000000000000), imLo := -((579216654939286 : ℝ) / 1000000000000000), imHi := -((579216654923128 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((815173642015706 : ℝ) / 1000000000000000), reHi := ((815173642031863 : ℝ) / 1000000000000000), imLo := -((579216654939286 : ℝ) / 1000000000000000), imHi := -((579216654923128 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family9_3258 : |(capturedModulations2584 9 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_9, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family9_tight_base_mem3258 : (record2680Cell2825Family9TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 9 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family9_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 9 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family9TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_9, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family9_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family9TightStageBox3258 stage).Mem w) : (record2680Cell2825Family9TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family9TightStageBox3258 stage).mul (record2680Cell2825Family9TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family9TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family9_tight_phase_box_mem3258 : (record2680Cell2825Family9TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 9 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family9_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family9_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
