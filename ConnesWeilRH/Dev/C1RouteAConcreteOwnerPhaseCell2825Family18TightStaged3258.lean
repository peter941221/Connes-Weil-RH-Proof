import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family18TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((852938438616034 : ℝ) / 1000000000000000), reHi := ((852938438616035 : ℝ) / 1000000000000000), imLo := ((522011513217132 : ℝ) / 1000000000000000), imHi := ((522011513217133 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((455007960137516 : ℝ) / 1000000000000000), reHi := ((455007960137521 : ℝ) / 1000000000000000), imLo := ((890487370046026 : ℝ) / 1000000000000000), imHi := ((890487370046032 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((585935512422997 : ℝ) / 1000000000000000), reHi := -((585935512422979 : ℝ) / 1000000000000000), imLo := ((810357683545726 : ℝ) / 1000000000000000), imHi := ((810357683545743 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((313359150563245 : ℝ) / 1000000000000000), reHi := -((313359150563193 : ℝ) / 1000000000000000), imLo := -((949634689108577 : ℝ) / 1000000000000000), imHi := -((949634689108525 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((803612085516659 : ℝ) / 1000000000000000), reHi := -((803612085516525 : ℝ) / 1000000000000000), imLo := ((595153439048777 : ℝ) / 1000000000000000), imHi := ((595153439048911 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((291584767976471 : ℝ) / 1000000000000000), reHi := ((291584767976849 : ℝ) / 1000000000000000), imLo := -((956544992713016 : ℝ) / 1000000000000000), imHi := -((956544992712638 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((829956646168453 : ℝ) / 1000000000000000), reHi := -((829956646167506 : ℝ) / 1000000000000000), imLo := -((557827899519284 : ℝ) / 1000000000000000), imHi := -((557827899518338 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((377656069035517 : ℝ) / 1000000000000000), reHi := ((377656069038147 : ℝ) / 1000000000000000), imLo := ((925945945245807 : ℝ) / 1000000000000000), imHi := ((925945945248437 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((714751787042664 : ℝ) / 1000000000000000), reHi := -((714751787035804 : ℝ) / 1000000000000000), imLo := ((699378211641814 : ℝ) / 1000000000000000), imHi := ((699378211648673 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((21740234141978 : ℝ) / 1000000000000000), reHi := ((21740234161381 : ℝ) / 1000000000000000), imLo := -((999763653189184 : ℝ) / 1000000000000000), imHi := -((999763653169781 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((21740234141978 : ℝ) / 1000000000000000), reHi := ((21740234161381 : ℝ) / 1000000000000000), imLo := -((999763653189184 : ℝ) / 1000000000000000), imHi := -((999763653169781 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family18_3258 : |(capturedModulations2584 18 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_18, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family18_tight_base_mem3258 : (record2680Cell2825Family18TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 18 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family18_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 18 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family18TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_18, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family18_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family18TightStageBox3258 stage).Mem w) : (record2680Cell2825Family18TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family18TightStageBox3258 stage).mul (record2680Cell2825Family18TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family18TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family18_tight_phase_box_mem3258 : (record2680Cell2825Family18TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 18 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family18_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family18_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
