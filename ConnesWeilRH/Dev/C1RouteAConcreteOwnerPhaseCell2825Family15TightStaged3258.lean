import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family15TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((899793767873192 : ℝ) / 1000000000000000), reHi := ((899793767873193 : ℝ) / 1000000000000000), imLo := ((436315453882353 : ℝ) / 1000000000000000), imHi := ((436315453882354 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((619257649406870 : ℝ) / 1000000000000000), reHi := ((619257649406875 : ℝ) / 1000000000000000), imLo := ((785187852460207 : ℝ) / 1000000000000000), imHi := ((785187852460213 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((233039927302161 : ℝ) / 1000000000000000), reHi := -((233039927302142 : ℝ) / 1000000000000000), imLo := ((972467167714671 : ℝ) / 1000000000000000), imHi := ((972467167714689 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((891384784566043 : ℝ) / 1000000000000000), reHi := -((891384784565996 : ℝ) / 1000000000000000), imLo := -((453247356135941 : ℝ) / 1000000000000000), imHi := -((453247356135892 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((589133668311545 : ℝ) / 1000000000000000), reHi := ((589133668311676 : ℝ) / 1000000000000000), imLo := ((808035593808597 : ℝ) / 1000000000000000), imHi := ((808035593808730 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((305843041723611 : ℝ) / 1000000000000000), reHi := -((305843041723239 : ℝ) / 1000000000000000), imLo := ((952081947013511 : ℝ) / 1000000000000000), imHi := ((952081947013882 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((812920067659223 : ℝ) / 1000000000000000), reHi := -((812920067658286 : ℝ) / 1000000000000000), imLo := -((582375277289728 : ℝ) / 1000000000000000), imHi := -((582375277288790 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((321678072803263 : ℝ) / 1000000000000000), reHi := ((321678072805882 : ℝ) / 1000000000000000), imLo := ((946849099632231 : ℝ) / 1000000000000000), imHi := ((946849099634850 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((793046434956906 : ℝ) / 1000000000000000), reHi := -((793046434950259 : ℝ) / 1000000000000000), imLo := ((609161187210400 : ℝ) / 1000000000000000), imHi := ((609161187217048 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((257845295975630 : ℝ) / 1000000000000000), reHi := ((257845295994276 : ℝ) / 1000000000000000), imLo := -((966186215673194 : ℝ) / 1000000000000000), imHi := -((966186215654549 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((257845295975630 : ℝ) / 1000000000000000), reHi := ((257845295994276 : ℝ) / 1000000000000000), imLo := -((966186215673194 : ℝ) / 1000000000000000), imHi := -((966186215654549 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family15_3258 : |(capturedModulations2584 15 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_15, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family15_tight_base_mem3258 : (record2680Cell2825Family15TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 15 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family15_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 15 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family15TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_15, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family15_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family15TightStageBox3258 stage).Mem w) : (record2680Cell2825Family15TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family15TightStageBox3258 stage).mul (record2680Cell2825Family15TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family15TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family15_tight_phase_box_mem3258 : (record2680Cell2825Family15TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 15 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family15_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family15_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
