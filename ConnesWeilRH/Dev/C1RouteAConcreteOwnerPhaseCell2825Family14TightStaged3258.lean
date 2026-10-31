import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family14TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((915225855473450 : ℝ) / 1000000000000000), reHi := ((915225855473451 : ℝ) / 1000000000000000), imLo := ((402941228311141 : ℝ) / 1000000000000000), imHi := ((402941228311142 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((675276733054215 : ℝ) / 1000000000000000), reHi := ((675276733054221 : ℝ) / 1000000000000000), imLo := ((737564460773172 : ℝ) / 1000000000000000), imHi := ((737564460773178 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((88002667591257 : ℝ) / 1000000000000000), reHi := -((88002667591237 : ℝ) / 1000000000000000), imLo := ((996120238975601 : ℝ) / 1000000000000000), imHi := ((996120238975621 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((984511060993676 : ℝ) / 1000000000000000), reHi := -((984511060993630 : ℝ) / 1000000000000000), imLo := -((175322476542992 : ℝ) / 1000000000000000), imHi := -((175322476542945 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((938524058437634 : ℝ) / 1000000000000000), reHi := ((938524058437744 : ℝ) / 1000000000000000), imLo := ((345213834794650 : ℝ) / 1000000000000000), imHi := ((345213834794761 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((761654816532541 : ℝ) / 1000000000000000), reHi := ((761654816532827 : ℝ) / 1000000000000000), imLo := ((647982978520586 : ℝ) / 1000000000000000), imHi := ((647982978520873 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((160236119094435 : ℝ) / 1000000000000000), reHi := ((160236119095246 : ℝ) / 1000000000000000), imLo := ((987078713242611 : ℝ) / 1000000000000000), imHi := ((987078713243422 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((948648772275845 : ℝ) / 1000000000000000), reHi := -((948648772273981 : ℝ) / 1000000000000000), imLo := ((316331324501448 : ℝ) / 1000000000000000), imHi := ((316331324503312 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((799868986274910 : ℝ) / 1000000000000000), reHi := ((799868986279629 : ℝ) / 1000000000000000), imLo := -((600174645244919 : ℝ) / 1000000000000000), imHi := -((600174645240200 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((279580790409586 : ℝ) / 1000000000000000), reHi := ((279580790422803 : ℝ) / 1000000000000000), imLo := -((960122170165580 : ℝ) / 1000000000000000), imHi := -((960122170152364 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((279580790409586 : ℝ) / 1000000000000000), reHi := ((279580790422803 : ℝ) / 1000000000000000), imLo := -((960122170165580 : ℝ) / 1000000000000000), imHi := -((960122170152364 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family14_3258 : |(capturedModulations2584 14 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_14, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family14_tight_base_mem3258 : (record2680Cell2825Family14TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 14 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family14_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 14 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family14TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_14, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family14_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family14TightStageBox3258 stage).Mem w) : (record2680Cell2825Family14TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family14TightStageBox3258 stage).mul (record2680Cell2825Family14TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family14TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family14_tight_phase_box_mem3258 : (record2680Cell2825Family14TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 14 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family14_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family14_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
