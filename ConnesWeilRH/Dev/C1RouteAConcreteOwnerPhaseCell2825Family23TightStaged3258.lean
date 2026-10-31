import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family23TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((752822993943579 : ℝ) / 1000000000000000), reHi := ((752822993943580 : ℝ) / 1000000000000000), imLo := ((658223016757865 : ℝ) / 1000000000000000), imHi := ((658223016757866 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((133484920420347 : ℝ) / 1000000000000000), reHi := ((133484920420352 : ℝ) / 1000000000000000), imLo := ((991050844316460 : ℝ) / 1000000000000000), imHi := ((991050844316465 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((964363552040753 : ℝ) / 1000000000000000), reHi := -((964363552040739 : ℝ) / 1000000000000000), imLo := ((264580686172199 : ℝ) / 1000000000000000), imHi := ((264580686172213 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((859994121009271 : ℝ) / 1000000000000000), reHi := ((859994121009308 : ℝ) / 1000000000000000), imLo := -((510303940636832 : ℝ) / 1000000000000000), imHi := -((510303940636794 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((479179776341028 : ℝ) / 1000000000000000), reHi := ((479179776341133 : ℝ) / 1000000000000000), imLo := -((877716777751118 : ℝ) / 1000000000000000), imHi := -((877716777751012 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((540773483891569 : ℝ) / 1000000000000000), reHi := -((540773483891280 : ℝ) / 1000000000000000), imLo := -((841168258507283 : ℝ) / 1000000000000000), imHi := -((841168258506994 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((415128078240264 : ℝ) / 1000000000000000), reHi := -((415128078239463 : ℝ) / 1000000000000000), imLo := ((909762979383175 : ℝ) / 1000000000000000), imHi := ((909762979383976 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((655337357314820 : ℝ) / 1000000000000000), reHi := -((655337357312695 : ℝ) / 1000000000000000), imLo := -((755336314571615 : ℝ) / 1000000000000000), imHi := -((755336314569490 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((141065896221044 : ℝ) / 1000000000000000), reHi := -((141065896215046 : ℝ) / 1000000000000000), imLo := ((990000208544559 : ℝ) / 1000000000000000), imHi := ((990000208550557 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((960200825855194 : ℝ) / 1000000000000000), reHi := -((960200825841623 : ℝ) / 1000000000000000), imLo := -((279310533356411 : ℝ) / 1000000000000000), imHi := -((279310533342840 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((960200825855194 : ℝ) / 1000000000000000), reHi := -((960200825841623 : ℝ) / 1000000000000000), imLo := -((279310533356411 : ℝ) / 1000000000000000), imHi := -((279310533342840 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family23_3258 : |(capturedModulations2584 23 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_23, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family23_tight_base_mem3258 : (record2680Cell2825Family23TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 23 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family23_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 23 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family23TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_23, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family23_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family23TightStageBox3258 stage).Mem w) : (record2680Cell2825Family23TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family23TightStageBox3258 stage).mul (record2680Cell2825Family23TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family23TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family23_tight_phase_box_mem3258 : (record2680Cell2825Family23TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 23 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family23_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family23_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
