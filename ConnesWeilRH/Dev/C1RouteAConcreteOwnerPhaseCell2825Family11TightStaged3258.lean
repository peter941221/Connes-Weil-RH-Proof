import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family11TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((953751992392856 : ℝ) / 1000000000000000), reHi := ((953751992392857 : ℝ) / 1000000000000000), imLo := ((300594639018488 : ℝ) / 1000000000000000), imHi := ((300594639018489 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((819285725986685 : ℝ) / 1000000000000000), reHi := ((819285725986691 : ℝ) / 1000000000000000), imLo := ((573385471732987 : ℝ) / 1000000000000000), imHi := ((573385471732992 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((342458201611062 : ℝ) / 1000000000000000), reHi := ((342458201611081 : ℝ) / 1000000000000000), imLo := ((939533064957955 : ℝ) / 1000000000000000), imHi := ((939533064957973 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((765444760298641 : ℝ) / 1000000000000000), reHi := -((765444760298592 : ℝ) / 1000000000000000), imLo := ((643501607559259 : ℝ) / 1000000000000000), imHi := ((643501607559310 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((171811362137151 : ℝ) / 1000000000000000), reHi := ((171811362137295 : ℝ) / 1000000000000000), imLo := -((985129867500054 : ℝ) / 1000000000000000), imHi := -((985129867499910 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((940961711681252 : ℝ) / 1000000000000000), reHi := -((940961711680916 : ℝ) / 1000000000000000), imLo := -((338513008834636 : ℝ) / 1000000000000000), imHi := -((338513008834300 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((770817885699200 : ℝ) / 1000000000000000), reHi := ((770817885700062 : ℝ) / 1000000000000000), imLo := ((637055560437958 : ℝ) / 1000000000000000), imHi := ((637055560438821 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((188320425827763 : ℝ) / 1000000000000000), reHi := ((188320425830195 : ℝ) / 1000000000000000), imLo := ((982107640339410 : ℝ) / 1000000000000000), imHi := ((982107640341842 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((929070834433872 : ℝ) / 1000000000000000), reHi := -((929070834428176 : ℝ) / 1000000000000000), imLo := ((369901858074833 : ℝ) / 1000000000000000), imHi := ((369901858080529 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((726345230773638 : ℝ) / 1000000000000000), reHi := ((726345230788439 : ℝ) / 1000000000000000), imLo := -((687330055891035 : ℝ) / 1000000000000000), imHi := -((687330055876234 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((726345230773638 : ℝ) / 1000000000000000), reHi := ((726345230788439 : ℝ) / 1000000000000000), imLo := -((687330055891035 : ℝ) / 1000000000000000), imHi := -((687330055876234 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family11_3258 : |(capturedModulations2584 11 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_11, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family11_tight_base_mem3258 : (record2680Cell2825Family11TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 11 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family11_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 11 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family11TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_11, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family11_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family11TightStageBox3258 stage).Mem w) : (record2680Cell2825Family11TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family11TightStageBox3258 stage).mul (record2680Cell2825Family11TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family11TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family11_tight_phase_box_mem3258 : (record2680Cell2825Family11TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 11 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family11_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family11_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
