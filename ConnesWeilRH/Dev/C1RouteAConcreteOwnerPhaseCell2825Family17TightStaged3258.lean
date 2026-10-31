import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family17TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((862962813068935 : ℝ) / 1000000000000000), reHi := ((862962813068936 : ℝ) / 1000000000000000), imLo := ((505267437363769 : ℝ) / 1000000000000000), imHi := ((505267437363770 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((489409633479697 : ℝ) / 1000000000000000), reHi := ((489409633479703 : ℝ) / 1000000000000000), imLo := ((872054018199139 : ℝ) / 1000000000000000), imHi := ((872054018199144 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((520956421314543 : ℝ) / 1000000000000000), reHi := -((520956421314526 : ℝ) / 1000000000000000), imLo := ((853583274842674 : ℝ) / 1000000000000000), imHi := ((853583274842692 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((457208814182338 : ℝ) / 1000000000000000), reHi := -((457208814182287 : ℝ) / 1000000000000000), imLo := -((889359376311995 : ℝ) / 1000000000000000), imHi := -((889359376311944 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((581920200468089 : ℝ) / 1000000000000000), reHi := -((581920200467949 : ℝ) / 1000000000000000), imLo := ((813245891650963 : ℝ) / 1000000000000000), imHi := ((813245891651103 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((322737760574741 : ℝ) / 1000000000000000), reHi := -((322737760574347 : ℝ) / 1000000000000000), imLo := -((946488424598921 : ℝ) / 1000000000000000), imHi := -((946488424598527 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((791680675799204 : ℝ) / 1000000000000000), reHi := -((791680675798201 : ℝ) / 1000000000000000), imLo := ((610935109128939 : ℝ) / 1000000000000000), imHi := ((610935109129942 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((253516584864681 : ℝ) / 1000000000000000), reHi := ((253516584867497 : ℝ) / 1000000000000000), imLo := -((967331040130907 : ℝ) / 1000000000000000), imHi := -((967331040128091 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((871458682399293 : ℝ) / 1000000000000000), reHi := -((871458682392414 : ℝ) / 1000000000000000), imLo := -((490468923460624 : ℝ) / 1000000000000000), imHi := -((490468923453745 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((518880470236497 : ℝ) / 1000000000000000), reHi := ((518880470255238 : ℝ) / 1000000000000000), imLo := ((854846803574851 : ℝ) / 1000000000000000), imHi := ((854846803593592 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((518880470236497 : ℝ) / 1000000000000000), reHi := ((518880470255238 : ℝ) / 1000000000000000), imLo := ((854846803574851 : ℝ) / 1000000000000000), imHi := ((854846803593592 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family17_3258 : |(capturedModulations2584 17 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_17, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family17_tight_base_mem3258 : (record2680Cell2825Family17TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 17 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family17_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 17 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family17TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_17, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family17_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family17TightStageBox3258 stage).Mem w) : (record2680Cell2825Family17TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family17TightStageBox3258 stage).mul (record2680Cell2825Family17TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family17TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family17_tight_phase_box_mem3258 : (record2680Cell2825Family17TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 17 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family17_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family17_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
