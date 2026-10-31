import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family27TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((670932794729536 : ℝ) / 1000000000000000), reHi := ((670932794729537 : ℝ) / 1000000000000000), imLo := ((741518162256605 : ℝ) / 1000000000000000), imHi := ((741518162256606 : ℝ) / 1000000000000000) }
  | 1 => { reLo := -((99698369912830 : ℝ) / 1000000000000000), reHi := -((99698369912824 : ℝ) / 1000000000000000), imLo := ((995017705891066 : ℝ) / 1000000000000000), imHi := ((995017705891071 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((980120470073457 : ℝ) / 1000000000000000), reHi := -((980120470073443 : ℝ) / 1000000000000000), imLo := -((198403286623488 : ℝ) / 1000000000000000), imHi := -((198403286623473 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((921272271713984 : ℝ) / 1000000000000000), reHi := ((921272271714020 : ℝ) / 1000000000000000), imLo := ((388918245099027 : ℝ) / 1000000000000000), imHi := ((388918245099065 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((697485197258107 : ℝ) / 1000000000000000), reHi := ((697485197258206 : ℝ) / 1000000000000000), imLo := ((716599190346792 : ℝ) / 1000000000000000), imHi := ((716599190346893 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((27028799211644 : ℝ) / 1000000000000000), reHi := -((27028799211358 : ℝ) / 1000000000000000), imLo := ((999634655268063 : ℝ) / 1000000000000000), imHi := ((999634655268348 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((998538888026662 : ℝ) / 1000000000000000), reHi := -((998538888026074 : ℝ) / 1000000000000000), imLo := -((54037848764500 : ℝ) / 1000000000000000), imHi := -((54037848763910 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((994159821801252 : ℝ) / 1000000000000000), reHi := ((994159821802493 : ℝ) / 1000000000000000), imLo := ((107917786832070 : ℝ) / 1000000000000000), imHi := ((107917786833315 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((976707502568895 : ℝ) / 1000000000000000), reHi := ((976707502571634 : ℝ) / 1000000000000000), imLo := ((214575055452311 : ℝ) / 1000000000000000), imHi := ((214575055455057 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((907915091150826 : ℝ) / 1000000000000000), reHi := ((907915091157358 : ℝ) / 1000000000000000), imLo := ((419154133048816 : ℝ) / 1000000000000000), imHi := ((419154133055359 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((907915091150826 : ℝ) / 1000000000000000), reHi := ((907915091157358 : ℝ) / 1000000000000000), imLo := ((419154133048816 : ℝ) / 1000000000000000), imHi := ((419154133055359 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family27_3258 : |(capturedModulations2584 27 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_27, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family27_tight_base_mem3258 : (record2680Cell2825Family27TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 27 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family27_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 27 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family27TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_27, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family27_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family27TightStageBox3258 stage).Mem w) : (record2680Cell2825Family27TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family27TightStageBox3258 stage).mul (record2680Cell2825Family27TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family27TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family27_tight_phase_box_mem3258 : (record2680Cell2825Family27TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 27 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family27_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family27_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
