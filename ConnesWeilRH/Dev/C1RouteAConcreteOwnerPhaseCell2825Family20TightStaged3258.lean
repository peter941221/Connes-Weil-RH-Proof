import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family20TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((812230033432805 : ℝ) / 1000000000000000), reHi := ((812230033432806 : ℝ) / 1000000000000000), imLo := ((583337271901721 : ℝ) / 1000000000000000), imHi := ((583337271901722 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((319435254420511 : ℝ) / 1000000000000000), reHi := ((319435254420516 : ℝ) / 1000000000000000), imLo := ((947608103718671 : ℝ) / 1000000000000000), imHi := ((947608103718676 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((795922236466610 : ℝ) / 1000000000000000), reHi := -((795922236466594 : ℝ) / 1000000000000000), imLo := ((605398871404622 : ℝ) / 1000000000000000), imHi := ((605398871404637 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((266984413003975 : ℝ) / 1000000000000000), reHi := ((266984413004022 : ℝ) / 1000000000000000), imLo := -((963700847365482 : ℝ) / 1000000000000000), imHi := -((963700847365436 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((857438646425872 : ℝ) / 1000000000000000), reHi := -((857438646425756 : ℝ) / 1000000000000000), imLo := -((514586210090705 : ℝ) / 1000000000000000), imHi := -((514586210090587 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((470402064768916 : ℝ) / 1000000000000000), reHi := ((470402064769239 : ℝ) / 1000000000000000), imLo := ((882452206898864 : ℝ) / 1000000000000000), imHi := ((882452206899188 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((557443794922389 : ℝ) / 1000000000000000), reHi := -((557443794921511 : ℝ) / 1000000000000000), imLo := ((830214680370223 : ℝ) / 1000000000000000), imHi := ((830214680371101 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((378512831007195 : ℝ) / 1000000000000000), reHi := -((378512831004756 : ℝ) / 1000000000000000), imLo := -((925596044052691 : ℝ) / 1000000000000000), imHi := -((925596044050251 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((713456073530758 : ℝ) / 1000000000000000), reHi := -((713456073524391 : ℝ) / 1000000000000000), imLo := ((700699958000525 : ℝ) / 1000000000000000), imHi := ((700699958006890 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((18039137697982 : ℝ) / 1000000000000000), reHi := ((18039137715990 : ℝ) / 1000000000000000), imLo := -((999837281525527 : ℝ) / 1000000000000000), imHi := -((999837281507519 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((18039137697982 : ℝ) / 1000000000000000), reHi := ((18039137715990 : ℝ) / 1000000000000000), imLo := -((999837281525527 : ℝ) / 1000000000000000), imHi := -((999837281507519 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family20_3258 : |(capturedModulations2584 20 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_20, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family20_tight_base_mem3258 : (record2680Cell2825Family20TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 20 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family20_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 20 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family20TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_20, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family20_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family20TightStageBox3258 stage).Mem w) : (record2680Cell2825Family20TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family20TightStageBox3258 stage).mul (record2680Cell2825Family20TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family20TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family20_tight_phase_box_mem3258 : (record2680Cell2825Family20TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 20 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family20_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family20_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
