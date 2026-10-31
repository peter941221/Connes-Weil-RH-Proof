import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family21TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((793145990812456 : ℝ) / 1000000000000000), reHi := ((793145990812457 : ℝ) / 1000000000000000), imLo := ((609031556865591 : ℝ) / 1000000000000000), imHi := ((609031556865592 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((258161125483744 : ℝ) / 1000000000000000), reHi := ((258161125483750 : ℝ) / 1000000000000000), imLo := ((966101875212422 : ℝ) / 1000000000000000), imHi := ((966101875212428 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((866705666577938 : ℝ) / 1000000000000000), reHi := -((866705666577920 : ℝ) / 1000000000000000), imLo := ((498819894873587 : ℝ) / 1000000000000000), imHi := ((498819894873605 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((502357424956561 : ℝ) / 1000000000000000), reHi := ((502357424956613 : ℝ) / 1000000000000000), imLo := -((864660058977531 : ℝ) / 1000000000000000), imHi := -((864660058977479 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((495274035182042 : ℝ) / 1000000000000000), reHi := -((495274035181897 : ℝ) / 1000000000000000), imLo := -((868736801381573 : ℝ) / 1000000000000000), imHi := -((868736801381428 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((509407260149329 : ℝ) / 1000000000000000), reHi := -((509407260148931 : ℝ) / 1000000000000000), imLo := ((860525562262387 : ℝ) / 1000000000000000), imHi := ((860525562262785 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((481008486615243 : ℝ) / 1000000000000000), reHi := -((481008486614150 : ℝ) / 1000000000000000), imLo := -((876715937921494 : ℝ) / 1000000000000000), imHi := -((876715937920400 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((537261671610731 : ℝ) / 1000000000000000), reHi := -((537261671607759 : ℝ) / 1000000000000000), imLo := ((843415612979192 : ℝ) / 1000000000000000), imHi := ((843415612982164 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((422699792443317 : ℝ) / 1000000000000000), reHi := -((422699792435108 : ℝ) / 1000000000000000), imLo := -((906269764186775 : ℝ) / 1000000000000000), imHi := -((906269764178565 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((642649770954471 : ℝ) / 1000000000000000), reHi := -((642649770932647 : ℝ) / 1000000000000000), imLo := ((766160082416986 : ℝ) / 1000000000000000), imHi := ((766160082438809 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((642649770954471 : ℝ) / 1000000000000000), reHi := -((642649770932647 : ℝ) / 1000000000000000), imLo := ((766160082416986 : ℝ) / 1000000000000000), imHi := ((766160082438809 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family21_3258 : |(capturedModulations2584 21 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_21, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family21_tight_base_mem3258 : (record2680Cell2825Family21TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 21 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family21_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 21 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family21TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_21, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family21_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family21TightStageBox3258 stage).Mem w) : (record2680Cell2825Family21TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family21TightStageBox3258 stage).mul (record2680Cell2825Family21TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family21TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family21_tight_phase_box_mem3258 : (record2680Cell2825Family21TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 21 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family21_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family21_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
