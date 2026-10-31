import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family12TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((944176648846841 : ℝ) / 1000000000000000), reHi := ((944176648846842 : ℝ) / 1000000000000000), imLo := ((329439608687766 : ℝ) / 1000000000000000), imHi := ((329439608687767 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((782939088455300 : ℝ) / 1000000000000000), reHi := ((782939088455306 : ℝ) / 1000000000000000), imLo := ((622098371456458 : ℝ) / 1000000000000000), imHi := ((622098371456463 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((225987232462431 : ℝ) / 1000000000000000), reHi := ((225987232462450 : ℝ) / 1000000000000000), imLo := ((974130263755290 : ℝ) / 1000000000000000), imHi := ((974130263755308 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((897859541527959 : ℝ) / 1000000000000000), reHi := -((897859541527912 : ℝ) / 1000000000000000), imLo := ((440282004727910 : ℝ) / 1000000000000000), imHi := ((440282004727959 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((612303512625440 : ℝ) / 1000000000000000), reHi := ((612303512625571 : ℝ) / 1000000000000000), imLo := -((790622797816113 : ℝ) / 1000000000000000), imHi := -((790622797815981 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((250168816853127 : ℝ) / 1000000000000000), reHi := -((250168816852755 : ℝ) / 1000000000000000), imLo := -((968202232529327 : ℝ) / 1000000000000000), imHi := -((968202232528955 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((874831126149267 : ℝ) / 1000000000000000), reHi := -((874831126148358 : ℝ) / 1000000000000000), imLo := ((484428013971928 : ℝ) / 1000000000000000), imHi := ((484428013972837 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((530658998556336 : ℝ) / 1000000000000000), reHi := ((530658998558810 : ℝ) / 1000000000000000), imLo := -((847585410004221 : ℝ) / 1000000000000000), imHi := -((847585410001747 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((436802054503211 : ℝ) / 1000000000000000), reHi := -((436802054496389 : ℝ) / 1000000000000000), imLo := -((899557649731798 : ℝ) / 1000000000000000), imHi := -((899557649724976 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((618407930378731 : ℝ) / 1000000000000000), reHi := -((618407930360495 : ℝ) / 1000000000000000), imLo := ((785857259075624 : ℝ) / 1000000000000000), imHi := ((785857259093860 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((618407930378731 : ℝ) / 1000000000000000), reHi := -((618407930360495 : ℝ) / 1000000000000000), imLo := ((785857259075624 : ℝ) / 1000000000000000), imHi := ((785857259093860 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family12_3258 : |(capturedModulations2584 12 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_12, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family12_tight_base_mem3258 : (record2680Cell2825Family12TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 12 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family12_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 12 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family12TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_12, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family12_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family12TightStageBox3258 stage).Mem w) : (record2680Cell2825Family12TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family12TightStageBox3258 stage).mul (record2680Cell2825Family12TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family12TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family12_tight_phase_box_mem3258 : (record2680Cell2825Family12TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 12 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family12_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family12_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
