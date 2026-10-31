import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family10TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((962160971088168 : ℝ) / 1000000000000000), reHi := ((962160971088169 : ℝ) / 1000000000000000), imLo := ((272481679594560 : ℝ) / 1000000000000000), imHi := ((272481679594561 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((851507468570652 : ℝ) / 1000000000000000), reHi := ((851507468570657 : ℝ) / 1000000000000000), imLo := ((524342474884872 : ℝ) / 1000000000000000), imHi := ((524342474884878 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((450129938063200 : ℝ) / 1000000000000000), reHi := ((450129938063217 : ℝ) / 1000000000000000), imLo := ((892963066906575 : ℝ) / 1000000000000000), imHi := ((892963066906593 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((594766077718450 : ℝ) / 1000000000000000), reHi := -((594766077718399 : ℝ) / 1000000000000000), imLo := ((803898819998762 : ℝ) / 1000000000000000), imHi := ((803898819998811 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((292506625590954 : ℝ) / 1000000000000000), reHi := -((292506625590811 : ℝ) / 1000000000000000), imLo := -((956263496106368 : ℝ) / 1000000000000000), imHi := -((956263496106224 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((828879747971052 : ℝ) / 1000000000000000), reHi := -((828879747970690 : ℝ) / 1000000000000000), imLo := ((559426816843405 : ℝ) / 1000000000000000), imHi := ((559426816843766 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((374083273192005 : ℝ) / 1000000000000000), reHi := ((374083273193012 : ℝ) / 1000000000000000), imLo := -((927395117907419 : ℝ) / 1000000000000000), imHi := -((927395117906412 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((720123409436473 : ℝ) / 1000000000000000), reHi := -((720123409433849 : ℝ) / 1000000000000000), imLo := -((693846002500055 : ℝ) / 1000000000000000), imHi := -((693846002497431 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((37155449629323 : ℝ) / 1000000000000000), reHi := ((37155449636747 : ℝ) / 1000000000000000), imLo := ((999309497880992 : ℝ) / 1000000000000000), imHi := ((999309497888416 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((997238945132842 : ℝ) / 1000000000000000), reHi := -((997238945117450 : ℝ) / 1000000000000000), imLo := ((74259587425241 : ℝ) / 1000000000000000), imHi := ((74259587440633 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((997238945132842 : ℝ) / 1000000000000000), reHi := -((997238945117450 : ℝ) / 1000000000000000), imLo := ((74259587425241 : ℝ) / 1000000000000000), imHi := ((74259587440633 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family10_3258 : |(capturedModulations2584 10 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family10_tight_base_mem3258 : (record2680Cell2825Family10TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 10 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family10_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 10 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family10TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family10_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family10TightStageBox3258 stage).Mem w) : (record2680Cell2825Family10TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family10TightStageBox3258 stage).mul (record2680Cell2825Family10TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family10TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family10_tight_phase_box_mem3258 : (record2680Cell2825Family10TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 10 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family10_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family10_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
