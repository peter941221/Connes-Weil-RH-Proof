import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family28TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((659065340877815 : ℝ) / 1000000000000000), reHi := ((659065340877816 : ℝ) / 1000000000000000), imLo := ((752085684249879 : ℝ) / 1000000000000000), imHi := ((752085684249880 : ℝ) / 1000000000000000) }
  | 1 => { reLo := -((131265752907221 : ℝ) / 1000000000000000), reHi := -((131265752907215 : ℝ) / 1000000000000000), imLo := ((991347215718941 : ℝ) / 1000000000000000), imHi := ((991347215718947 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((965538604227412 : ℝ) / 1000000000000000), reHi := -((965538604227396 : ℝ) / 1000000000000000), imLo := -((260259877327651 : ℝ) / 1000000000000000), imHi := -((260259877327635 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((864529592506783 : ℝ) / 1000000000000000), reHi := ((864529592506825 : ℝ) / 1000000000000000), imLo := ((502581917382635 : ℝ) / 1000000000000000), imHi := ((502581917382677 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((494822832639895 : ℝ) / 1000000000000000), reHi := ((494822832640013 : ℝ) / 1000000000000000), imLo := ((868993880472173 : ℝ) / 1000000000000000), imHi := ((868993880472291 : ℝ) / 1000000000000000) }
  | 5 => { reLo := -((510300728596522 : ℝ) / 1000000000000000), reHi := -((510300728596198 : ℝ) / 1000000000000000), imLo := ((859996026963949 : ℝ) / 1000000000000000), imHi := ((859996026964273 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((479186332788526 : ℝ) / 1000000000000000), reHi := -((479186332787635 : ℝ) / 1000000000000000), imLo := -((877713198299967 : ℝ) / 1000000000000000), imHi := -((877713198299076 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((540760916939497 : ℝ) / 1000000000000000), reHi := -((540760916937076 : ℝ) / 1000000000000000), imLo := ((841176337464480 : ℝ) / 1000000000000000), imHi := ((841176337466900 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((415155261427602 : ℝ) / 1000000000000000), reHi := -((415155261420910 : ℝ) / 1000000000000000), imLo := -((909750575112819 : ℝ) / 1000000000000000), imHi := -((909750575106126 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((655292217832642 : ℝ) / 1000000000000000), reHi := -((655292217814905 : ℝ) / 1000000000000000), imLo := ((755375475672012 : ℝ) / 1000000000000000), imHi := ((755375475689749 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((655292217832642 : ℝ) / 1000000000000000), reHi := -((655292217814905 : ℝ) / 1000000000000000), imLo := ((755375475672012 : ℝ) / 1000000000000000), imHi := ((755375475689749 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family28_3258 : |(capturedModulations2584 28 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_28, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family28_tight_base_mem3258 : (record2680Cell2825Family28TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 28 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family28_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 28 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family28TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_28, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family28_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family28TightStageBox3258 stage).Mem w) : (record2680Cell2825Family28TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family28TightStageBox3258 stage).mul (record2680Cell2825Family28TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family28TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family28_tight_phase_box_mem3258 : (record2680Cell2825Family28TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 28 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family28_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family28_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
